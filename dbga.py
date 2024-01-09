##########################################################################
#                                                                        #
#      May you do good and not evil                                      #
#      May you find forgiveness for yourself and forgive others          #
#      May you share freely, never taking more than you give.            #
#                                                                        #
##########################################################################

from __future__ import annotations

import os
import re
import sys
import json
import shutil
import sqlite3
import pandas as pd
from glob import glob
from typing import Union, Callable
from datetime import datetime as dt
from collections import defaultdict as dd
from traceback import format_exception as fe

# Remember to update this for tracking purposes!
__version__ = '1.0.3'

# ToDo flags: [_]

##########################################################################

EXT                 = '.data302'                # File extension to identify files related to the answer key and submission files
EXT_REPORT          =  '.summary.txt'           # File extension for per student output
KEY_Q               = 'q'                       
KEY_SQL             = 'sql'                     # To identify sql statements in dictionaries
KEY_PARAMS          = 'params'                  # To identify sql statement parameters in dictionaries
KEY_PARAM_FLAGS     = 'param_flags'             # To identify sql parameter rules defined by the professor for each question
KEY_SETUP           = 'setup'                   # To identify any setup (create view) statements in dictionaries
KEY_RESULTS         = 'results'                 
KEY_SORTED_ROWS     = 'sorted_rows'

# Names, etc. used in output files
KEY_CORRECT         = 'Output matches key'
KEY_SUMMARY         = 'Output'
KEY_NROWS           = 'Number of records returned'
KEY_RUNTIME         = 'Runtime (secs)'
FLAG_MISSING        = float('nan')
KEY_UNUSED          = 'Unrecognized key(s) in submission'
HEADER_LINE         = ''.join(['-']*79)

# Parameter rules - We do not want people using parameters instead of including the logic in their queries, when applicable
NO_HARD_PARAMS      = 1           # Hard params = values hardcoded in queries, e.g. "WHERE value = 123"
NO_SOFT_PARAMS      = 2           # Soft params = parameters passed into queries, e.g. using ? or :param_name, etc.
NO_PARAMS           = NO_HARD_PARAMS + NO_SOFT_PARAMS

# Various other settings related to display and comparison
MAX_ROWS_IN_SHORT_DF  = 10        # How many rows in the short version of a dataframe
MAX_STR_LEN           = 20        # Truncate long strings when converting dataframe to a string
ROUNDING_PREC         = 2         # Number of decimal places when rounding floats
NAN_REPR              = 'NaN'     # Text to use, to avoid comparing the floats NaN == NaN

# Some settings for debugging
DBG_CLEANUP_TEMP_DBS    = True      # Set to False to NOT cleanup temp databases (i.e., the clones for each submission)
DBG_ENFORCE_PARAM_RULES = True      # Set to False to ignore param_flags when checking Submissions
DBG_TRACEBACK_LIMIT     = None      # Set to an integer to only print that many entries from tracebacks, or None to print all.

DBG_SETTINGS = {'Clean up temporary dbs  '   : DBG_CLEANUP_TEMP_DBS,
                'Enforce parameter rules '   : DBG_ENFORCE_PARAM_RULES,
                'Traceback limit         '   : DBG_TRACEBACK_LIMIT
               }
##########################################################################

# Helpers
#region
def format_time_interval(t0:dt, 
                         t1:dt
                         ) -> float:
    return (t1-t0).total_seconds()

def print_and_wait(string:str)->None:
    '''
    Print without an endline, call a regular print after to finish line.
    '''
    sys.stdout.write(string)
    sys.stdout.flush()
    return

def get_settings() -> str:
    '''
    Get DBG_SETTINGS as formatted string
    '''
    settings = ''
    for key, value in DBG_SETTINGS.items():
        settings += '\t' + key + '= ' + str(value) + '\n'
    return settings

def timestamp() -> str:
    return str(dt.now()).replace(':', '.').replace(' ', '-')

def unhandled(e:Exception) -> None:
    '''
    Used to avoid unhandled exceptions, but where we are not really "handling" the exception.
    Not to be used in actual deployments.
    '''
    print('---WARNING FOR THE DEVELOPER---')
    print('Unhandled exception in ' + sys._getframe().f_back.f_code.co_name)
    print('\n')
    for line in fe(e):
        print(line)
    print('\n')
    return
#endregion

#region
class TBD():
    '''
    Placeholder class to use for type hinting if we haven't decided on a type yet. 
    Should not be used in actual deployments.
    '''
    pass
##########################################################################
class RowLimitException(Exception):
    '''
    The RowLimitException should be raised when a query returns "far too many" rows 
    (i.e., greater than DFLT_QUERY_LIMIT, unless overridden when calling DB.run_query()) 
    This is most likely to occur when a user submits a query with one or more unintentional cartesian joins.

    If a query is expected to return more than DFLT_QUERY_LIMIT rows, then either change the default value, or override when calling DB.run_query().

    Keep in mind that memory is finite!
    '''
    pass
class SQLFormatException(Exception):
    '''
    SQLFormatException should be raised with the query appears malformed in some way, 
    e.g. unterminated block comments, missing the semicolon...
    '''
    pass
class SQLActionException(Exception):

    '''
    To be raised when a flagged word is found in a query, i.e. action queries from other users that we do not want to run locally.
    This is primarily meant to be raised if users try to alter the structure of the database with the exception of creating or dropping views.
    '''
    pass
class SQLNotFoundException(Exception):
    '''
    To be raised when the SQL for a question is not found in a Submission.
    '''
    pass
class HardcodedParameterException(Exception):
    '''
    To be raised when a Submission contains hardcoded parameters and the key says these are not allowed for a particular question.
    '''
    pass
class JSONFormatException(Exception):
    '''
    To be raised if anything goes wrong loading a Submission json.
    '''
    pass
class DBCloneException(Exception):
    '''
    To be raised if anything goes wrong cloning a database.
    '''
    pass
##########################################################################
#endregion

class Prof:
    def __init__(self, 
                 path_db:str,
                 verbose:bool=True
                 ):
        
        settings = 'Settings:\n' + get_settings() + '\n'
        if verbose:
            print(settings)
        
        self.log        = settings  # String to store the log
        self.key_raw    = {}        # A dictionary created from a json (.DATA302) file
        self.key        = {}        # The key once processed containing results
        self.setups     = []        # Obtained from the key_raw, optional. Designed to store code to create views.
        self.path_db    = path_db
        self.db         = DB(path_db)
        return
    
    def grade_all(self, 
                  path_submissions:str,
                  path_out:str,
                  clear_previous_output:bool = True,
                  verbose:bool = False
                  ) -> TBD:
        
        # Initialize grade summary sheet
        self.grades = {}

        # Initialize list of runtimes
        self.runtimes = []

        # Get submission files
        pattern = (path_submissions + '/*' + EXT)
        self.submission_files = glob(pattern)
        # Sort
        self.submission_files.sort()
        self.submissions = {}

        # Ensure output directory exists
        if not os.path.exists(path_out):
            os.mkdir(path_out)

        # Clear previous output
        if clear_previous_output:
            [os.remove(f) for f in glob(path_out + '*')]

        for file in self.submission_files:
            t0 = dt.now()
            uname = self.grade_one_submission(file, path_out, verbose)
            runtime = format_time_interval(t0, dt.now())
            
            print('Runtime:', runtime)
            self.log += 'Runtime: ' + str(runtime) + '\n'
            self.runtimes.append([uname, runtime])
        
        # Log sorted runtimes
        self.runtimes = sorted(self.runtimes, 
                               key=lambda x: x[1],
                               reverse=True
                               )
        self.log += HEADER_LINE + '\n'
        self.log += '\nRuntimes:\n'
        for x in self.runtimes:
            self.log += x[0].ljust(20) + str(x[1]) + '\n'

        # Output the grade sheet
        self.grades_df = pd.DataFrame.from_dict(self.grades, orient='index')
        self.grades_df.to_csv(path_out + '/_grades.csv', na_rep='NaN')

        # Output the log
        with open(path_out + '_log.txt', 'w') as f:
            f.write(self.log)
        return

    def grade_one_submission(self, 
                             path_submission:str,
                             path_out:str,
                             verbose = False
                             ) -> str: # Return the user name
        
        print(HEADER_LINE, '\n')
        self.log += HEADER_LINE + '\n'
    
        s = Submission(self.path_db, 
                       path_submission, 
                       verbose=verbose
                       )
        self.submissions[s.uname] = s
        self.grades[s.uname] = {}

        # Always print user name
        status = 'Grading submission for: ' + s.uname + '\n'
        print(status)
        self.log += status

        # For each query in the key...
        for q_id in self.key.keys():
            s.report_data[q_id] = {}
            try:
                t0 = dt.now()
                correct, summary, num_rows = self.grade_one_question(s, q_id)
                runtime = format_time_interval(t0, dt.now())
            except Exception as e:
                summary = ''.join(fe(e, limit=DBG_TRACEBACK_LIMIT))
                # Print error info if verbose
                if verbose:
                    print('Error in', q_id, ':\n')
                    print(summary)
                correct = FLAG_MISSING
                num_rows = FLAG_MISSING
                runtime = FLAG_MISSING
            finally:
                # Add details to student report
                s.report_data[q_id][KEY_SUMMARY] = summary
                s.report_data[q_id][KEY_NROWS] = num_rows
                # [_] Also report number of rows from key?
                s.report_data[q_id][KEY_CORRECT] = correct
                s.report_data[q_id][KEY_RUNTIME] = runtime

                # Add grade to gradesheet
                self.grades[s.uname][q_id] = correct

        # Always print grade info
        total_correct = sum([x for x in self.grades[s.uname].values() if type(x) == bool])
        num_questions = len(self.grades[s.uname])
        status = 'Minimum grade: ' + str(total_correct) + '/' + str(num_questions) + '\n'
        print(status)
        self.log += status

        # Cleanup temp db
        s.cleanup()

        # Output report
        path_report = (path_out + '/' + s.uname + EXT_REPORT).replace('//', '/')
        s.write_report(path_report)
        self.log += 'Report saved to: ' + path_report + '\n'
        return s.uname
    
    def grade_one_question(self, 
                           s:Submission, 
                           q_id:str
                           ) -> tuple[Union[bool, float], 
                                      str,
                                      int
                                      ]:
        try:
            # Get the parameter settings
            param_flags = self.key_raw[q_id][KEY_PARAM_FLAGS]

            # [_] Remove? # Get the results rows from the key
            #key = self.key[q_id][KEY_ROWS]

            # Get the Submission SQL
            sql, params = s.get_sql(q_id)

            # Add to the report data
            s.report_data[q_id][KEY_SQL] = sql
            s.report_data[q_id][KEY_PARAMS] = params

            # Prepare Query object
            query = Query(sql, params)

            # Do parameter checks
            if DBG_ENFORCE_PARAM_RULES:
                if (param_flags & NO_HARD_PARAMS):
                    if not(query.no_hard_params()):
                        raise HardcodedParameterException(str(q_id) + ' appears to contain hardcoded parameter(s), which are not allowed for this question.')
                if (param_flags & NO_SOFT_PARAMS):
                    if (params is not None):
                        s.report_data[q_id][KEY_PARAMS + '_note'] = 'No parameters allowed, setting params to None. Expect an error.'
                        query.params = None

            # Run the query
            results = s.db.run_query(query=query)

            # Get the total number of rows returned
            num_rows = len(results.rows)

            # Compare the sorted results to the key
            correct = self.key[q_id][KEY_RESULTS] == results

            # Summarize the raw output (i.e., no sorting)
            summary = results.as_df_short_string()

        except Exception as e:
            # Do not handle here - pass back to the calling function
            raise e
        
            #summary = fe(e)
            #print('Error in', str(q_id) + '. Details:', '\n')
            #for line in summary:
            #    print(line)
            #correct = FLAG_MISSING
            #summary = ''.join(summary)
            #num_rows = FLAG_MISSING
        return correct, summary, num_rows
    
    def make_key(self, 
                 path_key:str
                 ) -> None:
        '''Build the answer key...'''
        with open(path_key, 'r') as f:
            self.key_raw = json.load(f)

        try:
            # Run any setup queries
            if KEY_SETUP in self.key_raw:
                self.setups = self.key_raw[KEY_SETUP]
                for sql in self.setups:
                    self.db.run_query(sql)

            # For each item in the key...
            for q_id, q_elements in self.key_raw.items():
                # Is this q_id like q1, q2, etc?
                if re.match(KEY_Q + '\d(\d)?$', q_id) is not None:
                    # Create a new entry in the key
                    self.key[q_id] = {}

                    # Verify param_flags exist
                    if KEY_PARAM_FLAGS not in q_elements:
                        raise ValueError('Key for ' + str(q_id) + ' missing ' + KEY_PARAM_FLAGS)
                    
                    # Save the sql statement
                    self.key[q_id][KEY_SQL] = q_elements[KEY_SQL]
                    
                    # Save the parameters, if any
                    if KEY_PARAMS in q_elements:
                        self.key[q_id][KEY_PARAMS] = q_elements[KEY_PARAMS]
                    else:
                        self.key[q_id][KEY_PARAMS] = None

                    # Store the results as a Results object
                    self.key[q_id][KEY_RESULTS] = self.db.run_query(self.key[q_id][KEY_SQL],
                                                                    self.key[q_id][KEY_PARAMS]
                                                                    )
        except Exception as e:
            print('Error building key!')
            for line in fe(e, limit=DBG_TRACEBACK_LIMIT):
                print(line)
        return
    
    def key_as_dataframe(self, 
                         q_id:str
                         ) -> pd.DataFrame:
        '''
        Search the key and return results for question "q_id" (if exists) as a DataFrame.
        '''
        try:
            df = self.key[q_id][KEY_RESULTS].as_df()
        except:
            print('No key for ' + str(q_id) + ' found.')
            df = pd.DataFrame()
        return df

##########################################################################
class Submission:
    def __init__(self, 
                 path_db:str, 
                 path_submission:str,
                 clear_views:bool=True,
                 verbose:bool=True
                 ):
        '''
        Inputs:
            path_db:            Path to the database
            path_submission:    Path to the submission file
            clear_views:        Whether to clear views from the database clone. Default is True
            verbose:            Set to False to suppress most output to the screen.  Default is True.

        There should not be a need for a user to use this class directly.
        Instead, students should use the validate_submission_format method defined in this module.
            
        A Submission is based on a JSON file containing SQL statements to be run.
        The structure of this file (key : value) is:

            setup : A list of action queries to run. DROP VIEW and CREATE VIEW are allowed, most other actions (e.g., DROP TABLE) will not be run.
                    These queries will be run in the order they appear in the list.

            qN : Where N is an integer indicating the question.  Each qN can contain two keys,
                sql    : Required. The SQL statement.
                params : Optional. Parameters to be passed to the query as either a tuple or a dictionary.

        When a new Submission is instantiated, the default behavior is:

        1) Verify the submission file exists
        2) Attempt to read in the submisssion file
        3) Make a clone of the database
        4) Clear all views from the clone
        5) Run queries in the setup key, if any. (Primarily meant for users to create views needed for the submission)

        The database clone will be deleted when the object goes out of scope (i.e., __del__ is called), or can be removed
        by calling the cleanup() method.
        '''
        self.verbose = verbose

        self.report = ''         # The report to output as one long string
        self.report_data = {}    # A dictionary to store results for each question. 
                                 # Will be iterated over and added to the report when calling Submission.write_report()

        # Validate file exists and parse user name, or raise a FileNotFoundError
        self.__get_submission_file(path_submission)
        self.report += 'Submission file: ' + self.path_submission + '\n'

        # Load the json
        self.__load_json()

        # Make a copy of the database, removing any existing copy first
        self.__get_db_clone(path_db)
        
        # Clear views from the database clone
        if clear_views: self.__clear_views()

        # Run any setup queries on the database clone
        self.__run_setup_queries()
        return
    
    def __get_submission_file(self, 
                              path_submission:str
                              ) -> None:
        # Check if the file exists
        if os.path.exists(path_submission):
            # Parse into folder / file name
            path_parts = os.path.split(path_submission)

            # Extract the user name from the file name.
            # Assumes it is formatted as if it was downloaded from blackboard, 
            # otherwise it will probably just be the file name.
            self.uname = path_parts[1].split('_attempt')[0].split('_')[-1]
            if self.verbose: print('Found submission for:', self.uname, '\n')
            
            # Save the path to the Submission object
            self.path_submission = path_submission
        else:
            # Raise an error if the file was not found
            raise FileNotFoundError(path_submission)
        return

    def __load_json(self) -> None:
        # Try to load the JSON file. If any errors occur raise a custom exception and include the original exception info.
        try:
            with open(self.path_submission, 'r') as f:
                self.submission = json.load(f)
                if self.verbose: print('Submission json data loaded.\n')
        except Exception as e:
            summary = fe(e)
            summary += '\nError loading JSON data. Additional details above.'
            raise JSONFormatException(''.join(summary))
        return
    
    def __get_db_clone(self, 
                       base_path:str
                       ) -> None:
        try:
            # Create name for clone
            self.path_db = base_path + '.' + self.uname

            # Remove clone if it already exists
            if os.path.exists(self.path_db):
                os.remove(self.path_db)
            
            # Create new clone
            shutil.copyfile(base_path, self.path_db)
            
            # Initialize DB object
            self.db = DB(self.path_db)
            if self.verbose: print('Database cloned to:', self.path_db, '\n')
        except Exception as e:
            summary = fe(e)
            summary += '\nError cloning database. Additional details above.'
            raise DBCloneException(''.join(summary))
        return
    
    def __clear_views(self):
        if self.verbose: print_and_wait('Dropping views from clone...')
        views = self.db.run_query("SELECT name FROM sqlite_master WHERE type = 'view';").rows
        sql = "DROP VIEW IF EXISTS %s ;"
        for v in views:
            self.db.run_query(sql % v[0])
        if self.verbose: print(' done.\n')
        return
    
    def __run_setup_queries(self) -> None:
        '''
        Run queries found in the setup key of the submission and log the results to the report.
        DROP VIEW and CREATE VIEW are allowed. Most other actions (like dropping tables or inserting records)
        will result in the DB object throwing an exception.
        '''
        if KEY_SETUP in self.submission:
            self.report += '\nRunning action queries...\n'
            self.setups = self.submission[KEY_SETUP]
            for sql in self.setups:
                try:
                    self.report += '\n\n' + HEADER_LINE + '\n' + sql
                    self.db.run_query(sql)
                    self.report += '\n\t...success!\n'
                except Exception as e:
                    self.report += '\n...failure. Details below:\n'
                    
                    if self.verbose: print('\n')
                    for line in fe(e):
                        if self.verbose: print(line)
                        self.report += line
                finally:
                    self.report += HEADER_LINE + '\n'
        else:
            self.setups = None
        return
        
    def __del__(self):
        # If this throws an error, it's probably because self.path_db does not exist.
        # This shouldn't be possible, so we should probably remove the try/except. [_]
        try:
            self.cleanup()
        except Exception as e:
            for line in fe(e):
                print(line)
            pass
        return

    def cleanup(self):
        '''
        Remove the database clone, unless we've disabled this for debugging purposes.
        '''
        if DBG_CLEANUP_TEMP_DBS:
            if os.path.exists(self.path_db):
                if self.verbose: print_and_wait('\nCleaning up...')
                os.remove(self.path_db)
                if self.verbose: print(' done\n')
        else:
            print('WARNING: db cleanup disabled. If this is not desired, set DBG_CLEANUP_TEMP_DBS to True.')
        return

    def write_report(self, 
                     path_out:str,
                     header_len:int = 79
                     ) -> None:
        '''
        Function loops over the contents of self.report_data,
        appends them to self.report, and then outputs self.report to path_out
        '''

        # Items in self.report_data are typically related to a particular question
        # in an assignment, but can also be used to store additional info if needed.
        # It is assumed that each item in self.report_data is a dictionary (see the inner loop)
        for q_id, q_data in self.report_data.items():
            self.report += '\n' + (q_id).center(header_len, '-') + '\n'

            if type(q_data) == dict:
                for subkey, subvalue in q_data.items():
                    self.report += '\n' + subkey + ':\n'
                    self.report +=  str(subvalue) + '\n'
            else:
                self.report += str(q_data) + '\n'
            
            self.report += '\n' +  ('end of ' + q_id).center(header_len, '-') + '\n\n'
        
        with open(path_out, 'w') as f:
            f.write(self.report)
        print('Report saved to: ', path_out)
        return
    
    def run_query(self, 
                  sql:str, 
                  params:Union[tuple, dict] = None
                  ) -> pd.DataFrame:
        '''
        Convenience method that might not be needed [_]
        '''

        # Verifying that we do not actually need this method:
        raise NotImplementedError

        try:
            results = self.db.run_query(sql, params)
            return results.as_df()
        except Exception as e:
            for line in fe(e):
                print(line)
        return
    
    def get_sql(self, 
                q_id:str
                ) -> tuple[
                    str,
                    Union[tuple, dict]
                    ]:
        '''
        Search for q_id in the submission and return the sql and params associated with it,
        or raise an exception if q_id is not found.
        '''
        if q_id in self.submission.keys():
            q = self.submission[q_id]
            sql = q[KEY_SQL]
            if KEY_PARAMS in q:
                params = q[KEY_PARAMS]
            else:
                params = None
            return sql, params
        else:
            raise SQLNotFoundException('Submission for ' + str(q_id) + ' not found.')
        return
 
##########################################################################
class DB:

    # Decided not to define these globally, as they are unlikely to need to be overridden
    # unless we start working with much larger datasets.

    DFLT_QUERY_CHUNK = int(5000)    # Retrieve query results this many rows at a time
    DFLT_QUERY_LIMIT = int(1e6-1)   # Triggers an exception if a query returns more than this many rows

    def __init__(self, 
                 db_name : str, 
                 create = False):
        '''
        Inputs:
            db_name: Path to the database
            create:  Whether to create the database if it does not exist, or throw an exception. Default is to throw an exception if file not found.
        '''
        if self.__db_exists(db_name):
            self.db_name = db_name
        else:
            if create:
                conn = sqlite3.connect(db_name)
                conn.close()
                self.db_name = db_name
            else:
                self = None
                raise FileNotFoundError(db_name)
        return
    
    def __db_exists(self, 
                    db_name: str
                    ) -> bool:
        return os.path.exists(db_name)
    
    def __connect(self) -> None:
        '''
        Create a connection and cursor to the database.
        '''
        self.conn = sqlite3.connect(self.db_name)
        self.curs = self.conn.cursor()
        return
    
    def __close(self) -> None:
        '''
        Close connection to the database.
        '''
        try:
            self.conn.close()
        except Exception as e:
            # [_] Possible to get here?
            for line in fe(e):
                print(line)
            print("\nAttempted to close a connection that doesn't exist.")
            raise e
        return

    def run_query(self, 
                  sql               :str                = None, 
                  params            :Union[tuple, dict] = None,
                  query             :Query              = None,
                  chunk_size        :int                = DFLT_QUERY_CHUNK,
                  query_limit       :int                = DFLT_QUERY_LIMIT,
                  prevent_actions   :bool               = True
                  ) -> Results:
        
        '''
        Run a query and return a Results object.

        Inputs:
            sql:                A SQL statement.
            params:             Either a tuple, dictionary, or None.
            query:              A Query object. If not None, then sql and params should be None, and vice versa.
            chunk_size:         Number of rows to retrieve at a time
            query_limit:        Max number of rows before a RowLimitException is thrown
            prevent_actions:    Should almost always be True
        '''
        try:
            self.__connect()

            # Validate proper inputs passed and set self.current_query
            msg_bad_params = """If 'sql' and/or 'params' are specified, 'query' should be None.
                                If passing a prepared Query object for 'query', then both 'sql' and 'params' should be None.
                             """
            if query is not None:
                if (sql is not None) | (params is not None):
                    raise ValueError(msg_bad_params)
                else:
                    self.current_query = query
                    params = query.params
            elif (sql is not None) | (params is not None):
                if query is not None:
                    raise ValueError(msg_bad_params)
                else:
                    self.current_query = Query(sql, params)

            # Check for unwanted actions and raise error if found
            if prevent_actions:
                if not self.current_query.is_allowed():
                    raise(SQLActionException)

            # Run the query
            if params is None:
                self.curs.execute(self.current_query.sql)
            else:
                self.curs.execute(self.current_query.sql, self.current_query.params)
            
            if self.curs.description is None:
                # If we are here, then the query must have been an action query.
                # self.conn.commit() # [_] Should not be needed, but a reminder to test more cases
                
                return Results(None, None)
            
            # If we are here, then it must have been a SELECT query. Get the outputs ready
            columns = [c[0] for c in self.curs.description]
            rows = []
            eof = False

            while query_limit >= 0:
                chunk = self.curs.fetchmany(chunk_size)
                if len(chunk) > 0:
                    rows += chunk
                
                if len(chunk) < chunk_size:
                    eof = True
                    break
                query_limit -= len(chunk)

            if not(eof):
                raise(RowLimitException)

            return Results(rows, columns)

        except Exception as e:
            # We actually do not want to handle anything here, should be the callers responsibility.
            raise e
            
            #summary = fe(e)  #Python >= 3.10, syntax different in older versions
            #for line in summary:
            #    print(line)
            #return [''.join(summary)], ('Error', )
        finally:
            # No matter what else happens, make sure we do not leave our connection open.
            self.__close()
        return

##########################################################################
class Query:
    '''
    A SQL query that exists independent of any database. 
    In can check itself for basic formatting (e.g., does it end with a semicolon?),
    remove comments, and answer some basic questions about whether or not it
    "might" contain hardcoded parameters, or actions that shouldn't be run.
    '''
    UNSAFE_WORDS = ['create table', 
                    'drop table', 
                    'create index', 
                    'drop index',
                    'delete', 
                    'insert',
                    'update'
                    ]
    
    def __init__(self, 
                 sql : str,
                 params : Union[tuple, dict] = None):    
        self.sql = sql
        if params is not None:
            if type(params) not in [tuple, dict]:
                raise TypeError('Parameters must be tuple, dict, or None, not ' + str(type(params)))
        self.params = params
        self.__clean()
        return
    
    def __repr__(self):
        my_repr = object.__repr__(self) + "\n\nsql:\n" + self.sql + "\n\nparams:\n" + str(self.params)
        return my_repr
    
    def __clean(self) -> None:
        temp = self.__fix_query_end(self.sql)
        temp = self.__without_comments(temp)
        temp = self.__without_whitespace(temp)
        temp = self.__standardize_comparisons(temp)
        self.sql_clean = temp
        return

    def __fix_query_end(self, sql:str) -> str:
        '''
        Find the last semicolon,
        remove everything after it, 
        and surround it with \n
        '''
        idx = sql.rfind(';')
        if idx == -1:
            raise SQLFormatException('No semicolon found in query.')
        sql = sql[:idx] + '\n;\n'
        return sql

    def __without_comments(self, 
                           sql:str = None
                           ) -> str:
        if sql is None: # [_] Should sql really be optional?
            sql = self.sql     
        sql = self.__remove_single_line_comments(sql)
        sql = self.__remove_block_comments(sql)
        sql = re.sub(r'\n+', '\n', sql)
        return sql
    
    def __remove_single_line_comments(self, 
                                      sql:str
                                      ) -> str:
        idx = sql.find('--')
        while idx != -1:
            idx2 = sql.find('\n', idx)
            if idx2 == -1:
                # [_] Test with a line comment at the bottom (handled by __fix_query_end)
                raise SQLFormatException('Unterminated line comment detected.')
            else:
                sql = sql[:idx] + sql[idx2:]
            idx = sql.find('--')
            #print('\t\t-----removed a line comment from', idx, 'to', idx2, '\n', sql)
        return sql

    def __remove_block_comments(self, 
                                sql:str
                                ) -> str:
        idx = sql.find('/*')
        while idx != -1:
            idx2 = sql.find('*/', idx)
            if idx2 == -1:
                raise SQLFormatException('Unterminated block comment detected.')
            else:
                sql = sql[:idx] + sql[idx2+2:]
            idx = sql.find('/*')
            #print('\t\t-----removed a block comment from', idx, 'to', idx2, "(+2)", '\n', sql)
        return sql

    def __without_whitespace(self, 
                             sql:str
                             ) -> str:
        # [_] Needs a name change?  Since it also converts to lower case.
        return ' '.join(sql.split()).lower()
    
    def __standardize_comparisons(self, 
                                  sql:str
                                  ) -> str:
        to_replace = {'==' : '=',
                      '<>' : '!='
                      }
        for key, value in to_replace.items():
            sql = sql.replace(key, value)
        return sql
    
    def is_allowed(self) -> bool:
        for word in self.UNSAFE_WORDS:
            if word in self.sql_clean:
                print('Unsafe word(s) found:', word)
                return False
        return True
    
    def no_hard_params(self, 
                       verbose:bool=False
                       ) -> bool:
        comps = ['!=', '=', '>', '<', ' in ', ' in(', ' like ', ' between ']
        tokens = [':', '@', '?', '$', '.', '(select ', '( select ', 'is null', 'is not null']
        
        sql = self.sql_clean

        def find_last_comp(sql:str
                           ) -> tuple[str, int]:
            '''
            Find the last comparison operator,
            return the type and position
            '''
            idx = -1
            found_comp = None
            for c in comps:
                new_idx = sql.rfind(c)
                if new_idx > idx:
                    found_comp = c
                    idx = new_idx
            return found_comp, idx
        
        def find_token_after(sql:str, 
                             idx:int
                             ) -> tuple[str, int]:
            '''
            Search for a matching token after idx,
            return the token and position
            '''
            sql_after = sql[idx:]
            for t in tokens:
                idx = sql_after.find(t)
                if idx > -1:
                    return t, idx
            return None, -1
        
        # Start searching
        while True:
            if verbose: print('\nChecking:\n', sql, '\n\n')    
            found_comp, idx_comp = find_last_comp(sql)
            if idx_comp != -1:
                if verbose: print('Found', found_comp, 'at', idx_comp)
                found_token, idx_token = find_token_after(sql, idx_comp)
                if idx_token == -1:
                    if verbose: print('No match found for', found_comp, '\n')
                    return False
                else:
                    if verbose: print('\tmatched by', found_token, 'offset by', idx_token, '\n')
                    sql = sql[:idx_comp]
            else:
                break
        return True

    def autosort(self) -> None:
        # [_] A relic of sorts! :-)
        self.rows_sorted = sorted(self.rows, 
                                  key=lambda z: list((str(z[i]) for i in range(len(z)))))
        return 

##########################################################################
class Results:
    '''
    Class to save rows and column labels as an object with a few methods to display, 
    and an equality test to compare two Results objects.
    '''

    def __init__(self, 
                 rows:list[tuple], 
                 cols:tuple
                 ):
        self.rows = rows
        self.cols = cols
        if rows is not None:
            #self.rows_sorted = self.as_sorted_and_rounded()
            self.rows_sorted = self.__sort_and_round()
        else:
            self.rows_sorted = rows
        return
    
    def __repr__(self) -> str:
        return self.as_df_short_string()
    
    def __eq__(self, 
               other: Results
               ) -> bool:
        if type(self) != type(other):
            raise ValueError('Cannot compare Results object to object of type: ' + str(type(other)))
        return self.rows_sorted == other.rows_sorted
    
    ### Defining new methods for sorting and rounding.  Eliminate the old ones after ample testing. [_]
    def __sort_and_round(self,
                         prec: int = ROUNDING_PREC
                        ) -> list[tuple]:
        '''
        Note that rows_sorted might not have a consistent column ordering,
        so self.cols should NOT be used in conjunction with self.rows_sorted
        '''
        rows_sorted = []
        for row in self.rows:
            # Make a mutable version of the row
            row = list(row)
            for idx, value in enumerate(row):
                # Rounding
                if '.' in str(value):
                    try:
                        value = round(float(value), prec)
                    except ValueError:
                        pass
                # Make NaN strings
                if value != value:
                    value = NAN_REPR
                # Update the element in the list
                row[idx] = str(value)
            # Append the row as a tuple
            rows_sorted.append(tuple(sorted(row)))
        return sorted(rows_sorted)
    ### end of new sorting/rounding methods.
    
    def __sort_by_columns_and_round(self, 
                                    prec:int
                                    ) -> list[tuple]:
        '''
        Need a better name here!

        Sorts and rounds things. 
        
        If there's a reason why two apparantly identical results are getting labeled as unequal, the flawed logic should be here!

        Also: Doing too much work to accept simple mistakes the students could/should just get right.
        '''

        # [_] Quick fix, and probably not 100% Sort by rows, then columns, then rows again.
        temp_rows = sorted(self.rows)
        #first_row_as_string = [str(x) for x in self.rows[0]]
        first_row_as_string = [str(x) for x in temp_rows[0]]
        idx = sorted(range(len(first_row_as_string)), 
                     key=lambda i: first_row_as_string[i]
                     )
        sorted_by_column = []
        #for row in self.rows:
        for row in temp_rows:
            sorted_row = []
            for i in idx:
                val = row[i]
                
                # If there's a decimal, try to round it 
                #   (checking isnumeric() is not the way to go, and no errors have been thrown by the float() call yet)
                if '.' in str(val): 
                    try:
                        val = round(float(val), prec)
                    except ValueError:
                        pass
                
                # Make NaN's strings 
                if val != val:
                    val = NAN_REPR

                # Always store the values as strings, as inefficient as that might be, but for the purposes of comparison with other results.
                # I got 99 problems, and 0.000000001 ain't one.
                sorted_row.append(str(val))
            sorted_by_column.append(tuple(sorted_row))
        return sorted_by_column
    
    def as_sorted_and_rounded(self, 
                              prec:int = ROUNDING_PREC
                              ) -> list[tuple]:
        # [_] The age old question: Do we sort by rows or columns first?
        #   Answer: Don't be so lenient!
        temp = self.__sort_by_columns_and_round(prec)
        return sorted(temp)
    
    def as_df(self) -> pd.DataFrame:
        '''
        Return the Results as a pandas DataFrame
        '''
        return pd.DataFrame(data = self.rows,
                            columns = self.cols)

    def as_df_short_string(self, 
                           max_len:int = MAX_ROWS_IN_SHORT_DF,
                           max_str_len:int = MAX_STR_LEN
                           ) -> str:
        '''
        Return the Results as a string representation of the pandas DataFrame.
        '''
        head_tail_len = max_len//2
        if len(self.rows) > max_len:
            df_head = pd.DataFrame(data = self.rows[0:head_tail_len],
                                   columns = self.cols
                                   ).applymap(lambda y: y[:max_str_len] if isinstance(y, str) else y)
            
            df_tail = pd.DataFrame(data = self.rows[-head_tail_len:],
                                   columns = self.cols
                                   ).applymap(lambda y: y[:max_str_len] if isinstance(y, str) else y)
            
            df_str = '(NOTE: Output truncated to save space in this report)\nHead:\n' + \
                    df_head.to_string(index=False) + \
                    '\n\nTail:\n' + \
                    df_tail.to_string(index=False)
        else:
            df_str = pd.DataFrame(data=self.rows, 
                                  columns=self.cols
                                  ).applymap(lambda y: y[:max_str_len] if isinstance(y, str) else y).to_string(index=False)

        return df_str

##########################################################################    
def run_ga(path_db:str,
           path_key:str,
           path_subs:str,
           path_out:str
           ) -> Prof:
    '''
    Run the grader and output the Prof object.
    '''
    p = Prof(path_db)
    p.make_key(path_key)
    p.grade_all(path_subs, path_out)
    return p

def validate_submission_format(path_db:str, 
                               path_submission:str,
                               num_questions:int,
                               path_out:str = None,
                               verbose:bool = False
                               ) -> None:
    '''
    Method for students to validate the format of their submission.

    Inputs:
        path_db:            Path to the database.
        path_submission:    Path to the submission (.data302) file.
        num_questions:      Number of questions in the assignment.
        path_out:           Optional. Path to save the output report. If omitted, output file will begin with 'VALIDATION' and end with '.txt'
        verbose:            Optional. If True, will also print output to the screen.  Default is False.
    '''
    
    if path_out is None:
        path_parts = os.path.split(path_submission)
        path_out = os.path.join(path_parts[0], 'VALIDATION_' + path_parts[1].replace(EXT, '.txt'))

    # This will already clear all views, run any queries under the setup key, and write results to the report
    s = Submission(path_db, path_submission, verbose=verbose)

    # Get all keys in the dictionary
    keys = list(s.submission.keys())

    # Remove the setup key if it exists
    if KEY_SETUP in keys: keys.remove(KEY_SETUP)

    # Search for each question, based on the value provided for num_questions
    for _id in range(1, num_questions+1):
        q_id = KEY_Q + str(_id)
        s.report_data[q_id] = {}

        try:
            # Try to retrieve the SQL for this question
            sql, params = s.get_sql(q_id)
            s.report_data[q_id][KEY_SQL] = sql
            s.report_data[q_id][KEY_PARAMS] = params

            # Remove the key from the list of keys
            keys.remove(q_id)

            # Try to run the query and record the runtime
            t0 = dt.now()
            results = s.db.run_query(sql, params)
            runtime = format_time_interval(t0, dt.now())
            
            # Summarize the output
            summary = results.as_df_short_string()
            s.report_data[q_id][KEY_SUMMARY] = summary
            s.report_data[q_id][KEY_NROWS] = len(results.rows)
            s.report_data[q_id][KEY_RUNTIME] = runtime

        except Exception as e:
            summary = ''.join(fe(e))
            if verbose:
                print('Error processing', q_id, ':\n')
                print(summary)

            s.report_data[q_id][KEY_SUMMARY] = summary
            s.report_data[q_id][KEY_NROWS] = FLAG_MISSING
            s.report_data[q_id][KEY_RUNTIME] = FLAG_MISSING

    # [_] Verify a few different combinations of inputs here.
    s.report_data[KEY_UNUSED] = '\nNothing to worry about here!\n'
    if len(keys) > 0:
        s.report_data[KEY_UNUSED] = '\n'
        for k in keys:
            s.report_data[KEY_UNUSED] += k + '\n'

    # Write output
    s.write_report(path_out)
    
    # Clean up
    s.cleanup()
    return