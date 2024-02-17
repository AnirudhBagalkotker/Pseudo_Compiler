#include <iostream>
#include <vector>
#include <set>
#include <fstream>
#include <cstring>
#include <string>
#include <iomanip>
#include <map>
#include <unordered_map>
#include <stack>

#define MAX 1000
#define COLUMNS 5
#define LEN 45

using namespace std;

class RegExToDFA
{
    int initStates[LEN], finStates[LEN], a = 0, b = 0;
    string initStatesDFA[LEN], finStatesDFA[LEN];
    int numInitStatesDFA = 0, numFinStatesDFA = 0;

    /**
     * Initializes the 2D array NFAtable with -1 values.
     *
     * @param NFAtable the 2D array to be initialized
     *
     * @return void
     *
     * @throws None
     */
    void initialiseNFA(int NFAtable[][COLUMNS])
    {
        for (int i = 0; i < MAX; i++)
        {
            for (int j = 0; j < COLUMNS; j++)
                NFAtable[i][j] = -1;
        }
    }

    /**
     * Returns the name of the state corresponding to the given integer.
     *
     * @param i the integer value representing the state
     *
     * @return the name of the state
     *
     * @throws None
     */
    string stateName(int i)
    {
        int a[100], j = 0;
        string p = "Q";
        if (i == 0)
        {
            p += '0';
            return p;
        }

        while (i > 0)
        {
            a[j++] = i % 10;
            i /= 10;
        }

        for (int i = j - 1; i >= 0; i--)
        {
            int x = a[i];
            switch (x)
            {
            case 0:
                p += '0';
                break;
            case 1:
                p += '1';
                break;
            case 2:
                p += '2';
                break;
            case 3:
                p += '3';
                break;
            case 4:
                p += '4';
                break;
            case 5:
                p += '5';
                break;
            case 6:
                p += '6';
                break;
            case 7:
                p += '7';
                break;
            case 8:
                p += '8';
                break;
            case 9:
                p += '9';
                break;
            }
        }
        return p;
    }

    /**
     * A function to check and initialize the states based on the State Mapping and e-closure.
     *
     * @param v the vector of integers to check
     * @param s the string to use for initialization
     *
     * @return void
     *
     * @throws None
     */
    void checkStates(vector<int> v, string s)
    {
        for (int i = 0; i < v.size(); i++)
        {
            if (v[i] == initStates[0])
                initStatesDFA[numInitStatesDFA++] = s;
            if (v[i] == finStates[0])
                finStatesDFA[numFinStatesDFA++] = s;
        }
    }

    /**
     * Validates the input word by checking if it contains only 'a' or 'b' characters.
     *
     * @param word the input word to be validated
     *
     * @return true if the word contains only 'a' or 'b' characters, false otherwise
     *
     * @throws None
     */
    bool validateWord(string word)
    {
        int len = word.length();
        for (int i = 0; i < len; i++)
        {
            if (word[i] != 'a' && word[i] != 'b')
                return false;
        }

        return true;
    }

    /**
     * Reduces the finStates array by removing the element at index x and shifting the
     * following elements to the left.
     *
     * @param x the index of the element to be removed
     *
     * @return void
     *
     * @throws None
     */
    void reduceFinalStates(int x)
    {
        b--;
        for (int i = x; i < b; i++)
            finStates[i] = finStates[i + 1];
    }

    /**
     * Simplifies the expression by replacing characters in the input string according
     * to specific rules, as we have no symbol for concatenation operation
     *
     * @param s the input string to be simplified
     *
     * @return the simplified string
     *
     * @throws None
     */
    string addBrackets(string s)
    {
        int l = s.length(), j = 0;
        char x[5000];
        string p;

        x[j++] = '(';

        for (int i = 0; i < l; i++)
        {
            x[j++] = s[i];

            if (s[i] >= 97 && s[i] <= 122 && s[i + 1] >= 97 && s[i + 1] <= 122)
                x[j++] = '.';
            else if (s[i] == ')' && s[i + 1] == '(')
                x[j++] = '.';
            else if (s[i] >= 97 && s[i] <= 122 && s[i + 1] == '(')
                x[j++] = '.';
            else if (s[i] == ')' && s[i + 1] >= 97 && s[i + 1] <= 122)
                x[j++] = '.';
            else if (s[i] == '?' && (s[i + 1] == '(' || (s[i + 1] >= 97 && s[i + 1] < 122)))
                x[j++] = '.';
            else if (s[i] == '*' && (s[i + 1] == '(' || (s[i + 1] >= 97 && s[i + 1] < 122)))
                x[j++] = '.';
            else if (s[i] == '+' && (s[i + 1] == '(' || (s[i + 1] >= 97 && s[i + 1] < 122)))
                x[j++] = '.';
        }

        x[j++] = ')';

        for (int i = 0; i < j; i++)
            p += x[i];

        return p;
    }

    /**
     * Calculate the epsilon closure of a state in the NFA table.
     *
     * @param NFAtable the NFA transition table
     * @param state the state for which epsilon closure needs to be calculated
     *
     * @return a vector containing the epsilon closure of the given state
     *
     * @throws None
     */
    vector<int> eClosure(int NFAtable[][COLUMNS], int state)
    {
        stack<int> s;
        map<int, int> m;
        vector<int> v;
        int nxtState;

        s.push(state);
        m[state] = 1;

        while (!s.empty())
        {
            nxtState = s.top();
            s.pop();
            if (NFAtable[nxtState][3] == -1)
                continue;
            else
            {
                s.push(NFAtable[nxtState][3]);
                m[NFAtable[nxtState][3]] = 1;

                if (NFAtable[nxtState][4] == -1)
                    continue;
                else
                {
                    s.push(NFAtable[nxtState][4]);
                    m[NFAtable[nxtState][4]] == -1;
                }
            }
        }

        map<int, int>::iterator itr;
        itr = m.begin();

        while (itr != m.end())
        {
            v.push_back(itr->first);
            itr++;
        }
        return v;
    }

    /**
     * Converts a regular expression to postfix notation using stack and character array.
     * Iterates through input string and processes each character according to the rules of
     * a regular expression, then constructs and returns the resulting postfix expression.
     *
     * @param s the input regular expression
     *
     * @return the postfix notation of the regular expression
     *
     * @throws None
     */
    string regExToPostfix(string s)
    {
        int l = s.length(), j = 0;
        char a[5000];
        stack<char> ch;

        string p;

        for (int i = 0; i < l; i++)
        {
            char x = s[i];
            switch (x)
            {
            case 'a':
                a[j++] = 'a';
                break;
            case 'b':
                a[j++] = 'b';
                break;
            case '(':
                ch.push('(');
                break;
            case ')':
                while (!ch.empty())
                {
                    if (ch.top() == '(')
                    {
                        ch.pop();
                        break;
                    }
                    else
                    {
                        a[j++] = ch.top();
                        ch.pop();
                    }
                }
                break;
            case '.':
                if (ch.empty())
                    ch.push('.');
                else
                {
                    char temp = ch.top();
                    if (temp == '(')
                        ch.push('.');
                    else if (temp == '*' || temp == '?' || temp == '+')
                    {
                        a[j++] = ch.top();
                        ch.pop();
                        if (ch.top() == '.')
                            a[j++] = '.';
                        else
                            ch.push('.');
                    }
                    else if (temp == '.')
                    {
                        a[j++] = ch.top();
                        ch.pop();
                        ch.push('.');
                    }
                    else if (temp == '|')
                        ch.push('.');
                }
                break;
            case '|':
                if (ch.empty())
                    ch.push('|');
                else
                {
                    char temp = ch.top();
                    if (temp == '(')
                        ch.push('|');
                    else if (temp == '*' || temp == '.' || temp == '?' || temp == '+')
                    {
                        a[j++] = ch.top();
                        ch.pop();
                        ch.push('|');
                    }
                }
                break;
            case '+':
                if (ch.empty())
                    ch.push('+');
                else
                {
                    char temp = ch.top();
                    if (temp == '(' || temp == '.' || temp == '|')
                        ch.push('+');
                    else
                    {
                        a[j++] = ch.top();
                        ch.pop();
                        ch.push('+');
                    }
                }
                break;
            case '*':
                if (ch.empty())
                    ch.push('*');
                else
                {
                    char temp = ch.top();
                    if (temp == '(' || temp == '.' || temp == '|')
                        ch.push('*');
                    else
                    {
                        a[j++] = ch.top();
                        ch.pop();
                        ch.push('*');
                    }
                }
                break;
            case '?':
                if (ch.empty())
                    ch.push('?');
                else
                {
                    char temp = ch.top();
                    if (temp == '(' || temp == '.' || temp == '|')
                        ch.push('?');
                    else
                    {
                        a[j++] = ch.top();
                        ch.pop();
                        ch.push('?');
                    }
                }
                break;
            }
        }

        for (int i = 0; i < j; i++)
            p += a[i];

        return p;
    }

    /**
     * Converts a regular expression in postfix notation to a non-deterministic finite
     * automaton (NFA) represented by NFAtable.
     *
     * @param s the input regular expression in postfix notation
     * @param NFAtable the 2D array representing the NFA table
     *
     * @return the number of states in the NFA
     *
     * @throws None
     */
    int regExPostfixToNFA(string s, int NFAtable[][COLUMNS])
    {
        stack<int> stateStack;
        int l = s.length(), states = 1, m, n, j, counter;

        for (int i = 0; i < l; i++)
        {
            char x = s[i];
            switch (x)
            {
            case 'a':
                NFAtable[states][0] = states;
                initStates[a++] = states;
                states += 1;
                NFAtable[states - 1][1] = states;
                finStates[b++] = states;
                NFAtable[states][0] = states;
                states += 1;
                break;
            case 'b':
                NFAtable[states][0] = states;
                initStates[a++] = states;
                states += 1;
                NFAtable[states - 1][2] = states;
                finStates[b++] = states;
                NFAtable[states][0] = states;
                states += 1;
                break;
            case '.':
                m = finStates[b - 2];
                n = initStates[a - 1];
                NFAtable[m][3] = n;
                reduceFinalStates(b - 2);
                a--;
                break;
            case '|':
                for (j = a - 1, counter = 0; counter < 2; counter++)
                {
                    m = initStates[j - counter];
                    NFAtable[states][3 + counter] = m;
                }
                a -= 2;
                initStates[a++] = states;
                NFAtable[states][0] = states;
                states += 1;
                for (j = b - 1, counter = 0; counter < 2; counter++)
                {
                    m = finStates[j - counter];
                    NFAtable[m][3] = states;
                }
                b -= 2;
                finStates[b++] = states;
                NFAtable[states][0] = states;
                states += 1;
                break;
            case '+':
                m = initStates[a - 1];
                NFAtable[states][3] = m;
                NFAtable[states][0] = states;
                initStates[a - 1] = states;

                states += 1;
                n = finStates[b - 1];
                NFAtable[n][3] = m;
                NFAtable[n][4] = states;
                finStates[b - 1] = states;
                NFAtable[states][0] = states;
                states += 1;
                break;
            case '*':
                m = initStates[a - 1];
                NFAtable[states][3] = m;
                NFAtable[states][0] = states;
                initStates[a - 1] = states;

                states += 1;
                n = finStates[b - 1];
                NFAtable[n][3] = m;
                NFAtable[n][4] = states;
                NFAtable[states - 1][4] = states;
                finStates[b - 1] = states;
                NFAtable[states][0] = states;
                states += 1;
                break;
            case '?':
                // Assuming the element before '?' is already processed and its initial and final states are at the top of the stacks
                m = initStates[a - 1]; // Initial state of the last processed element
                n = finStates[b - 1];  // Final state of the last processed element

                // Add epsilon transitions to simulate the '?' functionality
                // Create a new initial state with epsilon transitions to both the original initial state and a new final state
                NFAtable[states][0] = states;     // New initial state
                NFAtable[states][3] = m;          // Epsilon transition to the original initial state
                NFAtable[states][4] = states + 1; // Epsilon transition to the new final state
                initStates[a - 1] = states;       // Update the initial state to the new initial state
                states += 1;

                // Create a new final state
                NFAtable[n][3] = states;      // Add epsilon transition from original final state to new final state
                NFAtable[states][0] = states; // Set the new final state
                finStates[b - 1] = states;    // Update the final state to the new final state
                states += 1;
                break;
            }
        }
        return states;
    }

    /**
     * Converts the given NFA table to a DFA table and returns the number of states in the DFA.
     *
     * @param NFAtable 2D array representing the NFA table
     * @param states number of states in the NFA
     * @param DFAtable 2D array to store the DFA table
     *representing
     * @return the number of states in the DFA table
     *
     * @throws None
     */
    int NFAtoDFA(int NFAtable[][COLUMNS], int states, string DFAtable[][3])
    {
        int state = 0, j = 0, counter = 0;
        map<vector<int>, string> map_state;
        vector<int> v, v1, v2, v3, v4;

        bool flag[states];
        memset(flag, true, sizeof(flag)); // to make sure all states E-closure found

        v = eClosure(NFAtable, initStates[0]);
        flag[initStates[a]] = false;

        map_state[v] = stateName(j++);
        checkStates(v, map_state[v]); // to check whether current state is initial or not

        stack<vector<int>> st;
        st.push(v);
        // transition of e-closure to over input symbol a
        while (true)
        {
            while (!st.empty())
            {
                vector<int> v;
                v = st.top();
                st.pop();
                counter += 1;
                DFAtable[state][0] = map_state[v]; // find transition of a state over input symbol 'a' and 'b'

                for (int i = 0; i < v.size(); i++)
                {
                    flag[v[i]] = false;
                    int temp = NFAtable[v[i]][1];  // over input symbol a
                    int temp1 = NFAtable[v[i]][2]; // over input symbol b
                    if (temp >= 0)
                        v1.push_back(temp);
                    if (temp1 >= 0)
                        v3.push_back(temp1);
                }

                map<int, int> map_temp, map_temp1; // to remove duplicate state
                map<int, int>::iterator it;

                for (int i = 0; i < v1.size(); i++)
                {
                    v2 = eClosure(NFAtable, v1[i]);
                    for (int j = 0; j < v2.size(); j++)
                        map_temp[v2[j]] = 1;
                    v2.clear();
                }

                for (int i = 0; i < v3.size(); i++)
                {
                    v4 = eClosure(NFAtable, v3[i]);
                    for (int j = 0; j < v4.size(); j++)
                        map_temp1[v4[j]] = 1;
                    v4.clear();
                }

                for (it = map_temp.begin(); it != map_temp.end(); it++)
                {
                    v2.push_back(it->first);
                    flag[it->first] = false;
                }

                for (it = map_temp1.begin(); it != map_temp1.end(); it++)
                {
                    v4.push_back(it->first);
                    flag[it->first] = false;
                }

                if (v2.empty())
                    DFAtable[state][1] = "X";

                else
                {
                    string t = map_state[v2];
                    char flag1 = t[0];
                    if (flag1 == 'Q')
                        DFAtable[state][1] = map_state[v2]; // checking v2 has already been mapped or not
                    else
                    {
                        DFAtable[state][1] = stateName(j++);
                        map_state[v2] = DFAtable[state][1];
                        checkStates(v2, map_state[v2]);
                        st.push(v2); // not mapped state will be pushed into stack
                    }
                }

                if (v4.empty())
                    DFAtable[state][2] = "X";
                else
                {
                    string t = map_state[v4];
                    char flag1 = t[0];
                    if (flag1 == 'Q')
                        DFAtable[state][2] = map_state[v4];
                    else
                    {
                        DFAtable[state][2] = stateName(j++);
                        map_state[v4] = DFAtable[state][2];
                        checkStates(v4, map_state[v4]);
                        st.push(v4);
                    }
                }
                v1.clear();
                v2.clear();
                v3.clear();
                v4.clear();
                state += 1;
            }

            int k = 1;
            for (k = 1; k < states; k++)
            {
                if (flag[k])
                {
                    v = eClosure(NFAtable, k);
                    map_state[v] = stateName(j++);
                    checkStates(v, map_state[v]);
                    st.push(v);
                    break;
                }
            }

            if (k == states)
                break;
        }

        return state;
    }

    /**
     * A function to tokenize a string based on a given DFA table and initial state.
     *
     * @param DFAtable a 2D array representing the DFA table
     * @param word the input string to be tokenized
     * @param state the initial state for tokenization
     *
     * @return true if the word is accepted by the DFA, false otherwise
     *
     * @throws None
     */
    bool tokenizeString(string DFAtable[][3], string word, int state)
    {
        int len = word.length();
        string temp = initStatesDFA[0];
        bool check = validateWord(word); // makes sure that word need to be simulated is only consist of 'a' and 'b'

        if (!check)
            temp = "X";

        int i = 0;
        for (i = 0; i < len; i++)
        {
            if (temp == "X")
            {
                return false;
                break;
            }
            else
            {
                int j = 0;

                for (j = 0; j < state; j++)
                {
                    if (temp == DFAtable[j][0])
                        break;
                }

                if (word[i] == 'a')
                    temp = DFAtable[j][1];
                else if (word[i] == 'b')
                    temp = DFAtable[j][2];
            }
        }

        if (i == len)
        {
            int j = 0;
            for (j = 0; j < numFinStatesDFA; j++)
            {
                if (temp == finStatesDFA[j])
                {
                    return true;
                    break;
                }
            }
            if (j == numFinStatesDFA)
                return false;
        }
    }

public:
    bool driverCode(string s, string word)
    {
        /*  In NFAtable :-
            0th COLUMN represents states
            1st COLUMN represents states over input 'a'
            2nd COLUMN represents states over input 'b'
            3rd COLUMN represents states over input 'e'(epsilon)
            -1 in states COLUMNS represent no state changes over that input.
         */

        int NFAtable[MAX][COLUMNS];
        initialiseNFA(NFAtable);
        int states = 0;

        s = addBrackets(s);
        s = regExToPostfix(s);

        states = regExPostfixToNFA(s, NFAtable);

        string DFAtable[states][3];
        int DFAstate = 0;
        DFAstate = NFAtoDFA(NFAtable, states, DFAtable);

        return tokenizeString(DFAtable, word, DFAstate);
    }

    void clear()
    {
        this->a = 0;
        this->b = 0;
        this->numInitStatesDFA = 0;
        this->numFinStatesDFA = 0;
    }
};

int main()
{
    ifstream inputFile("input.txt");
    if (!inputFile.is_open())
    {
        cout << "failed to open file!" << endl;
        return 1;
    }
    string str;
    getline(inputFile, str);

    vector<string> regex;
    string temp;
    while (getline(inputFile, temp))
    {
        regex.push_back(temp);
    }
    inputFile.close();

    ofstream outputFile("output.txt");
    if (!outputFile.is_open())
    {
        cout << "failed to open output file" << endl;
        return 1;
    }

    int i = 0;
    int end = str.size();
    int j = end;
    while (i != str.size())
    {
        j = end - i;
        while (j != 0)
        {
            RegExToDFA obj[regex.size()];
            int check = 0;
            for (int k = 0; k < regex.size(); k++)
            {
                if (obj[k].driverCode(regex[k], str.substr(i, j)))
                {
                    outputFile << "<" << str.substr(i, j) << ", " << k + 1 << ">";
                    i = i + j;
                    check = 1;
                    break;
                }
            }
            if (check == 1)
                break;
            j--;
        }
        if (j == 0)
        {
            outputFile << "<" << str.substr(i, j + 1) << ", 0>";
            i = i + 1;
        }
    }
    outputFile << endl;
    outputFile.close();
    return 0;
}