/*
* Centrality Measures Calculator (Closeness, Node Betweenness, Edge Betweenness)
* Copyright (C) 2013 George Piskas
*
* This program is free software; you can redistribute it and/or modify
* it under the terms of the GNU General Public License as published by
* the Free Software Foundation; either version 2 of the License, or
* (at your option) any later version.
*
* This program is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
* GNU General Public License for more details.
*
* You should have received a copy of the GNU General Public License along
* with this program; if not, write to the Free Software Foundation, Inc.,
* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*
* Contact: geopiskas@gmail.com
* Important notice: Works with Linux.
*/

#include <iostream>
#include <cstdio>
#include <fstream>

#include <vector>
#include <queue>
#include <stack>
#include <map>
#include <set>
#include <list>

#include <cstring>
#include <sstream>
#include <algorithm>
#include <limits>

using namespace std;

// A simple neighbor struct, consisting of the target neighbor and the edge weight.
struct neighbor {
    int target;
    int weight;
    neighbor(int mTarget, int mWeight) : target(mTarget), weight(mWeight) {
    }
};

// The new adjacency list type.
typedef vector<vector<neighbor> > adjacency_list;

// Dijkstra's algorithm is used to calculate all the single source shortest paths in a weighted graph and the source's closeness.
float dijkstra_SSSP(int src, int n, stack<int> &visitStack, vector<int> &sigma, list<int> *pred, adjacency_list &adjList) {
    // Closeness counter.
    float closeness = 0;

    // Vector that holds the distances from the source.
    vector<int> dist;
    dist.resize(n, numeric_limits<int>::max());
    dist[src] = 0;
    
    // Queue used for the Dijkstra's algorithm.
    set<pair<int, int> > visitQueue;
    visitQueue.insert(make_pair(dist[src], src));

    // While there are still elements in the queue.
    while (!visitQueue.empty()) {
        // Pop the first.
        set<pair<int, int> >::iterator vPair = visitQueue.begin();
        int srcDist = vPair->first;
        int v = vPair->second;
        visitQueue.erase(vPair);
        visitStack.push(v);

        // Closeness part aggregation.
        closeness += srcDist;

        // Check the neighbors w of v.
        for (vector<neighbor>::iterator it = adjList[v].begin(); it != adjList[v].end(); it++) {
            int w = it->target;
            int newDist = srcDist + it->weight;
            // Node w found for the first time or the new distance is shorter?
            if (newDist < dist[w]) {
                visitQueue.erase(make_pair(dist[w], w));
                visitQueue.insert(make_pair(newDist, w));
                dist[w] = newDist;
                pred[w].clear();
                sigma[w] = 0;
            }
            // Is the shortest path to w via u?
            if (newDist == dist[w]) {
                pred[w].push_back(v);
                sigma[w] += sigma[v];
            }
        }
    }
    // Closeness part inversion.
    if (closeness!=0) {
        return 1.0 / closeness;
    } else {
        return 0;
    }
}

// BFS algorithm is used to calculate all the single source shortest paths in a non weighted graph and the source's closeness.
float bfs_SSSP(int src, int n, stack<int> &visitStack, vector<int> &sigma, list<int> *pred, adjacency_list &adjList) {
    // Closeness counter.
    float closeness = 0;
    
    // Vector that holds the distances from the source.
    vector<int> dist;
    dist.resize(n, -1);
    dist[src] = 0;

    // Queue used for the Bfs algorithm.
    queue<int> visitQueue;
    visitQueue.push(src);
    
    // While there are still elements in the queue.
    while (!visitQueue.empty()) {
        // Pop the first.
        int v = visitQueue.front();
        visitQueue.pop();
        visitStack.push(v);

        // Closeness part aggregation.
        closeness += dist[v];
        
        // Check the neighbors w of v.
        for (vector<neighbor>::iterator it = adjList[v].begin(); it != adjList[v].end(); it++) {
            int w = it->target;
            // Node w found for the first time?
            if (dist[w] < 0) {
                visitQueue.push(w);
                dist[w] = dist[v] + 1;
            }
            // Is the shortest path to w via u?
            if (dist[w] == dist[v] + 1) {
                pred[w].push_back(v);
                sigma[w] += sigma[v];
            }
        }

    }    
    // Closeness part inversion.
    if (closeness!=0) {
        return 1.0 / closeness;
    } else {
        return 0;
    }
}

// Given two node indices, this function returns a string representation with
// the smallest index first, a dash, and the second index after.
string getEdgeTag(int n1, int n2) {
    ostringstream os;
    if (n1 <= n2) {
        os << n1 << "-" << n2;
    } else {
        os << n2 << "-" << n1;
    }
    return os.str();
}

// Prompts the user to type an input filename and returns the file pointer.
FILE * readPrompt() {
    FILE * fp;
    char str[100];
    
    // Prompt filename input.
    cout << "Enter filename: ";
    cin >> str;
    
    // Append .net if the user did not provide it.
    if (strstr(str, ".net") == NULL) {
        strcat(str, ".net");
    }
    
    // Open the file and return fp, if it exists, otherwise exit with error.
    fp = fopen(str, "r");
    if (fp == NULL) {
        cout << "File '" << str << "' not found.";
        exit(EXIT_FAILURE);
    } else {
        return fp;
    }
}

// Prints input file statistics just after input has finished.
void printInputStats(bool isWeigthed, int n, int e) {
    ofstream out;
    out.open ("out_graph_stats.txt");
    cout << "\n==================="
            << "\nINPUT GRAPH STATS"
            << "\n>Weighted: " << boolalpha << bool(isWeigthed)
            << "\n>#ofNodes: " << n
            << "\n>#ofEdges: " << e
            << "\n===================\n\n";
    out << "Weighted: " << boolalpha << bool(isWeigthed)
            << "\n>#ofNodes: " << n
            << "\n>#ofEdges: " << e;
    out.close();
}

// Reads an input file and fills up the adjacency list as well as the edges.
void readGraph(int &n, bool &isWeigthed, adjacency_list &adjList, map<string, float> edgeList) {

    int e = 0; // Total number of edges (for statistics).
    isWeigthed = false;

    char * line = NULL;
    size_t len = 0;
    FILE * fp = readPrompt();

    // Find n, the total number of nodes.
    if (getline(&line, &len, fp) != -1) {
        strtok(line, " ");
        n = atoi(strtok(NULL, " "));

    }

    // Reserve n space for adjacency list. If it fails, n was not parsed.
    if (n) {
        adjList.reserve(n);
    } else {
        cout << "Malformed input. Number of nodes undefined.";
        exit(EXIT_FAILURE);
    }

    // Skip n lines until edges part.
    for (int i = 0; i <= n; i++) {
        if(getline(&line, &len, fp) == -1) {
            cout << "Malformed input. Missing data.";
            exit(EXIT_FAILURE);
        }
    }
    
    // Read the nodes and the edges, one by one, and fill up adjList and edgeBetweenness.
    int start, end, weight;
    while (getline(&line, &len, fp) != -1) {
        e += 1;

        start = atoi(strtok(line, " ")) - 1;
        end = atoi(strtok(NULL, " ")) - 1;
        weight = atoi(strtok(NULL, " "));
        
        // Check if the graph is weighted. If w<=0, the input is malformed
        if (weight > 1) {
            isWeigthed = true;
        } else if(weight<=0) {
            cout << "Malformed input. Edge w weight=0.";
            exit(EXIT_FAILURE);
        }
        
        edgeList.insert(pair<string, float>(getEdgeTag(start, end), 0));
        adjList[start].push_back(neighbor(end, weight));
        adjList[end].push_back(neighbor(start, weight));
    }

    if (line) {
        free(line);
    }
    
    // Print statistics after reading.
    printInputStats(isWeigthed, n, e);
}

// Clears the variables or re-initializes to 0, so that they are ready for the next loop.
void resetVariables(int src, int n, list<int> *pred, vector<int> &sigma, vector<float> &delta) {
    for (int i = 0; i < n; i++) {
        pred[i].clear();
    }

    sigma.clear();
    sigma.resize(n, 0);
    sigma[src] = 1;

    delta.clear();
    delta.resize(n, 0);
}

// Prints Closeness Centrality.
void printCloseness( int n, vector<float> closeness, bool normalize) {
    float nrml = 1;
    if (normalize) {
        nrml = 1.0/(n - 1);
    } 
    ofstream out;
    out.open ("out_closeness.txt");
    cout << "> Closeness Centrality" << endl;    
    for (int i = 0; i < n; i++) {
        cout << "Node " << i << ": " << closeness[i] / nrml << endl;
        out << "Node " << i << ": " << closeness[i] / nrml << endl;
    }
    out.close();
}

// Prints Node Betweenness Centrality.
void printNodeBetweenness( int n, vector<float> nodeBetweenness, bool normalize) {
    float nrml = 1;
    if (normalize) {
        nrml = (n - 1)*(n - 2);
    }
    ofstream out;
    out.open ("out_node_betweenness.txt");
    cout << endl << "> Node Betweenness Centrality" << endl;
    for (int i = 0; i < n; i++) {
        cout << "Node " << i << ": " << nodeBetweenness[i] / nrml << endl;
        out << "Node " << i << ": " << nodeBetweenness[i] / nrml << endl;
    }
    out.close();
}

// Prints Edge Betweenness Centrality.
void printEdgeBetweenness( int n, map<string, float> edgeBetweenness, bool normalize) {
    float nrml = 1;
    if (normalize) {
        nrml = n * (n - 1);
    }
    ofstream out;
    out.open ("out_edge_tweenness.txt");
    cout << endl << "> Edge Betweenness Centrality" << endl;
    for (map<string, float>::iterator it = edgeBetweenness.begin(); it != edgeBetweenness.end(); it++) {
        cout << "Edge " << it->first << ": " << it->second / nrml << endl;
        out << "Edge " << it->first << ": " << it->second / nrml << endl;
    }
    out.close();
}


int main(void) {
    int n; // Number of nodes
    bool isWeigthed; // Weighted graph check.
    adjacency_list adjList; // Adjacency list.

    // Centrality measures.
    map<string, float> edgeBetweenness;
    vector<float> nodeBetweenness;
    nodeBetweenness.resize(n, 0);
    vector<float> closeness;
    closeness.resize(n, 0);

    // Input is read, and values are set to all the arguments.
    readGraph(n, isWeigthed, adjList, edgeBetweenness);

    list<int> pred[n]; // List of predecessors of node v.
    vector<int> sigma;
    vector<float> delta;
    stack<int> visitStack; // Stack that holds the inverse order of visited nodes.
    
    // For each node of the graph.
    for (int src = 0; src < n; src++) { 
        // Prepare the variables for the next loop.
        resetVariables(src, n, pred, sigma, delta);

        if (isWeigthed) {
            // Closeness part. Using Dijkstra because graph is weighted.
            closeness[src] = dijkstra_SSSP(src, n, visitStack, sigma, pred, adjList);
        } else {
            // Closeness part.
            closeness[src] = bfs_SSSP(src, n, visitStack, sigma, pred, adjList);
        }

        // Get the inverse order of visited nodes.
        while (!visitStack.empty()) {
            int w = visitStack.top();
            visitStack.pop();
            
            // For each predecessors of node w, do the math!
            for (list<int>::iterator it = pred[w].begin(); it != pred[w].end(); it++) {
                int v = *it;
                float c = ((float) sigma[v] / (float) sigma[w]) * (1.0 + delta[w]);

                delta[v] += c;

                // Edge betweenness aggregation part.
                string tag = getEdgeTag(v, w);
                float tempC = edgeBetweenness[tag];
                edgeBetweenness.erase(tag);
                edgeBetweenness.insert(pair<string, float>(tag, tempC + c));
            }
            // Node betweenness aggregation part.
            if (w != src) {
                nodeBetweenness[w] += delta[w];
            }
        }

    }
    
    // Printing output.
    printCloseness(n, closeness, true);
    printNodeBetweenness(n, nodeBetweenness, true);
    printEdgeBetweenness(n, edgeBetweenness, true);
    
    return 0;
}