import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.*;

public class DijkstraBellmanFloyd {
    int v;                      // Number of Vertices
    int e;                      // Number of Edges
    int sv;                     // Source Vertex
    int currentDistance;        // Current distance from source
    int INT_MAX = 2147483647;

    int [][] adjMatrix;
    // Space Complexity: O(n)
    List<Vertex> vertices = new ArrayList<>();
    // Space Complexity: O(n)
    ArrayList<Integer> visited = new ArrayList<>();
    // Space Complexity: O(n)
    ArrayList<Integer> listOfGraph = new ArrayList<>();

    // Runtime: O(V*n)
    // Constructor for graph
    public DijkstraBellmanFloyd(ArrayList<Integer> array) {
        this.v = array.get(0);
        this.sv = array.get(1);
        this.e = array.get(2);
        for (int i = 3; i < array.size(); i++) {
            listOfGraph.add(array.get(i));
        }

        addVertices();
        parseArray(listOfGraph);
        formAdjM(listOfGraph);
    }

    // Exception for Bellman-Ford if NegativeWeightCycle is found
    public static class NegativeWeightCycle extends Exception {
        public NegativeWeightCycle(String message)
        {
            super(message);
        }
    }

    public class Vertex implements Comparable<Vertex> {
        String name;
        String parent;
        Vertex closestVertex;
        Map<Vertex, Integer> connectedVertices = new HashMap<>(4, .5f);

        // O(1)
        // Constructor for Vertex
        public Vertex(String name) {
            this.name = name;
            parent = null;
        }

        // Runtime: O(n^2)
        // Helps set up adjacent vertices to each vertex
        public void setUpAdjacentVertices(ArrayList<Integer> array, Vertex givenVertex) {
            for (int i = 0; i < array.size(); i++) {
                if (i % 3 == 0) {
//                    System.out.println("Edge given : " + givenVertex.name + " Weight added: " + array.get(i+2));
                    if (array.get(i) == Integer.parseInt(givenVertex.name))
                        givenVertex.connectedVertices.put(vertices.get(array.get(i + 1) - 1), array.get(i + 2));
                    else
                        vertices.get(array.get(i + 1) - 1).connectedVertices.put(vertices.get(array.get(i) - 1), array.get(i + 2));
                }
            }
        }

        public int compareTo(Vertex o) {
            return new nameComparator().compare(name, o.name);
        }

        public class nameComparator implements Comparator<Vertex> {
            public int compare(Vertex v1, Vertex v2) {
                String v1s = v1.name;
                String v2s = v2.name;
                Integer a1 = Integer.parseInt(v1s);
                Integer a2 = Integer.parseInt(v2s);
                return a1.compareTo(a2);
            }
            // O(n)
            public int compare(String name, String name1) {
                Integer a1 = Integer.parseInt(name);
                Integer a2 = Integer.parseInt(name1);
                return a1.compareTo(a2);
            }
        }
    }

    // Runtime: Average: O(V*nlog(n)) Worst: O(V*n^2)
    // Actual implementation of Dijkstra's Algorithm
    public void dijkstraAlgorithm() throws FileNotFoundException {
        Map<Vertex, Integer> table = new TreeMap<>();
        Vertex temp;
        int tempDistance = 0;
        int currentVertex = sv;

        // Updates adjacent nodes parent and distance from source values
        while (visited.size() != v) {
            temp = vertices.get(currentVertex - 1);


            if (currentVertex == sv) {
                temp.parent = String.valueOf(-1);
                table.put(temp, -1);

                for (Map.Entry<Vertex, Integer> entry : temp.connectedVertices.entrySet()) {
//                    System.out.println("Key = " + entry.getKey().name + ", Value: " + entry.getValue());
                    entry.getKey().parent = temp.name;
                    table.put(entry.getKey(), entry.getValue());
                }
            } else {

                for (Map.Entry<Vertex, Integer> entry : temp.connectedVertices.entrySet()) {
//                    System.out.println("Key = " + entry.getKey().name + ", Value: " + entry.getValue());
                    if (entry.getKey().parent == null) {
                        entry.getKey().parent = temp.name;
                        table.put(entry.getKey(), (entry.getValue() + tempDistance));
                    } else if (table.get(entry.getKey()) > (tempDistance + entry.getValue())) {
                        entry.getKey().parent = temp.name;
                        table.put(entry.getKey(), (entry.getValue() + tempDistance));
                    }
                }
            }

            currentDistance = tempDistance;

            // Checks whether the next vertex being traversed was visited or not
            if (checkVisited(Integer.parseInt(temp.closestVertex.name))) {
                visited.add(currentVertex);
                if (visited.size() < v) {
                    currentVertex = Integer.parseInt(findNextVertex(table).name);
                    tempDistance = currentDistance;
                }

            } else {
                visited.add(currentVertex);
//                currentVertex = Integer.parseInt(temp.closestVertex.name);
//                tempDistance += findClosestVertex(temp);
                currentVertex = Integer.parseInt(findNextVertex(table).name);
                tempDistance = currentDistance;
            }


        }
        printDijkstra(table);
    }

    // My implementation of Bellman-Ford Algorithm
    public void bellmanFordAlgorithm() throws Exception {
        int[][] matrix = new int[e * 2][3];
        int count = 0;
        int index = 0;
        currentDistance = INT_MAX;

        // Make two sets of edges by flipping vertices
        for (int n = 0; n < 2; n++) {
            for (int i = 0; i < e; i++) {
                if (n == 0)
                {
                    matrix[count][index] = adjMatrix[i][index];
                    matrix[count][index + 1] = adjMatrix[i][index + 1];
                    matrix[count][index + 2] = adjMatrix[i][index + 2];
                    count++;
                }
                else {
                    matrix[count][index] = adjMatrix[i][index + 1];
                    matrix[count][index + 1] = adjMatrix[i][index];
                    matrix[count][index + 2] = adjMatrix[i][index + 2];
                    count++;
                }
            }
        }

        // Create a distance matrix
        int[][] distance = new int[v][3];
        for (int j = 0; j < v; j++)
        {
            distance[j][1] = INT_MAX;
            distance[j][0] = j + 1;
        }

        // Set source to 0
        distance[sv-1][1] = 0;

        // Calculate the shortest distance and set parents
        for (int n = 0; n < v - 1; n++)
        {
            for (int i = 0; i < e * 2; i++)
            {
                if (distance[matrix[i][0] - 1][1] != INT_MAX && distance[matrix[i][0] - 1][1] + matrix[i][2] < distance[matrix[i][1] - 1][1])
                {
                    distance[matrix[i][1] - 1][1] = distance[matrix[i][0] - 1][1] + matrix[i][2];
                    distance[matrix[i][1] - 1][2] = matrix[i][0];
                }
            }
        }

        // Throw negative weight cycle if it is found
        for (int i = 0; i < e * 2; i++)
        {
            if (distance[matrix[i][0] - 1][1] != INT_MAX && distance[matrix[i][0] - 1][1] + matrix[i][2] < distance[matrix[i][1] - 1][1])
            {
                throw new NegativeWeightCycle("This graph contains a Negative Weight Cycle!");
            }
        }
        printBF(distance, v, 3);
    }

    // My implementation of Floyd-Warshall Algorithm
    public void floydWarshallAlgorithm() throws FileNotFoundException {
        int[][] changingMatrix = new int[v][v];

        // Calculate all the weights and transfer to the matrix
        for (int i = 0; i < v; i++)
        {
            for (int j = 0; j < v; j++)
            {
                for (int k = 0; k < e; k++)
                {
                    if (adjMatrix[k][0] == i)
                    {
                        changingMatrix[adjMatrix[k][0] - 1][adjMatrix[k][1] - 1] = adjMatrix[k][2];
                        changingMatrix[adjMatrix[k][1] - 1][adjMatrix[k][0] - 1] = adjMatrix[k][2];
                    }
                    else if (i == j)
                    {
                        changingMatrix[i][j] = 0;
                    }
                    else if (changingMatrix[i][j] == 0)
                    {
                        changingMatrix[i][j] = 9999;
                    }
                }
            }
        }

        // Run the official algorithm given by Professor Gerber
        for (int i = 0; i < v; i++)
        {
            for (int j = 0; j < v; j++)
            {
                for (int k = 0; k < v; k++)
                {
                    changingMatrix[i][j] = Math.min(changingMatrix[i][j], changingMatrix[i][k] + changingMatrix[k][j]);
                }
            }

        }
        printFW(changingMatrix, v, v);
    }

    // Prints matrix to it's own seperate file
    public void printMatrix(int[][] matrix, int column, int row, File filename) throws FileNotFoundException {
        PrintWriter pw = new PrintWriter(filename);

        pw.printf("%d\n", v);
        for (int i = 0; i < column; i++)
        {
            for (int j = 0; j < row; j++)
            {
                pw.printf(matrix[i][j] + " ");
            }
            pw.printf("\n");
        }
        pw.close();
    }

//    public void printMatrix2(int[][] matrix, int column, int row) throws FileNotFoundException {
//        for (int i = 0; i < column; i++)
//        {
//            for (int j = 0; j < row; j++)
//            {
//                System.out.print(matrix[i][j] + " ");
//            }
//            System.out.println();
//        }
//        System.out.println();
//    }

    public void formAdjM(ArrayList<Integer> array) {
        adjMatrix = new int[e][3];
        int count = 0;
        for (int i = 0; i <= array.size(); i++)
        {
            if (i % 3 == 0 & i != 0)
            {
                adjMatrix[count][0] = array.get(i - 3);
                adjMatrix[count][1] = array.get(i - 2);
                adjMatrix[count][2] = array.get(i - 1);
                count++;
            }
        }
    }

    // O(V*n)
    // Separates the array taken from scanner into smaller arrays for each vertex
    public void parseArray(ArrayList<Integer> array) {

        ArrayList<Integer> parsedArray = new ArrayList<>();
        for (int count = 1; count < v + 1; count++) {
            for (int i = 0; i < array.size(); i++) {
                if (array.get(i) == count) {
                    while ((i + 1) % 3 != 0)
                        i++;

                    parsedArray.add(array.get(i - 2));
                    parsedArray.add(array.get(i - 1));
                    parsedArray.add(array.get(i));
                }
            }

            constructVertices(parsedArray, count);
            parsedArray.clear();
        }
    }

    // Runtime: O(n^2)
    // Fills in the values need per vertex to complete my implementation of Dijkstra's Algorithm
    public void constructVertices(ArrayList<Integer> array, int i) {
        Vertex tempVertex = vertices.get(i - 1);

        tempVertex.setUpAdjacentVertices(array, tempVertex);

        findClosestVertex(tempVertex);
    }

    // O(V)
    // Adds all the vertices necessary for graph
    public void addVertices() {
        for (int i = 1; i < v + 1; i++) {
            Vertex newVertex = new Vertex(String.valueOf(i));
            vertices.add(newVertex);
        }
    }

    // Runtime: O(n^2)
    // Finds the next vertex to be traversed from Dijkstra's Algorithm.
    public Vertex findNextVertex(Map<Vertex, Integer> currentVertices) {
        Vertex tempVertex = null;
        int temp = INT_MAX;
        for (Map.Entry<Vertex, Integer> t : currentVertices.entrySet()) {
            if (t.getValue() < temp && t.getValue() > currentDistance) {
                tempVertex = t.getKey();
                temp = t.getValue();
            } else if (t.getValue() == currentDistance && !checkVisited(Integer.parseInt(t.getKey().name))) {
                tempVertex = t.getKey();
                temp = t.getValue();
            }
        }
        currentDistance = temp;
        return tempVertex;
    }

    // O(n)
    // Finds the closest vertex for any given vertex in the graph
    public void findClosestVertex(Vertex vertex) {
        Map<Vertex, Integer> tempHash = vertex.connectedVertices;
        int temp = INT_MAX;
        for (Map.Entry<Vertex, Integer> t : tempHash.entrySet()) {
            if (t.getValue() < temp) {
                vertex.closestVertex = t.getKey();
                temp = t.getValue();
            }
//            System.out.println("Connected Edge: " + t.getKey().name + " Distance: " + t.getValue());
        }
    }

    // Runtime: O(1)
    // Checks the visited array to see if vertex is within it
    public boolean checkVisited(int vertex) {
        return visited.contains(vertex);
    }

    // Runtime: O(V)
    // Simple print function to satisfy output parameters
    public void printDijkstra(Map<Vertex, Integer> table) throws FileNotFoundException {
        PrintWriter pw = new PrintWriter("C:\\Users\\joshi\\IdeaProjects\\SkipList\\Dijkstra'sAlgorithm\\Dijkstra'sAlgorithm\\cop3503-asn2-output-frazer-joshua-d.txt");

        pw.printf("%d\n", v);
        (table).forEach((key, value) -> pw.printf(key.name + " " + value + " " + key.parent + "\n"));
        pw.close();
    }

    public void printBF(int[][] matrix, int column, int row) throws FileNotFoundException {
        File filename = new File("cop3503-asn3-output-frazer-joshua-bf.txt");
        printMatrix(matrix, column, row, filename);
    }

    public void printFW(int[][] matrix, int column, int row) throws FileNotFoundException {
        File filename = new File("cop3503-asn3-output-frazer-joshua-fw.txt");
        printMatrix(matrix, column, row, filename);
    }

    // Runtime: Average: O(V*nlog(n)) Worst: O(V*n^2)
    public static void main(String[] args) throws Exception {

        File filename = new File("cop3503-asn3-input.txt");
        Scanner s = new Scanner(filename);
        int n;

        ArrayList<Integer> arrayFromFile = new ArrayList<>();
        while (s.hasNext()) {
            if (s.hasNextInt()) {
                n = s.nextInt();
                arrayFromFile.add(n);
            } else
                s.next();
        }

        DijkstraBellmanFloyd spanningTree1 = new DijkstraBellmanFloyd(arrayFromFile);
        spanningTree1.bellmanFordAlgorithm();
        spanningTree1.floydWarshallAlgorithm();

        s.close();
    }
}


