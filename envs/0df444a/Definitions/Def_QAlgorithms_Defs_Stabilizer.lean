-- Prove2me | Definitions.Def_QAlgorithms_Defs_Stabilizer
-- name    : QAlgorithms_Defs_Stabilizer
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:38:39.264574+00:00
-- url     : https://prove2.me/theorems/fcc1e044-9676-4b00-ad5e-c923e2a2a0ef
-- title:
--   Stabilizer states, measurement-controlled Clifford circuits, classical samplers
-- statement:
--   Stabilizer states, measurement-controlled Clifford circuits, classical samplers
--
--   ### QAlgorithms.Stabilizer.Pauli
--
--   This defines a type `Pauli` with exactly four distinct elements, named $I$, $X$, $Y$, $Z$. It has decidable equality. Beyond their names, no meaning is attached to the elements by this declaration.
--
--   ### QAlgorithms.Stabilizer.Pauli.mat
--
--   This assigns to each `Pauli` symbol a $2\times 2$ complex matrix. Rows and columns are indexed by the bit values $0$ (false) and $1$ (true), in the order $(0, 1)$:
--   $$I \mapsto \begin{pmatrix}1&0\\0&1\end{pmatrix},\quad X \mapsto \begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Y \mapsto \begin{pmatrix}0&-i\\ i&0\end{pmatrix},\quad Z \mapsto \begin{pmatrix}1&0\\0&-1\end{pmatrix}.$$
--   In more detail:
--
--   - $Y$ has entry $i$ at (row $1$, column $0$), entry $-i$ at (row $0$, column $1$), and $0$ on the diagonal.
--   - $Z$ is diagonal with $1$ on bit $0$ and $-1$ on bit $1$.
--
--   ### QAlgorithms.Stabilizer.Pauli.mul
--
--   This is a multiplication table that sends a pair $(P, Q)$ of `Pauli` symbols to a pair $(c, R)$, where $c \in \mathbb{Z}/4$ is a phase exponent and $R$ is a `Pauli` symbol. The table is:
--
--   - $(I, Q) \mapsto (0, Q)$ for every $Q$, and $(P, I) \mapsto (0, P)$ for every $P$.
--   - $(X,X), (Y,Y), (Z,Z) \mapsto (0, I)$.
--   - $(X, Y) \mapsto (1, Z)$ and $(Y, X) \mapsto (3, Z)$.
--   - $(Y, Z) \mapsto (1, X)$ and $(Z, Y) \mapsto (3, X)$.
--   - $(Z, X) \mapsto (1, Y)$ and $(X, Z) \mapsto (3, Y)$.
--
--   This is purely a lookup table. The declaration itself states no relation between the table and the matrices of `Pauli.mat`.
--
--   ### QAlgorithms.Stabilizer.PauliString
--
--   For $n \in \mathbb{N}$, a Pauli string on $n$ qubits consists of:
--
--   - a phase exponent $c \in \mathbb{Z}/4$;
--   - an assignment $q \mapsto P_q$ of a `Pauli` symbol to each qubit $q \in \{0, \dots, n-1\}$.
--
--   No constraints are imposed. For $n = 0$, a Pauli string is just a phase exponent.
--
--   ### QAlgorithms.Stabilizer.PauliString.toMatrix
--
--   This sends a Pauli string $P = (c, (P_q)_q)$ on $n$ qubits to the $2^n \times 2^n$ complex matrix indexed by bit strings $y, z \in \{0,1\}^n$:
--   $$\mathrm{mat}(P)(y,z) = i^{\bar c}\prod_{q=0}^{n-1} \mathrm{mat}(P_q)(y_q, z_q).$$
--   Here:
--
--   - $\bar c \in \{0,1,2,3\}$ is the canonical representative of $c$.
--   - $\mathrm{mat}(P_q)$ is the $2\times2$ matrix assigned by `Pauli.mat`.
--
--   Equivalently, this is $i^{\bar c}$ times the tensor product $\mathrm{mat}(P_0)\otimes\cdots\otimes\mathrm{mat}(P_{n-1})$, with qubit $q$ read from bit $q$ of the index. For $n = 0$, the result is the $1\times1$ matrix $(i^{\bar c})$.
--
--   ### QAlgorithms.Stabilizer.PauliString.mul
--
--   This defines a formal product of two Pauli strings $P = (c, (P_q))$ and $Q = (d, (Q_q))$ on $n$ qubits. For each qubit $q$, write $(e_q, R_q)$ for the result that `Pauli.mul` gives for $(P_q, Q_q)$. The product is the Pauli string with:
--
--   - phase exponent $c + d + \sum_{q=0}^{n-1} e_q$, computed in $\mathbb{Z}/4$;
--   - qubit-wise symbols $R_q$.
--
--   The declaration itself asserts no relation to matrix multiplication.
--
--   ### QAlgorithms.Stabilizer.PauliString.Commute
--
--   For two Pauli strings $P, Q$ on $n$ qubits, "$P$ commutes with $Q$" is defined to mean
--   $$\mathrm{mat}(P)\,\mathrm{mat}(Q) = \mathrm{mat}(Q)\,\mathrm{mat}(P),$$
--   an equality of $2^n\times 2^n$ complex matrices. Here $\mathrm{mat}$ is the matrix of a Pauli string described above, including its phase factor $i^{\bar c}$.
--
--   ### QAlgorithms.Stabilizer.Tableau
--
--   For $n \in \mathbb{N}$, a tableau on $n$ qubits is a family $T = (T_0, \dots, T_{n-1})$ of exactly $n$ Pauli strings, each acting on $n$ qubits and indexed by $\{0, \dots, n-1\}$. No constraints are imposed. For $n = 0$, there is exactly one tableau, the empty family.
--
--   ### QAlgorithms.Stabilizer.subProd
--
--   Given a tableau $T$ on $n$ qubits and a subset $s \subseteq \{0, \dots, n-1\}$, this is the ordered matrix product
--   $$\mathrm{subProd}(T, s) = A_0 A_1 \cdots A_{n-1}, \qquad A_i = \begin{cases}\mathrm{mat}(T_i) & i \in s,\\ \mathbb{1} & i \notin s,\end{cases}$$
--   taken with increasing index from left to right. Here $\mathrm{mat}(T_i)$ is the $2^n \times 2^n$ matrix of the Pauli string $T_i$, including its phase.
--
--   So it is the product of the matrices $\mathrm{mat}(T_i)$ for $i \in s$, in increasing order of $i$. For $s = \emptyset$, and also for $n = 0$, it is the identity matrix.
--
--   ### QAlgorithms.Stabilizer.IsValidTableau
--
--   A tableau $T = (T_0,\dots,T_{n-1})$ on $n$ qubits is called valid when all four of the following hold:
--
--   1. **Real signs.** Every $T_j$ has phase exponent $0$ or $2$ in $\mathbb{Z}/4$. That is, its matrix is $+$ or $-$ the tensor product of its single-qubit Pauli matrices.
--   2. **Commutation.** For all $i, j$ (including $i = j$, where it holds trivially), $\mathrm{mat}(T_i)\,\mathrm{mat}(T_j) = \mathrm{mat}(T_j)\,\mathrm{mat}(T_i)$.
--   3. **Independence up to phase.** For every index $j$, every subset $s \subseteq \{0,\dots,n-1\}$ with $j \notin s$, and every $c \in \{0,1,2,3\}$:
--   $$\mathrm{mat}(T_j) \ne i^{c}\cdot \mathrm{subProd}(T, s),$$
--   where $\mathrm{subProd}(T,s)$ is the product of the $\mathrm{mat}(T_i)$, $i \in s$, in increasing order. Taking $s = \emptyset$, this says in particular that no $\mathrm{mat}(T_j)$ equals $\pm\mathbb{1}$ or $\pm i\,\mathbb{1}$.
--   4. **No $-\mathbb{1}$.** For every subset $s$ (including $s = \emptyset$), $\mathrm{subProd}(T, s) \ne -\mathbb{1}$.
--
--   For $n = 0$, conditions 1–3 are vacuous. Condition 4 reduces to $(1) \ne (-1)$ for $1\times 1$ matrices, which holds, so the empty tableau is valid.
--
--   ### QAlgorithms.Stabilizer.tableauProjector
--
--   For a tableau $T = (T_0,\dots,T_{n-1})$ on $n$ qubits, this is the $2^n\times 2^n$ complex matrix
--   $$\Pi_T = \prod_{j=0}^{n-1} \tfrac12\bigl(\mathbb{1} + \mathrm{mat}(T_j)\bigr),$$
--   with the product taken in increasing order of $j$ from left to right. Here $\mathrm{mat}(T_j)$ is the matrix of the Pauli string $T_j$, including its phase.
--
--   No validity of $T$ is assumed. For $n = 0$, $\Pi_T$ is the $1\times1$ identity matrix.
--
--   ### QAlgorithms.Stabilizer.encPauli
--
--   This defines a map from the four single-qubit Pauli labels $\{I, X, Y, Z\}$ to strings of Booleans, which are finite lists of bits. Throughout, write $1$ for `true` and $0$ for `false`. Each label becomes a two-bit string:
--
--   $$
--   I \mapsto 00,\qquad X \mapsto 10,\qquad Y \mapsto 11,\qquad Z \mapsto 01 .
--   $$
--
--   The first bit is $1$ exactly for $X$ and $Y$. The second bit is $1$ exactly for $Y$ and $Z$.
--
--   ### QAlgorithms.Stabilizer.pauliOfBits
--
--   This defines a function that takes two bits $(a, b)$ and returns a Pauli label:
--
--   $$
--   (0,0) \mapsto I,\qquad (1,0) \mapsto X,\qquad (1,1) \mapsto Y,\qquad (0,1) \mapsto Z .
--   $$
--
--   All four bit pairs are covered, so the function is total. It sends each pair to the label whose two-bit code under the encoding $I\mapsto 00$, $X\mapsto 10$, $Y\mapsto 11$, $Z\mapsto 01$ is that pair.
--
--   ### QAlgorithms.Stabilizer.encPhase
--
--   For a phase $c \in \mathbb{Z}/4\mathbb{Z}$, let $v \in \{0,1,2,3\}$ be its canonical representative. The encoding is the two-bit string
--
--   $$
--   \big[\,v \ge 2,\; v \text{ is odd}\,\big],
--   $$
--
--   where each entry is $1$ if the condition holds and $0$ otherwise. Explicitly:
--
--   $$
--   0 \mapsto 00,\quad 1 \mapsto 01,\quad 2 \mapsto 10,\quad 3 \mapsto 11.
--   $$
--
--   This is the two-bit binary expansion of $v$, most significant bit first.
--
--   ### QAlgorithms.Stabilizer.encodeTableau
--
--   Fix $n \in \mathbb{N}$ and a tableau $T$ on $n$ qubits. Here $T$ is any function assigning to each row index $j \in \{0,\dots,n-1\}$ a Pauli string $T_j$. Each $T_j$ consists of:
--
--   - a phase $c_j \in \mathbb{Z}/4\mathbb{Z}$, and
--   - a label $P_{j,q} \in \{I,X,Y,Z\}$ for each qubit $q \in \{0,\dots,n-1\}$.
--
--   No validity condition is imposed on $T$. The encoding of row $j$ is the concatenation
--
--   $$
--   R_j = \mathrm{encPhase}(c_j)\;\mathrm{encPauli}(P_{j,0})\;\mathrm{encPauli}(P_{j,1})\cdots\mathrm{encPauli}(P_{j,n-1}).
--   $$
--
--   In this concatenation:
--
--   - $\mathrm{encPhase}$ sends $c_j$ to the 2-bit binary expansion of its representative in $\{0,1,2,3\}$.
--   - $\mathrm{encPauli}$ is $I\mapsto 00$, $X\mapsto 10$, $Y\mapsto 11$, $Z\mapsto 01$.
--
--   So $R_j$ has length $2n+2$. The full encoding is the concatenation $R_0 R_1 \cdots R_{n-1}$, a bit string of length $n(2n+2)$. When $n = 0$ the encoding is the empty string.
--
--   ### QAlgorithms.Stabilizer.decodeTableau
--
--   Given $n \in \mathbb{N}$ and an arbitrary bit string $s$, this produces a tableau on $n$ qubits. That is, it returns a Pauli string for each row $j \in \{0,\dots,n-1\}$.
--
--   **Reading convention.** Write $s[k]$ for the $k$-th bit of $s$, indexed from $0$. If $k$ is at least the length of $s$, then $s[k]$ is taken to be $0$; this is a default value, not an error. All index arithmetic below is ordinary natural-number arithmetic. For row $j$, set the offset
--
--   $$
--   b_j = j\,(2n+2).
--   $$
--
--   **Phase of row $j$.** The phase is the element of $\mathbb{Z}/4\mathbb{Z}$
--
--   $$
--   c_j = 2\cdot[s[b_j]=1] + [s[b_j+1]=1].
--   $$
--
--   **Pauli labels of row $j$.** For each qubit $q \in \{0,\dots,n-1\}$, the label is
--
--   $$
--   P_{j,q} = \mathrm{pauliOfBits}\big(s[b_j+2+2q],\; s[b_j+3+2q]\big),
--   $$
--
--   where $(0,0)\mapsto I$, $(1,0)\mapsto X$, $(1,1)\mapsto Y$, $(0,1)\mapsto Z$.
--
--   **Edge cases.**
--
--   - The input $s$ may have any length. Bits beyond position $n(2n+2)-1$ are ignored.
--   - Missing bits are read as $0$. In particular, a too-short or empty string decodes rows with no supplied bits as phase $0$ with all labels $I$.
--
--   ### QAlgorithms.Stabilizer.CliffordOp
--
--   For each $n \in \mathbb{N}$, this defines a data type of operations on $n$ qubits. Each element is exactly one of five kinds:
--
--   1. $\mathrm{pauli}(q, P)$: a qubit index $q \in \{0,\dots,n-1\}$ together with a Pauli label $P \in \{I,X,Y,Z\}$.
--   2. $\mathrm{h}(q)$: a qubit index $q$.
--   3. $\mathrm{s}(q)$: a qubit index $q$.
--   4. $\mathrm{cnot}(c, t)$: two qubit indices $c, t$ together with a proof that $c \ne t$.
--   5. $\mathrm{measure}(M)$: an arbitrary function $M$ assigning a Pauli label to each of the $n$ qubits.
--
--   No phase is included in $M$, and $M$ may be all-identity. For $n = 0$ there are no qubit indices, so the only element is $\mathrm{measure}$ of the empty assignment.
--
--   ### QAlgorithms.Stabilizer.wire1
--
--   For $n \in \mathbb{N}$ and a qubit index $q \in \{0,\dots,n-1\}$, this is the injective map from the one-element set $\{0\}$ into $\{0,\dots,n-1\}$ sending $0 \mapsto q$. Injectivity holds trivially because the domain has only one element.
--
--   ### QAlgorithms.Stabilizer.wire2
--
--   For $n \in \mathbb{N}$ and qubit indices $c, t \in \{0,\dots,n-1\}$ with $c \ne t$, this is the map from $\{0,1\}$ into $\{0,\dots,n-1\}$ given by
--
--   $$
--   0 \mapsto c,\qquad 1 \mapsto t.
--   $$
--
--   It is injective precisely because $c \neq t$.
--
--   ### QAlgorithms.Stabilizer.CliffordOp.mat
--
--   This assigns to each operation $\mathrm{op}$ on $n$ qubits a complex $2^n \times 2^n$ matrix. Rows and columns are indexed by bit vectors $y, z \in \{0,1\}^n$. Write $y_a$ for the bit of $y$ at qubit $a$.
--
--   **Single-qubit cases.** Let $U$ be a $2\times 2$ matrix indexed by bits, acting on qubit $q$. Its embedding is the $2^n \times 2^n$ matrix with entries
--
--   $$
--   \big(U^{(q)}\big)_{y,z} =
--   \begin{cases}
--   U_{y_q,\,z_q} & \text{if } y_a = z_a \text{ for every } a \neq q,\\
--   0 & \text{otherwise.}
--   \end{cases}
--   $$
--
--   - **$\mathrm{pauli}(q,P)$** gives $U^{(q)}$ with $U$ chosen according to $P$:
--     - $P = I$: $U$ is the $2\times2$ identity.
--     - $P = X$: $U_{a,b} = 0$ if $a=b$ and $1$ otherwise.
--     - $P = Y$: $U_{a,b} = 0$ if $a=b$; $U_{1,0} = i$; $U_{0,1} = -i$.
--     - $P = Z$: $U = \mathrm{diag}(1,-1)$, indexed by $0,1$.
--   - **$\mathrm{h}(q)$** gives $U^{(q)}$ with $U_{a,b} = -1/\sqrt2$ if $a=b=1$ and $1/\sqrt2$ otherwise.
--   - **$\mathrm{s}(q)$** gives $U^{(q)}$ with $U = \mathrm{diag}(1, i)$.
--
--   **Two-qubit case.** $\mathrm{cnot}(c,t)$ gives the matrix with
--
--   $$
--   \text{entry}_{y,z} =
--   \begin{cases}
--   1 & \text{if } y_a = z_a \ \forall a \notin\{c,t\},\ \ y_c = z_c,\ \ y_t = z_t \oplus z_c,\\
--   0 & \text{otherwise,}
--   \end{cases}
--   $$
--
--   where $\oplus$ is exclusive or.
--
--   **Measurement case.** $\mathrm{measure}(M)$ gives the $2^n\times 2^n$ identity matrix, regardless of $M$.
--
--   ### QAlgorithms.Stabilizer.encBits
--
--   For a finite list of bits $r = (\beta_1,\dots,\beta_k)$, possibly empty, the encoding is the bit string
--
--   $$
--   1\,\beta_1\;1\,\beta_2\;\cdots\;1\,\beta_k\;0\,0 .
--   $$
--
--   Each bit is preceded by a $1$, and the list is terminated by $00$. The result has length $2k+2$, and the empty list encodes to $00$.
--
--   ### QAlgorithms.Stabilizer.encHist
--
--   For a finite list $h = (o_1,\dots,o_k)$, possibly empty, each entry $o_i$ is either "nothing" or "some bit $\beta$". Each entry is encoded as a three-bit block:
--
--   $$
--   \text{nothing} \mapsto 1\,0\,0,\qquad \text{some } \beta \mapsto 1\,1\,\beta .
--   $$
--
--   These blocks are concatenated in order, followed by a single terminating $0$. The result has length $3k+1$, and the empty list encodes to $0$.
--
--   ### QAlgorithms.Stabilizer.encCtrlInput
--
--   The inputs are:
--
--   - a number $n \in \mathbb{N}$,
--   - a list of bits $r = (\beta_1,\dots,\beta_k)$, and
--   - a list $h = (o_1,\dots,o_m)$ whose entries are each either "nothing" or "some bit".
--
--   The output is the concatenation of three parts.
--
--   1. **Unary $n$:** $n$ ones followed by a single $0$, i.e. $1^n 0$.
--   2. **Encoding of $r$:** each $\beta_i$ written as $1\,\beta_i$, followed by $00$.
--   3. **Encoding of $h$:** each entry written as $100$ if it is "nothing" and $11\beta$ if it is "some $\beta$", followed by a single $0$.
--
--   In display form:
--
--   $$
--   1^n\,0\;\;\big(1\beta_1\cdots1\beta_k\,00\big)\;\;\big(\text{blocks of } h\big)\,0 .
--   $$
--
--   ### QAlgorithms.Stabilizer.encOp
--
--   This is a function from "either nothing or a Clifford operation on $n$ qubits" to finite bit strings, where $n$ is an implicit natural number. Bits are written $0$ for false and $1$ for true, and $\Vert$ denotes concatenation.
--
--   Two auxiliary encodings are used:
--
--   - $\mathrm{enc}_{\mathbb N}(k) = 1^k\,0$, i.e. $k$ ones followed by a single zero (a unary encoding).
--   - $\mathrm{enc}_P$ encodes the four single-qubit Pauli labels as two bits:
--   $$I \mapsto 00,\quad X \mapsto 10,\quad Y \mapsto 11,\quad Z \mapsto 01.$$
--
--   The encoding is defined case by case:
--
--   - **No operation** is encoded as the one-bit string $0$.
--   - **Pauli $P$ on qubit $q$** (with $q\in\{0,\dots,n-1\}$) is encoded as $1 \Vert \mathrm{enc}_{\mathbb N}(0)\Vert \mathrm{enc}_{\mathbb N}(q)\Vert \mathrm{enc}_P(P)$.
--   - **Hadamard on qubit $q$** is encoded as $1\Vert \mathrm{enc}_{\mathbb N}(1)\Vert\mathrm{enc}_{\mathbb N}(q)$.
--   - **Phase gate $S$ on qubit $q$** is encoded as $1\Vert \mathrm{enc}_{\mathbb N}(2)\Vert\mathrm{enc}_{\mathbb N}(q)$.
--   - **CNOT with control $c$ and target $t$** is encoded as $1\Vert \mathrm{enc}_{\mathbb N}(3)\Vert\mathrm{enc}_{\mathbb N}(c)\Vert\mathrm{enc}_{\mathbb N}(t)$. The proof that $c\neq t$ is not encoded.
--   - **Measurement of the Pauli string $M=(M_0,\dots,M_{n-1})$**, where each $M_q\in\{I,X,Y,Z\}$, is encoded as
--   $$1\Vert \mathrm{enc}_{\mathbb N}(4)\Vert \mathrm{enc}_P(M_0)\Vert\cdots\Vert\mathrm{enc}_P(M_{n-1}).$$
--     No phase is encoded. For $n=0$ the Pauli part is empty.
--
--   Qubit indices are encoded in unary by their numerical value.
--
--   ### QAlgorithms.Stabilizer.MCCFamily
--
--   A structure consisting of five components: two polynomials, a controller function, and two properties of the controller.
--
--   **Polynomials.** $\mathrm{rbits}$ and $\mathrm{steps}$ are polynomials with natural-number coefficients.
--
--   **Controller.** $\mathrm{ctrl}$ takes three inputs:
--
--   - a natural number $n$;
--   - an arbitrary finite bit string $r$, of any length (it is not tied to $\mathrm{rbits}(n)$);
--   - a "history" $h$, which is a finite list whose entries are each either "none" or a bit.
--
--   It returns either nothing or a Clifford operation on $n$ qubits. A Clifford operation is one of: a Pauli $I,X,Y,Z$ on one qubit, a Hadamard on one qubit, an $S$ gate on one qubit, a CNOT on two distinct qubits, or a measurement of an $n$-qubit Pauli string $M\in\{I,X,Y,Z\}^n$.
--
--   **Property 1 (halting).** For all $n,r,h$:
--   $$\mathrm{steps}(n)\le |h| \implies \mathrm{ctrl}(n,r,h)=\text{nothing}.$$
--   Nothing is required for histories shorter than $\mathrm{steps}(n)$.
--
--   **Property 2 (polynomial-time controller).** There exists a function $g$ on bit strings satisfying two conditions:
--
--   - $g$ is polynomial-time computable. This means Mathlib's TM2 polynomial-time computability, with bit strings encoded as themselves.
--   - For all $n,r,h$:
--   $$g\big(\mathrm{enc}_{\mathbb N}(n)\Vert \mathrm{enc}_B(r)\Vert \mathrm{enc}_H(h)\big)=\mathrm{encOp}(\mathrm{ctrl}(n,r,h)).$$
--
--   The encodings in Property 2 are:
--
--   - $\mathrm{enc}_{\mathbb N}(n)=1^n0$.
--   - $\mathrm{enc}_B(r)$ replaces each bit $\beta$ of $r$ by $1\beta$ and then appends $00$.
--   - $\mathrm{enc}_H(h)$ replaces each "none" by $100$ and each bit $\beta$ by $11\beta$, then appends a final $0$.
--   - $\mathrm{encOp}$ is the operation encoding above.
--
--   The number of qubits on which the operations act is exactly $n$.
--
--   ### QAlgorithms.Stabilizer.MCCFamily.step
--
--   Given a family $F$, a natural number $n$, a bit string $r$, and a pair $(\psi,h)$, this defines a probability distribution on such pairs. Here $\psi\in\mathbb C^{\{0,1\}^n}$ is any vector, not necessarily of norm $1$, and $h$ is a history list. The result depends on $\mathrm{ctrl}(n,r,h)$.
--
--   **If $\mathrm{ctrl}(n,r,h)$ is nothing:** the point mass at $(\psi,h)$.
--
--   **If $\mathrm{ctrl}(n,r,h)$ is a measurement of $M=(M_0,\dots,M_{n-1})$:** let $P_M$ be the $2^n\times 2^n$ matrix with entries
--   $$(P_M)_{y,z}=\prod_{q=0}^{n-1}(\sigma_{M_q})_{y_q,z_q},$$
--   i.e. the tensor product of the Pauli matrices, with phase $1$. Here $\sigma_I=\mathbf 1$, $\sigma_X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $\sigma_Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$, and $\sigma_Z=\mathrm{diag}(1,-1)$, indexed by $\{0,1\}$. Set
--   $$\Pi_{\mathrm{true}}=\tfrac12(\mathbf 1-P_M),\qquad \Pi_{\mathrm{false}}=\tfrac12(\mathbf 1+P_M),\qquad p=\min\!\big(1,\ \|\Pi_{\mathrm{true}}\psi\|^2\big).$$
--   A bit $\beta$ is drawn with $\Pr[\beta=\mathrm{true}]=p$ and $\Pr[\beta=\mathrm{false}]=1-p$. Note that this is $1-p$, not $\|\Pi_{\mathrm{false}}\psi\|^2$; the two agree only when $\|\psi\|=1$. The outcome is the pair
--   $$\Big(\|\Pi_\beta\psi\|^{-1}\,\Pi_\beta\psi,\ \ h \Vert [\beta]\Big),$$
--   with the convention $0^{-1}=0$. So if $\Pi_\beta\psi=0$, the new vector is the zero vector.
--
--   **If $\mathrm{ctrl}(n,r,h)$ is any other operation $o$:** the point mass at $(U_o\psi,\ h\Vert[\text{none}])$. The matrix $U_o$ is the $2^n\times2^n$ matrix acting as follows, and as the identity on all other qubits:
--
--   - the Pauli $\sigma_P$ on qubit $q$, for a Pauli operation;
--   - the Hadamard $\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ on qubit $q$;
--   - $S=\mathrm{diag}(1,i)$ on qubit $q$;
--   - for a CNOT, the map $|a,b\rangle\mapsto|a,b\oplus a\rangle$ with $a$ on qubit $c$ and $b$ on qubit $t$.
--
--   ### QAlgorithms.Stabilizer.MCCFamily.run
--
--   Given a family $F$, a natural number $n$, a bit string $r$, and a basis label $x\in\{0,1\}^n$, this defines for each $k\in\mathbb N$ a probability distribution $\mathrm{run}_k$ on pairs (vector in $\mathbb C^{\{0,1\}^n}$, history). It is defined recursively:
--
--   - $\mathrm{run}_0$ is the point mass at $(|x\rangle,[\,])$, where $|x\rangle$ is the standard basis vector at $x$ and $[\,]$ is the empty history.
--   - $\mathrm{run}_{k+1}$ is obtained by drawing a pair from $\mathrm{run}_k$ and then applying the random transition $\mathrm{step}(F,n,r,\cdot)$ to it.
--
--   In other words, $\mathrm{run}_k$ is the distribution after $k$ steps of the Markov chain started at $(|x\rangle,[\,])$.
--
--   ### QAlgorithms.Stabilizer.MCCFamily.finalDist
--
--   Given a family $F$, a natural number $n$, and $x\in\{0,1\}^n$, this is a probability distribution on $2^n\times2^n$ complex matrices, sampled in three stages:
--
--   1. Draw a bit string $r$ uniformly at random from $\{0,1\}^{\mathrm{rbits}(n)}$. If $\mathrm{rbits}(n)=0$, this is the single empty string.
--   2. Draw $(\psi,h)$ from $\mathrm{run}_{\mathrm{steps}(n)}$ with parameters $F,n,r,x$.
--   3. Output the matrix $|\psi\rangle\langle\psi|$, with entries $(a,b)\mapsto\psi_a\overline{\psi_b}$.
--
--   The history $h$ is discarded.
--
--   ### QAlgorithms.Stabilizer.RandPolyTimeSampler
--
--   A structure consisting of three components:
--
--   - a polynomial $\mathrm{rbits}$ with natural-number coefficients;
--   - a function $f$ from finite bit strings to finite bit strings;
--   - a proof that $f$ is polynomial-time computable, in the sense of Mathlib's TM2 polynomial-time computability with bit strings encoded as themselves.
--
--   ### QAlgorithms.Stabilizer.RandPolyTimeSampler.outDist
--
--   Given a sampler $A=(\mathrm{rbits},f,\cdot)$ and an input bit string $w$, this is the probability distribution on bit strings obtained as follows:
--
--   1. Draw $r$ uniformly at random from $\{0,1\}^{\mathrm{rbits}(|w|)}$, where $|w|$ is the length of $w$.
--   2. Output
--   $$f\big(w\Vert \mathrm{enc}_B(r)\big).$$
--
--   Here $\mathrm{enc}_B(r)$ replaces each bit $\beta$ of $r$ by $1\beta$ and then appends $00$. The input $w$ itself is concatenated raw, without any delimiter.
--
--   ### QAlgorithms.Stabilizer.encInput
--
--   For a natural number $n$ and $x=(x_0,\dots,x_{n-1})\in\{0,1\}^n$, this is the bit string
--   $$1^n\,0\ \Vert\ x_0x_1\cdots x_{n-1}.$$
--   That is, $n$ is written in unary as $n$ ones followed by a zero, and then the bits of $x$ follow in index order. For $n=0$ the result is the single bit $0$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Stabilizer.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_LinearSystems
import Definitions.Def_QAlgorithms_ClassicalStringComputability

/-!
# Stabilizer states, measurement-controlled Clifford circuits, classical samplers
(shared definition layer)

de Wolf §20.1–20.3 (pp.185–188), for the Gottesman–Knill theorem (Theorem 6).
-/

namespace QAlgorithms.Stabilizer

open scoped NNReal

open QAlgorithms.Complexity

/-- de Wolf p.185 (§20.1): the one-qubit Paulis `I, X, Y, Z`. -/
inductive Pauli where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq

/-- The matrix of a one-qubit Pauli (`pauliX`, `pauliY`, `pauliZ` of the Gates module). -/
def Pauli.mat : Pauli → Matrix Bool Bool ℂ
  | .I => 1
  | .X => pauliX
  | .Y => pauliY
  | .Z => pauliZ

/-- The product of two one-qubit Paulis, as `i^c · R` (`XY = iZ`, `YX = −iZ`, `YZ = iX`, `ZY = −iX`,
`ZX = iY`, `XZ = −iY`; `P P = I`). -/
def Pauli.mul : Pauli → Pauli → ZMod 4 × Pauli
  | .I, q => (0, q)
  | p, .I => (0, p)
  | .X, .X => (0, .I)
  | .Y, .Y => (0, .I)
  | .Z, .Z => (0, .I)
  | .X, .Y => (1, .Z)
  | .Y, .X => (3, .Z)
  | .Y, .Z => (1, .X)
  | .Z, .Y => (3, .X)
  | .Z, .X => (1, .Y)
  | .X, .Z => (3, .Y)

/-- de Wolf p.185 (§20.1: "`P_n = {+1, −1, +i, −i} · {I, X, Y, Z}^{⊗n}`"): an `n`-qubit Pauli with
phase `i^phase`. -/
structure PauliString (n : ℕ) where
  /-- The phase exponent: the factor is `i^phase ∈ {1, i, −1, −i}`. -/
  phase : ZMod 4
  /-- The one-qubit Pauli on each wire. -/
  ops : Fin n → Pauli

/-- The `2ⁿ × 2ⁿ` matrix `i^phase · P_1 ⊗ ⋯ ⊗ P_n` (wire `0` is the first factor). -/
noncomputable def PauliString.toMatrix {n : ℕ} (P : PauliString n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => Complex.I ^ P.phase.val * ∏ q : Fin n, (P.ops q).mat (y q) (z q)

/-- The (symbolic) product of two Pauli strings, wire by wire, with the phases collected. -/
def PauliString.mul {n : ℕ} (P Q : PauliString n) : PauliString n :=
  ⟨P.phase + Q.phase + ∑ q : Fin n, (Pauli.mul (P.ops q) (Q.ops q)).1,
    fun q => (Pauli.mul (P.ops q) (Q.ops q)).2⟩

/-- de Wolf p.185: two Pauli strings commute (as matrices). -/
def PauliString.Commute {n : ℕ} (P Q : PauliString n) : Prop :=
  P.toMatrix * Q.toMatrix = Q.toMatrix * P.toMatrix

/-- de Wolf p.185, p.187: a stabilizer description of an `n`-qubit state: `n` Pauli strings. -/
abbrev Tableau (n : ℕ) := Fin n → PauliString n

/-- The ordered product `Π_{i ∈ s} T_i` (increasing `i`) of the matrices of a subfamily. -/
noncomputable def subProd {n : ℕ} (T : Tableau n) (s : Finset (Fin n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  (List.ofFn fun i : Fin n => if i ∈ s then (T i).toMatrix else 1).prod

/-- de Wolf p.185 (§20.1 and footnote 2): `T` describes a stabilizer state: its `n` elements have
phases `±1`, pairwise commute, are independent (no element is `±1, ±i` times a product of some
other elements), and `−I` is not a product of some of them. -/
def IsValidTableau {n : ℕ} (T : Tableau n) : Prop :=
  (∀ j, (T j).phase = 0 ∨ (T j).phase = 2) ∧
  (∀ i j, (T i).Commute (T j)) ∧
  (∀ (j : Fin n) (s : Finset (Fin n)), j ∉ s → ∀ c : ZMod 4,
    (T j).toMatrix ≠ Complex.I ^ c.val • subProd T s) ∧
  ∀ s : Finset (Fin n), subProd T s ≠ -1

/-- de Wolf p.185 (footnote 3: "this global phase wouldn't even be there if we took the density
matrix view"): `Π_j (I + T_j)/2`, which for a valid tableau is the projector `|ψ⟩⟨ψ|` onto the
unique stabilized state. -/
noncomputable def tableauProjector {n : ℕ} (T : Tableau n) : Matrix (Qubits n) (Qubits n) ℂ :=
  (List.ofFn fun j : Fin n => (2⁻¹ : ℂ) • (1 + (T j).toMatrix)).prod

/-- Two bits for a one-qubit Pauli: `I = 00`, `X = 10`, `Y = 11`, `Z = 01`. -/
def encPauli : Pauli → Str
  | .I => [false, false]
  | .X => [true, false]
  | .Y => [true, true]
  | .Z => [false, true]

/-- The Pauli encoded by two bits (inverse of `encPauli`). -/
def pauliOfBits : Bool → Bool → Pauli
  | false, false => .I
  | true, false => .X
  | true, true => .Y
  | false, true => .Z

/-- Two bits for a phase exponent `c ∈ ZMod 4` (its value in binary, high bit first). -/
def encPhase (c : ZMod 4) : Str :=
  [decide (2 ≤ c.val), decide (c.val % 2 = 1)]

/-- de Wolf p.187 ("`n` stabilizers, which can be written down with `n × (2n + 2)` bits"): the
encoding of a tableau: for each stabilizer, two phase bits and two bits per qubit. -/
def encodeTableau {n : ℕ} (T : Tableau n) : Str :=
  (List.ofFn fun j : Fin n => encPhase (T j).phase ++ (List.ofFn fun q => encPauli ((T j).ops q)).flatten).flatten

/-- Reads a tableau from the first `n(2n + 2)` bits of a string (missing bits read as `0`);
the inverse of `encodeTableau`. -/
def decodeTableau (n : ℕ) (s : Str) : Tableau n :=
  fun j => ⟨(if s.getD (j * (2 * n + 2)) false then 2 else 0) +
      (if s.getD (j * (2 * n + 2) + 1) false then 1 else 0),
    fun q => pauliOfBits (s.getD (j * (2 * n + 2) + 2 + 2 * q) false)
      (s.getD (j * (2 * n + 2) + 3 + 2 * q) false)⟩

/-- de Wolf p.186 (§20.2): the operations of a measurement-controlled Clifford circuit on `n`
qubits: a Pauli gate, `H`, `S`, `CNOT` (control `c`, target `t`), or the measurement of a Pauli
`M ∈ {I, X, Y, Z}^{⊗n}` (projectors `(I ± M)/2`). -/
inductive CliffordOp (n : ℕ) where
  | pauli (q : Fin n) (P : Pauli)
  | h (q : Fin n)
  | s (q : Fin n)
  | cnot (c t : Fin n) (hct : c ≠ t)
  | measure (M : Fin n → Pauli)

/-- The single wire `q` as an embedding `Fin 1 ↪ Fin n`. -/
def wire1 {n : ℕ} (q : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => q, fun a b _ => Subsingleton.elim a b⟩

/-- The wires `(c, t)`, `c ≠ t`, as an embedding `Fin 2 ↪ Fin n`. -/
def wire2 {n : ℕ} (c t : Fin n) (hct : c ≠ t) : Fin 2 ↪ Fin n :=
  ⟨Fin.cons c fun _ : Fin 1 => t,
    Fin.cons_injective_iff.2 ⟨by rintro ⟨_, h⟩; exact hct h.symm, fun a b _ => Subsingleton.elim a b⟩⟩

/-- The unitary of a gate operation (the identity for a measurement, which is handled separately). -/
noncomputable def CliffordOp.mat {n : ℕ} : CliffordOp n → Matrix (Qubits n) (Qubits n) ℂ
  | .pauli q P => embedOp (Gate.ofMatrix1 P.mat).mat (wire1 q)
  | .h q => embedOp (Gate.ofMatrix1 hadamard).mat (wire1 q)
  | .s q => embedOp (Gate.ofMatrix1 phaseS).mat (wire1 q)
  | .cnot c t hct => embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct)
  | .measure _ => 1

/-- Self-delimiting code of a bit list: each bit `β` as `1β`, then `00`. -/
def encBits (l : List Bool) : Str :=
  l.flatMap (fun β => [true, β]) ++ [false, false]

/-- Code of a transcript: `100` for a gate step, `11β` for a measurement with outcome `β`, then `0`. -/
def encHist (hist : List (Option Bool)) : Str :=
  hist.flatMap (fun o => match o with
    | none => [true, false, false]
    | some β => [true, true, β]) ++ [false]

/-- Code of the controller's input `(n, r, transcript)`, with `n` in unary. -/
def encCtrlInput (n : ℕ) (r : List Bool) (hist : List (Option Bool)) : Str :=
  encNat n ++ encBits r ++ encHist hist

/-- Code of the controller's answer: `0` for "halt", otherwise `1`, a tag, and the arguments. -/
def encOp {n : ℕ} : Option (CliffordOp n) → Str
  | none => [false]
  | some (.pauli q P) => [true] ++ encNat 0 ++ encNat q ++ encPauli P
  | some (.h q) => [true] ++ encNat 1 ++ encNat q
  | some (.s q) => [true] ++ encNat 2 ++ encNat q
  | some (.cnot c t _) => [true] ++ encNat 3 ++ encNat c ++ encNat t
  | some (.measure M) => [true] ++ encNat 4 ++ (List.ofFn fun q => encPauli (M q)).flatten

/-- de Wolf p.186–187 (§20.2: "we can then let the next gate depend on the earlier measurement
outcomes, using some polynomial-time classical (possibly randomized) algorithm to compute what the
next gate or measurement would be"; "strictly speaking we'd have to talk about families of
circuits `{C_n}`"): a family of measurement-controlled Clifford circuits. On `n` qubits, with random
bits `r` (`rbits(n)` of them) and the transcript of the steps so far (`none` for a gate, `some β`
for a measurement with outcome `β`, `false` meaning `+1`), the controller names the next operation
or halts (`none`); it halts after at most `steps(n)` operations, and it is computable in
polynomial time from `(n, r, transcript)` (`n` in unary). -/
structure MCCFamily where
  /-- The number of random bits, a polynomial in `n`. -/
  rbits : Polynomial ℕ
  /-- The bound on the number of operations, a polynomial in `n`. -/
  steps : Polynomial ℕ
  /-- The classical controller. -/
  ctrl : (n : ℕ) → List Bool → List (Option Bool) → Option (CliffordOp n)
  /-- It halts within `steps(n)` operations. -/
  halts : ∀ n r hist, steps.eval n ≤ hist.length → ctrl n r hist = none
  /-- It is polynomial-time computable. -/
  polytime : ∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ n r hist, g (encCtrlInput n r hist) = encOp (ctrl n r hist)

/-- One step of the run with random bits `r`: query the controller on the transcript; apply a gate,
or measure the Pauli `M` (outcome `β` with Born probability `‖(I + (−1)^β M)/2 ψ‖²`, followed by
renormalization), or halt. The `min 1` only matters for non-unit `ψ`, which a run never reaches. -/
noncomputable def MCCFamily.step (F : MCCFamily) (n : ℕ) (r : List Bool)
    (st : EuclideanSpace ℂ (Qubits n) × List (Option Bool)) :
    PMF (EuclideanSpace ℂ (Qubits n) × List (Option Bool)) :=
  match F.ctrl n r st.2 with
  | none => PMF.pure st
  | some (.measure M) =>
      let proj : Bool → Matrix (Qubits n) (Qubits n) ℂ := fun β =>
        (2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))
      (PMF.bernoulli (min 1 (Real.toNNReal (‖act (proj true) st.1‖ ^ 2))) (min_le_left _ _)).map
        fun β => (((‖act (proj β) st.1‖)⁻¹ : ℝ) • act (proj β) st.1, st.2 ++ [some β])
  | some op => PMF.pure (act op.mat st.1, st.2 ++ [none])

/-- The law of the state after `k` steps, from `|x⟩` with random bits `r`. -/
noncomputable def MCCFamily.run (F : MCCFamily) (n : ℕ) (r : List Bool) (x : Qubits n) :
    ℕ → PMF (EuclideanSpace ℂ (Qubits n) × List (Option Bool))
  | 0 => PMF.pure (ket x, [])
  | k + 1 => (F.run n r x k).bind (F.step n r)

/-- de Wolf p.187 (§20.2–20.3: the circuit "samples from a probability distribution over
stabilizer states"): the law of the final state `|ψ_final⟩⟨ψ_final|` (a density matrix, so the
global phase is discarded) when the circuit runs on `|x⟩` with uniformly random bits `r` and Born
measurement outcomes. -/
noncomputable def MCCFamily.finalDist (F : MCCFamily) (n : ℕ) (x : Qubits n) :
    PMF (Matrix (Qubits n) (Qubits n) ℂ) :=
  (PMF.uniformOfFintype (Fin (F.rbits.eval n) → Bool)).bind fun r =>
    (F.run n (List.ofFn r) x (F.steps.eval n)).map fun st => pureDensity st.1

/-- de Wolf p.26 (§2.2: randomized algorithms receive random bits as an extra input), p.187
(Theorem 6: "a classical polynomial-time algorithm that … samples"): a classical randomized
polynomial-time algorithm: a polynomial-time computable `f` run on the input followed by
`rbits(|w|)` uniformly random bits. -/
structure RandPolyTimeSampler where
  /-- The number of random bits, a polynomial in the input length. -/
  rbits : Polynomial ℕ
  /-- The deterministic polynomial-time part. -/
  f : Str → Str
  /-- `f` is polynomial-time computable. -/
  polytime : PolyTimeComputable f

/-- The output distribution of the sampler on input `w`. -/
noncomputable def RandPolyTimeSampler.outDist (A : RandPolyTimeSampler) (w : Str) : PMF Str :=
  (PMF.uniformOfFintype (Fin (A.rbits.eval w.length) → Bool)).map fun r => A.f (w ++ encBits (List.ofFn r))

/-- The input `(n, x)` of the simulator: `n` in unary, then the bits of `x`. -/
def encInput (n : ℕ) (x : Qubits n) : Str :=
  encNat n ++ List.ofFn x

/-! ### Sanity tests -/

example : Pauli.mul .X .Y = (1, .Z) := rfl

/-- `XY = iZ` as matrices, matching `Pauli.mul .X .Y = (1, .Z)`. -/
example : pauliX * pauliY = Complex.I • pauliZ := by
  ext a b
  cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool]

/-- The one-qubit `Z` stabilizer `+Z` projects onto `|0⟩`: `(I + Z)/2 = |0⟩⟨0|`. -/
example : tableauProjector (fun _ : Fin 1 => (⟨0, fun _ => .Z⟩ : PauliString 1))
    (fun _ => false) (fun _ => false) = 1 := by
  simp [tableauProjector, PauliString.toMatrix, Pauli.mat, pauliZ]
  norm_num

/-- Encoding then decoding a tableau gives it back (here `n = 1`, the stabilizer `−Y`). -/
example : (decodeTableau 1 (encodeTableau fun _ : Fin 1 => (⟨2, fun _ => .Y⟩ : PauliString 1)) 0).phase
    = 2 ∧ (decodeTableau 1 (encodeTableau fun _ : Fin 1 => (⟨2, fun _ => .Y⟩ : PauliString 1)) 0).ops 0
    = .Y := by
  decide

/-- With zero steps, a circuit outputs its initial basis state. -/
example (F : MCCFamily) (n : ℕ) (r : List Bool) (x : Qubits n) : F.run n r x 0 = PMF.pure (ket x, []) :=
  rfl

end QAlgorithms.Stabilizer


