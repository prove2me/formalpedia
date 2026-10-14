-- Prove2me | Definitions.Def_QAlgorithms_Defs_Circuit
-- name    : QAlgorithms_Defs_Circuit
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:25:09.893862+00:00
-- url     : https://prove2.me/theorems/dc785940-30f0-4e77-9435-adbb2ba2b1f5
-- title:
--   Quantum circuits over a gate set (shared definition layer)
-- statement:
--   Quantum circuits over a gate set (shared definition layer)
--
--   ### QAlgorithms.Gate
--
--   A *gate* is a pair $(k, M)$ consisting of:
--
--   - an **arity** $k\in\mathbb{N}$, and
--   - a complex matrix $M$ whose rows and columns are indexed by $\{0,1\}^k$. Here $\{0,1\}^k$ means all functions $\{0,\dots,k-1\}\to\{\mathsf{false},\mathsf{true}\}$, i.e. bit strings of length $k$. So $M$ has size $2^k\times 2^k$.
--
--   No condition is imposed on $M$. In particular:
--
--   - $M$ need not be unitary or even invertible; any $2^k\times 2^k$ complex matrix, including the zero matrix, gives a gate.
--   - Arity $k=0$ is allowed. In that case $M$ is a $1\times 1$ matrix, i.e. a single complex number.
--
--   ### QAlgorithms.Gate.IsUnitary
--
--   For a gate $g=(k,M)$, the proposition "$g$ is unitary" asserts that $M$ belongs to the unitary group of $2^k\times 2^k$ complex matrices indexed by $\{0,1\}^k$. That is,
--
--   $$
--   M^\dagger M = I \quad\text{and}\quad M M^\dagger = I,
--   $$
--
--   where $M^\dagger$ is the conjugate transpose of $M$ and $I$ is the identity matrix on $\{0,1\}^k$. For arity $0$, this says the single entry of $M$ is a complex number of modulus $1$.
--
--   ### QAlgorithms.Gate.ofMatrix1
--
--   Given any complex $2\times 2$ matrix $M$ with rows and columns indexed by $\{\mathsf{false},\mathsf{true}\}$, this produces the gate of arity $1$ whose matrix $M'$ is indexed by bit strings $b,b'\in\{0,1\}^1$. Its entries are
--
--   $$
--   M'_{b,b'} \;=\; M_{b(0),\,b'(0)}.
--   $$
--
--   That is, the one-bit string $b$ is identified with its single bit $b(0)$, and $M$ is copied over unchanged. No unitarity of $M$ is assumed.
--
--   ### QAlgorithms.Gate.ofMatrix2
--
--   Given any complex $4\times4$ matrix $M$ with rows and columns indexed by pairs in $\{\mathsf{false},\mathsf{true}\}^2$, this produces the gate of arity $2$ whose matrix $M'$ is indexed by bit strings $b,b'\in\{0,1\}^2$. Its entries are
--
--   $$
--   M'_{b,b'} \;=\; M_{(b(0),\,b(1)),\,(b'(0),\,b'(1))}.
--   $$
--
--   So bit $0$ of the string corresponds to the **first** component of the pair, and bit $1$ to the **second**. For example, applied to $\mathrm{CNOT}$, the gate's wire $0$ is the control and wire $1$ is the target. No unitarity of $M$ is assumed.
--
--   ### QAlgorithms.embedOp
--
--   The inputs are:
--
--   - natural numbers $k$ and $n$;
--   - an arbitrary complex matrix $M$ indexed by $\{0,1\}^k\times\{0,1\}^k$ (bit strings of length $k$);
--   - an injective map $w:\{0,\dots,k-1\}\to\{0,\dots,n-1\}$, which places the $j$-th qubit of $M$ on wire $w(j)$.
--
--   Because $w$ must be injective, such a $w$ exists only when $k\le n$. For $k=0$, $w$ is the empty map.
--
--   The output is the matrix $E_w(M)$ indexed by $\{0,1\}^n\times\{0,1\}^n$. For $y,z\in\{0,1\}^n$, let $y\circ w\in\{0,1\}^k$ denote the string $j\mapsto y(w(j))$, i.e. the bits of $y$ read off at the wires $w(0),\dots,w(k-1)$, in that order. The entries are
--
--   $$
--   E_w(M)_{y,z} \;=\; \begin{cases} M_{\,y\circ w,\; z\circ w} & \text{if } y(a)=z(a) \text{ for every wire } a \notin \{w(0),\dots,w(k-1)\},\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   In words, $M$ acts on the wires in the image of $w$, in the order given by $w$, and the identity acts on all other wires. The ordering is not required to be monotone.
--
--   Two edge cases:
--
--   - If $k=0$, then $M$ is a scalar $c$, and $E_w(M)=c\,I$.
--   - If $w$ is a bijection, $E_w(M)$ is $M$ with its qubits relabelled by $w$.
--
--   ### QAlgorithms.GateApp
--
--   Fix a set $S$ of gates (an arbitrary set of pairs (arity, matrix) as above) and a number of wires $n\in\mathbb{N}$. A *gate application* over $S$ on $n$ wires consists of three pieces of data:
--
--   - a gate $g=(k,M)$;
--   - a proof that $g\in S$;
--   - an injective map $w:\{0,\dots,k-1\}\to\{0,\dots,n-1\}$, saying which wire carries each of the gate's $k$ qubits.
--
--   Injectivity forces $k\le n$. Nothing further is required. In particular, no unitarity is required unless $S$ itself contains only unitary gates.
--
--   ### QAlgorithms.Circuit
--
--   For a gate set $S$ and a wire count $n\in\mathbb{N}$, a *circuit* over $S$ on $n$ wires is a finite list $(g_1,\dots,g_m)$ of gate applications over $S$ on $n$ wires, in the sense of the previous definition. The list's order is part of the data, and the length $m$ may be $0$ (the empty circuit). Repetitions are allowed. This declaration assigns no matrix or semantics to the list; it is only the data type.
--
--   ### QAlgorithms.Circuit.unitary
--
--   **Setting.** Fix a set $S$ of gates and a number of wires $n \in \mathbb{N}$.
--
--   - A *gate* is a pair consisting of an arity $k \in \mathbb{N}$ and an arbitrary complex $2^k \times 2^k$ matrix $M$. Its rows and columns are indexed by bit strings $\{0,1\}^k$. Nothing here requires $M$ to be unitary.
--   - A *gate application* on $n$ wires consists of a gate $g \in S$ of arity $k$ together with an injective map $w : \{0,\dots,k-1\} \to \{0,\dots,n-1\}$ assigning its wires.
--   - A circuit $c$ is a finite list $c = (g_1, \dots, g_m)$ of gate applications, possibly empty.
--
--   **Embedding a gate.** Each application $g_j$, with matrix $M_j$ and wire map $w_j$, is turned into the $2^n \times 2^n$ matrix $E_j$, indexed by $y, z \in \{0,1\}^n$:
--
--   $$
--   (E_j)_{y,z} \;=\; \begin{cases} (M_j)_{\,y\circ w_j,\; z\circ w_j} & \text{if } y_a = z_a \text{ for every wire } a \notin \operatorname{range}(w_j),\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   Here $y \circ w_j$ is the $k$-bit string read off $y$ at the wires $w_j(0), \dots, w_j(k-1)$, in that order. In words, $E_j$ is $M_j$ acting on the selected wires, tensored with the identity on the remaining wires.
--
--   **The circuit matrix.** The matrix of $c$ is the product in reverse list order, so the first gate in the list acts first on column vectors:
--
--   $$
--   U_c \;=\; E_m E_{m-1} \cdots E_1 .
--   $$
--
--   For the empty circuit, $U_c$ is the $2^n \times 2^n$ identity. $U_c$ is unitary whenever all the gate matrices are, but the definition does not assume this.
--
--   ### QAlgorithms.Circuit.size
--
--   For a gate set $S$, a number of wires $n$, and a circuit $c$ on $n$ wires over $S$ (a finite list of gate applications as described above), the size of $c$ is the length of the list. That is, it is the total number of gate applications, counted with repetition.
--
--   - The empty circuit has size $0$.
--   - No account is taken of depth, gate arity, or which gates are used.
--
--   ### QAlgorithms.inputState
--
--   Given $n \in \mathbb{N}$, a bit string $x \in \{0,1\}^n$, and a number $w \in \mathbb{N}$ of extra wires, the input state is a vector in $\mathbb{C}^{\{0,1\}^{n+w}}$, the $2^{n+w}$-dimensional complex Euclidean space with coordinates indexed by bit strings of length $n+w$. It is the standard basis vector
--
--   $$
--   |x\,0^w\rangle \;=\; e_{(x_0,\dots,x_{n-1},0,\dots,0)},
--   $$
--
--   which has a $1$ in the coordinate of the concatenated string ($x$ followed by $w$ zeros) and $0$ elsewhere.
--
--   - When $w = 0$, this is just $e_x$.
--   - When $n = 0$, it is $e_{0^w}$.
--
--   ### QAlgorithms.Circuit.ComputesBool
--
--   **Data.**
--
--   - A gate set $S$ and natural numbers $n$ (input length) and $w$ (number of ancilla wires).
--   - A circuit $c$ over $S$ on $n+w$ wires, with matrix $U_c = E_m \cdots E_1$ as in `Circuit.unitary`.
--   - An output wire $\mathrm{out} \in \{0, \dots, n+w-1\}$.
--   - A Boolean function $f : \{0,1\}^n \to \{0,1\}$.
--
--   **Assertion.** "$c$ computes $f$" means: for every input $x \in \{0,1\}^n$, let
--
--   $$
--   \psi_x = U_c\, e_{x0^w}
--   $$
--
--   be the result of applying the matrix $U_c$ to the basis vector of $x$ followed by $w$ zeros. Then
--
--   $$
--   \sum_{\substack{z \in \{0,1\}^{n+w} \\ z_{\mathrm{out}} = f(x)}} \bigl|\langle e_z, \psi_x\rangle\bigr|^2 \;=\; \sum_{\substack{z \\ z_{\mathrm{out}} = f(x)}} |(\psi_x)_z|^2 \;\ge\; \frac{2}{3}.
--   $$
--
--   **Remarks.**
--
--   - The bound $2/3$ is non-strict and the same for every $x$.
--   - The output wire may be one of the first $n$ (input) wires or one of the ancilla wires.
--   - Gate matrices are not required to be unitary. So $\psi_x$ need not be a unit vector, and the left-hand side is then not necessarily a probability; it could even exceed $1$.
--   - When $n = 0$, there is a single input, the empty string.
--
--   ### QAlgorithms.ApproxUpToPhase
--
--   **Data.** A finite index set $\iota$ with decidable equality, two complex $\iota \times \iota$ matrices $U$ and $V$, and a real number $\varepsilon$.
--
--   **Assertion.** $U$ approximates $V$ up to phase within $\varepsilon$ if there exists a real $\theta$ such that
--
--   $$
--   \bigl\| U - e^{i\theta} V \bigr\|_{\mathrm{op}} \;\le\; \varepsilon .
--   $$
--
--   Here $\|\cdot\|_{\mathrm{op}}$ is the spectral norm, i.e. the operator norm induced by the Euclidean norm on $\mathbb{C}^\iota$.
--
--   **Remarks.**
--
--   - The inequality is non-strict.
--   - If $\varepsilon < 0$ the condition can never hold.
--   - No unitarity of $U$ or $V$ is assumed.
--
--   ### QAlgorithms.IsUniversal
--
--   A set $S$ of gates is called universal if the following holds for every $k \in \mathbb{N}$, every unitary $2^k \times 2^k$ complex matrix $U$, and every real $\delta > 0$. Here $U$ has rows and columns indexed by $\{0,1\}^k$, and unitary means $U^* U = U U^* = I$.
--
--   There exists a circuit $c$ over $S$ on exactly $k$ wires whose matrix $U_c$ satisfies
--
--   $$
--   \exists\, \theta \in \mathbb{R}:\quad \bigl\| U - e^{i\theta}\, U_c \bigr\|_{\mathrm{op}} \le \delta .
--   $$
--
--   Here $U_c = E_m \cdots E_1$ is the reverse-order product of the embedded gate matrices, as in `Circuit.unitary`, and $\|\cdot\|_{\mathrm{op}}$ is the spectral norm.
--
--   **Remarks.**
--
--   - No ancilla wires are allowed: the circuit acts on the same $k$ wires as $U$.
--   - Every gate application needs an injective wire map, so only gates of arity at most $k$ can appear in a circuit on $k$ wires.
--   - The case $k = 0$ is included. There $U$ is a $1 \times 1$ unit-modulus scalar, and the empty circuit has matrix $I$.
--   - The gates in $S$ themselves are not required to be unitary.
--
--   ### QAlgorithms.ClosedUnderInverse
--
--   A set $S$ of gates is closed under inverse if, for every gate $g \in S$ with arity $k$ and matrix $M$, the gate with the same arity $k$ and matrix $M^*$ also belongs to $S$. Here $M^*$ is the conjugate transpose of $M$.
--
--   The condition uses the conjugate transpose, not the matrix inverse. The two coincide only when $M$ is unitary, which is not assumed.
--
--   ### QAlgorithms.su2Ball
--
--   For a real number $\varepsilon$, this is the subset of the special unitary group
--
--   $$
--   \mathrm{SU}(2) = \{U \in \mathbb{C}^{2\times 2} : U^*U = UU^* = I,\ \det U = 1\}
--   $$
--
--   given by
--
--   $$
--   \mathrm{Ball}(\varepsilon) \;=\; \{\, U \in \mathrm{SU}(2) \;:\; \| I - U \|_{\mathrm{op}} \le \varepsilon \,\}.
--   $$
--
--   Here $\|\cdot\|_{\mathrm{op}}$ is the spectral norm.
--
--   - The inequality is non-strict.
--   - For $\varepsilon < 0$ the set is empty.
--   - For $\varepsilon = 0$ the set is $\{I\}$.
--
--   ### QAlgorithms.IsNet
--
--   **Data.** Two subsets $\Gamma, S \subseteq \mathrm{SU}(2)$ (special unitary $2\times 2$ complex matrices) and a real number $\varepsilon$.
--
--   **Assertion.** $\Gamma$ is an $\varepsilon$-net for $S$ if
--
--   $$
--   \forall A \in S\ \ \exists U \in \Gamma:\quad \| A - U \|_{\mathrm{op}} \le \varepsilon ,
--   $$
--
--   where $\|\cdot\|_{\mathrm{op}}$ is the spectral norm.
--
--   **Remarks.**
--
--   - $\Gamma$ is not required to be contained in $S$.
--   - If $S$ is empty, the condition holds vacuously for every $\Gamma$ and $\varepsilon$.
--   - If $S$ is nonempty and either $\Gamma$ is empty or $\varepsilon < 0$, the condition fails.
--
--   ### QAlgorithms.commutatorSet
--
--   For a subset $\Gamma \subseteq \mathrm{SU}(2)$, this is the set of all group commutators of pairs of elements of $\Gamma$:
--
--   $$
--   [\Gamma,\Gamma]_{\mathrm{set}} \;=\; \{\, W \in \mathrm{SU}(2) \;:\; \exists\, U, V \in \Gamma,\ W = U V U^{-1} V^{-1} \,\}.
--   $$
--
--   Here $U^{-1}$ is the group inverse in $\mathrm{SU}(2)$, which equals $U^*$.
--
--   - $U = V$ is allowed, giving $W = I$. So $I$ belongs to the set whenever $\Gamma \neq \emptyset$.
--   - If $\Gamma$ is empty, the set is empty.
--   - This is only the set of single commutators, not the subgroup they generate.
--
--   ### QAlgorithms.OracleStep
--
--   **Parameters.**
--
--   - A gate set $S$.
--   - A number of oracles $r \in \mathbb{N}$.
--   - An arity function $a : \{0,\dots,r-1\} \to \mathbb{N}$, where oracle $k$ acts on $a_k$ qubits.
--   - A number of wires $n$.
--
--   **The data type.** An oracle step is exactly one of two kinds of data.
--
--   1. **A gate step.** This is a gate application on $n$ wires: a gate from $S$ of some arity $\ell$ together with an injective wire map $\{0,\dots,\ell-1\} \to \{0,\dots,n-1\}$.
--   2. **A query step.** This consists of:
--      - an oracle index $k \in \{0,\dots,r-1\}$;
--      - a Boolean flag "adjoint";
--      - an optional control wire, either none or some $c \in \{0,\dots,n-1\}$;
--      - an injective wire map $w : \{0,\dots,a_k-1\} \to \{0,\dots,n-1\}$;
--      - a guarantee that, if a control wire $c$ is present, then $c \notin \operatorname{range}(w)$.
--
--   **Remarks.**
--
--   - This declaration only specifies the data. It assigns no matrix or meaning to a step.
--   - If $r = 0$, no query steps exist, and every step is a gate step.
--   - If $a_k > n$, there are no query steps to oracle $k$, since no injective wire map exists.
--
--   ### QAlgorithms.OracleCircuit
--
--   Given a gate set $S$, a number of oracles $r$, an arity function $a : \{0,\dots,r-1\} \to \mathbb{N}$, and a number of wires $n$, an oracle circuit is a finite, ordered, possibly empty list of oracle steps $(s_1, \dots, s_m)$.
--
--   Each step $s_j$ is either:
--
--   - a gate application from $S$ on $n$ wires, or
--   - a query to some oracle $k$, recording an adjoint flag, an optional control wire, and an injective placement of the oracle's $a_k$ wires among the $n$ wires, with the control wire, if present, distinct from those wires.
--
--   Repetitions are allowed, and there is no bound on the length.
--
--   ### QAlgorithms.controlledQubits
--
--   Let $m \in \mathbb{N}$ and let $M$ be any complex matrix whose rows and columns are indexed by bit strings $y \in \{0,1\}^m$, i.e. functions $\{0,\dots,m-1\} \to \{\text{false},\text{true}\}$. Here true is read as $1$ and false as $0$. No unitarity or other condition is imposed on $M$.
--
--   The definition produces a matrix $C(M)$ indexed by bit strings of length $m+1$. For such a string $y = (y_0, y_1, \dots, y_m)$, write $y_0$ for its first bit and $\bar y = (y_1,\dots,y_m) \in \{0,1\}^m$ for the remaining bits. The entries are
--
--   $$
--   C(M)_{y,z} = \begin{cases} M_{\bar y, \bar z} & \text{if } y_0 = z_0 = 1,\\ \delta_{\bar y, \bar z} & \text{if } y_0 = z_0 = 0,\\ 0 & \text{if } y_0 \neq z_0. \end{cases}
--   $$
--
--   Equivalently, it is the block matrix $|0\rangle\langle 0| \otimes I + |1\rangle\langle 1| \otimes M$. Coordinate $0$ is the control bit, and $M$ acts on the last $m$ coordinates. This comes from the general "controlled" construction: on index pairs $(p,q)$ it is $0$ unless the control bits agree, $M$ when both control bits are $1$, and the identity when both are $0$.
--
--   ### QAlgorithms.OracleStep.mat
--
--   **Setting.**
--
--   - $S$ is a set of gates. A gate consists of an arity $k$ and an arbitrary complex $2^k \times 2^k$ matrix on $\{0,1\}^k$; unitarity is not required.
--   - $r \in \mathbb{N}$ is a number of oracles, and $a = (a_0,\dots,a_{r-1})$ gives the number of qubits $a_k$ of oracle $k$.
--   - $n$ is the number of circuit wires.
--   - $\mathrm{orc}$ is an arbitrary family of complex matrices $O_k$, each indexed by $\{0,1\}^{a_k}$. Again, no unitarity is assumed.
--
--   **Steps.** An oracle-circuit step is one of two kinds:
--
--   - **A gate application.** This is a gate $g \in S$ of arity $k$ together with an injective wire assignment $w : \{0,\dots,k-1\} \hookrightarrow \{0,\dots,n-1\}$.
--   - **A query.** This consists of:
--     - an oracle index $k < r$;
--     - a Boolean "adjoint" flag;
--     - an optional control wire $c$;
--     - an injective wire assignment $w : \{0,\dots,a_k-1\} \hookrightarrow \{0,\dots,n-1\}$;
--     - the requirement that a control wire $c$, if present, is not in the image of $w$.
--
--   **Embedding.** Throughout, the embedding $\mathrm{Emb}(N, w)$ of a $k$-qubit matrix $N$ along an injection $w$ is the $2^n \times 2^n$ matrix given by
--
--   $$
--   \mathrm{Emb}(N,w)_{y,z} = \begin{cases} N_{y\circ w,\; z \circ w} & \text{if } y_a = z_a \text{ for every wire } a \notin \operatorname{im} w,\\ 0 & \text{otherwise.} \end{cases}
--   $$
--
--   Here $y \circ w$ is the $k$-bit string $(y_{w(0)},\dots,y_{w(k-1)})$.
--
--   **The matrix of a step.** The definition assigns to each step a $2^n\times 2^n$ matrix as follows:
--
--   - **Gate step** $(g, w)$: the matrix is $\mathrm{Emb}(\text{matrix of } g,\, w)$.
--   - **Uncontrolled query** $(k, \text{adj}, \text{none}, w)$: the matrix is $\mathrm{Emb}(\tilde O_k, w)$. Here $\tilde O_k = O_k^{*}$ (the conjugate transpose) if adj is true, and $\tilde O_k = O_k$ otherwise.
--   - **Controlled query** $(k, \text{adj}, c, w)$: the matrix is $\mathrm{Emb}\big(C(\tilde O_k), w'\big)$.
--     - $C$ is the controlled construction defined in the previous entry: control on its first coordinate, $\tilde O_k$ on the rest.
--     - $w' : \{0,\dots,a_k\} \hookrightarrow \{0,\dots,n-1\}$ sends $0 \mapsto c$ and $i+1 \mapsto w(i)$. It is injective because $c \notin \operatorname{im} w$.
--
--   ### QAlgorithms.OracleCircuit.unitary
--
--   With the setting of the previous entry, an oracle circuit is a finite list of steps $c = (s_1, \dots, s_L)$. Given an oracle family $\mathrm{orc} = (O_k)$, let $M_i$ be the matrix assigned to $s_i$ by the step-matrix definition above. The circuit's matrix is the product in reverse list order:
--
--   $$
--   U_c(\mathrm{orc}) = M_L \, M_{L-1} \cdots M_1 .
--   $$
--
--   So the first step in the list is applied first to a column vector. For the empty list ($L = 0$) the result is the $2^n \times 2^n$ identity.
--
--   Despite the name, the result is just a matrix product. It is unitary only when the gate matrices and oracles involved are; neither is assumed.
--
--   ### QAlgorithms.OracleStep.IsQueryTo
--
--   For a fixed oracle index $k < r$, this is a Boolean-valued test on a single oracle-circuit step:
--
--   - A gate-application step returns false.
--   - A query step returns true exactly when its oracle index $k'$ equals $k$.
--
--   The adjoint flag, the presence or absence of a control wire, and the wire assignment are all ignored.
--
--   ### QAlgorithms.OracleCircuit.queryCount
--
--   For an oracle circuit $c = (s_1,\dots,s_L)$ and an oracle index $k < r$, the query count is
--
--   $$
--   \#\{\, i \in \{1,\dots,L\} : s_i \text{ is a query step with oracle index } k \,\}.
--   $$
--
--   Occurrences are counted with multiplicity along the list. Adjoint queries and controlled queries each count as one query, exactly like plain queries to $O_k$. For the empty circuit the count is $0$.
--
--   ### QAlgorithms.OracleCircuit.gateCount
--
--   For an oracle circuit $c = (s_1,\dots,s_L)$, the gate count is the number of indices $i$ such that $s_i$ is a gate-application step (as opposed to a query step of any kind). Occurrences are counted with multiplicity, and the count is $0$ for the empty circuit.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Circuit.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Gates
/-!
# Quantum circuits over a gate set (shared definition layer)

A gate is a matrix on `k` qubits; a circuit on `n` wires is a list of gates from a gate set,
each placed on an ordered tuple of distinct wires, applied in list order (head first). Its size
is the number of gates. Oracle circuits add black-box calls, so that statements counting both
queries and other gates can be stated (de Wolf §2.4, the CKS cost model).
-/

namespace QAlgorithms

/-- de Wolf p.26 (§2.1.2), p.121 (§13.1); Childs p.9 (§1.2): an elementary gate, a matrix acting
on `arity` qubits (wire `a` of the gate is the `a`-th tensor factor, most significant first).
A gate set is a `Set Gate`. Unitarity is the separate predicate `Gate.IsUnitary`, because a gate
set's being unitary is a hypothesis of the source's statements. -/
structure Gate where
  /-- The number of qubits the gate acts on. -/
  arity : ℕ
  /-- The gate's matrix on `arity` qubits. -/
  mat : Matrix (Qubits arity) (Qubits arity) ℂ

/-- de Wolf p.26 (§2.1.2): a quantum gate is a unitary transformation. -/
def Gate.IsUnitary (g : Gate) : Prop :=
  g.mat ∈ Matrix.unitaryGroup (Qubits g.arity) ℂ

/-- A single-qubit matrix (indexed by `Bool`) as an arity-1 gate. -/
def Gate.ofMatrix1 (M : Matrix Bool Bool ℂ) : Gate :=
  ⟨1, M.submatrix (fun b => b 0) (fun b => b 0)⟩

/-- A two-qubit matrix (indexed by `Bool × Bool`) as an arity-2 gate; gate wire `0` is the first
factor (the control of `cnot` and of a `controlled` gate). -/
def Gate.ofMatrix2 (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Gate :=
  ⟨2, M.submatrix (fun b => (b 0, b 1)) (fun b => (b 0, b 1))⟩

/-- Childs p.9 (§1.2), de Wolf p.26 (§2.1.2), p.129 (§14.2, Definition 2): the operator `M` on
`k` qubits applied to the ordered tuple of distinct wires `w` of an `n`-qubit register, tensored
with the identity on the other wires (gate wire `a` is register wire `w a`). Its `(y, z)` entry is
`M (y ∘ w) (z ∘ w)` when `y` and `z` agree off the range of `w`, and `0` otherwise. -/
def embedOp {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z =>
    if ∀ a : Fin n, a ∉ Set.range w → y a = z a then M (y ∘ w) (z ∘ w) else 0

/-- de Wolf p.26, Childs p.9: one gate of a circuit over the gate set `S` on `n` wires: a gate of
`S` and the distinct wires it acts on. -/
structure GateApp (S : Set Gate) (n : ℕ) where
  /-- The gate. -/
  gate : Gate
  /-- It belongs to the gate set. -/
  mem : gate ∈ S
  /-- The register wires it acts on, in the order of the gate's own wires. -/
  wires : Fin gate.arity ↪ Fin n

/-- de Wolf p.26 (§2.1.2), p.121 (§13.1); Childs p.9 (§1.2), p.10 (§1.3): a quantum circuit on
`n` wires over the gate set `S`, a list of gate applications performed in list order (head
first). -/
abbrev Circuit (S : Set Gate) (n : ℕ) := List (GateApp S n)

/-- The unitary `U_t ⋯ U_2 U_1` implemented by the circuit `[U_1, …, U_t]` (the first gate is the
rightmost factor; the empty circuit implements the identity). -/
def Circuit.unitary {S : Set Gate} {n : ℕ} (c : Circuit S n) : Matrix (Qubits n) (Qubits n) ℂ :=
  (c.map fun g => embedOp g.gate.mat g.wires).reverse.prod

/-- de Wolf p.25–26, Childs p.9: the size of a circuit, its number of elementary gates. -/
def Circuit.size {S : Set Gate} {n : ℕ} (c : Circuit S n) : ℕ :=
  c.length

/-- de Wolf p.121 (§13.1): the initial state `|x, 0^w⟩`: the input `x` on wires `0, …, n-1`
followed by `w` workspace qubits in `|0⟩`. -/
noncomputable def inputState {n : ℕ} (x : Qubits n) (w : ℕ) : EuclideanSpace ℂ (Qubits (n + w)) :=
  ket (Fin.append x (fun _ : Fin w => false))

/-- de Wolf p.121 (§13.1): the circuit `c` on `n + w` wires computes `f : {0,1}ⁿ → {0,1}` if for
every input `x`, measuring the output wire `out` of the final state `C|x, 0^w⟩` gives `f(x)` with
probability at least `2/3` (worst case over `x`). De Wolf's "first qubit" is `out = 0`. -/
def Circuit.ComputesBool {S : Set Gate} {n w : ℕ} (c : Circuit S (n + w)) (out : Fin (n + w))
    (f : Qubits n → Bool) : Prop :=
  ∀ x : Qubits n, probEvent (act c.unitary (inputState x w)) (fun z => z out = f x) ≥ 2 / 3

/-- Childs p.10 (§1.3, (1.3)–(1.4)) with p.16 (§2.2: "a global phase is irrelevant"): `V`
approximates `U` to precision `ε` in the spectral norm up to a global phase,
`∃ θ, ‖U − e^{iθ} V‖ ≤ ε`. The phase is allowed because the source's own universal set
`{H, T, C}` generates only circuits of determinant `1` on three or more qubits, so it could not
be universal under the phase-sensitive reading of (1.3). -/
def ApproxUpToPhase {ι : Type*} [Fintype ι] [DecidableEq ι] (U V : Matrix ι ι ℂ) (ε : ℝ) : Prop :=
  ∃ θ : ℝ, specNorm (U - Complex.exp (θ * Complex.I) • V) ≤ ε

/-- Childs p.10 (§1.3): a gate set is universal if every unitary on any fixed number `k` of qubits
can be approximated to any precision `δ > 0` by a circuit over the set on those `k` qubits
(no ancillas), up to a global phase (`ApproxUpToPhase`). That every gate is a unitary on one or
two qubits (Childs's setting) is a hypothesis of the statements, not part of this predicate. -/
def IsUniversal (S : Set Gate) : Prop :=
  ∀ (k : ℕ) (U : Matrix (Qubits k) (Qubits k) ℂ), U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
    ∀ δ : ℝ, 0 < δ → ∃ c : Circuit S k, ApproxUpToPhase U c.unitary δ

/-- Childs p.15 (Theorem 2.1): a gate set is closed under inverses: with every gate `U` it contains
`U† = U⁻¹` (on the same number of qubits). -/
def ClosedUnderInverse (S : Set Gate) : Prop :=
  ∀ g ∈ S, (⟨g.arity, star g.mat⟩ : Gate) ∈ S

/-- Childs p.16 (§2.2, (2.8)): the ball `S_ε = {U ∈ SU(2) : ‖I − U‖ ≤ ε}` around the identity. -/
def su2Ball (ε : ℝ) : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  {U | specNorm (1 - (U : Matrix (Fin 2) (Fin 2) ℂ)) ≤ ε}

/-- Childs p.16 (§2.2): `Γ` is an `ε`-net for `S` (both subsets of `SU(2)`) if every `A ∈ S` has
some `U ∈ Γ` with `‖A − U‖ ≤ ε`. -/
def IsNet (Γ S : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) : Prop :=
  ∀ A ∈ S, ∃ U ∈ Γ, specNorm ((A : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)) ≤ ε

/-- Childs p.16 (§2.2, (2.7)): `⟦Γ, Γ⟧ = {⟦U, V⟧ : U, V ∈ Γ}` with the group commutator
`⟦U, V⟧ = U V U⁻¹ V⁻¹`. -/
def commutatorSet (Γ : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Set (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  {W | ∃ U ∈ Γ, ∃ V ∈ Γ, W = U * V * U⁻¹ * V⁻¹}

/-! ### Circuits with oracle calls -/

/-- One step of an oracle circuit over the gate set `S` on `n` wires, with `r` black boxes of
arities `a k`: either a gate of `S`, or a call to oracle `k` (its inverse if `adjoint`), possibly
controlled on a wire `control` that is not among the call's wires. -/
inductive OracleStep (S : Set Gate) {r : ℕ} (a : Fin r → ℕ) (n : ℕ) where
  /-- An elementary gate. -/
  | gate (g : GateApp S n)
  /-- A call to oracle `k` on the distinct wires `wires`. -/
  | query (k : Fin r) (adjoint : Bool) (control : Option (Fin n)) (wires : Fin (a k) ↪ Fin n)
      (hc : ∀ c, control = some c → c ∉ Set.range wires)

/-- de Wolf p.29 (§2.4), p.30 (§2.4.1); Childs p.105 (§21.1); CKS2017 (cost model): a gate-level
circuit with black-box calls, applied in list order (head first). The gates do not depend on the
oracles: the oracles enter only through `OracleCircuit.unitary`'s argument (trap Q2). -/
abbrev OracleCircuit (S : Set Gate) {r : ℕ} (a : Fin r → ℕ) (n : ℕ) := List (OracleStep S a n)

/-- The controlled version of an operator on `m` qubits, as an operator on `m + 1` qubits whose
wire `0` is the control. -/
def controlledQubits {m : ℕ} (M : Matrix (Qubits m) (Qubits m) ℂ) :
    Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
  (controlled M).submatrix (fun y => (y 0, Fin.tail y)) (fun y => (y 0, Fin.tail y))

/-- The matrix of one oracle-circuit step on the whole register, given the oracles `orc`. -/
def OracleStep.mat {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleStep S a n → Matrix (Qubits n) (Qubits n) ℂ
  | .gate g => embedOp g.gate.mat g.wires
  | .query k adj none wires _ => embedOp (if adj then star (orc k) else orc k) wires
  | .query k adj (some c) wires hc =>
      embedOp (controlledQubits (if adj then star (orc k) else orc k))
        ⟨Fin.cons c wires, Fin.cons_injective_iff.2 ⟨hc c rfl, wires.injective⟩⟩

/-- The unitary implemented by an oracle circuit with the oracles `orc` (first step rightmost). -/
def OracleCircuit.unitary {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (c.map (OracleStep.mat orc)).reverse.prod

/-- Whether a step is a call to oracle `k` (plain, inverse or controlled). -/
def OracleStep.IsQueryTo {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ} (k : Fin r) :
    OracleStep S a n → Bool
  | .gate _ => false
  | .query k' _ _ _ _ => decide (k' = k)

/-- The number of calls to oracle `k` in any variant (plain, inverse, controlled): the query
count of de Wolf §2.4 and of CKS2017. -/
def OracleCircuit.queryCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) (k : Fin r) : ℕ :=
  c.countP (OracleStep.IsQueryTo k)

/-- The number of elementary-gate steps ("other operations", CKS's gate complexity). -/
def OracleCircuit.gateCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) : ℕ :=
  c.countP fun s => match s with
    | .gate _ => true
    | .query _ _ _ _ _ => false

/-! ### Sanity tests -/

theorem embedOp_one {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso; apply hyz; funext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨b, rfl⟩ := ha; exact congrFun h2 b
      · exact h1 a ha
    · rfl
    · rfl

example : Circuit.unitary ([] : Circuit ∅ 3) = 1 := rfl

/-- Embedding a gate on the single wire of a one-qubit register gives the gate itself. -/
example (y z : Qubits 1) :
    embedOp (hadamard.submatrix (fun b : Qubits 1 => b 0) (fun b => b 0))
      (Function.Embedding.refl (Fin 1)) y z = hadamard (y 0) (z 0) := by
  unfold embedOp
  rw [Matrix.of_apply, if_pos (fun a ha => absurd ⟨a, rfl⟩ ha)]
  rfl

example {S : Set Gate} {n : ℕ} (g h : GateApp S n) :
    Circuit.unitary [g, h] = embedOp h.gate.mat h.wires * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

/-- A circuit without oracle calls does not depend on the oracles. -/
example {S : Set Gate} {n : ℕ} (g : GateApp S n)
    (orc orc' : (k : Fin 1) → Matrix (Qubits ((fun _ => 1) k)) (Qubits ((fun _ => 1) k)) ℂ) :
    OracleCircuit.unitary [OracleStep.gate g] orc = OracleCircuit.unitary [OracleStep.gate g] orc' :=
  rfl

end QAlgorithms


