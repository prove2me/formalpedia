-- Prove2me | Definitions.Def_QAlgorithms_Defs_LocCircuit
-- name    : QAlgorithms_Defs_LocCircuit
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:59:11.697839+00:00
-- url     : https://prove2.me/theorems/ea493980-2577-4f27-b36c-a8ff2e0e5281
-- title:
--   Circuits of locations: preparation, gates, measurement, wait; faults and output distributions
-- statement:
--   Circuits of locations: preparation, gates, measurement, wait; faults and output distributions
--
--   ### QAlgorithms.LocKind
--
--   An enumerated type with exactly six distinct values:
--   - $\mathrm{prep}$ (preparation),
--   - $\mathrm{had}$ (Hadamard),
--   - $\mathrm{tgate}$ ($T$ gate),
--   - $\mathrm{cnot}$,
--   - $\mathrm{meas}$ (measurement),
--   - $\mathrm{wait}$.
--
--   Equality between values is decidable.
--
--   ### QAlgorithms.LocKind.arity
--
--   The function on the six location kinds that gives the number of qubits a kind acts on:
--   - $\mathrm{cnot}$ has arity $2$.
--   - Each of $\mathrm{prep}$, $\mathrm{had}$, $\mathrm{tgate}$, $\mathrm{meas}$, $\mathrm{wait}$ has arity $1$.
--
--   ### QAlgorithms.LocKind.IsGate
--
--   The Boolean predicate on location kinds:
--   - It is true for $\mathrm{had}$, $\mathrm{tgate}$ and $\mathrm{cnot}$.
--   - It is false for $\mathrm{prep}$, $\mathrm{meas}$ and $\mathrm{wait}$.
--
--   ### QAlgorithms.LocKind.idealMatrix
--
--   For each location kind $\kappa$, this gives a $2^{a}\times 2^{a}$ complex matrix, where $a$ is the arity of $\kappa$. Rows and columns are indexed by bit strings of length $a$.
--
--   **$\mathrm{had}$.** The Hadamard
--   $$\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$$
--   on one qubit.
--
--   **$\mathrm{tgate}$.** The $T$ gate $\mathrm{diag}(1, e^{i\pi/4})$ on one qubit.
--
--   **$\mathrm{cnot}$.** The two-qubit CNOT with the first qubit as control:
--   - the entry at row $(p_1,p_2)$, column $(q_1,q_2)$ is $1$ if $p_1 = q_1$ and $p_2 = q_2 \oplus q_1$, and $0$ otherwise;
--   - equivalently, $|q_1,q_2\rangle \mapsto |q_1, q_2\oplus q_1\rangle$.
--
--   **$\mathrm{prep}$, $\mathrm{meas}$, $\mathrm{wait}$.** The $2\times 2$ identity matrix.
--
--   ### QAlgorithms.Loc
--
--   For a number of wires $N$, a location $l$ consists of three pieces of data:
--   - **Kind.** A kind $\kappa \in \{\mathrm{prep},\mathrm{had},\mathrm{tgate},\mathrm{cnot},\mathrm{meas},\mathrm{wait}\}$. Let $a$ be its arity: $2$ for $\mathrm{cnot}$, $1$ otherwise.
--   - **Wires.** An injective map $w : \{0,\dots,a-1\} \to \{0,\dots,N-1\}$, giving an ordered tuple of $a$ distinct wires.
--   - **Condition.** An arbitrary function $\mathrm{cond}$, which takes a partial assignment of bits to pairs of natural numbers and returns a Boolean. Its input is a map $(\mathbb{N}\times\mathbb{N}) \to \{0,1\}\cup\{\text{undefined}\}$.
--
--   **Edge cases.** No further constraints are imposed. If $N = 0$, no location exists, because no map into the empty set exists.
--
--   ### QAlgorithms.Loc.qubits
--
--   For a location $l$ on $N$ wires, this is the finite set of wires it touches:
--   $$\mathrm{qubits}(l) = \{\,w(0),\dots,w(a-1)\,\} \subseteq \{0,\dots,N-1\}.$$
--   Here $w$ is the wire map of $l$ and $a$ is the arity of its kind. Because $w$ is injective, this set has exactly $a$ elements: one for non-CNOT kinds, two for CNOT.
--
--   ### QAlgorithms.LocCircuit
--
--   A location circuit on $N$ wires is a finite list of time steps. Each time step is a finite list of locations on $N$ wires.
--
--   No constraints are imposed. In particular:
--   - locations in the same step may share wires;
--   - steps may be empty;
--   - the list of steps may be empty.
--
--   ### QAlgorithms.LocCircuit.locAt
--
--   **Setting.** A located circuit $C$ on $N$ qubits consists of a finite list of time steps $C = (L_0, L_1, \dots, L_{S-1})$. Each step $L_s$ is a finite list of *locations*. A location $l$ has three parts:
--
--   - a kind, one of preparation, Hadamard, $T$ gate, CNOT, measurement, or wait;
--   - an injective assignment of its $1$ (or, for CNOT, $2$) wires to qubits in $\{0, \dots, N-1\}$;
--   - a classical condition.
--
--   **Definition.** For a pair $\ell = (s, j)$ of natural numbers, $\mathrm{locAt}_C(\ell)$ is the $j$-th entry of step $s$, counted from $0$, if it exists, and "none" otherwise. Explicitly:
--
--   - If $s \ge S$, step $s$ is treated as the empty list, so the result is "none".
--   - If $s < S$ but $j \ge |L_s|$, the result is also "none".
--
--   ### QAlgorithms.LocCircuit.locs
--
--   For a located circuit $C$ with steps $L_0, \dots, L_{S-1}$, each a list of locations as above, $\mathrm{locs}(C)$ is the finite set of index pairs
--
--   $$\mathrm{locs}(C) = \{(s, j) \in \mathbb{N}^2 : s < S,\ j < |L_s|\}.$$
--
--   These are exactly the pairs $\ell$ for which $\mathrm{locAt}_C(\ell)$ is defined. Empty steps contribute no pairs.
--
--   ### QAlgorithms.LocCircuit.numQubits
--
--   For any located circuit $C$ on $N$ qubits, $\mathrm{numQubits}(C) = N$. This is the number $N$ fixed in the type of the circuit. It does not depend on the steps or locations of $C$, and in particular it does not count only the qubits that are actually used.
--
--   ### QAlgorithms.LocCircuit.numSteps
--
--   For a located circuit $C$ with step list $(L_0, \dots, L_{S-1})$, $\mathrm{numSteps}(C) = S$. This is the length of the step list. Every step is counted, including steps that contain no locations.
--
--   ### QAlgorithms.LocCircuit.size
--
--   For a located circuit $C$ with steps $L_0, \dots, L_{S-1}$, $\mathrm{size}(C)$ is the cardinality of the set $\mathrm{locs}(C) = \{(s,j) : s < S,\ j < |L_s|\}$. Since these index pairs are distinct, this equals
--
--   $$\sum_{s<S} |L_s|,$$
--
--   the total number of locations of every kind, including preparations, measurements and waits.
--
--   ### QAlgorithms.LocCircuit.measIds
--
--   For a located circuit $C$ with steps $L_0, \dots, L_{S-1}$, $\mathrm{measIds}(C)$ is the list of all index pairs $(s, j)$ such that the $j$-th location of step $s$ (both counted from $0$) has kind "measurement".
--
--   The list is ordered by step $s$ increasing, and within a step by position $j$ increasing. It contains no repetitions. Locations of any other kind do not appear.
--
--   ### QAlgorithms.LocCircuit.measCount
--
--   For a located circuit $C$, $\mathrm{measCount}(C)$ is the length of the list $\mathrm{measIds}(C)$. That list holds the index pairs $(s,j)$ of all measurement-kind locations, in step-then-position order. So $\mathrm{measCount}(C)$ is the total number of measurement locations in $C$.
--
--   ### QAlgorithms.LocCircuit.outcomeAt
--
--   Let $C$ be a located circuit and $r = (r_0, r_1, \dots, r_{k-1})$ a finite list of bits. Let $\mathrm{measIds}(C) = (m_0, m_1, \dots, m_{M-1})$ be its measurement locations in step-then-position order.
--
--   Pair the two lists positionally, $(m_i, r_i)$ for $i < \min(M, k)$; the longer list is truncated. For an index pair $\ell$, define
--
--   $$\mathrm{outcomeAt}_C(r, \ell) = \begin{cases} r_i & \text{if } \ell = m_i \text{ for some } i < \min(M,k),\\ \text{none} & \text{otherwise.}\end{cases}$$
--
--   The $m_i$ are distinct, so $i$ is unique when it exists. The "none" case covers three situations:
--
--   - $\ell$ is not a measurement location;
--   - $\ell$ is not a location at all;
--   - $\ell$ is the $i$-th measurement with $i \ge k$, i.e. $r$ is too short.
--
--   Bits $r_i$ with $i \ge M$ are ignored.
--
--   ### QAlgorithms.qubitsOf
--
--   For a finite list $l_1, \dots, l_p$ of locations on $N$ qubits, $\mathrm{qubitsOf}$ is the union of their qubit sets:
--
--   $$\mathrm{qubitsOf}(l_1, \dots, l_p) = \bigcup_{i=1}^{p} Q(l_i) \subseteq \{0, \dots, N-1\}.$$
--
--   Here $Q(l)$ is the set of qubits that location $l$ acts on, i.e. the image of its wire assignment: one qubit, or two for a CNOT. The empty list gives $\emptyset$.
--
--   ### QAlgorithms.stepLive
--
--   For a set $\mathrm{live} \subseteq \{0, \dots, N-1\}$ of qubits and a list $st$ of locations on $N$ qubits, define
--
--   $$\mathrm{stepLive}(\mathrm{live}, st) = \Big(\mathrm{live} \,\cup\, \bigcup_{l \in st,\ l \text{ a preparation}} Q(l)\Big) \setminus \bigcup_{l \in st,\ l \text{ a measurement}} Q(l),$$
--
--   where $Q(l)$ is the set of qubits acted on by $l$.
--
--   Qubits of preparation locations are added and qubits of measurement locations are removed, with the removal applied last. Two consequences follow:
--
--   - A qubit that is both prepared and measured in $st$ is not in the result.
--   - A measured qubit is removed whether or not it was in $\mathrm{live}$.
--
--   Locations of all other kinds have no effect.
--
--   ### QAlgorithms.LocCircuit.liveBefore
--
--   Let $C$ be a located circuit with steps $L_0, \dots, L_{S-1}$, and let $\mathrm{liveIn} \subseteq \{0,\dots,N-1\}$ be an initial set of qubits. The sets $\mathrm{liveBefore}_C(\mathrm{liveIn}, s)$, for $s \in \mathbb{N}$, are defined recursively by
--
--   $$\mathrm{liveBefore}(0) = \mathrm{liveIn}, \qquad \mathrm{liveBefore}(s+1) = \mathrm{stepLive}\big(\mathrm{liveBefore}(s),\ L_s\big).$$
--
--   Here $\mathrm{stepLive}(X, L) = (X \cup \text{qubits of preparations in } L) \setminus \text{qubits of measurements in } L$. For $s \ge S$, $L_s$ is taken to be the empty list, so the sequence is constant from $s = S$ on.
--
--   ### QAlgorithms.LocCircuit.IsWellFormed
--
--   Let $C$ be a located circuit on $N$ qubits with steps $L_0, \dots, L_{S-1}$, and let $\mathrm{liveIn}, \mathrm{liveOut} \subseteq \{0,\dots,N-1\}$. Write:
--
--   - $Q(l)$ for the set of qubits a location $l$ acts on;
--   - $V_s = \mathrm{liveBefore}_C(\mathrm{liveIn}, s)$ for the live set before step $s$. Here $V_0 = \mathrm{liveIn}$ and $V_{s+1} = (V_s \cup \text{qubits of preparations in } L_s) \setminus \text{qubits of measurements in } L_s$.
--
--   **Definition.** $C$ is well-formed from $\mathrm{liveIn}$ to $\mathrm{liveOut}$ if both of the following hold.
--
--   1. For every step index $s < S$, all four of these conditions hold:
--      - **(a) Disjointness.** Any two locations occupying different positions in the list $L_s$ act on disjoint qubit sets.
--      - **(b) Coverage.** Every qubit $q \in V_s$ lies in $Q(l)$ for some location $l \in L_s$, of any kind, including wait.
--      - **(c) Preparations.** Every location $l \in L_s$ of kind preparation satisfies $Q(l) \cap V_s = \emptyset$.
--      - **(d) Other kinds.** Every location $l \in L_s$ of any other kind (Hadamard, $T$, CNOT, measurement, wait) satisfies $Q(l) \subseteq V_s$.
--   2. **Final live set.** $V_S = \mathrm{liveOut}$.
--
--   **Not constrained.** The classical conditions attached to locations are not restricted by this definition. When $S = 0$, condition 1 is vacuous and the definition reduces to $\mathrm{liveIn} = \mathrm{liveOut}$.
--
--   ### QAlgorithms.LocCircuit.IsIdealCircuit
--
--   This is a property of a location circuit $C$ on $N$ qubits (wires $0,\dots,N-1$). Such a circuit is a list of time steps $C_0, C_1, \dots, C_{S-1}$. Each step is a list of *locations* $l$, and each location has three parts:
--
--   - a kind: preparation, Hadamard, $T$ gate, CNOT, measurement, or wait;
--   - an injective list of wires (two for CNOT, one otherwise);
--   - a classical condition $\mathrm{cond}_l$, a Boolean-valued function of a partial table $\mathbb{N}\times\mathbb{N} \to \{\text{true},\text{false},\text{undefined}\}$ of measurement outcomes.
--
--   $C$ is *ideal* when two conditions hold. The first is that $C$ is well-formed with empty input live set and empty output live set. This means the following. Define live sets by
--   $$
--   L_0 = \emptyset, \qquad L_{s+1} = \bigl(L_s \cup \mathrm{prepQubits}(C_s)\bigr) \setminus \mathrm{measQubits}(C_s),
--   $$
--   where $\mathrm{prepQubits}$ and $\mathrm{measQubits}$ are the unions of the wire sets of the preparation and measurement locations of the step. Then for every step $s < S$:
--
--   - the locations of $C_s$ have pairwise disjoint wire sets;
--   - every qubit in $L_s$ is a wire of some location of $C_s$;
--   - every preparation location of $C_s$ has wires disjoint from $L_s$;
--   - every non-preparation location of $C_s$ has all its wires in $L_s$.
--
--   In addition, $L_S = \emptyset$.
--
--   The second condition is that every location in every step has the constant condition $\mathrm{cond}_l \equiv \text{true}$.
--
--   When $C$ has no steps, the first condition holds trivially because $L_0 = \emptyset$.
--
--   ### QAlgorithms.ErrAssign
--
--   For $N \in \mathbb{N}$ and a type $E$ (an environment register), an *error assignment* is any function
--   $$
--   \mathrm{err} : \mathbb{N}\times\mathbb{N} \to \{\text{none}\} \cup \mathrm{Superop}(Q_N\times E),
--   $$
--   where $Q_N = \{0,1\}^N$. It assigns to each address $(s,j)$ (read as step $s$, position $j$) either "no error" or a superoperator.
--
--   Here a superoperator on $Q_N \times E$ is **any** map from complex $(Q_N\times E)\times(Q_N\times E)$ matrices to matrices of the same shape. Nothing requires it to be linear, completely positive, or trace-preserving. Addresses that do not correspond to any location are also allowed to carry a value.
--
--   ### QAlgorithms.CQState
--
--   For $N \in \mathbb{N}$ and a type $E$, a classical–quantum state is any function
--   $$
--   \rho : \{0,1\}^{*} \to \mathbb{C}^{(Q_N\times E)\times(Q_N\times E)}.
--   $$
--   It assigns to every finite list $r$ of bits (read as a measurement record) a complex matrix $\rho(r)$ on the joint system of $N$ qubits and the environment $E$, with $Q_N = \{0,1\}^N$.
--
--   No positivity, trace, or normalization condition is imposed on the matrices $\rho(r)$.
--
--   ### QAlgorithms.qubitOp1
--
--   Let $M$ be a complex $2\times 2$ matrix indexed by bits, and let $q$ be a wire, $0 \le q < N$. Then $\mathrm{qubitOp1}(M,q)$ is the $2^N\times 2^N$ matrix indexed by $y,z \in \{0,1\}^N$ with
--   $$
--   \mathrm{qubitOp1}(M,q)_{y,z} = \begin{cases} M_{y_q,\,z_q} & \text{if } y_a = z_a \text{ for all } a \neq q,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   That is, it is $M$ acting on qubit $q$, tensored with the identity on all other qubits.
--
--   ### QAlgorithms.resetKraus
--
--   For a bit $b$, $\mathrm{resetKraus}(b)$ is the $2\times 2$ matrix with entries
--   $$
--   \mathrm{resetKraus}(b)_{y,z} = \begin{cases} 1 & \text{if } y = 0 \text{ and } z = b,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   In other words, $\mathrm{resetKraus}(b) = |0\rangle\langle b|$.
--
--   ### QAlgorithms.measProj
--
--   For a bit $b$, $\mathrm{measProj}(b)$ is the $2\times 2$ matrix with entry $1$ at $(b,b)$ and $0$ elsewhere. In other words, $\mathrm{measProj}(b) = |b\rangle\langle b|$, the projector onto computational basis state $b$.
--
--   ### QAlgorithms.Loc.apply
--
--   This defines how a single location $l$ on $N$ qubits acts on a classical–quantum state. The environment $E$ is a finite type with decidable equality. The inputs are:
--
--   - an outcome lookup $O$, which maps each record $r$ to a partial table $O(r) : \mathbb{N}\times\mathbb{N} \to \{\text{true},\text{false},\text{undefined}\}$;
--   - an optional error $e$, either "none" or an arbitrary map $\Phi$ on $(Q_N\times E)$-matrices;
--   - a state $\rho$, which is a function from bit lists to such matrices.
--
--   Some notation used below:
--
--   - $\mathcal{E}$ is the error map: $\mathcal{E}(X) = X$ if $e$ is none, and $\mathcal{E}(X) = \Phi(X)$ if $e = \Phi$.
--   - $q$ is the first wire of $l$.
--   - $\widehat{A} = A \otimes I_E$ is the extension of an $N$-qubit matrix to the joint system.
--   - $K_b = \mathrm{qubitOp1}(|0\rangle\langle b|, q)$ is the reset Kraus operator on qubit $q$.
--   - $P_b = \mathrm{qubitOp1}(|b\rangle\langle b|, q)$ is the measurement projector on qubit $q$.
--   - $\dagger$ denotes the conjugate transpose.
--
--   The resulting state $\rho'$ is defined case by case on the kind of $l$:
--
--   - **Preparation:** the qubit is reset to $0$ and the error is applied *afterwards*:
--   $$
--   \rho'(r) = \mathcal{E}\Bigl(\textstyle\sum_{b\in\{0,1\}} \widehat{K_b}\,\rho(r)\,\widehat{K_b}^{\dagger}\Bigr).
--   $$
--
--   - **Measurement:** the error is applied *before* the projection, and the last record bit selects the outcome. If $r$ is empty, $\rho'(r) = 0$. If $r = r'\,b$ (last bit $b$), then
--   $$
--   \rho'(r) = \widehat{P_b}\;\mathcal{E}\bigl(\rho(r')\bigr)\;\widehat{P_b}^{\dagger}.
--   $$
--   Only the first (and only) wire $q$ is used.
--
--   - **Wait:** $\rho'(r) = \mathcal{E}(\rho(r))$.
--
--   - **Hadamard, $T$, CNOT:** the gate is applied only if the classical condition holds, and the error is applied *afterwards*:
--   $$
--   \rho'(r) = \begin{cases}\mathcal{E}\bigl(\widehat{U}\,\rho(r)\,\widehat{U}^{\dagger}\bigr) & \text{if } \mathrm{cond}_l(O(r)) = \text{true},\\ \mathcal{E}(\rho(r)) & \text{otherwise.}\end{cases}
--   $$
--     Here $U$ is the ideal gate placed on the wires of $l$ (identity elsewhere):
--     - the Hadamard $\tfrac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$;
--     - the $T$ gate $\mathrm{diag}(1, e^{i\pi/4})$;
--     - CNOT, with control the first wire of $l$ and target the second.
--
--   ### QAlgorithms.runStep
--
--   This runs one time step, applying its locations one after another. The inputs are:
--
--   - an outcome lookup $O$;
--   - an error assignment $\mathrm{err}$;
--   - a step number $s$;
--   - a list of locations $l_0, l_1, \dots, l_{k-1}$;
--   - a starting position $j$;
--   - a state $\rho$.
--
--   The result is
--   $$
--   \mathrm{runStep}(O,\mathrm{err},s,[l_0,\dots,l_{k-1}],j,\rho) = \mathrm{apply}_{l_{k-1}} \circ \cdots \circ \mathrm{apply}_{l_0}(\rho).
--   $$
--   Each factor is defined by
--   $$
--   \mathrm{apply}_{l_i} = \mathrm{Loc.apply}\bigl(l_i,\ O,\ \mathrm{err}(s, j+i),\ \cdot\,\bigr).
--   $$
--   So $l_i$ receives the error at address $(s, j+i)$. All locations use the same outcome lookup $O$. For an empty list the state is returned unchanged.
--
--   ### QAlgorithms.LocCircuit.runFrom
--
--   This runs a list of steps $C'_0, \dots, C'_{m-1}$, starting at step number $s$, on a state $\rho$, for a circuit $C$ on $N$ qubits and an error assignment $\mathrm{err}$. Steps are processed in order. Step $C'_i$ is executed as
--   $$
--   \mathrm{runStep}(O_{s+i}, \mathrm{err}, s+i, C'_i, 0, \cdot),
--   $$
--   which starts at position $0$, so its $j$-th location gets error $\mathrm{err}(s+i, j)$.
--
--   The outcome lookup for step number $t$ is
--   $$
--   O_t(r)(\ell) = \begin{cases}\mathrm{outcome}_C(r,\ell) & \text{if } \ell_1 < t,\\ \text{undefined} & \text{otherwise.}\end{cases}
--   $$
--   Here $\mathrm{outcome}_C(r,\ell)$ is defined as follows:
--
--   - List the measurement locations of $C$ as addresses $(s',j')$, in step order and then in position order within each step: $\mu_0, \mu_1, \dots$.
--   - Pair this list with the bits of $r$.
--   - $\mathrm{outcome}_C(r,\ell)$ is $r_k$ if $\ell = \mu_k$ with $k < |r|$, and undefined otherwise.
--
--   As a result, conditions only see outcomes of measurements from strictly earlier step numbers $t$ that also lie within the record. If the list of steps is empty, the state is returned unchanged.
--
--   ### QAlgorithms.LocCircuit.run
--
--   For a location circuit $C$ on $N$ qubits with steps $C_0,\dots,C_{S-1}$, an error assignment $\mathrm{err}$, and a classical–quantum state $\rho$:
--   $$
--   \mathrm{run}(C,\mathrm{err},\rho) = \mathrm{runFrom}(C, \mathrm{err}, [C_0,\dots,C_{S-1}], 0, \rho).
--   $$
--   That is, all steps of $C$ are executed in order, starting at step number $0$. Step $s$'s $j$-th location receives error $\mathrm{err}(s,j)$, and gate conditions see only outcomes from steps $< s$, as described under `runFrom`.
--
--   ### QAlgorithms.initState
--
--   For $N \in \mathbb{N}$ and an arbitrary complex matrix $\sigma_0$ on a type $E$, the initial classical–quantum state is
--   $$
--   \mathrm{initState}_N(\sigma_0)(r) = \begin{cases} |0^N\rangle\langle 0^N| \otimes \sigma_0 & \text{if } r \text{ is the empty list},\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   Here $|0^N\rangle\langle 0^N|$ is the matrix with entries $\psi_a\overline{\psi_b}$ for $\psi = |0\cdots0\rangle$; this is $1$ at $(0^N, 0^N)$ and $0$ elsewhere. No condition on $\sigma_0$ is imposed: it need not be positive or have trace $1$.
--
--   ### QAlgorithms.LocCircuit.outDist
--
--   Let $C$ be a location circuit on $N$ qubits, $E$ a finite type with decidable equality, $\mathrm{err}$ an error assignment, and $\sigma_0$ an arbitrary complex matrix on $E$. Let $M$ be the number of measurement locations of $C$.
--
--   $\mathrm{outDist}$ assigns a real number to each bit string $r = (r_0,\dots,r_{M-1}) \in \{0,1\}^M$:
--   $$
--   \mathrm{outDist}(C,\mathrm{err},\sigma_0)(r) = \operatorname{Re}\,\operatorname{tr}\Bigl(\mathrm{run}\bigl(C,\mathrm{err},\mathrm{initState}_N(\sigma_0)\bigr)(r_0 r_1\cdots r_{M-1})\Bigr).
--   $$
--   This is the real part of the trace of the final matrix at the full record $r$, read as a list. The trace is over the joint system $\{0,1\}^N\times E$.
--
--   No normalization is performed. Since $\sigma_0$ and the error maps are unrestricted, the values need not be nonnegative and need not sum to $1$. When $M = 0$ there is a single, empty record.
--
--   ### QAlgorithms.LocCircuit.idealOutDist
--
--   This defines the **noiseless measurement-outcome function** of a location circuit $C$ on $N$ qubits. Let $M$ be the number of measurement locations of $C$. The result is a real-valued function on bit strings $r=(r_0,\dots,r_{M-1})\in\{0,1\}^M$:
--
--   $$
--   \mathrm{idealOutDist}_C(r) \;=\; \operatorname{Re}\operatorname{Tr}\,\rho_{\mathrm{fin}}(r_0,\dots,r_{M-1}).
--   $$
--
--   Here $\rho_{\mathrm{fin}}$ comes from the following run.
--
--   **The state.** A classical–quantum state is a function assigning to every finite bit list $r$ a matrix on $\{0,1\}^N\times\{\ast\}$. The environment is a single point (one-dimensional) with environment state the $1\times1$ identity $[1]$.
--
--   **The initial state.** It is
--   $$
--   \rho_0(r)=\begin{cases}|0^N\rangle\langle 0^N|\otimes[1] & r \text{ empty},\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   **The steps.** The steps $s=0,1,\dots$ of $C$ are processed in order, and within each step the locations $j=0,1,\dots$ are processed in list order. Every location is error-free (the error assignment is "none" everywhere). A location $l$ transforms $\rho$ into $\rho'$ as follows, where $q$ denotes the first wire of $l$:
--
--   - **Preparation:** $\rho'(r)=\sum_{b\in\{0,1\}}K_b\,\rho(r)\,K_b^\dagger$, where $K_b=|0\rangle\langle b|$ acts on qubit $q$ (identity elsewhere).
--   - **Measurement:**
--     - If $r$ is empty, $\rho'(r)=0$.
--     - Otherwise, let $b$ be the last entry of $r$ and $r^-$ be $r$ with that entry removed. Then $\rho'(r)=\Pi_b\,\rho(r^-)\,\Pi_b$, with $\Pi_b=|b\rangle\langle b|$ on qubit $q$.
--   - **Wait:** $\rho'=\rho$.
--   - **Hadamard, $T$, CNOT:**
--     - The gate is applied only if the location's classical condition evaluates to true on $O_s(r)$. In that case $\rho'(r)=U\rho(r)U^\dagger$.
--     - Otherwise $\rho'(r)=\rho(r)$.
--     - $U$ is the ideal gate embedded on $l$'s wires: $H$, $T=\mathrm{diag}(1,e^{i\pi/4})$, or CNOT with the first wire as control.
--     - $O_s(r)$ is the map that sends a location $\ell'$ to the bit of $r$ recorded for it, but only if $\ell'$ lies in an earlier step than $s$; otherwise it sends $\ell'$ to "none".
--     - The bit recorded for a measurement location is found by pairing the list of all measurement locations of $C$ (ordered by step, then position within the step) with the entries of $r$.
--
--   No well-formedness of $C$ is assumed. Nothing asserts that the values are nonnegative or sum to $1$.
--
--   ### QAlgorithms.pushDist
--
--   This defines the **pushforward** of a real function along a list decoder. The inputs are:
--
--   - natural numbers $M, M'$;
--   - a decoding map $\mathrm{dec}$ from finite bit lists to finite bit lists;
--   - a real function $\mu$ on $\{0,1\}^{M'}$.
--
--   The result is the real function on $\{0,1\}^M$ given by
--   $$
--   \mathrm{pushDist}(r)\;=\;\sum_{\substack{r'\in\{0,1\}^{M'}\\ \mathrm{dec}(r'_0,\dots,r'_{M'-1})\,=\,(r_0,\dots,r_{M-1})}}\mu(r').
--   $$
--
--   Equality is equality of lists, so it includes equality of lengths. If $\mathrm{dec}$ never outputs a list of length $M$, the function is identically $0$. No condition is placed on $\mu$ (it need not be nonnegative or normalized) or on $\mathrm{dec}$.
--
--   ### QAlgorithms.PauliArrangement
--
--   A **Pauli arrangement** is any function assigning to each pair $(s,j)$ of natural numbers one of two things:
--
--   - either "no fault";
--   - or an ordered pair $(P,Q)$ of single-qubit Pauli labels, each from $\{I,X,Y,Z\}$.
--
--   There are no constraints. In particular:
--
--   - the pair $(I,I)$ is allowed and still counts as a fault entry;
--   - the function may be non-"none" at infinitely many pairs.
--
--   ### QAlgorithms.faultyLocs
--
--   For a location circuit $C$ on $N$ qubits and a Pauli arrangement $f$, this is the finite set of **faulty locations**:
--   $$
--   \mathrm{faultyLocs}(C,f)=\{(s,j)\in\mathrm{locs}(C)\;:\; f(s,j)\neq\text{none}\}.
--   $$
--
--   Here $\mathrm{locs}(C)$ is the set of pairs $(s,j)$ with $s$ less than the number of steps of $C$ and $j$ less than the number of locations in step $s$.
--
--   Some consequences of the literal definition:
--
--   - Entries of $f$ outside $\mathrm{locs}(C)$ are ignored.
--   - A location assigned $(I,I)$ is counted as faulty.
--
--   ### QAlgorithms.locPauli
--
--   For $k\in\mathbb N$ and Pauli labels $P,Q$, this is the $2^k\times 2^k$ matrix on $k$ qubits
--   $$
--   \mathrm{locPauli}(k,P,Q)_{y,z}=\prod_{i=0}^{k-1}\sigma^{(i)}_{y_i,z_i},\qquad \sigma^{(0)}=P,\quad \sigma^{(i)}=Q\ (i\ge1).
--   $$
--
--   Here $I,X,Y,Z$ denote the usual matrices with $Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$, indexed with row/column $0$ first. In other words, the matrix is $P\otimes Q\otimes\cdots\otimes Q$, with $P$ on wire $0$. Special cases:
--
--   - $k=0$: it is the $1\times1$ identity.
--   - $k=1$: it is $P$.
--   - $k=2$: it is $P\otimes Q$.
--
--   ### QAlgorithms.pauliErr
--
--   For a location circuit $C$ on $N$ qubits and a Pauli arrangement $f$, this is the error assignment with a one-dimensional environment, defined at each pair $\ell=(s,j)$ as follows.
--
--   **When there is an error.** If $C$ has a location $l$ at $\ell$ and $f(\ell)=(P,Q)$, the error at $\ell$ is the conjugation map
--   $$
--   \rho\;\longmapsto\;(E_\ell\otimes[1])\,\rho\,(E_\ell\otimes[1])^\dagger .
--   $$
--
--   - $E_\ell$ is the $N$-qubit matrix that acts as $\mathrm{locPauli}(k,P,Q)$ on the wires of $l$, in their listed order, and as the identity on all other wires.
--   - $k$ is the arity of $l$: $2$ for CNOT, $1$ for every other kind.
--
--   Concretely, $(E_\ell)_{y,z}$ equals $\mathrm{locPauli}(y|_{w},z|_{w})$ if $y$ and $z$ agree off the wire set $w$, and equals $0$ otherwise.
--
--   **When there is no error.** In all other cases (no location at $\ell$, or $f(\ell)$ is none) the assignment at $\ell$ is "no error".
--
--   This applies to every location kind, including preparation, measurement and wait.
--
--   ### QAlgorithms.IsLocError
--
--   Let $w$ be an injective listing of $k$ wires among $N$ wires, let $E$ be a finite environment index set, and let $\Phi$ be a map from matrices on $\{0,1\}^N\times E$ to matrices on the same space. The proposition asserts that there exists a map $\Psi$ on matrices over $\{0,1\}^k\times E$ satisfying two conditions.
--
--   **Condition 1: $\Psi$ is a channel.** This means there exist $m\in\mathbb N$ and matrices $K_1,\dots,K_m$ on $\{0,1\}^k\times E$ such that
--
--   $$
--   \sum_a K_a^\dagger K_a=1 \quad\text{and}\quad \Psi(\rho)=\sum_a K_a\rho K_a^\dagger \ \text{ for every matrix }\rho.
--   $$
--
--   **Condition 2: $\Phi$ is the lift of $\Psi$ along $w$.** This means that for all matrices $X$ and all indices $p=(y,e)$, $q=(y',e')$:
--
--   $$
--   \Phi(X)_{p,q}=\Psi(\tilde X)_{(y\circ w,\,e),\,(y'\circ w,\,e')},
--   $$
--
--   where
--
--   $$
--   \tilde X_{(a,e_1),(b,e_2)}=X_{(y[w\leftarrow a],\,e_1),\,(y'[w\leftarrow b],\,e_2)}.
--   $$
--
--   - $y\circ w\in\{0,1\}^k$ is the restriction of $y$ to the wires $w(0),\dots,w(k-1)$.
--   - $y[w\leftarrow a]$ is the string equal to $a_i$ at wire $w(i)$ and equal to $y$ on all other wires.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/LocCircuit.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
/-!
# Circuits of locations: preparation, gates, measurement, wait; faults and output distributions
(shared definition layer)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages), §4.1 and Def. 6.

Model. A circuit on `N` qubits (wires `Fin N`) is a list of time steps, each a list of locations
(§4.1, p.17): preparation of `|0⟩`, the gates `H`, `R_{π/8} = diag(1, e^{iπ/4})` (frozen `gateT`)
and CNOT, standard-basis measurement, and wait. A location is identified by `(s, j) : ℕ × ℕ`
(time step `s`, position `j` in the step). The measurement record lists the outcomes in
step-major order. Gate locations may be classically controlled by earlier outcomes (classical
computation is perfect and free, p.17); the condition reads the outcomes by location id and sees
only the outcomes of earlier time steps. The state of the computer is classical–quantum: for each
measurement record, a subnormalized density matrix on the qubits and an environment register `E`
(trivial, `Fin 1`, when no environment is needed). An error assignment puts a superoperator on
qubits ⊗ environment at some locations: after the location's ideal action, and before it for a
measurement location.
-/

namespace QAlgorithms

open scoped Matrix

/-- Gottesman intro p.17 (§4.1) and p.33 (Def. 6): the types of location: preparation of `|0⟩`,
the gates `H`, `R_{π/8}`, CNOT (the universal set of p.17), measurement in the standard basis, and
wait. -/
inductive LocKind where
  | prep
  | had
  | tgate
  | cnot
  | meas
  | wait
  deriving DecidableEq

/-- Gottesman intro p.18: the number of qubits a location involves (two for CNOT, one
otherwise). -/
def LocKind.arity : LocKind → ℕ
  | .cnot => 2
  | _ => 1

theorem LocKind.arity_pos (κ : LocKind) : 0 < κ.arity := by
  cases κ <;> decide

/-- Gottesman intro p.17 (§4.1): the gate locations `H`, `R_{π/8}`, CNOT (classical control is
meaningful for these only). -/
def LocKind.IsGate : LocKind → Bool
  | .had => true
  | .tgate => true
  | .cnot => true
  | _ => false

/-- Gottesman intro p.17 (§4.1): the ideal unitary of a location on its qubits: `H` (frozen
`hadamard`), `R_{π/8} = diag(1, e^{iπ/4})` (frozen `gateT`), CNOT (frozen `cnot`, control on the
first wire), and the identity for wait (and, unused, for preparation and measurement). -/
noncomputable def LocKind.idealMatrix : (κ : LocKind) → Matrix (Qubits κ.arity) (Qubits κ.arity) ℂ
  | .had => (Gate.ofMatrix1 hadamard).mat
  | .tgate => (Gate.ofMatrix1 gateT).mat
  | .cnot => (Gate.ofMatrix2 QAlgorithms.cnot).mat
  | .prep => 1
  | .meas => 1
  | .wait => 1

/-- Gottesman intro p.17 (§4.1): a location on `N` qubits: its type, the qubits it acts on (in
order: control first for CNOT), and, for gate locations, a classical condition on the earlier
measurement outcomes (given by location id; `none` for an outcome not available). The gate is
applied iff the condition holds; the location exists, and can be faulty, either way. The
condition is ignored for preparation, measurement and wait locations. -/
structure Loc (N : ℕ) where
  kind : LocKind
  wires : Fin kind.arity ↪ Fin N
  cond : (ℕ × ℕ → Option Bool) → Bool

/-- The set of qubits a location acts on. -/
def Loc.qubits {N : ℕ} (l : Loc N) : Finset (Fin N) :=
  Finset.univ.map l.wires

/-- Gottesman intro p.17 (§4.1) and p.33 (Def. 6): a circuit of locations on `N` qubits, organised
in time steps. -/
structure LocCircuit (N : ℕ) where
  steps : List (List (Loc N))

namespace LocCircuit

variable {N : ℕ}

/-- The location with id `(s, j)` (time step `s`, position `j`), if any. -/
def locAt (C : LocCircuit N) (ℓ : ℕ × ℕ) : Option (Loc N) :=
  (C.steps.getD ℓ.1 [])[ℓ.2]?

/-- Gottesman intro p.17: the set of (ids of) locations of the circuit. -/
def locs (C : LocCircuit N) : Finset (ℕ × ℕ) :=
  (Finset.range C.steps.length).biUnion fun s =>
    (Finset.range (C.steps.getD s []).length).image fun j => (s, j)

/-- The number of qubits of the circuit. -/
def numQubits (_ : LocCircuit N) : ℕ :=
  N

/-- The number of time steps of the circuit. -/
def numSteps (C : LocCircuit N) : ℕ :=
  C.steps.length

/-- Gottesman intro p.41 (Thm 10): `|C|`, the number of locations. -/
def size (C : LocCircuit N) : ℕ :=
  C.locs.card

/-- The ids of the measurement locations, in the order of the measurement record (step-major,
then by position). -/
def measIds (C : LocCircuit N) : List (ℕ × ℕ) :=
  C.steps.zipIdx.flatMap fun p =>
    p.1.zipIdx.filterMap fun q => if q.1.kind = .meas then some (p.2, q.2) else none

/-- The number of measurement locations, i.e. the length of the measurement record. -/
def measCount (C : LocCircuit N) : ℕ :=
  C.measIds.length

/-- The outcome recorded in `r` at the measurement location `ℓ` (`none` if `ℓ` is not a
measurement location or `r` is too short). -/
def outcomeAt (C : LocCircuit N) (r : List Bool) (ℓ : ℕ × ℕ) : Option Bool :=
  (C.measIds.zip r).lookup ℓ

end LocCircuit

/-- The qubits acted on by a list of locations. -/
def qubitsOf {N : ℕ} (ls : List (Loc N)) : Finset (Fin N) :=
  ls.foldr (fun l acc => l.qubits ∪ acc) ∅

/-- Gottesman intro p.33 (Def. 6: "the preparation locations introduce new qubits into the
circuit, and the measurement locations remove qubits"): the live qubits after a time step. -/
def stepLive {N : ℕ} (live : Finset (Fin N)) (st : List (Loc N)) : Finset (Fin N) :=
  (live ∪ qubitsOf (st.filter fun l => decide (l.kind = .prep))) \
    qubitsOf (st.filter fun l => decide (l.kind = .meas))

namespace LocCircuit

variable {N : ℕ}

/-- The live qubits at the start of time step `s`, starting from the live set `liveIn`. -/
def liveBefore (C : LocCircuit N) (liveIn : Finset (Fin N)) : ℕ → Finset (Fin N)
  | 0 => liveIn
  | s + 1 => stepLive (C.liveBefore liveIn s) (C.steps.getD s [])

/-- Gottesman intro p.33 (Def. 6), relative to boundary live sets: within each time step the
locations act on pairwise disjoint qubits; every live qubit ("not counting those to be added at
later time steps or removed at earlier time steps") is involved in a location of the step (hence
in exactly one); a preparation acts only on a qubit that is not live and every other location only
on live qubits; and the live qubits after the last step are `liveOut`. A full circuit has
`liveIn = liveOut = ∅` (the first location of every qubit is a preparation and the last a
measurement); a gadget has the data qubits of its input and output blocks. -/
def IsWellFormed (C : LocCircuit N) (liveIn liveOut : Finset (Fin N)) : Prop :=
  (∀ s < C.steps.length,
    (C.steps.getD s []).Pairwise (fun l l' => Disjoint l.qubits l'.qubits) ∧
    (∀ q ∈ C.liveBefore liveIn s, ∃ l ∈ C.steps.getD s [], q ∈ l.qubits) ∧
    (∀ l ∈ C.steps.getD s [], l.kind = .prep → Disjoint l.qubits (C.liveBefore liveIn s)) ∧
    (∀ l ∈ C.steps.getD s [], l.kind ≠ .prep → l.qubits ⊆ C.liveBefore liveIn s)) ∧
  C.liveBefore liveIn C.steps.length = liveOut

/-- Gottesman intro p.19 ("the original circuit takes no input: all qubits used in it must be
prepared using preparation locations"; its output is the outcome of the final measurements) and
p.33 (Def. 6): an ideal circuit: well formed with empty boundaries, and without classical
control. -/
def IsIdealCircuit (C : LocCircuit N) : Prop :=
  C.IsWellFormed ∅ ∅ ∧ ∀ st ∈ C.steps, ∀ l ∈ st, l.cond = fun _ => true

end LocCircuit

/-- Gottesman intro p.18 (§4.1) and p.40 (Def. 12): an error assignment for a circuit on `N`
qubits with environment `E`: `some Φ` at a location applies the superoperator `Φ` (on qubits ⊗
environment) right after the location's ideal operation (right before it, for a measurement):
"the actual error should be considered to be the action of the failed component times the inverse
of the desired component". -/
abbrev ErrAssign (N : ℕ) (E : Type*) :=
  ℕ × ℕ → Option (Superop (Qubits N × E) (Qubits N × E))

/-- A classical–quantum state: for each measurement record, a subnormalized density matrix on
qubits ⊗ environment. -/
abbrev CQState (N : ℕ) (E : Type*) :=
  List Bool → Matrix (Qubits N × E) (Qubits N × E) ℂ

/-- The single-qubit operator `M` on wire `q` (identity elsewhere). -/
def qubitOp1 {N : ℕ} (M : Matrix Bool Bool ℂ) (q : Fin N) : Matrix (Qubits N) (Qubits N) ℂ :=
  embedOp (Gate.ofMatrix1 M).mat (Stabilizer.wire1 q)

/-- The reset Kraus operators `|0⟩⟨b|` (a preparation location resets its qubit to `|0⟩`). -/
def resetKraus (b : Bool) : Matrix Bool Bool ℂ :=
  Matrix.of fun y z => if y = false ∧ z = b then 1 else 0

/-- The standard-basis projectors `|b⟩⟨b|` (p.17: measurement of individual qubits in the
standard basis). -/
def measProj (b : Bool) : Matrix Bool Bool ℂ :=
  Matrix.of fun y z => if y = b ∧ z = b then 1 else 0

/-- Gottesman intro pp.17–18: the action of one location on a classical–quantum state, with the
condition reading the outcomes through `O` and with the assigned error `e`. Preparation: reset
the qubit to `|0⟩`, then the error. Gate: the ideal unitary on its qubits if the condition holds
(identity otherwise), then the error. Wait: the error only. Measurement: the error, then the
branch of record `r ++ [b]` receives `Π_b ρ_r Π_b`. -/
noncomputable def Loc.apply {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E] (l : Loc N)
    (O : List Bool → ℕ × ℕ → Option Bool) (e : Option (Superop (Qubits N × E) (Qubits N × E)))
    (ρ : CQState N E) : CQState N E :=
  let errF : Matrix (Qubits N × E) (Qubits N × E) ℂ → Matrix (Qubits N × E) (Qubits N × E) ℂ :=
    fun X => match e with
      | none => X
      | some Φ => Φ X
  let q : Fin N := l.wires ⟨0, l.kind.arity_pos⟩
  let lift : Matrix (Qubits N) (Qubits N) ℂ → Matrix (Qubits N × E) (Qubits N × E) ℂ :=
    fun M => Matrix.kronecker M 1
  match l.kind with
  | .prep => fun r => errF (krausApply (fun b : Bool => lift (qubitOp1 (resetKraus b) q)) (ρ r))
  | .meas => fun r => match r.getLast? with
      | none => 0
      | some b => conjSuperop (lift (qubitOp1 (measProj b) q)) (errF (ρ r.dropLast))
  | .wait => fun r => errF (ρ r)
  | .had | .tgate | .cnot => fun r => errF (if l.cond (O r) then
      conjSuperop (lift (embedOp l.kind.idealMatrix l.wires)) (ρ r) else ρ r)

/-- The locations of one time step `s`, applied in list order (position `j` upward). -/
noncomputable def runStep {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (O : List Bool → ℕ × ℕ → Option Bool) (err : ErrAssign N E) (s : ℕ) :
    List (Loc N) → ℕ → CQState N E → CQState N E
  | [], _, ρ => ρ
  | l :: ls, j, ρ => runStep O err s ls (j + 1) (l.apply O (err (s, j)) ρ)

namespace LocCircuit

variable {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

/-- The time steps `s, s + 1, …` given by the list, in order; at step `s` the conditions see the
outcomes of the measurement locations of steps `< s`. -/
noncomputable def runFrom (C : LocCircuit N) (err : ErrAssign N E) :
    List (List (Loc N)) → ℕ → CQState N E → CQState N E
  | [], _, ρ => ρ
  | st :: rest, s, ρ =>
      C.runFrom err rest (s + 1)
        (runStep (fun r ℓ => if ℓ.1 < s then C.outcomeAt r ℓ else none) err s st 0 ρ)

/-- Gottesman intro pp.17–18: the classical–quantum state after running the whole circuit with the
error assignment `err` from the state `ρ`. -/
noncomputable def run (C : LocCircuit N) (err : ErrAssign N E) (ρ : CQState N E) : CQState N E :=
  C.runFrom err C.steps 0 ρ

end LocCircuit

/-- The initial state: all qubits `|0⟩` (immaterial for circuits that prepare every qubit before
use), the environment in `σ0`, the empty record. -/
noncomputable def initState (N : ℕ) {E : Type*} (σ0 : Matrix E E ℂ) : CQState N E :=
  fun r => if r = [] then Matrix.kronecker (pureDensity (zeroKet N)) σ0 else 0

namespace LocCircuit

variable {N : ℕ}

/-- Gottesman intro p.19 and p.36 (Thm 7): the output distribution of the circuit: the
probability of each measurement record (outcomes in step-major order) under the error assignment
`err`, the environment starting in `σ0`. -/
noncomputable def outDist {E : Type*} [Fintype E] [DecidableEq E] (C : LocCircuit N)
    (err : ErrAssign N E) (σ0 : Matrix E E ℂ) : (Fin C.measCount → Bool) → ℝ :=
  fun r => (C.run err (initState N σ0) (List.ofFn r)).trace.re

/-- Gottesman intro p.19: the output distribution of the circuit without errors. -/
noncomputable def idealOutDist (C : LocCircuit N) : (Fin C.measCount → Bool) → ℝ :=
  C.outDist (E := Fin 1) (fun _ => none) 1

end LocCircuit

/-- Gottesman intro p.19 ("the final fault-tolerant measurement gadgets will produce classical
information which should … give the same outcome as the original circuit"): the distribution of
the classically decoded record `dec r′` when `r′` has distribution `μ`. -/
def pushDist {M M' : ℕ} (dec : List Bool → List Bool) (μ : (Fin M' → Bool) → ℝ) :
    (Fin M → Bool) → ℝ :=
  fun r => ∑ r' ∈ Finset.univ.filter (fun r' : Fin M' → Bool => dec (List.ofFn r') = List.ofFn r), μ r'

/-- Gottesman intro p.20 ("restrict attention to cases where the error associated to each fault is
a Pauli operator"): a Pauli fault arrangement: `some (P, Q)` makes the location faulty with the
Pauli error `P` on its first qubit and `Q` on its second (`Q` is ignored for one-qubit
locations). -/
abbrev PauliArrangement :=
  ℕ × ℕ → Option (Stabilizer.Pauli × Stabilizer.Pauli)

/-- The faulty locations of the circuit under a Pauli arrangement (p.20: the `s` of a gadget is
their number). -/
def faultyLocs {N : ℕ} (C : LocCircuit N) (fa : PauliArrangement) : Finset (ℕ × ℕ) :=
  C.locs.filter fun ℓ => fa ℓ ≠ none

/-- The Pauli operator `P` (first qubit) `⊗ Q` (other qubits) on the qubits of a location. -/
noncomputable def locPauli (k : ℕ) (P Q : Stabilizer.Pauli) : Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun y z => ∏ i : Fin k, (if (i : ℕ) = 0 then P else Q).mat (y i) (z i)

/-- Gottesman intro p.20: the error assignment of a Pauli arrangement: conjugation by the Pauli
error on the qubits of each faulty location (trivial environment). -/
noncomputable def pauliErr {N : ℕ} (C : LocCircuit N) (fa : PauliArrangement) :
    ErrAssign N (Fin 1) :=
  fun ℓ => match C.locAt ℓ, fa ℓ with
    | some l, some pq =>
        some (conjSuperop (Matrix.kronecker (embedOp (locPauli l.kind.arity pq.1 pq.2) l.wires)
          (1 : Matrix (Fin 1) (Fin 1) ℂ)))
    | _, _ => none

/-- Gottesman intro p.18 ("an error that can affect all of the qubits involved in the action") and
p.40 (Def. 12: "any quantum operation"): `Φ` is an admissible error at a location with qubits `w`:
some quantum operation on those qubits jointly with the environment, the identity on the other
qubits. -/
def IsLocError {N k : ℕ} (w : Fin k ↪ Fin N) {E : Type*} [Fintype E] [DecidableEq E]
    (Φ : Superop (Qubits N × E) (Qubits N × E)) : Prop :=
  ∃ Ψ : Superop ((Fin k → Bool) × E) ((Fin k → Bool) × E), IsChannel Ψ ∧ Φ = liftSuperop w Ψ

/-! ### Sanity tests -/

example : LocKind.cnot.arity = 2 ∧ LocKind.meas.arity = 1 := ⟨rfl, rfl⟩

example (y z : Qubits 1) : LocKind.had.idealMatrix y z = hadamard (y 0) (z 0) := rfl

example {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E] (err : ErrAssign N E) (ρ : CQState N E) :
    (⟨[]⟩ : LocCircuit N).run err ρ = ρ := rfl

example {N : ℕ} : (⟨[]⟩ : LocCircuit N).IsWellFormed ∅ ∅ :=
  ⟨fun s hs => absurd hs (by simp), rfl⟩

example : (⟨[[⟨.prep, Stabilizer.wire1 0, fun _ => true⟩], [⟨.meas, Stabilizer.wire1 0, fun _ => true⟩]]⟩ :
    LocCircuit 1).measIds = [(1, 0)] := rfl

example {M : ℕ} (μ : (Fin M → Bool) → ℝ) : pushDist id μ = μ := by
  funext r
  simp [pushDist, List.ofFn_inj, Finset.filter_eq']

example {N : ℕ} (C : LocCircuit N) : faultyLocs C (fun _ => none) = ∅ := by
  simp [faultyLocs]

example {N : ℕ} (C : LocCircuit N) (ℓ : ℕ × ℕ) : pauliErr C (fun _ => none) ℓ = none := by
  simp only [pauliErr]
  split <;> simp_all

end QAlgorithms


