-- Prove2me | Definitions.Def_QAlgorithms_Defs_FaultTolerance
-- name    : QAlgorithms_Defs_FaultTolerance
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T18:01:28.174956+00:00
-- url     : https://prove2.me/theorems/be4ab200-54d2-49af-8df0-eb0cf4a726ed
-- title:
--   Fault-tolerant protocols: gadgets, ideal and *-decoders, Defs. 1–5, ExRecs and their
-- statement:
--   Fault-tolerant protocols: gadgets, ideal and *-decoders, Defs. 1–5, ExRecs and their
--
--   ### QAlgorithms.FTProtocol
--
--   A **fault-tolerance protocol** is a bundle of the following data, with no conditions imposed.
--
--   **Sizes:**
--   - $n\in\mathbb N$, the number of code qubits;
--   - $t\in\mathbb N$;
--   - $A\in\mathbb N$, the number of ancilla qubits per block.
--
--   **Code data:**
--   - a complex linear subspace $\mathcal C\subseteq\mathbb C^{\{0,1\}^n}$ (the code);
--   - a $2^n\times 2$ complex matrix $\mathrm{enc}$, with rows indexed by $\{0,1\}^n$ and columns by $\{0,1\}$;
--   - a map $\mathrm{dec}$ from $2^n\times 2^n$ complex matrices to $2\times2$ complex matrices. It is an arbitrary function, not required to be linear.
--
--   **Circuits:**
--   - for each location kind $\kappa\in\{\text{prep},H,T,\text{CNOT},\text{meas},\text{wait}\}$, a location circuit $\mathrm{gadget}_\kappa$ on $a(\kappa)\cdot(n+A)$ qubits, where $a(\text{CNOT})=2$ and $a(\kappa)=1$ otherwise;
--   - a location circuit $\mathrm{ec}$ on $n+A$ qubits.
--
--   **Measurement decoding:**
--   - a map $\mathrm{measDecode}$ from finite bit lists to bits.
--
--   ### QAlgorithms.IsEncodingOf
--
--   For a subspace $\mathcal C\subseteq\mathbb C^{\{0,1\}^n}$ and a $2^n\times2$ complex matrix $\mathrm{enc}$, the proposition asserts both of the following:
--
--   1. $\mathrm{enc}^\dagger\,\mathrm{enc}=I_2$, i.e. $\mathrm{enc}$ is an isometry $\mathbb C^2\to\mathbb C^{2^n}$.
--   2. The image of the linear map $\psi\mapsto\mathrm{enc}\,\psi$, from $\mathbb C^2$ to $\mathbb C^{2^n}$, equals $\mathcal C$.
--
--   Together these force $\dim\mathcal C=2$, and hence $n\ge1$.
--
--   ### QAlgorithms.IsIdealDecoder
--
--   For a $2^n\times 2$ matrix $\mathrm{enc}$, a number $t\in\mathbb N$, and a map $D$ from $2^n\times2^n$ matrices to $2\times2$ matrices, the proposition asserts two things.
--
--   **(i) $D$ is a channel.** There exist $m$ and $2\times 2^n$ matrices $K_1,\dots,K_m$ with $\sum_a K_a^\dagger K_a=I_{2^n}$ and $D(\rho)=\sum_aK_a\rho K_a^\dagger$ for all $\rho$.
--
--   **(ii) $D$ undoes low-weight errors on encoded states.** For every matrix $E$ in the complex linear span of all Pauli-string matrices of weight at most $t$, and every unit vector $\psi\in\mathbb C^2$, set $v=E\,\mathrm{enc}\,\psi$. Then
--
--   $$
--   D\big(|v\rangle\langle v|\big)=\|v\|^2\,|\psi\rangle\langle\psi| .
--   $$
--
--   The span used in (ii) is defined as follows:
--
--   - A Pauli-string matrix is $i^{c}\,\sigma_1\otimes\cdots\otimes\sigma_n$ with $c\in\mathbb Z/4$ and each $\sigma_j\in\{I,X,Y,Z\}$.
--   - Its weight is the number of positions $j$ with $\sigma_j\ne I$.
--   - The span includes $E=0$, for which the condition reads $D(0)=0$.
--
--   ### QAlgorithms.IsStarDecoder
--
--   Let $D$ be a map from $2^n\times2^n$ matrices to $2\times2$ matrices, and let $W$ be a complex matrix with rows indexed by $\{0,1\}\times\{0,\dots,\sigma-1\}$ and columns indexed by $\{0,1\}^n$. The proposition asserts three conditions:
--
--   1. $W^\dagger W=I_{2^n}$;
--   2. $WW^\dagger=I_{2\sigma}$;
--   3. for every $2^n\times2^n$ matrix $\rho$, $\operatorname{Tr}_2\!\big(W\rho W^\dagger\big)=D(\rho)$.
--
--   In condition 3, $\operatorname{Tr}_2$ traces out the second factor:
--   $$
--   \operatorname{Tr}_2(M)_{b,b'}=\sum_{h=0}^{\sigma-1}M_{(b,h),(b',h)}.
--   $$
--
--   Conditions 1 and 2 say that $W$ is unitary. This is satisfiable only when $2\sigma=2^n$, i.e. $n\ge1$ and $\sigma=2^{n-1}$. For any other $\sigma$ (in particular $\sigma=0$, or $n=0$) the proposition is false.
--
--   ### QAlgorithms.blockLayout
--
--   For $k,n,A\in\mathbb N$, this is an explicit bijection
--   $$
--   \{0,1\}^{k(n+A)}\;\xrightarrow{\ \sim\ }\;\big(\{0,1\}^n\big)^k\times\big(\{0,1\}^A\big)^k .
--   $$
--
--   It splits the $k(n+A)$ wires into $k$ consecutive blocks of $n+A$ wires each. Block $i$ consists of wires $(n+A)i,\dots,(n+A)i+n+A-1$. Within block $i$:
--
--   - the first $n$ wires form the data string;
--   - the last $A$ wires form the ancilla string.
--
--   Explicitly, a bit string $z$ is sent to the pair $\big((x_i)_{i<k},(a_i)_{i<k}\big)$, where
--   $$
--   x_i(j)=z\big((n+A)i+j\big)\ \ (j<n),\qquad a_i(j')=z\big((n+A)i+n+j'\big)\ \ (j'<A).
--   $$
--
--   ### QAlgorithms.singleLayout
--
--   For natural numbers $n$ and $A$, $\mathrm{singleLayout}(n,A)$ is a bijection
--   $$\{0,1\}^{n+A}\;\xrightarrow{\ \sim\ }\;\big(\{0\}\to\{0,1\}^n\big)\times\big(\{0\}\to\{0,1\}^A\big).$$
--   Here a bit string on $n+A$ wires is a function from $\{0,\dots,n+A-1\}$ to $\{0,1\}$. The map works in two steps:
--
--   1. It splits $z$ into its first $n$ bits $(z_0,\dots,z_{n-1})$ (the "data" part) and its last $A$ bits $(z_n,\dots,z_{n+A-1})$ (the "ancilla" part).
--   2. It wraps each part as the constant function on the one-element index set $\{0\}$ ("block $0$").
--
--   The inverse concatenates the data string of block $0$ followed by the ancilla string of block $0$. Edge cases: $n=0$ or $A=0$ (an empty part) are allowed.
--
--   ### QAlgorithms.blockDataWires
--
--   For natural numbers $k,n,A$, $\mathrm{blockDataWires}(k,n,A)$ is a finite set of wires among the $k(n+A)$ wires $\{0,\dots,k(n+A)-1\}$. It is the image of all pairs $(i,j)$ with $0\le i<k$ and $0\le j<n$ under Mathlib's standard product-to-index bijection $\{0,\dots,k-1\}\times\{0,\dots,n+A-1\}\to\{0,\dots,k(n+A)-1\}$, $(i,j')\mapsto (n+A)\,i+j'$, applied with $j'=j$. That is,
--   $$\mathrm{blockDataWires}(k,n,A)=\{(n+A)\,i+j \;:\; 0\le i<k,\ 0\le j<n\}.$$
--   Thinking of the wires as $k$ consecutive blocks of length $n+A$, these are the first $n$ wires of each block. It has $kn$ elements. It is empty if $k=0$ or $n=0$.
--
--   ### QAlgorithms.ecDataWires
--
--   For natural numbers $n$ and $A$, $\mathrm{ecDataWires}(n,A)$ is the set of wires
--   $$\{0,1,\dots,n-1\}\subseteq\{0,\dots,n+A-1\},$$
--   the image of $\{0,\dots,n-1\}$ under the inclusion that keeps each index's value. These are the first $n$ of the $n+A$ wires. It is empty if $n=0$.
--
--   ### QAlgorithms.embedVia
--
--   The inputs are:
--
--   - natural numbers $N,k,n,A$;
--   - a bijection $L:\{0,1\}^N\to(\{0,\dots,k-1\}\to\{0,1\}^n)\times(\{0,\dots,k-1\}\to\{0,1\}^A)$. Write $L(y)=(L_1(y),L_2(y))$: the "data" strings of $k$ blocks and the "ancilla" strings of $k$ blocks;
--   - a complex matrix $X$ indexed by $k$-tuples of $n$-bit strings.
--
--   The output $\mathrm{embedVia}(L,X)$ is a complex matrix indexed by pairs $(y,e)$, where $y\in\{0,1\}^N$ and $e$ ranges over the one-element set $\{0\}$ (a trivial "environment" factor). Its entries are
--   $$\mathrm{embedVia}(L,X)_{(y,e),(y',e')}=\begin{cases}X_{L_1(y),\,L_1(y')} & \text{if } L_2(y)\text{ and }L_2(y')\text{ are both the all-zero ancilla assignment},\\ 0&\text{otherwise.}\end{cases}$$
--   Thus, transported through $L$, it equals $X\otimes|0\cdots0\rangle\langle0\cdots0|_{\text{ancillas}}$, tensored with the $1\times1$ matrix $[1]$. No positivity, trace, or other condition is imposed on $X$.
--
--   ### QAlgorithms.traceVia
--
--   The inputs are:
--
--   - natural numbers $N,k,n,A$;
--   - a bijection $L:\{0,1\}^N\to(\{0,\dots,k-1\}\to\{0,1\}^n)\times(\{0,\dots,k-1\}\to\{0,1\}^A)$ (data strings and ancilla strings of $k$ blocks);
--   - a complex matrix $Y$ indexed by pairs $(y,e)$ with $y\in\{0,1\}^N$ and $e\in\{0\}$.
--
--   The output $\mathrm{traceVia}(L,Y)$ is the matrix indexed by $k$-tuples of $n$-bit strings given by
--   $$\mathrm{traceVia}(L,Y)_{x,x'}=\sum_{a\in(\{0,\dots,k-1\}\to\{0,1\}^A)}\ \sum_{e\in\{0\}} Y_{(L^{-1}(x,a),\,e),\ (L^{-1}(x',a),\,e)}.$$
--   This is the partial trace of $Y$ over all ancilla bits (as identified by $L$) and over the trivial one-dimensional environment factor. No condition is imposed on $Y$.
--
--   ### QAlgorithms.gadgetOut
--
--   The inputs are:
--
--   - a natural number $N$;
--   - a located circuit $G$ on $N$ qubits: a list of time steps, each a list of locations; each location has a kind (prep, H, T, CNOT, meas, wait), an ordered tuple of distinct wires (2 for CNOT, otherwise 1), and a classical condition;
--   - a Pauli fault arrangement $\mathrm{fa}$, which assigns to every pair $\ell=(s,j)$ (step $s$, position $j$) either "no fault" or a pair of single-qubit Paulis $(P,Q)\in\{I,X,Y,Z\}^2$;
--   - a complex matrix $\rho_{\mathrm{in}}$ indexed by $\{0,1\}^N\times\{0\}$;
--   - a Boolean predicate $B$ on finite bit lists.
--
--   Let $M$ be the number of measurement locations of $G$. Then
--   $$\mathrm{gadgetOut}(G,\mathrm{fa},\rho_{\mathrm{in}},B)=\sum_{\substack{r\in\{0,1\}^M\\ B(r_0,\dots,r_{M-1})=\text{true}}}\ \mathrm{run}_G\big(\mathcal E_{\mathrm{fa}},\ \sigma_0\big)(r_0,\dots,r_{M-1}).$$
--
--   **The initial state.** $\sigma_0$ is the classical–quantum state, i.e. a map from outcome records (bit lists) to matrices. It assigns $\rho_{\mathrm{in}}$ to the empty record and $0$ to every other record.
--
--   **What the run does.** $\mathrm{run}_G$ processes the locations in order: step by step, and within a step in list order. At each location it acts on the matrix stored under each record $r$:
--
--   - **prep:** resets the location's first wire to $|0\rangle$, using Kraus operators $|0\rangle\langle b|$ for $b\in\{0,1\}$.
--   - **meas:** maps the record $r$ (ending in bit $b$) to the conjugation by the projector $|b\rangle\langle b|$ on the first wire, applied to the matrix stored under $r$ with its last bit removed. The empty record gets $0$.
--   - **wait:** does nothing.
--   - **H, T, CNOT:** conjugates by the ideal gate on the location's wires if the location's condition evaluated on the earlier-step outcomes recorded in $r$ is true; otherwise does nothing.
--
--   **The errors.** $\mathcal E_{\mathrm{fa}}$ assigns an error to location $\ell$ only if $\ell$ is an actual location of $G$ and $\mathrm{fa}(\ell)=(P,Q)$. The error is conjugation by the Pauli operator that applies $P$ on the location's first wire and $Q$ on its remaining wire (if any), tensored with $[1]$ on the environment. The error is applied:
--
--   - after the ideal action, for prep, gates and wait;
--   - before the projection, for meas.
--
--   The result is an unnormalized matrix on $\{0,1\}^N\times\{0\}$: the sum of the branches over all length-$M$ outcome records accepted by $B$. If $M=0$, the sum has the single empty record.
--
--   ### QAlgorithms.faultCount
--
--   The inputs are a natural number $N$, a located circuit $G$ on $N$ qubits, and a Pauli fault arrangement $\mathrm{fa}$ (assigning to each pair $(s,j)$ either "no fault" or a pair of Paulis). Then $\mathrm{faultCount}(G,\mathrm{fa})$ is the natural number
--   $$\#\{(s,j)\;:\; s<\text{(number of steps of }G),\ j<\text{(number of locations in step }s),\ \mathrm{fa}(s,j)\neq\text{no fault}\}.$$
--   This counts the faulty locations that are actual locations of $G$. Fault assignments at pairs $(s,j)$ outside $G$ are not counted.
--
--   ### QAlgorithms.LocKind.IsGateOrWait
--
--   For a location kind $\kappa\in\{\text{prep},\text{H},\text{T},\text{CNOT},\text{meas},\text{wait}\}$, $\mathrm{IsGateOrWait}(\kappa)$ is the proposition
--   $$\kappa=\text{H}\ \lor\ \kappa=\text{T}\ \lor\ \kappa=\text{CNOT}\ \lor\ \kappa=\text{wait}.$$
--   It is false exactly for prep and meas.
--
--   ### QAlgorithms.FTProtocol.gateOp
--
--   **The protocol.** Fix a protocol $P$ with the following components:
--
--   - a block size $n$ and an ancilla count $A$;
--   - for each location kind $\kappa$, a gadget circuit $G_\kappa$ on $a_\kappa(n+A)$ qubits, where the arity $a_\kappa$ is $2$ for CNOT and $1$ otherwise;
--   - an error-correction circuit;
--   - a classical decoder.
--
--   **The definition.** For a kind $\kappa$ (any of the six; no restriction to gates is imposed) and a Pauli fault arrangement $\mathrm{fa}$, $P.\mathrm{gateOp}(\kappa,\mathrm{fa})$ is the map sending a complex matrix $X$ indexed by $a_\kappa$-tuples of $n$-bit strings to
--   $$\mathrm{tr}_{\mathrm{anc}}\Big(\sum_{r\in\{0,1\}^{M_\kappa}}\mathrm{run}_{G_\kappa}\big(\mathcal E_{\mathrm{fa}},\ \sigma_X\big)(r)\Big).$$
--   In this formula:
--
--   - **The layout.** The $a_\kappa(n+A)$ wires are arranged as $a_\kappa$ consecutive blocks of $n+A$. Wire $(n+A)i+j$ is data bit $j$ of block $i$ when $j<n$, and ancilla bit $j-n$ of block $i$ when $j\ge n$.
--   - **The input $\sigma_X$.** It is the classical–quantum state that assigns, to the empty record, $X\otimes|0\cdots0\rangle\langle0\cdots0|$ on all ancilla bits, times $[1]$ on a trivial one-dimensional environment, transported through this layout. Every other record gets $0$.
--   - **The run.** $\mathrm{run}_{G_\kappa}$ executes the gadget location by location. At each location it conditions on earlier outcomes and stores the post-measurement branch under each outcome record.
--   - **The faults.** $\mathcal E_{\mathrm{fa}}$ inserts, at each actual location $\ell$ of $G_\kappa$ with $\mathrm{fa}(\ell)=(P_1,Q_1)$, conjugation by $P_1$ on the location's first wire and $Q_1$ on its second wire (if any). The fault comes after prep, gate and wait actions, and before measurement projections.
--   - **The outcomes.** The sum runs over all records of length $M_\kappa$, the number of measurement locations of $G_\kappa$. No outcome is filtered out.
--   - **The partial trace.** $\mathrm{tr}_{\mathrm{anc}}$ is the partial trace over all ancilla bits of all blocks and over the trivial environment.
--
--   The output is not required to be normalized or positive. Nothing about well-formedness of $G_\kappa$ is assumed.
--
--   ### QAlgorithms.FTProtocol.prepState
--
--   **The protocol.** Fix a protocol $P$ with:
--
--   - a block size $n$ and an ancilla count $A$;
--   - a preparation gadget $G_{\text{prep}}$, a located circuit on $1\cdot(n+A)$ qubits.
--
--   **The definition.** For a Pauli fault arrangement $\mathrm{fa}$, $P.\mathrm{prepState}(\mathrm{fa})$ is the complex matrix indexed by $n$-bit strings obtained as follows:
--
--   1. **Start.** Take the classical–quantum state that assigns, to the empty record, the pure all-zero state $|0^{n+A}\rangle\langle0^{n+A}|$ on all $n+A$ wires, tensored with the $1\times1$ identity $[1]$ on a trivial environment. Every other record gets $0$.
--   2. **Run.** Run $G_{\text{prep}}$ with the Pauli faults dictated by $\mathrm{fa}$. At each actual location $\ell$ with $\mathrm{fa}(\ell)=(P_1,Q_1)$, conjugate by $P_1$ on its first wire and $Q_1$ on its second wire (if any); this comes after prep, gate and wait actions, and before measurement projections. Sum the resulting branch matrices over all outcome records of length equal to the number of measurement locations of $G_{\text{prep}}$; no outcome is excluded.
--   3. **Trace out ancillas.** Take the partial trace over the last $A$ wires (the ancillas of the single block, where wire $j<n$ is data bit $j$) and over the trivial environment.
--   4. **Reindex.** Reindex from one-block tuples $\{0\}\to\{0,1\}^n$ to $n$-bit strings $y$, via $y\mapsto(\text{the constant tuple }y)$.
--
--   The input state is fixed to all-zeros on every wire, data included. The result need not be normalized.
--
--   ### QAlgorithms.FTProtocol.measFunctional
--
--   **The protocol.** Fix a protocol $P$ with:
--
--   - a block size $n$ and an ancilla count $A$;
--   - a measurement gadget $G_{\text{meas}}$ on $1\cdot(n+A)$ qubits;
--   - a classical decoding map $\mathrm{dec}$ from bit lists to bits.
--
--   **The definition.** For a Pauli fault arrangement $\mathrm{fa}$, a bit $\beta$, and a complex matrix $\rho$ indexed by $n$-bit strings, $P.\mathrm{measFunctional}(\mathrm{fa},\beta)(\rho)$ is the complex number
--   $$\mathrm{Tr}\Big(\sum_{\substack{r\in\{0,1\}^{M}\\ \mathrm{dec}(r_0,\dots,r_{M-1})=\beta}}\mathrm{run}_{G_{\text{meas}}}\big(\mathcal E_{\mathrm{fa}},\ \sigma_\rho\big)(r)\Big).$$
--   In this formula:
--
--   - **The input $\sigma_\rho$.** It assigns, to the empty record, $\rho$ on the data wires $0,\dots,n-1$ tensored with $|0^A\rangle\langle0^A|$ on the ancilla wires $n,\dots,n+A-1$ and with $[1]$ on a trivial environment. Here $\rho$ is first reindexed to one-block tuples, i.e. tuple $x\mapsto$ string $x_0$. Every other record gets $0$.
--   - **The run.** $\mathrm{run}$ executes $G_{\text{meas}}$ with the Pauli faults of $\mathrm{fa}$. At each actual location with $\mathrm{fa}(\ell)=(P_1,Q_1)$, conjugate by $P_1$ on its first wire and $Q_1$ on its second wire; this comes after prep, gate and wait actions, and before measurement projections.
--   - **The outcomes.** $M$ is the number of measurement locations of $G_{\text{meas}}$. The sum keeps exactly the outcome records whose decoded bit equals $\beta$.
--   - **The trace.** $\mathrm{Tr}$ is the full trace over $\{0,1\}^{n+A}\times\{0\}$.
--
--   No condition (density matrix or otherwise) is imposed on $\rho$.
--
--   ### QAlgorithms.FTProtocol.ecOp
--
--   **The protocol.** Fix a protocol $P$ with:
--
--   - a block size $n$ and an ancilla count $A$;
--   - an error-correction circuit $G_{\text{ec}}$, a located circuit on $n+A$ qubits.
--
--   **The definition.** For a Pauli fault arrangement $\mathrm{fa}$, $P.\mathrm{ecOp}(\mathrm{fa})$ is the map sending a complex matrix $\rho$ indexed by $n$-bit strings to the matrix indexed by $n$-bit strings obtained as follows:
--
--   1. **Embed.** Reindex $\rho$ to one-block tuples ($x\mapsto x_0$). Then embed it as $\rho$ on the first $n$ wires (data) tensored with $|0^A\rangle\langle0^A|$ on the last $A$ wires (ancillas) and with $[1]$ on a trivial environment. This is the split of $\mathrm{singleLayout}(n,A)$. The embedded matrix is assigned to the empty outcome record; every other record gets $0$.
--   2. **Run.** Run $G_{\text{ec}}$ with the Pauli faults of $\mathrm{fa}$. At each actual location with $\mathrm{fa}(\ell)=(P_1,Q_1)$, conjugate by $P_1$ on its first wire and $Q_1$ on its second wire (if any); this comes after prep, gate and wait actions, and before measurement projections.
--   3. **Sum over outcomes.** Sum the branch matrices over all outcome records of length equal to the number of measurement locations of $G_{\text{ec}}$; no record is excluded.
--   4. **Trace out ancillas.** Take the partial trace over the $A$ ancilla wires and the trivial environment.
--   5. **Reindex back.** Reindex back to $n$-bit strings ($y\mapsto$ constant tuple $y$).
--
--   No condition is imposed on $\rho$, and the output need not be normalized.
--
--   ### QAlgorithms.FTProtocol.filterOp
--
--   This definition is relative to a fixed fault-tolerance protocol $P$. From $P$ it uses only the number $n$ of physical qubits per code block and a code subspace $\mathcal C \subseteq (\mathbb C^2)^{\otimes n}$. The basis of $(\mathbb C^2)^{\otimes n}$ is indexed by $n$-bit strings.
--
--   For a natural number $r$, define the **filter space** as the complex linear span of all vectors $Pc$ such that:
--
--   - $c \in \mathcal C$;
--   - $P$ is a Pauli-string matrix $i^{a}\,(\sigma_1 \otimes \cdots \otimes \sigma_n)$ with $a \in \mathbb Z/4$ and each $\sigma_q \in \{I, X, Y, Z\}$;
--   - $P$ has weight at most $r$, meaning at most $r$ of the factors $\sigma_q$ differ from $I$.
--
--   $$\mathcal F_r = \operatorname{span}_{\mathbb C}\{\, Pc : c\in\mathcal C,\ P \text{ a Pauli string of weight} \le r \,\}.$$
--
--   Let $\Pi_r$ be the $2^n\times 2^n$ matrix of the orthogonal projection onto $\mathcal F_r$. The filter operation $F_r$ is the map on all $2^n\times 2^n$ complex matrices $\rho$ given by conjugation:
--
--   $$F_r(\rho) = \Pi_r\, \rho\, \Pi_r^{\dagger} = \Pi_r\, \rho\, \Pi_r .$$
--
--   The second equality holds because $\Pi_r$ is Hermitian.
--
--   Edge cases:
--
--   - For $r = 0$, the only Pauli strings are scalar multiples $i^a I$, so $\mathcal F_0 = \mathcal C$ and $\Pi_0$ is the projector onto $\mathcal C$.
--   - If $\mathcal C = 0$, then $\Pi_r = 0$ for every $r$.
--   - If $r \ge n$ and $\mathcal C \ne 0$, all Pauli strings are allowed. Their span applied to $\mathcal C$ is the whole space, so $\Pi_r = I$.
--
--   ### QAlgorithms.FTProtocol.IsFaultTolerant
--
--   **The protocol.** This is a property of a fault-tolerance protocol $P$, which consists of the following data:
--
--   - natural numbers $n$ (data qubits per block), $t$ (fault budget) and $A$ (ancilla qubits per block);
--   - a subspace $\mathcal C\subseteq(\mathbb C^2)^{\otimes n}$;
--   - a $2^n\times 2$ complex matrix $\mathrm{enc}$;
--   - an arbitrary map $\mathrm{dec}$ from $2^n\times2^n$ complex matrices to $2\times2$ complex matrices;
--   - for every location kind $\kappa$, a "gadget" circuit $G_\kappa$ on $a_\kappa(n+A)$ wires;
--   - an error-correction circuit $G_{\mathrm{EC}}$ on $n+A$ wires;
--   - a classical map $\mathrm{measDecode}$ from bit lists to bits.
--
--   The location kinds are preparation, Hadamard, $T$, CNOT, measurement and wait. The arity $a_\kappa$ is $2$ for CNOT and $1$ otherwise.
--
--   **Blocks.** In a circuit on $k(n+A)$ wires, block $i$ consists of wires $i(n+A),\dots,i(n+A)+n+A-1$. Its first $n$ wires are the data wires and its last $A$ wires are the ancilla wires.
--
--   **Fault arrangements.** A circuit is a list of steps. Each step is a list of locations, and a location has a kind, an ordered tuple of distinct wires, and a classical condition. A location is addressed by the pair (step index, position within the step).
--
--   A fault arrangement $f$ assigns to every address either nothing or a pair $(Q_1,Q_2)$ of single-qubit Paulis. The number of faults $\#_G(f)$ is the number of actual locations of $G$ that receive a pair. Values of $f$ at addresses that are not locations of $G$ are ignored.
--
--   **Noisy run.** Running a circuit $G$ with faults $f$ means executing $G$ on a classical–quantum state, that is, matrices indexed by measurement-outcome records, with a trivial one-dimensional environment. At each faulty location, conjugation by $Q_1$ is inserted on its first wire, and by $Q_2$ on its second wire for a CNOT. This insertion happens:
--
--   - after the location's ideal action for preparations (reset to $|0\rangle$), gates and waits;
--   - before the outcome projection for measurements.
--
--   Gate locations act only when their classical condition on earlier outcomes holds.
--
--   **Derived operations.** Four objects are built from noisy runs.
--
--   - **Gadget operation $\mathcal G^f_\kappa$.** For a matrix $X$ on $a_\kappa$ data blocks:
--     1. tensor $X$ with $|0\cdots0\rangle\langle0\cdots0|$ on all ancilla wires;
--     2. run $G_\kappa$ with faults $f$;
--     3. sum the result over all outcome records;
--     4. trace out the ancillas.
--   - **EC operation $\mathcal E^f$.** The same construction with the single-block circuit $G_{\mathrm{EC}}$.
--   - **Prepared state $\sigma^f$.** Run $G_{\mathrm{prep}}$ from $|0\cdots0\rangle\langle 0\cdots0|$ on all $n+A$ wires, sum over all records, and trace out the ancillas.
--   - **Measurement functional $M^f_\beta(\rho)$.** Tensor $\rho$ with zero ancillas and run $G_{\mathrm{meas}}$ with faults $f$. Sum over exactly those outcome records $s$ with $\mathrm{measDecode}(s)=\beta$, and take the trace.
--
--   **Notation.**
--
--   - $F_r(\rho)=\Pi_r\rho\Pi_r$, where $\Pi_r$ is the orthogonal projector onto $\operatorname{span}\{Pc: c\in\mathcal C,\ P \text{ a Pauli string } i^a\sigma_1\otimes\cdots\otimes\sigma_n \text{ with at most } r \text{ non-identity factors}\}$.
--   - For maps $\Phi_1,\dots,\Phi_k$ on single-block matrices, $\bigotimes_i\Phi_i$ is defined by applying the tensor product to matrix units and extending linearly:
--   $$\Big(\bigotimes_i\Phi_i\Big)(X)_{y,y'}=\sum_{x,x'}X_{x,x'}\prod_i\big[\Phi_i(E_{x_ix_i'})\big]_{y_i,y_i'}.$$
--   - $U_\kappa$ is the ideal gate: $H$ for Hadamard, $T=\operatorname{diag}(1,e^{i\pi/4})$, CNOT with the first qubit as control, and $I$ for wait.
--   - A superoperator is a *channel* if, for some $m$, it equals $\rho\mapsto\sum_{j<m}E_j\rho E_j^\dagger$ for all $\rho$, with $\sum_j E_j^\dagger E_j=I$.
--   - Equalities between maps are equalities on **all** complex matrices, not only on density matrices.
--
--   $P$ is fault-tolerant iff all of the following hold.
--
--   1. **Code.** $\dim\mathcal C = 2$, and every matrix $E$ acting on at most $2t$ qubits is detectable on $\mathcal C$.
--      - "Acting on at most $2t$ qubits" means $E$ is some matrix on some tuple of wires inside a set of at most $2t$ wires, tensored with the identity elsewhere.
--      - "Detectable" means there is a constant $c$ with $\langle\psi,E\psi\rangle=c$ for all unit $\psi\in\mathcal C$.
--      - This conjunct forces $n\ge1$.
--   2. **Encoding.** $\mathrm{enc}^\dagger\mathrm{enc}=I_2$ and the range of $\mathrm{enc}$ is $\mathcal C$.
--   3. **Ideal decoder.** $\mathrm{dec}$ is a channel. For every $E$ in the complex span of Pauli strings of weight $\le t$ and every unit $\psi\in\mathbb C^2$,
--   $$\mathrm{dec}\big(|E\,\mathrm{enc}\,\psi\rangle\langle E\,\mathrm{enc}\,\psi|\big)=\|E\,\mathrm{enc}\,\psi\|^2\,|\psi\rangle\langle\psi|.$$
--   4. **Well-formedness.** Every circuit below is well-formed from an input live set $L_{\mathrm{in}}$ to an output live set $L_{\mathrm{out}}$.
--      - The live sets evolve as $L_0=L_{\mathrm{in}}$ and $L_{s+1}=(L_s\cup\text{prep wires of step }s)\setminus\text{meas wires of step }s$.
--      - In every step:
--        - distinct locations use disjoint wires;
--        - every wire in $L_s$ is used by some location;
--        - preparation locations use only wires outside $L_s$;
--        - all other locations use only wires in $L_s$.
--      - The final live set equals $L_{\mathrm{out}}$.
--
--      The required live sets are:
--      - $G_{\mathrm{prep}}$: from $\emptyset$ to the $n$ data wires;
--      - $G_{\mathrm{meas}}$: from the data wires to $\emptyset$;
--      - each $G_\kappa$ for $\kappa\in\{H,T,\mathrm{CNOT},\mathrm{wait}\}$: from the data wires of its $a_\kappa$ blocks to the same set;
--      - $G_{\mathrm{EC}}$: from the first $n$ of its $n+A$ wires to the same set.
--   5. **Meas.** For all $f$ and $r$ with $r+\#_{G_{\mathrm{meas}}}(f)\le t$, all bits $\beta$ and all $2^n\times2^n$ matrices $\rho$:
--   $$M^f_\beta(F_r\rho)=\big[\mathrm{dec}(F_r\rho)\big]_{\beta\beta}.$$
--   6. **Prep A.** For all $f$ with $c=\#_{G_{\mathrm{prep}}}(f)\le t$: $F_c(\sigma^f)=\sigma^f$.
--   7. **Prep B.** For all $f$ with $\#_{G_{\mathrm{prep}}}(f)\le t$: $\mathrm{dec}(\sigma^f)=|0\rangle\langle0|$.
--   8. **Gate A.** For all $\kappa\in\{H,T,\mathrm{CNOT},\mathrm{wait}\}$, all $f$, and all $r_1,\dots,r_{a_\kappa}\in\mathbb N$ with $c+\sum_ir_i\le t$, where $c=\#_{G_\kappa}(f)$:
--   $$\Big(\bigotimes_i F_{c+\sum_j r_j}\Big)\circ\mathcal G^f_\kappa\circ\Big(\bigotimes_iF_{r_i}\Big)=\mathcal G^f_\kappa\circ\Big(\bigotimes_iF_{r_i}\Big).$$
--      The same total index $c+\sum_j r_j$ is used on every output block.
--   9. **Gate B.** Under the same hypotheses as Gate A:
--   $$\Big(\bigotimes_i\mathrm{dec}\Big)\circ\mathcal G^f_\kappa\circ\Big(\bigotimes_iF_{r_i}\Big)=\big(\rho\mapsto U_\kappa\rho U_\kappa^\dagger\big)\circ\Big(\bigotimes_i\mathrm{dec}\Big)\circ\Big(\bigotimes_iF_{r_i}\Big).$$
--   10. **EC A.** For all $f$ with $c=\#_{G_{\mathrm{EC}}}(f)\le t$: $F_c\circ\mathcal E^f=\mathcal E^f$.
--   11. **EC B.** For all $f$ and $r$ with $r+\#_{G_{\mathrm{EC}}}(f)\le t$: $\mathrm{dec}\circ\mathcal E^f\circ F_r=\mathrm{dec}\circ F_r$.
--
--   ### QAlgorithms.LocKind.leadCount
--
--   This function assigns a natural number to each of the six location kinds (preparation, Hadamard, $T$, CNOT, measurement, wait). The arity of a kind is $2$ for CNOT and $1$ for every other kind.
--
--   - A preparation location gets the value $0$.
--   - Every other kind gets its arity: $1$ for Hadamard, $T$, measurement and wait, and $2$ for CNOT.
--
--   ### QAlgorithms.LocKind.trailCount
--
--   This function assigns a natural number to each of the six location kinds (preparation, Hadamard, $T$, CNOT, measurement, wait). The arity of a kind is $2$ for CNOT and $1$ otherwise.
--
--   - A measurement location gets the value $0$.
--   - Every other kind gets its arity: $1$ for preparation, Hadamard, $T$ and wait, and $2$ for CNOT.
--
--   ### QAlgorithms.ExRecFaults
--
--   For a location kind $\kappa$, an object of this type is a triple $(\mathrm{lead},\mathrm{gad},\mathrm{trail})$ of fault arrangements.
--
--   A *fault arrangement* is a function assigning to every pair of natural numbers (step index, position within the step) either nothing or a pair of single-qubit Paulis from $\{I,X,Y,Z\}$.
--
--   The three components are:
--
--   - $\mathrm{lead}$: a family of $\ell_\kappa$ fault arrangements, indexed by $\{0,\dots,\ell_\kappa-1\}$;
--   - $\mathrm{gad}$: a single fault arrangement;
--   - $\mathrm{trail}$: a family of $\tau_\kappa$ fault arrangements, indexed by $\{0,\dots,\tau_\kappa-1\}$.
--
--   The counts depend on $\kappa$:
--
--   - $\ell_\kappa$ is $0$ for preparation and the arity of $\kappa$ otherwise.
--   - $\tau_\kappa$ is $0$ for measurement and the arity otherwise.
--   - The arity is $2$ for CNOT and $1$ otherwise.
--
--   So a preparation has no lead arrangements and one trail arrangement. A measurement has one lead arrangement and no trail arrangements. A CNOT has two of each, and Hadamard, $T$ and wait have one of each.
--
--   There are no constraints on the arrangements.
--
--   ### QAlgorithms.ExRecFaults.count
--
--   This definition uses three inputs:
--
--   - a fault-tolerance protocol $P$, with error-correction circuit $G_{\mathrm{EC}}$ and, for each kind $\kappa$, a gadget circuit $G_\kappa$;
--   - a location kind $\kappa$;
--   - fault data $F=(\mathrm{lead},\mathrm{gad},\mathrm{trail})$ for $\kappa$, with $\mathrm{lead}_i$ for $i<\ell_\kappa$ and $\mathrm{trail}_j$ for $j<\tau_\kappa$. Here $\ell_\kappa$ is $0$ for preparation and the arity otherwise, and $\tau_\kappa$ is $0$ for measurement and the arity otherwise.
--
--   It also takes an arbitrary subset $\mathrm{trunc}\subseteq\{0,\dots,\tau_\kappa-1\}$.
--
--   For a circuit $G$ and a fault arrangement $f$, let $\#_G(f)$ be the number of actual locations of $G$ (addressed by step index and position within step) to which $f$ assigns a Pauli pair. Values of $f$ at non-location addresses do not count.
--
--   The count is the natural number
--
--   $$\sum_{i<\ell_\kappa}\#_{G_{\mathrm{EC}}}(\mathrm{lead}_i)+\#_{G_\kappa}(\mathrm{gad})+\sum_{j<\tau_\kappa,\ j\notin\mathrm{trunc}}\#_{G_{\mathrm{EC}}}(\mathrm{trail}_j).$$
--
--   Trailing arrangements whose index lies in $\mathrm{trunc}$ are not counted.
--
--   ### QAlgorithms.FTProtocol.leadOp
--
--   Fix a fault-tolerance protocol $P$ with $n$ data qubits and $A$ ancilla qubits per block and an error-correction circuit $G_{\mathrm{EC}}$ on $n+A$ wires. Let $k$ be a natural number and $\mathrm{lead}_0,\dots,\mathrm{lead}_{k-1}$ fault arrangements.
--
--   **EC operation.** For a fault arrangement $f$, the map $\mathcal E^f$ acts on a $2^n\times2^n$ matrix $\rho$ as follows:
--
--   1. tensor $\rho$ with $|0^A\rangle\langle0^A|$ on the ancillas;
--   2. run $G_{\mathrm{EC}}$ with the Pauli faults prescribed by $f$, inserted at each faulty location (after preparations, gates and waits; before measurement projections);
--   3. sum the resulting matrices over all measurement-outcome records;
--   4. partially trace out the ancillas.
--
--   **The lead operation.** It acts on matrices indexed by $k$-tuples of $n$-bit strings:
--
--   $$\mathcal L(X)=\Big(\bigotimes_{i<k}\mathcal E^{\mathrm{lead}_i}\Big)(X).$$
--
--   Here the tensor product of maps is defined through matrix units and extended linearly:
--
--   $$\Big(\bigotimes_i\Phi_i\Big)(X)_{y,y'}=\sum_{x,x'}X_{x,x'}\prod_i\big[\Phi_i(E_{x_ix'_i})\big]_{y_i,y'_i}.$$
--
--   For $k=0$, the index set has a single element and the product is empty, so $\mathcal L$ maps a $1\times1$ matrix to itself.
--
--   ### QAlgorithms.FTProtocol.trailOp
--
--   Fix a fault-tolerance protocol $P$ (with $n$ data qubits per block, $A$ ancilla qubits per block, and an error-correction circuit $G_{\mathrm{EC}}$). The inputs are:
--
--   - a natural number $k$;
--   - fault arrangements $\mathrm{trail}_0,\dots,\mathrm{trail}_{k-1}$;
--   - a subset $\mathrm{trunc}\subseteq\{0,\dots,k-1\}$.
--
--   For each $j<k$, define a map $\Phi_j$ on $2^n\times2^n$ matrices:
--
--   - $\Phi_j$ is the identity map if $j\in\mathrm{trunc}$;
--   - otherwise $\Phi_j=\mathcal E^{\mathrm{trail}_j}$.
--
--   Here $\mathcal E^f(\rho)$ is obtained in four steps:
--
--   1. tensor $\rho$ with $|0^A\rangle\langle 0^A|$;
--   2. run $G_{\mathrm{EC}}$ with the Pauli faults $f$;
--   3. sum over all measurement-outcome records;
--   4. trace out the ancillas.
--
--   The trail operation acts on matrices $X$ indexed by $k$-tuples of $n$-bit strings:
--
--   $$\mathcal T(X)_{y,y'}=\sum_{x,x'}X_{x,x'}\prod_{j<k}\big[\Phi_j(E_{x_jx'_j})\big]_{y_j,y'_j}.$$
--
--   This is the tensor product of the $\Phi_j$, applied to matrix units $E_{ab}$ and extended linearly.
--
--   ### QAlgorithms.FTProtocol.GateExRecCorrect
--
--   **Setting.** Fix a fault-tolerance protocol $P$. It has $n$ data and $A$ ancilla qubits per block, an arbitrary decoding map $\mathrm{dec}$ from $2^n\times2^n$ to $2\times2$ complex matrices, gadget circuits $G_\kappa$, and an error-correction circuit $G_{\mathrm{EC}}$.
--
--   **Inputs.**
--
--   - A location kind $\kappa$ of arity $k$: $k=2$ for CNOT and $k=1$ otherwise.
--   - Fault arrangements $\mathrm{lead}_i$ and $\mathrm{trail}_i$ for $i<k$.
--   - A fault arrangement $\mathrm{gad}$.
--   - A subset $\mathrm{trunc}\subseteq\{0,\dots,k-1\}$.
--
--   **Operations involved.**
--
--   - $\mathcal L=\bigotimes_i\mathcal E^{\mathrm{lead}_i}$ and $\mathcal T=\bigotimes_i\Phi_i$, where $\Phi_i$ is the identity map if $i\in\mathrm{trunc}$ and $\mathcal E^{\mathrm{trail}_i}$ otherwise.
--   - $\mathcal E^f$ is the EC operation: tensor with zero ancillas, run $G_{\mathrm{EC}}$ with Pauli faults $f$, sum over outcome records, and trace out the ancillas.
--   - $\mathcal G^{\mathrm{gad}}_\kappa$ is the gadget operation: tensor $k$ data blocks with zero ancillas, run $G_\kappa$ with faults $\mathrm{gad}$, sum over all outcome records, and trace out the ancillas.
--   - $\bigotimes$ of maps means applying them to matrix units and extending linearly.
--   - $U_\kappa$ is $H$, $T=\operatorname{diag}(1,e^{i\pi/4})$, or CNOT (first qubit as control) for those kinds, and the identity for wait, preparation and measurement.
--
--   **The proposition.** The two composite maps agree on every complex matrix $X$ indexed by $k$-tuples of $n$-bit strings:
--
--   $$\Big(\bigotimes_{i<k}\mathrm{dec}\Big)\circ\mathcal T\circ\mathcal G^{\mathrm{gad}}_\kappa\circ\mathcal L=\big(\rho\mapsto U_\kappa\rho U_\kappa^\dagger\big)\circ\Big(\bigotimes_{i<k}\mathrm{dec}\Big)\circ\mathcal L.$$
--
--   The kind $\kappa$ is not restricted to gates.
--
--   ### QAlgorithms.ExRecCorrect
--
--   This is a proposition about three inputs:
--
--   - a fault-tolerance protocol $P$, with $n$ data and $A$ ancilla qubits per block, decoding map $\mathrm{dec}$ from $2^n\times2^n$ to $2\times2$ matrices, gadgets $G_\kappa$, and EC circuit $G_{\mathrm{EC}}$;
--   - a location kind $\kappa$;
--   - fault data $F=(\mathrm{lead},\mathrm{gad},\mathrm{trail})$ for $\kappa$, together with a subset $\mathrm{trunc}$ of the trailing indices.
--
--   **Operations involved.**
--
--   - $\mathcal E^f$ is the EC operation: tensor with zero ancillas, run $G_{\mathrm{EC}}$ with Pauli faults $f$, sum over all outcome records, and trace out the ancillas.
--   - $\sigma^{f}$ is the prepared state: run $G_{\mathrm{prep}}$ with faults $f$ from all-zero on its $n+A$ wires, sum over all records, and trace out the ancillas.
--   - $M^{f}_\beta(\rho)$ is the measurement functional: tensor $\rho$ with zero ancillas, run $G_{\mathrm{meas}}$ with faults $f$, sum over the outcome records whose decoded value is $\beta$, and take the trace.
--
--   The definition proceeds by cases on $\kappa$.
--
--   - **Preparation.** There is one trailing index $0$. Let $\Phi$ be the identity if $0\in\mathrm{trunc}$ and $\mathcal E^{\mathrm{trail}_0}$ otherwise. The condition is
--   $$\mathrm{dec}\big(\Phi(\sigma^{\mathrm{gad}})\big)=|0\rangle\langle0|.$$
--   - **Measurement.** There is one leading index $0$ and no trailing index, so $\mathrm{trunc}$ is necessarily empty and is unused. The condition is that for both bits $\beta$ and every $2^n\times2^n$ matrix $\rho$,
--   $$M^{\mathrm{gad}}_\beta\big(\mathcal E^{\mathrm{lead}_0}(\rho)\big)=\big[\mathrm{dec}(\mathcal E^{\mathrm{lead}_0}(\rho))\big]_{\beta\beta}.$$
--   - **Hadamard, $T$, CNOT, wait.** With arity $k$ ($2$ for CNOT, $1$ otherwise), the condition is the following equality on all matrices indexed by $k$-tuples of $n$-bit strings:
--   $$\Big(\bigotimes_i\mathrm{dec}\Big)\circ\mathcal T\circ\mathcal G^{\mathrm{gad}}_\kappa\circ\mathcal L=(\rho\mapsto U_\kappa\rho U_\kappa^\dagger)\circ\Big(\bigotimes_i\mathrm{dec}\Big)\circ\mathcal L.$$
--     The objects in this equality are:
--     - $\mathcal L=\bigotimes_i\mathcal E^{\mathrm{lead}_i}$;
--     - $\mathcal T=\bigotimes_i\Phi_i$, where $\Phi_i$ is the identity for $i\in\mathrm{trunc}$ and $\mathcal E^{\mathrm{trail}_i}$ otherwise;
--     - $\mathcal G^{\mathrm{gad}}_\kappa$ is the gadget operation (tensor with zero ancillas, run $G_\kappa$ with faults $\mathrm{gad}$, sum over records, and trace out the ancillas);
--     - $U_\kappa\in\{H,\ T=\operatorname{diag}(1,e^{i\pi/4}),\ \mathrm{CNOT},\ I\}$;
--     - $\bigotimes$ of maps is defined on matrix units and extended linearly.
--
--   ### QAlgorithms.pairedSuperop
--
--   The inputs are:
--
--   - natural numbers $k$ and $\sigma$;
--   - a complex $2^k\times 2^k$ matrix $U$, indexed by $k$-bit strings;
--   - an arbitrary map $V$ from matrices indexed by $\{0,\dots,\sigma-1\}^k$ to matrices of the same size, not assumed linear or a channel.
--
--   The result is a map on matrices $X$ indexed by $k$-tuples of pairs $(b_i,s_i)\in\{0,1\}\times\{0,\dots,\sigma-1\}$. It is computed in four steps.
--
--   1. **Regroup.** View $X$ as indexed by pairs $(b,s)$ with $b\in\{0,1\}^k$ and $s\in\{0,\dots,\sigma-1\}^k$.
--   2. **Apply $V$ blockwise.** For each pair of bit strings $b,b'$, apply $V$ to the block $\big(X_{(b,s),(b',s')}\big)_{s,s'}$ and place the result back in that block:
--   $$Y_{(b,s),(b',s')}=\big[V\big((X_{(b,\cdot),(b',\cdot)})\big)\big]_{s,s'}.$$
--   3. **Conjugate.** Form $Z=(U\otimes I)\,Y\,(U\otimes I)^\dagger$, with $U$ acting on the bit strings.
--   4. **Ungroup.** Re-index $Z$ back to $k$-tuples of pairs.
--
--   When $V$ is linear, this is $(U\cdot U^\dagger)\otimes V$ up to the regrouping of indices. When $\sigma=0$, the index sets are empty if $k\ge1$.
--
--   ### QAlgorithms.FTProtocol.GateExRecCorrectStar
--
--   **Setting.** Fix a fault-tolerance protocol $P$. It has $n$ data and $A$ ancilla qubits per block, gadget circuits $G_\kappa$, and an error-correction circuit $G_{\mathrm{EC}}$.
--
--   **Inputs.**
--
--   - A natural number $\sigma$.
--   - A complex $(2\sigma)\times2^n$ matrix $W$, with rows indexed by $\{0,1\}\times\{0,\dots,\sigma-1\}$ and columns by $n$-bit strings. No isometry or unitarity is assumed.
--   - A location kind $\kappa$ of arity $k$: $2$ for CNOT, $1$ otherwise.
--   - Fault arrangements $\mathrm{lead}_i$ and $\mathrm{trail}_i$ for $i<k$, a fault arrangement $\mathrm{gad}$, and a subset $\mathrm{trunc}\subseteq\{0,\dots,k-1\}$.
--
--   **Operations involved.**
--
--   - $\mathcal L=\bigotimes_i\mathcal E^{\mathrm{lead}_i}$.
--   - $\mathcal T=\bigotimes_i\Phi_i$, where $\Phi_i$ is the identity for $i\in\mathrm{trunc}$ and $\mathcal E^{\mathrm{trail}_i}$ otherwise.
--   - $\mathcal E^f$ is the EC operation: tensor with zero ancillas, run $G_{\mathrm{EC}}$ with Pauli faults $f$, sum over all outcome records, and trace out the ancillas.
--   - $\mathcal G^{\mathrm{gad}}_\kappa$ is the gadget operation, defined analogously with $G_\kappa$ on $k$ blocks.
--   - $\mathcal W=\bigotimes_i(\rho\mapsto W\rho W^\dagger)$, mapping matrices on $k$ blocks of $n$ qubits to matrices indexed by $k$-tuples of pairs in $\{0,1\}\times\{0,\dots,\sigma-1\}$.
--   - All tensor products of maps are defined on matrix units and extended linearly.
--   - $U_\kappa$ is $H$, $T=\operatorname{diag}(1,e^{i\pi/4})$, CNOT (first qubit as control), or the identity, according to $\kappa$.
--
--   **The proposition.** There exists a map $V$ on matrices indexed by $\{0,\dots,\sigma-1\}^k$ satisfying two conditions.
--
--   1. $V$ is a channel: for some $m$ and matrices $E_0,\dots,E_{m-1}$ with $\sum_jE_j^\dagger E_j=I$, we have $V(\rho)=\sum_jE_j\rho E_j^\dagger$ for all $\rho$.
--   2. The following equality holds on all matrices $X$ indexed by $k$-tuples of $n$-bit strings:
--   $$\mathcal W\circ\mathcal T\circ\mathcal G^{\mathrm{gad}}_\kappa\circ\mathcal L=\mathrm{Pair}(U_\kappa,V)\circ\mathcal W\circ\mathcal L.$$
--
--   Here $\mathrm{Pair}(U,V)$ acts on a matrix $Y$ indexed by $k$-tuples of pairs as follows:
--
--   1. regroup the indices into (bit strings) × (strings over $\{0,\dots,\sigma-1\}$);
--   2. apply $V$ to each block indexed by a pair of bit strings;
--   3. conjugate by $U\otimes I$;
--   4. ungroup.
--
--   ### QAlgorithms.ExRecCorrectStar
--
--   This is a predicate defined by cases on a location kind $\kappa$. Its inputs are:
--
--   - a fault-tolerance protocol $P$, which supplies:
--     - a code block of $n$ data qubits and $A$ ancilla qubits;
--     - a "decoder" superoperator;
--     - for each kind $\kappa \in \{\mathrm{prep},\mathrm{had},\mathrm{tgate},\mathrm{cnot},\mathrm{meas},\mathrm{wait}\}$, a gadget circuit $G_\kappa$ on $a_\kappa(n+A)$ qubits, where the arity $a_\kappa$ is $2$ for cnot and $1$ otherwise;
--     - an error-correction circuit $G_{\mathrm{EC}}$ on $n+A$ qubits;
--     - a classical decoding map $\mathrm{measDecode}$ from bit lists to bits;
--   - a natural number $\sigma$;
--   - an arbitrary complex matrix $W$ with rows indexed by $\{0,1\}\times\{0,\dots,\sigma-1\}$ and columns indexed by $n$-bit strings (no isometry or unitarity condition is imposed);
--   - a fault record $F$ for kind $\kappa$, consisting of:
--     - "leading" Pauli arrangements $F.\mathrm{lead}_i$, for $i$ ranging over $0$ indices if $\kappa=\mathrm{prep}$ and $a_\kappa$ indices otherwise;
--     - one gadget arrangement $F.\mathrm{gad}$;
--     - "trailing" arrangements $F.\mathrm{trail}_j$, for $j$ ranging over $0$ indices if $\kappa=\mathrm{meas}$ and $a_\kappa$ indices otherwise;
--   - a set $\mathrm{trunc}$ of trailing indices.
--
--   A Pauli arrangement assigns to each location id $(s,j)\in\mathbb N^2$ either nothing or a pair of single-qubit Paulis $(P_1,P_2)$.
--
--   **Operators used.** Write $\mathcal C_W(\rho)=W\rho W^\dagger$.
--
--   - $\mathrm{ecOp}(fa)(\rho)$ is computed as follows:
--     1. embed the $n$-qubit operator $\rho$ on the data wires of $G_{\mathrm{EC}}$, with the ancillas set to $|0\cdots0\rangle$;
--     2. run $G_{\mathrm{EC}}$ with Pauli faults $fa$. At each location where $fa$ gives $(P_1,P_2)$, conjugate by $P_1$ on its first wire and $P_2$ on its other wire. This happens after the location's action for preparations and gates, and before the projection for measurements;
--     3. sum the resulting unnormalized operators over all complete measurement-outcome strings;
--     4. trace out the ancillas.
--   - $\mathrm{prepState}(fa)$ is the analogous output of $G_{\mathrm{prep}}$ run from the all-zero state.
--   - $\mathrm{gateOp}(\kappa,fa)$ is the analogous superoperator of $G_\kappa$ on $a_\kappa$ data blocks.
--   - $\mathrm{measFunctional}(fa,\beta)(\rho)\in\mathbb C$ is the trace of the summed output of $G_{\mathrm{meas}}$ on input $\rho$ (ancillas zero). The sum is restricted to outcome strings $r$ with $\mathrm{measDecode}(r)=\beta$.
--
--   **Case $\kappa=\mathrm{prep}$.** Let $E$ be the identity map if trailing index $0$ belongs to $\mathrm{trunc}$, and $\mathrm{ecOp}(F.\mathrm{trail}_0)$ otherwise. The condition is that there is a density matrix $\tau$ on $\{0,\dots,\sigma-1\}$ (positive semidefinite, trace $1$) with
--   $$
--   W\,E\big(\mathrm{prepState}(F.\mathrm{gad})\big)\,W^\dagger=|0\rangle\langle 0|\otimes\tau .
--   $$
--   For $\sigma=0$ no such $\tau$ exists, so in that case this branch is false.
--
--   **Case $\kappa=\mathrm{meas}$.** Here $\mathrm{trunc}$ is irrelevant. The condition is that for every $\beta\in\{0,1\}$ and every $n$-qubit complex matrix $\rho$ (not only density matrices),
--   $$
--   \mathrm{measFunctional}(F.\mathrm{gad},\beta)\big(\mathrm{ecOp}(F.\mathrm{lead}_0)(\rho)\big)=\sum_{h<\sigma}\big(W\,\mathrm{ecOp}(F.\mathrm{lead}_0)(\rho)\,W^\dagger\big)_{(\beta,h),(\beta,h)} .
--   $$
--   The right-hand side is the $(\beta,\beta)$ entry of the partial trace over the second factor.
--
--   **Cases $\kappa\in\{\mathrm{had},\mathrm{tgate},\mathrm{cnot},\mathrm{wait}\}$.** Let $k=a_\kappa$. Define:
--
--   - $\mathcal L=\bigotimes_{i<k}\mathrm{ecOp}(F.\mathrm{lead}_i)$;
--   - $\mathcal T=\bigotimes_{j<k}\mathcal T_j$, where $\mathcal T_j$ is the identity if $j\in\mathrm{trunc}$ and $\mathrm{ecOp}(F.\mathrm{trail}_j)$ otherwise.
--
--   Here $\otimes$ of superoperators on blocks is defined linearly via matrix units. The condition is that there exists a quantum channel $V$ on $(\{0,\dots,\sigma-1\})^k$ such that, as maps on all matrices,
--   $$
--   \mathcal C_W^{\otimes k}\circ\mathcal T\circ\mathrm{gateOp}(\kappa,F.\mathrm{gad})\circ\mathcal L=\big(\mathcal C_{U_\kappa}\otimes V\big)\circ\mathcal C_W^{\otimes k}\circ\mathcal L .
--   $$
--   A quantum channel here means a map given by some finite Kraus family $\{E_j\}$ with $\sum_j E_j^\dagger E_j=I$. In the right-hand side:
--
--   - $\mathcal C_W^{\otimes k}$ outputs on $(\{0,1\}\times\{0..\sigma-1\})^k$, which is regrouped as $\{0,1\}^k\times\{0..\sigma-1\}^k$;
--   - $\mathcal C_{U_\kappa}$ conjugates the first factor by the ideal gate $U_\kappa$, which is the Hadamard $H$, $T=\mathrm{diag}(1,e^{i\pi/4})$, CNOT (first wire control), or the identity for wait;
--   - $V$ acts on the second factor.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/FaultTolerance.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_LocCircuit
/-!
# Fault-tolerant protocols: gadgets, ideal and *-decoders, Defs. 1–5, ExRecs and their
correctness (shared definition layer)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages), §§4.2, 5.1–5.2.

Model. A protocol uses one `[[n, 1, 2t + 1]]` code (p.19). Each gadget is a concrete circuit of
locations; a gadget for a location acting on `k` blocks runs on `k · (n + A)` qubits, where
physical qubit (block `i`, position `j`) is wire `finProdFinEquiv (i, j)`, positions `j < n` are
the block's data qubits and `n ≤ j < n + A` its ancillas. The superoperator a gadget implements
under a Pauli fault arrangement (p.20: faults are Pauli errors) is computed from
`LocCircuit.run`: the input on the data qubits, the ancillas in `|0⟩`, the measurement records
summed over, the ancillas traced out. All the diagram equations of Defs. 2–5 and 8 are equalities
of superoperators, i.e. on every input operator ("for all input states, including superpositions
and parts of entangled states", p.38).
-/

namespace QAlgorithms

open scoped Matrix

/-- Gottesman intro p.19 (Def. 1, §4.2), p.20 and p.33 (Def. 6): the data of a fault-tolerant
protocol for one `[[n, 1, 2t + 1]]` code: block length `n`, number `t` of errors corrected,
number `A` of ancillas per block, the code, its encoding isometry, the ideal decoder, a gadget for
every type of location (the wait gadget is the gate gadget for `U = I`, p.20), the error-correction
gadget, and the classical decoding of the measurement gadget's outcomes to the logical outcome. -/
structure FTProtocol where
  n : ℕ
  t : ℕ
  A : ℕ
  code : Submodule ℂ (EuclideanSpace ℂ (Qubits n))
  enc : Matrix (Qubits n) Bool ℂ
  dec : Superop (Qubits n) Bool
  gadget : (κ : LocKind) → LocCircuit (κ.arity * (n + A))
  ec : LocCircuit (n + A)
  measDecode : List Bool → Bool

/-- Gottesman intro p.19 (§4.2: one encoded qubit per block): `enc` encodes one qubit into the
code `C`: it is an isometry (`enc† enc = I`) with range `C`. -/
def IsEncodingOf {n : ℕ} (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)))
    (enc : Matrix (Qubits n) Bool ℂ) : Prop :=
  encᴴ * enc = 1 ∧ LinearMap.range (Matrix.toEuclideanLin enc) = C

/-- Gottesman intro p.19 (Def. 1: "a map constructed by taking the input state and performing a
decoding operation (including error correction) consisting of a circuit with no faulty
locations"): `D` is an ideal decoder for the encoding `enc` correcting `t` errors: a quantum
operation from one block to one qubit that maps `E (enc ψ)` back to `ψ` for every error `E` in the
span of the Pauli errors of weight `≤ t` and every normalized one-qubit state `ψ` (weighted by
`‖E enc ψ‖²`; by linearity this covers mixed and entangled inputs). Its action outside the
`t`-correctable inputs is unconstrained (any fault-free decoding circuit qualifies). -/
def IsIdealDecoder {n : ℕ} (enc : Matrix (Qubits n) Bool ℂ) (t : ℕ) (D : Superop (Qubits n) Bool) :
    Prop :=
  IsChannel D ∧ ∀ E ∈ pauliSpan n t, ∀ ψ : EuclideanSpace ℂ Bool, ‖ψ‖ = 1 →
    D (pureDensity (act E (Matrix.toEuclideanLin enc ψ))) =
      ((‖act E (Matrix.toEuclideanLin enc ψ)‖ ^ 2 : ℝ) : ℂ) • pureDensity ψ

/-- Gottesman intro p.37 (§5.2: "the *-decoder is a unitary operation" whose extra output holds the
error syndrome) and p.38 (Lemma 2: "the ideal decoder is just the *-decoder with the error syndrome
discarded"): `W` is a *-decoder for the ideal decoder `D` with syndrome register `Fin σ`. -/
def IsStarDecoder {n σ : ℕ} (D : Superop (Qubits n) Bool) (W : Matrix (Bool × Fin σ) (Qubits n) ℂ) :
    Prop :=
  Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ ∀ ρ, traceRight (W * ρ * Wᴴ) = D ρ

/-- The block layout of a gadget on `k` blocks: qubit `finProdFinEquiv (i, j)` is position `j` of
block `i`; positions `< n` are data, the others ancillas. -/
def blockLayout (k n A : ℕ) : Qubits (k * (n + A)) ≃ (Fin k → Qubits n) × (Fin k → Qubits A) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    ((Equiv.curry (Fin k) (Fin (n + A)) Bool).trans
      ((Equiv.arrowCongr (Equiv.refl (Fin k)) (qubitsAppendEquiv n A)).trans
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Qubits n) (fun _ => Qubits A))))

/-- The layout of the error-correction gadget on one block: positions `< n` are data. -/
def singleLayout (n A : ℕ) : Qubits (n + A) ≃ (Fin 1 → Qubits n) × (Fin 1 → Qubits A) :=
  (qubitsAppendEquiv n A).trans
    (Equiv.prodCongr (Equiv.funUnique (Fin 1) (Qubits n)).symm (Equiv.funUnique (Fin 1) (Qubits A)).symm)

/-- The data qubits of a gadget on `k` blocks. -/
def blockDataWires (k n A : ℕ) : Finset (Fin (k * (n + A))) :=
  Finset.univ.image fun p : Fin k × Fin n => finProdFinEquiv (p.1, Fin.castAdd A p.2)

/-- The data qubits of the error-correction gadget. -/
def ecDataWires (n A : ℕ) : Finset (Fin (n + A)) :=
  Finset.univ.image (Fin.castAdd A)

/-- The input operator `X` of the blocks' data placed on the data qubits, the ancillas in
`|0…0⟩⟨0…0|`, trivial environment. -/
def embedVia {N k n A : ℕ} (L : Qubits N ≃ (Fin k → Qubits n) × (Fin k → Qubits A))
    (X : Matrix (Fin k → Qubits n) (Fin k → Qubits n) ℂ) :
    Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ :=
  Matrix.of fun p p' =>
    if (L p.1).2 = (fun _ _ => false) ∧ (L p'.1).2 = (fun _ _ => false) then X (L p.1).1 (L p'.1).1
    else 0

/-- The partial trace over the ancillas and the environment, keeping the blocks' data. -/
def traceVia {N k n A : ℕ} (L : Qubits N ≃ (Fin k → Qubits n) × (Fin k → Qubits A))
    (Y : Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ) :
    Matrix (Fin k → Qubits n) (Fin k → Qubits n) ℂ :=
  Matrix.of fun x x' => ∑ a : Fin k → Qubits A, ∑ e : Fin 1, Y (L.symm (x, a), e) (L.symm (x', a), e)

/-- Gottesman intro p.20: the (unnormalized) state a gadget leaves under the Pauli arrangement
`fa`, started in `ρin`, summed over the measurement records accepted by `B`. -/
noncomputable def gadgetOut {N : ℕ} (G : LocCircuit N) (fa : PauliArrangement)
    (ρin : Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ) (B : List Bool → Bool) :
    Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ :=
  ∑ r : Fin G.measCount → Bool,
    if B (List.ofFn r) then G.run (pauliErr G fa) (fun r' => if r' = [] then ρin else 0) (List.ofFn r)
    else 0

/-- The number of faulty locations of a gadget under a Pauli arrangement (the `s` of its
diagram, p.20). -/
def faultCount {N : ℕ} (G : LocCircuit N) (fa : PauliArrangement) : ℕ :=
  (faultyLocs G fa).card

/-- Gottesman intro p.20 (Def. 4) and p.35 (Def. 8): the location types handled as gates: `H`,
`R_{π/8}`, CNOT and wait (the wait gadget being the gate gadget for `U = I`). -/
def LocKind.IsGateOrWait (κ : LocKind) : Prop :=
  κ = .had ∨ κ = .tgate ∨ κ = .cnot ∨ κ = .wait

namespace FTProtocol

variable (P : FTProtocol)

/-- Gottesman intro pp.20–21: the superoperator on the `k` input blocks implemented by the gadget
for the gate (or wait) location type `κ` under the Pauli arrangement `fa`. -/
noncomputable def gateOp (κ : LocKind) (fa : PauliArrangement) :
    Superop (Fin κ.arity → Qubits P.n) (Fin κ.arity → Qubits P.n) :=
  fun X => traceVia (blockLayout κ.arity P.n P.A)
    (gadgetOut (P.gadget κ) fa (embedVia (blockLayout κ.arity P.n P.A) X) fun _ => true)

/-- Gottesman intro p.21 (Def. 3): the block state output by the preparation gadget under `fa`
(it takes no input: every qubit is prepared inside it). -/
noncomputable def prepState (fa : PauliArrangement) : Matrix (Qubits P.n) (Qubits P.n) ℂ :=
  (traceVia (blockLayout 1 P.n P.A)
    (gadgetOut (P.gadget .prep) fa (Matrix.kronecker (pureDensity (zeroKet _)) 1) fun _ => true)).submatrix
      (fun y _ => y) (fun y _ => y)

/-- Gottesman intro p.20 (Def. 2): the measurement gadget under `fa` as an instrument on one
block: the weight of the decoded logical outcome `β` (`false` = `|0⟩`) on the block operator `ρ`.
Since every qubit of the gadget is measured, nothing else remains; equality of these functionals on
every block operator is equality of the instruments ("the remainder of the computer is left in the
same relative state"). -/
noncomputable def measFunctional (fa : PauliArrangement) (β : Bool) :
    Matrix (Qubits P.n) (Qubits P.n) ℂ → ℂ :=
  fun ρ => (gadgetOut (P.gadget .meas) fa
    (embedVia (blockLayout 1 P.n P.A) (ρ.submatrix (fun x => x 0) (fun x => x 0)))
    fun r => decide (P.measDecode r = β)).trace

/-- Gottesman intro p.21 (Def. 5): the superoperator on one block implemented by the
error-correction gadget under `fa`. -/
noncomputable def ecOp (fa : PauliArrangement) : Superop (Qubits P.n) (Qubits P.n) :=
  fun ρ => (traceVia (singleLayout P.n P.A)
    (gadgetOut P.ec fa (embedVia (singleLayout P.n P.A) (ρ.submatrix (fun x => x 0) (fun x => x 0)))
      fun _ => true)).submatrix (fun y _ => y) (fun y _ => y)

/-- Gottesman intro p.19 (Def. 1): the `r`-filter applied to a block. -/
noncomputable def filterOp (r : ℕ) : Superop (Qubits P.n) (Qubits P.n) :=
  conjSuperop (filterProj P.code r)

/-- Gottesman intro pp.19–22 (Defs. 1–5): the protocol is fault tolerant. The code is an
`[[n, 1, 2t + 1]]` code with encoding `enc` and ideal decoder `dec`; every gadget is a well-formed
circuit whose live qubits at its two ends are the data qubits of its input and output blocks; and,
for every Pauli fault arrangement with `s` faulty locations in the gadget and all filter sizes
(`F_r` the `r`-filter, applied to each block separately):
* Meas (Def. 2): `r + s ≤ t` → the gadget after `F_r` has the outcome weights of ideal decoding
  followed by a standard-basis measurement;
* Prep A, Prep B (Def. 3): `s ≤ t` → the output passes the `s`-filter, and decodes to `|0⟩`;
* Gate A, Gate B (Def. 4), for `H`, `R_{π/8}`, CNOT and wait: `s + Σ_i r_i ≤ t` → after the
  `r_i`-filters on the inputs, the output passes the `(s + Σ r_i)`-filter on each block, and
  decoding each block gives the ideal gate applied to the decoded inputs;
* EC A, EC B (Def. 5): `s ≤ t` → the output passes the `s`-filter, whatever the input;
  `r + s ≤ t` → decoding after the gadget equals decoding before it, after `F_r`. -/
def IsFaultTolerant : Prop :=
  IsQCode P.n 1 (2 * P.t + 1) P.code ∧ IsEncodingOf P.code P.enc ∧ IsIdealDecoder P.enc P.t P.dec ∧
  (P.gadget .prep).IsWellFormed ∅ (blockDataWires 1 P.n P.A) ∧
  (P.gadget .meas).IsWellFormed (blockDataWires 1 P.n P.A) ∅ ∧
  (∀ κ : LocKind, κ.IsGateOrWait →
    (P.gadget κ).IsWellFormed (blockDataWires κ.arity P.n P.A) (blockDataWires κ.arity P.n P.A)) ∧
  P.ec.IsWellFormed (ecDataWires P.n P.A) (ecDataWires P.n P.A) ∧
  -- Meas
  (∀ (fa : PauliArrangement) (r : ℕ), r + faultCount (P.gadget .meas) fa ≤ P.t →
    ∀ (β : Bool) (ρ : Matrix (Qubits P.n) (Qubits P.n) ℂ),
      P.measFunctional fa β (P.filterOp r ρ) = P.dec (P.filterOp r ρ) β β) ∧
  -- Prep A
  (∀ fa : PauliArrangement, faultCount (P.gadget .prep) fa ≤ P.t →
    P.filterOp (faultCount (P.gadget .prep) fa) (P.prepState fa) = P.prepState fa) ∧
  -- Prep B
  (∀ fa : PauliArrangement, faultCount (P.gadget .prep) fa ≤ P.t →
    P.dec (P.prepState fa) = pureDensity (ket false)) ∧
  -- Gate A
  (∀ κ : LocKind, κ.IsGateOrWait → ∀ (fa : PauliArrangement) (r : Fin κ.arity → ℕ),
    faultCount (P.gadget κ) fa + ∑ i, r i ≤ P.t →
      piSuperop (fun _ => P.filterOp (faultCount (P.gadget κ) fa + ∑ i, r i)) ∘ P.gateOp κ fa ∘
          piSuperop (fun i => P.filterOp (r i)) =
        P.gateOp κ fa ∘ piSuperop (fun i => P.filterOp (r i))) ∧
  -- Gate B
  (∀ κ : LocKind, κ.IsGateOrWait → ∀ (fa : PauliArrangement) (r : Fin κ.arity → ℕ),
    faultCount (P.gadget κ) fa + ∑ i, r i ≤ P.t →
      piSuperop (fun _ => P.dec) ∘ P.gateOp κ fa ∘ piSuperop (fun i => P.filterOp (r i)) =
        conjSuperop κ.idealMatrix ∘ piSuperop (fun _ => P.dec) ∘ piSuperop (fun i => P.filterOp (r i))) ∧
  -- EC A
  (∀ fa : PauliArrangement, faultCount P.ec fa ≤ P.t →
    P.filterOp (faultCount P.ec fa) ∘ P.ecOp fa = P.ecOp fa) ∧
  -- EC B
  (∀ (fa : PauliArrangement) (r : ℕ), r + faultCount P.ec fa ≤ P.t →
    P.dec ∘ P.ecOp fa ∘ P.filterOp r = P.dec ∘ P.filterOp r)

end FTProtocol

/-- Gottesman intro p.34 (Def. 7): the number of leading EC steps of an ExRec (one per input
block; none for a preparation). -/
def LocKind.leadCount : LocKind → ℕ
  | .prep => 0
  | κ => κ.arity

/-- Gottesman intro p.34 (Def. 7): the number of trailing EC steps of an ExRec (one per output
block; none for a measurement). -/
def LocKind.trailCount : LocKind → ℕ
  | .meas => 0
  | κ => κ.arity

/-- Gottesman intro p.34 (Def. 7), p.35 (Def. 9) and p.38 (Def. 10): a Pauli fault arrangement of
an ExRec of type `κ`: one for each leading EC, one for the gadget, one for each trailing EC. -/
structure ExRecFaults (κ : LocKind) where
  lead : Fin κ.leadCount → PauliArrangement
  gad : PauliArrangement
  trail : Fin κ.trailCount → PauliArrangement

/-- Gottesman intro p.35 (Def. 9) and p.38 (Def. 10): the number of faults in the ExRec, the
trailing ECs of the blocks in `trunc` being removed (truncation; `trunc = ∅` is the full ExRec). -/
def ExRecFaults.count (P : FTProtocol) {κ : LocKind} (F : ExRecFaults κ)
    (trunc : Finset (Fin κ.trailCount)) : ℕ :=
  ∑ i, faultCount P.ec (F.lead i) + faultCount (P.gadget κ) F.gad +
    ∑ i ∈ Finset.univ.filter (fun i => i ∉ trunc), faultCount P.ec (F.trail i)

namespace FTProtocol

variable (P : FTProtocol)

/-- The leading EC steps of a gate ExRec, one on each input block. -/
noncomputable def leadOp {k : ℕ} (lead : Fin k → PauliArrangement) :
    Superop (Fin k → Qubits P.n) (Fin k → Qubits P.n) :=
  piSuperop fun i => P.ecOp (lead i)

/-- The trailing EC steps of a gate ExRec, one on each output block not in `trunc` (removed
there, Def. 10). -/
noncomputable def trailOp {k : ℕ} (trail : Fin k → PauliArrangement) (trunc : Finset (Fin k)) :
    Superop (Fin k → Qubits P.n) (Fin k → Qubits P.n) :=
  piSuperop fun j => if j ∈ trunc then (fun ρ => ρ) else P.ecOp (trail j)

/-- Gottesman intro p.35 (Def. 8, eq. (72)): a gate or wait ExRec is correct for the ideal
decoder. -/
def GateExRecCorrect (κ : LocKind) (lead trail : Fin κ.arity → PauliArrangement)
    (gad : PauliArrangement) (trunc : Finset (Fin κ.arity)) : Prop :=
  piSuperop (fun _ => P.dec) ∘ P.trailOp trail trunc ∘ P.gateOp κ gad ∘ P.leadOp lead =
    conjSuperop κ.idealMatrix ∘ piSuperop (fun _ => P.dec) ∘ P.leadOp lead

end FTProtocol

/-- Gottesman intro p.35 (Def. 8, eqs. (72)–(74)) and p.38 (Def. 10, truncated ExRecs: "removing
the trailing EC step from each diagram"): the ExRec of type `κ` is correct for the fault
arrangement `F`. Gate and wait (72): decoding after the trailing ECs equals the ideal gate after
decoding after the leading ECs. Preparation (73): decoding after the trailing EC gives `|0⟩`.
Measurement (74): the gadget after the leading EC has the outcome weights of decoding after the
leading EC and measuring. -/
def ExRecCorrect (P : FTProtocol) :
    (κ : LocKind) → ExRecFaults κ → Finset (Fin κ.trailCount) → Prop
  | .prep, F, trunc =>
      P.dec ((if (⟨0, by decide⟩ : Fin LocKind.prep.trailCount) ∈ trunc then (fun ρ => ρ)
        else P.ecOp (F.trail ⟨0, by decide⟩)) (P.prepState F.gad)) = pureDensity (ket false)
  | .meas, F, _ =>
      ∀ β : Bool, P.measFunctional F.gad β ∘ P.ecOp (F.lead ⟨0, by decide⟩) =
        fun ρ => P.dec (P.ecOp (F.lead ⟨0, by decide⟩) ρ) β β
  | .had, F, trunc => P.GateExRecCorrect .had F.lead F.trail F.gad trunc
  | .tgate, F, trunc => P.GateExRecCorrect .tgate F.lead F.trail F.gad trunc
  | .cnot, F, trunc => P.GateExRecCorrect .cnot F.lead F.trail F.gad trunc
  | .wait, F, trunc => P.GateExRecCorrect .wait F.lead F.trail F.gad trunc

/-- Gottesman intro p.38 (eq. (83): "`U` ⊗ some operation `V` on the error syndrome"): the
superoperator `ρ ↦ U ρ U†` on the decoded qubits tensored with `V` on the syndrome registers,
acting on `k` (qubit, syndrome) pairs. -/
noncomputable def pairedSuperop {k σ : ℕ} (U : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (V : Superop (Fin k → Fin σ) (Fin k → Fin σ)) :
    Superop (Fin k → Bool × Fin σ) (Fin k → Bool × Fin σ) :=
  fun X =>
    (conjSuperop (Matrix.kronecker U (1 : Matrix (Fin k → Fin σ) (Fin k → Fin σ) ℂ))
      (idTensorSuperop (R := Fin k → Bool) V
        (X.submatrix (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin σ)).symm
          (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin σ)).symm))).submatrix
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin σ))
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin σ))

namespace FTProtocol

variable (P : FTProtocol)

/-- Gottesman intro p.38 (eq. (83)): a gate or wait ExRec is correct for the *-decoder `W`: for
some quantum operation `V` on the syndrome registers, the *-decoders after the trailing ECs give
the ideal gate on the decoded qubits and `V` on the syndromes, applied after the *-decoders after
the leading ECs. -/
def GateExRecCorrectStar {σ : ℕ} (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ) (κ : LocKind)
    (lead trail : Fin κ.arity → PauliArrangement) (gad : PauliArrangement)
    (trunc : Finset (Fin κ.arity)) : Prop :=
  ∃ V : Superop (Fin κ.arity → Fin σ) (Fin κ.arity → Fin σ), IsChannel V ∧
    piSuperop (fun _ => conjSuperop W) ∘ P.trailOp trail trunc ∘ P.gateOp κ gad ∘ P.leadOp lead =
      pairedSuperop κ.idealMatrix V ∘ piSuperop (fun _ => conjSuperop W) ∘ P.leadOp lead

end FTProtocol

/-- Gottesman intro p.38 (eq. (83) and "the definitions for preparation and measurement ExRecs are
similar; for the preparation ExRec, the error syndrome is brought in as a separate input on the RHS
of the definition, and for the measurement ExRec, the error syndrome is discarded immediately after
being produced"), with Def. 10's truncation: the ExRec is correct for the *-decoder `W`. -/
def ExRecCorrectStar (P : FTProtocol) {σ : ℕ} (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ) :
    (κ : LocKind) → ExRecFaults κ → Finset (Fin κ.trailCount) → Prop
  | .prep, F, trunc =>
      ∃ τ : Matrix (Fin σ) (Fin σ) ℂ, IsDensityMatrix τ ∧
        conjSuperop W ((if (⟨0, by decide⟩ : Fin LocKind.prep.trailCount) ∈ trunc then (fun ρ => ρ)
          else P.ecOp (F.trail ⟨0, by decide⟩)) (P.prepState F.gad)) =
          Matrix.kronecker (pureDensity (ket false)) τ
  | .meas, F, _ =>
      ∀ β : Bool, P.measFunctional F.gad β ∘ P.ecOp (F.lead ⟨0, by decide⟩) =
        fun ρ => traceRight (W * P.ecOp (F.lead ⟨0, by decide⟩) ρ * Wᴴ) β β
  | .had, F, trunc => P.GateExRecCorrectStar W .had F.lead F.trail F.gad trunc
  | .tgate, F, trunc => P.GateExRecCorrectStar W .tgate F.lead F.trail F.gad trunc
  | .cnot, F, trunc => P.GateExRecCorrectStar W .cnot F.lead F.trail F.gad trunc
  | .wait, F, trunc => P.GateExRecCorrectStar W .wait F.lead F.trail F.gad trunc

/-! ### Sanity tests -/

example {k n A : ℕ} (z : Qubits (k * (n + A))) (i : Fin k) (j : Fin n) :
    (blockLayout k n A z).1 i j = z (finProdFinEquiv (i, Fin.castAdd A j)) := rfl

example {k n A : ℕ} (z : Qubits (k * (n + A))) (i : Fin k) (a : Fin A) :
    (blockLayout k n A z).2 i a = z (finProdFinEquiv (i, Fin.natAdd n a)) := rfl

example {n A : ℕ} (z : Qubits (n + A)) (j : Fin n) :
    (singleLayout n A z).1 0 j = z (Fin.castAdd A j) := rfl

example : LocKind.leadCount .prep = 0 ∧ LocKind.trailCount .meas = 0 ∧
    LocKind.leadCount .cnot = 2 := ⟨rfl, rfl, rfl⟩

example {N : ℕ} (G : LocCircuit N) : faultCount G (fun _ => none) = 0 := by
  simp [faultCount, faultyLocs]

example (P : FTProtocol) (κ : LocKind) (F : ExRecFaults κ) (h : ∀ i, F.lead i = fun _ => none)
    (hg : F.gad = fun _ => none) : F.count P Finset.univ = 0 := by
  simp [ExRecFaults.count, h, hg, faultCount, faultyLocs]

end QAlgorithms


