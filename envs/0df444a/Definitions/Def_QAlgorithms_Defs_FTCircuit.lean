-- Prove2me | Definitions.Def_QAlgorithms_Defs_FTCircuit
-- name    : QAlgorithms_Defs_FTCircuit
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T18:02:44.512632+00:00
-- url     : https://prove2.me/theorems/93083033-5395-43e1-a55e-9a40650124d8
-- title:
--   The fault-tolerant circuit C′, its ExRecs, good and bad locations, the circuit C̃, local
-- statement:
--   The fault-tolerant circuit C′, its ExRecs, good and bad locations, the circuit C̃, local
--
--   ### QAlgorithms.FTProtocol.HasUniformDepth
--
--   For a fault-tolerance protocol $P$ with gadget circuits $G_\kappa$, one per location kind $\kappa\in\{\mathrm{prep},\mathrm{had},\mathrm{tgate},\mathrm{cnot},\mathrm{meas},\mathrm{wait}\}$, this is the proposition that every gadget has the same number of time steps as the preparation gadget:
--   $$
--   \forall \kappa:\quad \#\mathrm{steps}(G_\kappa)=\#\mathrm{steps}(G_{\mathrm{prep}}).
--   $$
--   The error-correction circuit of $P$ is not constrained.
--
--   ### QAlgorithms.FTProtocol.gadgetDepth
--
--   For a fault-tolerance protocol $P$, this is the natural number
--   $$
--   \max\big(\#\mathrm{steps}(G_{\mathrm{prep}}),\#\mathrm{steps}(G_{\mathrm{had}}),\#\mathrm{steps}(G_{\mathrm{tgate}}),\#\mathrm{steps}(G_{\mathrm{cnot}}),\#\mathrm{steps}(G_{\mathrm{meas}}),\#\mathrm{steps}(G_{\mathrm{wait}}),0\big).
--   $$
--   This is the maximum number of time steps (step lists, which may be empty) over the six gadget circuits of $P$. The error-correction circuit is not included.
--
--   ### QAlgorithms.FTProtocol.period
--
--   For a fault-tolerance protocol $P$, this is the natural number
--   $$
--   \mathrm{period}(P)=\mathrm{gadgetDepth}(P)+\#\mathrm{steps}(G_{\mathrm{EC}}).
--   $$
--   The first term is the maximum step count over the six gadget circuits (as above). The second term is the number of time steps of $P$'s error-correction circuit.
--
--   ### QAlgorithms.FTInstance
--
--   For a natural number $N$, $\mathrm{FTInstance}(N)$ is a tagged disjoint union with two kinds of elements:
--
--   - $\mathrm{gadget}(\ell)$ for an arbitrary pair $\ell=(s,j)\in\mathbb N\times\mathbb N$;
--   - $\mathrm{ec}(s,q)$ for an arbitrary $s\in\mathbb N$ and $q\in\{0,\dots,N-1\}$.
--
--   Two elements are equal exactly when they have the same tag and equal data, and this equality is decidable. No bound ties $\ell$ or $s$ to any circuit.
--
--   ### QAlgorithms.blockEmb
--
--   The inputs are natural numbers $n,A,k,N$ and an injective map $w:\{0,\dots,k-1\}\to\{0,\dots,N-1\}$. Set $B=n+A$. Then $\mathrm{blockEmb}(n,A,w)$ is the injective map
--   $$
--   \{0,\dots,kB-1\}\to\{0,\dots,NB-1\},\qquad aB+p\ \mapsto\ w(a)\,B+p\qquad(0\le a<k,\ 0\le p<B).
--   $$
--   In words, the index is split into a block number $a=\lfloor x/B\rfloor$ and an offset $p=x\bmod B$. Block $a$ is sent to block $w(a)$ with the same offset. Injectivity follows from that of $w$. If $B=0$ both index sets are empty.
--
--   ### QAlgorithms.ecEmb
--
--   The inputs are natural numbers $n,A,N$ and $q\in\{0,\dots,N-1\}$. Set $B=n+A$. Then $\mathrm{ecEmb}(n,A,q)$ is the injective map
--   $$
--   \{0,\dots,B-1\}\to\{0,\dots,NB-1\},\qquad p\mapsto qB+p,
--   $$
--   which places a single block of $B$ wires as the $q$-th block.
--
--   ### QAlgorithms.gadgetOffset
--
--   The inputs are a fault-tolerance protocol $P$, a located circuit $C$ on $N$ qubits (a list of time steps, each a list of locations of some kind), and $s,j,d\in\mathbb N$. The value is
--   $$
--   \mathrm{gadgetOffset}(P,C,s,j,d)=\sum_{l\in\text{first }j\text{ locations of step }s\text{ of }C}\#\big(\text{locations in step }d\text{ of }G_{\mathrm{kind}(l)}\big).
--   $$
--   The edge cases are:
--
--   - step $s$ of $C$ is taken to be empty if $s\ge\#\mathrm{steps}(C)$, giving value $0$;
--   - if $j$ exceeds the length of step $s$, all of its locations are used;
--   - step $d$ of a gadget is taken to be empty (contributing $0$) if $d$ is beyond the gadget's number of steps.
--
--   ### QAlgorithms.gadgetGlobalId
--
--   The inputs are a fault-tolerance protocol $P$, a located circuit $C$ on $N$ qubits, $s,j\in\mathbb N$, and a local location id $\mathrm{lid}=(d,i)\in\mathbb N^2$. The value is the pair
--   $$
--   \big(s\cdot\mathrm{period}(P)+d,\ \ \mathrm{gadgetOffset}(P,C,s,j,d)+i\big).
--   $$
--   Here $\mathrm{period}(P)$ is the maximum gadget step count plus the step count of $P$'s error-correction circuit. $\mathrm{gadgetOffset}(P,C,s,j,d)$ is the total number of locations in step $d$ of the gadgets of the first $j$ locations of step $s$ of $C$, with out-of-range steps counted as empty. No range checks are made on $s$, $j$, $d$, or $i$.
--
--   ### QAlgorithms.ecBlocks
--
--   For a located circuit $C$ on $N$ qubits and $s\in\mathbb N$, this is the list, in increasing order, of those $q\in\{0,\dots,N-1\}$ that satisfy the following: some location $l$ in step $s$ of $C$ has kind different from measurement and acts on $q$ (that is, $q$ is among the wires of $l$). If $s\ge\#\mathrm{steps}(C)$, the step is treated as empty and the list is empty.
--
--   ### QAlgorithms.ecGlobalId
--
--   The inputs are a fault-tolerance protocol $P$, $s,\mathrm{idx}\in\mathbb N$, and a local id $\mathrm{lid}=(d,i)\in\mathbb N^2$. The value is the pair
--   $$
--   \big(s\cdot\mathrm{period}(P)+\mathrm{gadgetDepth}(P)+d,\ \ \mathrm{idx}\cdot m_d+i\big),
--   $$
--   where $m_d$ is the number of locations in step $d$ of $P$'s error-correction circuit, and $m_d=0$ if $d$ is beyond its number of steps. In that case the second component is just $i$. Here $\mathrm{gadgetDepth}(P)$ is the maximum step count over the six gadgets, and $\mathrm{period}(P)$ is that plus the error-correction step count. No range checks are made.
--
--   ### QAlgorithms.decodedOutcomes
--
--   The inputs are:
--
--   - a fault-tolerance protocol $P$;
--   - a located circuit $C$ on $N$ qubits;
--   - a partial outcome assignment $O:\mathbb N^2\to\{\text{none}\}\cup\{0,1\}$.
--
--   The result is a partial assignment on ids $\mathrm{cid}=(c_1,c_2)\in\mathbb N^2$, defined as follows.
--
--   - **No location or non-measurement.** If $C$ has no location at $\mathrm{cid}$, the value is none. "No location" means $c_1\ge\#\mathrm{steps}(C)$ or $c_2\ge$ the length of step $c_1$. If $C$ has a location there but its kind is not measurement, the value is also none.
--   - **Measurement location.** Let $(\lambda_1,\dots,\lambda_M)$ be the list of positions $(d,i)$ of the measurement locations in the measurement gadget $G_{\mathrm{meas}}$, ordered by step and then by position within the step.
--     - If $O\big(\mathrm{gadgetGlobalId}(P,C,c_1,c_2,\lambda_t)\big)$ is defined for every $t$, the value is the bit
--       $$
--       \mathrm{measDecode}\Big(\big[O(\mathrm{gadgetGlobalId}(P,C,c_1,c_2,\lambda_1)),\dots,O(\mathrm{gadgetGlobalId}(P,C,c_1,c_2,\lambda_M))\big]\Big).
--       $$
--     - Otherwise the value is none.
--
--   If $M=0$, the "all defined" test holds vacuously, and the value is $\mathrm{measDecode}$ of the empty list.
--
--   ### QAlgorithms.gadgetPhaseStep
--
--   **Inputs.**
--
--   - $P$ is a fault-tolerance protocol. It has a code block size $n$, an ancilla count $A$, a gadget circuit $G_\kappa$ for each location kind $\kappa\in\{\mathrm{prep},\mathrm{had},\mathrm{tgate},\mathrm{cnot},\mathrm{meas},\mathrm{wait}\}$, and other fields not used here. $G_\kappa$ acts on $\mathrm{ar}(\kappa)\,(n+A)$ wires, where the arity $\mathrm{ar}$ is $2$ for cnot and $1$ otherwise.
--   - $C$ is a located circuit on $N$ wires, with $N$ implicit. It is a list of time steps $C_0, C_1, \dots$. Each step is a list of locations $l$, and each location has:
--     - a kind $l.\kappa$;
--     - an injective wire map $l.w:\{0,\dots,\mathrm{ar}(l.\kappa)-1\}\to\{0,\dots,N-1\}$;
--     - a condition $l.\mathrm{cond}$, a Boolean function of an outcome record $O:\mathbb N\times\mathbb N\to\{\text{true},\text{false},\text{undefined}\}$.
--   - $s,d\in\mathbb N$.
--
--   **Output.** The result is a list of pairs (location on $N(n+A)$ wires, tag). It is built as follows. Let $C_s$ be step $s$ of $C$; it is the empty list if $s$ is out of range. Write its entries as $(l_j)_j$ with $0$-based positions $j$. For each $j$ in order, and for each location $g$ of step $d$ of $G_{l_j.\kappa}$ in order (empty if $d$ is out of range), the list contains one entry:
--
--   - **kind:** $g.\kappa$.
--   - **wires:** $\beta_{l_j}\circ g.w$. Here $\beta_{l}$ is the block embedding $(i,p)\mapsto l.w(i)\cdot(n+A)+p$. It sends position $p\in\{0,\dots,n+A-1\}$ of the $i$-th sub-block of the gadget to position $p$ of the block attached to wire $l.w(i)$. A gadget wire index $x$ is first decomposed as $x = i(n+A)+p$.
--   - **condition:**
--   $$O\;\mapsto\; g.\mathrm{cond}\big(\mathrm{lid}\mapsto O(\gamma_{s,j}(\mathrm{lid}))\big)\;\wedge\;\begin{cases} l_j.\mathrm{cond}(\delta(O)) & l_j.\kappa\in\{\mathrm{had},\mathrm{tgate},\mathrm{cnot}\}\\ \text{true} & \text{otherwise.}\end{cases}$$
--     - $\gamma_{s,j}(a,b) = \big(s\cdot\pi + a,\ \mathrm{off}_{s,j}(a) + b\big)$.
--     - $\pi = D + |E_c|$ is the period. $D$ is the maximum number of steps over the six gadgets (the value $0$ if all are empty), and $|E_c|$ is the number of steps of $P$'s error-correction circuit.
--     - $\mathrm{off}_{s,j}(a)$ is the sum, over the first $j$ locations $l$ of $C_s$, of the length of step $a$ of $G_{l.\kappa}$ (that length is $0$ if the step is absent).
--     - The decoded record $\delta(O)$ is defined at a position $c$ as follows. If $C$ has a measurement location at $c$, and all values $O(\gamma_{c_1,c_2}(\mathrm{lid}))$ are defined for the measurement ids $\mathrm{lid}$ of $G_{\mathrm{meas}}$ (in their list order), then $\delta(O)(c)$ is $P$'s measurement decoder applied to that list of bits. In every other case $\delta(O)(c)$ is undefined.
--   - **tag:** "gadget at $(s,j)$".
--
--   All these entries are concatenated in the order of $j$, then of $g$.
--
--   ### QAlgorithms.ecPhaseStep
--
--   **Inputs.**
--
--   - $P$ is a fault-tolerance protocol with block size $n$, ancilla count $A$, and error-correction circuit $E_c$ on $n+A$ wires.
--   - $C$ is a located circuit on $N$ wires, with $N$ implicit. Its steps are lists of locations; each location carries a kind, an injective wire map into $\{0,\dots,N-1\}$, and a Boolean condition on outcome records $O$.
--   - $s,e\in\mathbb N$.
--
--   **The list of blocks.** Let $B_s=(q_0,q_1,\dots)$ be the list of wires $q\in\{0,\dots,N-1\}$, in increasing order, such that some location of step $s$ of $C$ has kind other than measurement and has $q$ among its wires. If $s$ is out of range the step is taken to be empty, and then $B_s$ is empty.
--
--   **Output.** For each index $\mathrm{idx}$ and wire $q=q_{\mathrm{idx}}$ of $B_s$, and each location $g$ of step $e$ of $E_c$ (empty if $e$ is out of range), the list contains one entry:
--
--   - **kind:** $g.\kappa$.
--   - **wires:** $p\mapsto q(n+A)+p$ composed with $g.w$, i.e. $g.w$ followed by placement into the block of wire $q$.
--   - **condition:** $O\mapsto g.\mathrm{cond}\big(\mathrm{lid}\mapsto O(\epsilon_{s,\mathrm{idx}}(\mathrm{lid}))\big)$, where
--   $$\epsilon_{s,\mathrm{idx}}(a,b)=\big(s\pi + D + a,\ \mathrm{idx}\cdot L_a + b\big).$$
--     - $D$ is the maximum step count over $P$'s six gadgets.
--     - $\pi = D+|E_c|$.
--     - $L_a$ is the length of step $a$ of $E_c$, or $0$ if that step is absent.
--   - **tag:** "error correction at step $s$ on wire $q$".
--
--   The entries are concatenated in the order of $\mathrm{idx}$, then of $g$.
--
--   ### QAlgorithms.ftTaggedSteps
--
--   **Inputs.** $P$ is a fault-tolerance protocol with block size $n$ and ancilla count $A$. $C$ is a located circuit on $N$ wires ($N$ implicit) with $L$ steps.
--
--   **Notation.**
--
--   - $D$ is the maximum number of steps over $P$'s six gadget circuits (the value $0$ if all are empty).
--   - $|E_c|$ is the number of steps of $P$'s error-correction circuit.
--   - $\mathrm{GP}(s,d)$ denotes the gadget-phase step list: for every location $l_j$ of step $s$ of $C$, the locations of step $d$ of the gadget for $l_j$'s kind, placed onto the blocks of $l_j$'s wires and tagged "gadget $(s,j)$", with conditions as defined for `gadgetPhaseStep`.
--   - $\mathrm{EP}(s,e)$ denotes the EC-phase step list: for each wire touched in step $s$ by a non-measurement location, the locations of step $e$ of the EC circuit, placed on that wire's block and tagged "EC $(s,q)$", as defined for `ecPhaseStep`.
--
--   **Output.** A list of time steps on $N(n+A)$ wires, each step a list of (location, tag) pairs, equal to
--   $$\big[\mathrm{GP}(0,0),\dots,\mathrm{GP}(0,D-1),\ \mathrm{EP}(0,0),\dots,\mathrm{EP}(0,|E_c|-1),\ \ \mathrm{GP}(1,0),\dots\ \ \dots,\mathrm{EP}(L-1,|E_c|-1)\big].$$
--   It has exactly $L\,(D+|E_c|)$ steps.
--
--   - If $L=0$ the result is the empty list.
--   - A gadget phase step $\mathrm{GP}(s,d)$ with $d$ beyond some gadget's length contributes nothing for locations of that kind.
--
--   ### QAlgorithms.ftCircuit
--
--   **Inputs.** $P$ is a fault-tolerance protocol with block size $n$ and ancilla count $A$. $C$ is a located circuit on $N$ wires ($N$ implicit) with $L$ steps.
--
--   **Output.** The located circuit on $N(n+A)$ wires obtained from the tagged step list of `ftTaggedSteps`, keeping each location and discarding its tag.
--
--   **The tagged step list.** For each original step $s=0,\dots,L-1$, in order, it consists of:
--
--   - **$D$ gadget-phase steps.** $D$ is the maximum step count over $P$'s six gadgets. Gadget-phase step $d$ collects, for every location $l_j$ of $C$'s step $s$, the $d$-th step of the gadget for $l_j$'s kind. Its wires are mapped so that sub-block $i$, position $p$ goes to wire $l_j.w(i)(n+A)+p$. Its conditions read outcomes at shifted global ids. For gate kinds they are additionally conjoined with $l_j$'s own condition evaluated on decoded measurement outcomes.
--   - **$|E_c|$ EC-phase steps.** EC-phase step $e$ applies the $e$-th step of $P$'s EC circuit to the block of every wire touched in step $s$ by a non-measurement location.
--
--   ### QAlgorithms.ftOwner
--
--   **Inputs.**
--
--   - $P$ is a fault-tolerance protocol.
--   - $C$ is a located circuit on $N$ wires ($N$ implicit).
--   - $\mathrm{id}=(a,b)\in\mathbb N\times\mathbb N$.
--
--   **Output.** An optional tag.
--
--   - **Defined case.** Consider step $a$ of the tagged step list $\mathrm{ftTaggedSteps}(P,C)$ (the empty list if $a$ is out of range). If its $b$-th entry (0-based) exists, the output is that entry's tag. The tag is either "gadget $(s,j)$", meaning the location belongs to the gadget replacing location $j$ of step $s$ of $C$, or "EC $(s,q)$", meaning it belongs to the error-correction block on wire $q$ after step $s$.
--   - **Undefined case.** If the entry does not exist, the output is "none".
--
--   ### QAlgorithms.ftDecode
--
--   **Inputs.**
--
--   - $P$ is a fault-tolerance protocol.
--   - $C$ is a located circuit on $N$ wires ($N$ implicit).
--   - $r$ is a finite list of bits, the measurement record of the fault-tolerant circuit $\widetilde C=\mathrm{ftCircuit}(P,C)$.
--
--   **The output-reading map $\mathrm{out}(c)$.** The measurement ids of a located circuit are the positions $(s,j)$ of its measurement-kind locations, listed by step and then by position. For a position $c$:
--
--   - If $c$ is the $k$-th measurement id of $\widetilde C$ and $r$ has a $k$-th entry, then $\mathrm{out}(c)$ is that entry ($0$-based).
--   - Otherwise $\mathrm{out}(c)$ is false.
--
--   **The id map $\gamma_{s,j}$.** It is defined by
--   $$\gamma_{s,j}(a,b) = \big(s\pi + a,\ \mathrm{off}_{s,j}(a)+b\big).$$
--
--   - $\pi = D+|E_c|$, where $D$ is the maximum gadget step count and $|E_c|$ is the EC step count.
--   - $\mathrm{off}_{s,j}(a)$ is the sum over the first $j$ locations $l$ of $C$'s step $s$ of the length of step $a$ of the gadget for $l$'s kind.
--
--   **Output.** The list indexed by the measurement ids $c=(c_1,c_2)$ of $C$, in order, whose entry for $c$ is
--   $$\mathrm{measDecode}_P\Big(\big[\mathrm{out}(\gamma_{c_1,c_2}(\mathrm{lid}))\big]_{\mathrm{lid}\in\text{meas-ids of }G_{\mathrm{meas}}}\Big),$$
--   where $\mathrm{measDecode}_P$ is $P$'s map from bit lists to a bit.
--
--   ### QAlgorithms.exRecLocs
--
--   **Inputs.**
--
--   - $P$ is a fault-tolerance protocol.
--   - $C$ is a located circuit on $N$ wires ($N$ implicit).
--   - $\ell=(\ell_1,\ell_2)\in\mathbb N\times\mathbb N$.
--   - $\mathrm{trunc}$ is a finite set of wires.
--
--   **The set of all location ids.** For a located circuit, this is $\{(s,j): s<\#\text{steps},\ j<|\text{step }s|\}$.
--
--   **Output.**
--
--   - **No location at $\ell$.** If $C$ has no location at position $\ell$ (step $\ell_1$, index $\ell_2$), the result is $\emptyset$.
--   - **A location $l$ at $\ell$.** Otherwise, let $l$ be that location, with qubit set $Q_l$ (the image of its wire map). The result is the set of location ids $\mathrm{id}$ of $\widetilde C=\mathrm{ftCircuit}(P,C)$ whose owner tag (as given by `ftOwner`) satisfies one of the following:
--     - the tag is "gadget $\ell'$" with $\ell'=\ell$;
--     - the tag is "EC $(s,q)$" with $q\in Q_l$ and **either** $l$'s kind is not prep and $s+1=\ell_1$ (a leading EC), **or** $l$'s kind is not meas, $s=\ell_1$, and $q\notin\mathrm{trunc}$ (a trailing EC).
--
--   **Remarks.**
--
--   - Ids without an owner are excluded. Every id of $\widetilde C$ in fact has one.
--   - When $\ell_1=0$ no leading EC can qualify.
--   - EC instances exist only for wires touched by a non-measurement location in that step.
--
--   ### QAlgorithms.truncOf
--
--   **Inputs.**
--
--   - $C$ is a located circuit on $N$ wires ($N$ implicit).
--   - $B$ is a finite set of positions in $\mathbb N\times\mathbb N$.
--   - $\ell=(\ell_1,\ell_2)$.
--
--   **Output.** A set of wires.
--
--   - If $C$ has no location at $\ell$, the result is $\emptyset$.
--   - Otherwise, with $l$ the location at $\ell$ and $Q_l$ its set of wires, the result is
--   $$\{\,q\in Q_l \;:\; \exists\,\ell'\in B,\ \ell'_1=\ell_1+1,\ C \text{ has a location } l' \text{ at } \ell' \text{ with } q\in Q_{l'}\,\}.$$
--     In words, these are the wires of $l$ that are also used by some location of $B$ lying in the immediately following step.
--
--   ### QAlgorithms.badAbove
--
--   **Inputs.**
--
--   - $P$ is a fault-tolerance protocol with fault parameter $t$.
--   - $C$ is a located circuit on $N$ wires ($N$ implicit) with $L$ steps.
--   - $S$ is a finite set of positions, interpreted as fault positions in $\mathrm{ftCircuit}(P,C)$.
--   - $k\in\mathbb N$.
--
--   **Definition (recursion on $k$).**
--
--   - **Base case:** $\mathrm{bad}_0=\emptyset$.
--   - **Step:** let $\sigma = L-(k+1)$, computed with truncated subtraction, so $\sigma=0$ whenever $k+1\ge L$. Then
--   $$\mathrm{bad}_{k+1}=\mathrm{bad}_k\ \cup\ \Big\{(\sigma,j): j<|C_\sigma|,\ \ t < \big|\,S\cap \mathrm{ExRec}\big((\sigma,j),\ \mathrm{trunc}_k(\sigma,j)\big)\big|\Big\}.$$
--     - $|C_\sigma|$ is the length of step $\sigma$; it is $0$ if the step is absent, and then nothing is added.
--     - $\mathrm{trunc}_k(\ell)$ is the set of wires of the location at $\ell$ that are also wires of some location in $\mathrm{bad}_k$ in step $\ell_1+1$, or $\emptyset$ if there is no location at $\ell$.
--     - $\mathrm{ExRec}(\ell,\mathrm{trunc})$ is the set of ids of $\mathrm{ftCircuit}(P,C)$ belonging to: the gadget replacing $\ell$; the EC blocks of step $\ell_1-1$ on $\ell$'s wires (only if $\ell$ is not a prep); and the EC blocks of step $\ell_1$ on $\ell$'s wires outside $\mathrm{trunc}$ (only if $\ell$ is not a meas).
--
--   **Effect.** Steps are processed from the last ($L-1$) downward. A location is declared bad when strictly more than $t$ faults of $S$ fall in its truncated extended rectangle.
--
--   **Edge case.** For $k\ge L$, step $0$ is re-examined at each further iteration.
--
--   ### QAlgorithms.badAssignment
--
--   **Inputs.**
--
--   - $P$ is a fault-tolerance protocol with fault parameter $t$.
--   - $C$ is a located circuit on $N$ wires ($N$ implicit) with $L$ steps.
--   - $S$ is a finite set of positions in $\mathrm{ftCircuit}(P,C)$.
--
--   **Output.** $\mathrm{bad}_L$, the result of `badAbove` after exactly $L$ iterations. The recursion examines the steps $L-1, L-2, \dots, 0$ of $C$, each once, in that order. It has two ingredients:
--
--   - **Bad locations.** A location $\ell=(\sigma,j)$ is added when $|S\cap \mathrm{ExRec}(\ell,\mathrm{trunc}(\ell))|>t$.
--   - **Truncation.** $\mathrm{trunc}(\ell)$ is the set of $\ell$'s wires shared with locations already declared bad in step $\sigma+1$.
--
--   $\mathrm{ExRec}(\ell,\mathrm{trunc})$ consists of the ids of $\mathrm{ftCircuit}(P,C)$ belonging to:
--
--   - the gadget for $\ell$;
--   - the preceding-step EC blocks on $\ell$'s wires, unless $\ell$ is a prep;
--   - the same-step EC blocks on $\ell$'s wires not in $\mathrm{trunc}$, unless $\ell$ is a meas.
--
--   If $L=0$ the result is $\emptyset$.
--
--   ### QAlgorithms.liftReg
--
--   **Inputs.**
--
--   - $\alpha$ is a type, $k\in\mathbb N$, and $N$ is implicit.
--   - $w:\{0,\dots,k-1\}\hookrightarrow\{0,\dots,N-1\}$ is injective.
--   - $\Psi$ is an arbitrary map from complex matrices indexed by $\alpha^{k}$ (functions $\{0,\dots,k-1\}\to\alpha$) to such matrices.
--
--   **The overwrite operation.** For $y\in\alpha^N$ and $z\in\alpha^k$, $\mathrm{ow}_w(y,z)\in\alpha^N$ agrees with $y$ off the range of $w$. At a position $w(i)$ it takes the value $z_i$; the choice of $i$ is unique by injectivity.
--
--   **Output.** The map sending a matrix $X$ indexed by $\alpha^N$ to the matrix with entries
--   $$\big(\mathrm{liftReg}_w\Psi\,(X)\big)_{y,y'} \;=\; \Psi\big(Z^{y,y'}\big)_{\,y\circ w,\ y'\circ w},\qquad Z^{y,y'}_{z,z'} = X_{\mathrm{ow}_w(y,z),\ \mathrm{ow}_w(y',z')}.$$
--   Here $y\circ w\in\alpha^k$ is the restriction of $y$ to the wires $w(0),\dots,w(k-1)$.
--
--   This is what the definition reduces to when one unfolds it. The definition attaches a trivial one-point environment to $X$, applies the general wire-lifting construction (with $\Psi$ adapted to that trivial environment), and removes the environment again.
--
--   No property of $\Psi$, such as linearity or complete positivity, is assumed.
--
--   ### QAlgorithms.pairLift
--
--   **Inputs.**
--
--   - $\sigma,k\in\mathbb N$, and $N$ is implicit.
--   - $w:\{0,\dots,k-1\}\hookrightarrow\{0,\dots,N-1\}$ is injective.
--   - $\Psi$ is an arbitrary map on complex matrices indexed by $(\{0,1\}\times\{0,\dots,\sigma-1\})^{k}$, i.e. $k$ (qubit, environment-symbol) pairs.
--
--   **The regrouping.** Let $e$ be the regrouping bijection
--   $$e:(\{0,1\}\times\{0..\sigma-1\})^N\to\{0,1\}^N\times\{0..\sigma-1\}^N,\qquad f\mapsto\big((f_i)_1)_i,\ ((f_i)_2)_i\big).$$
--   Its inverse zips a qubit string $b$ and an environment string $c$ into $(b_i,c_i)_i$.
--
--   **Output.** The map on matrices $X$ indexed by $\{0,1\}^N\times\{0,\dots,\sigma-1\}^N$ (the $N$ qubits together with one environment symbol per wire) given by
--   $$\mathrm{pairLift}_w\Psi(X)_{(b,c),(b',c')} \;=\; \mathrm{liftReg}_w\Psi\big(X\circ e\big)_{\,e^{-1}(b,c),\ e^{-1}(b',c')}.$$
--
--   - $(X\circ e)_{f,f'} = X_{e(f),e(f')}$.
--   - $\mathrm{liftReg}_w\Psi(Y)_{y,y'} = \Psi(Z)_{y\circ w,\,y'\circ w}$, with $Z_{z,z'} = Y_{\mathrm{ow}_w(y,z),\,\mathrm{ow}_w(y',z')}$.
--   - $\mathrm{ow}_w(y,z)$ replaces the entries of $y$ at positions $w(i)$ by $z_i$.
--
--   So $\Psi$ acts jointly on qubits $w(0),\dots,w(k-1)$ and on the environment symbols attached to those same wires. No property of $\Psi$ is assumed.
--
--   ### QAlgorithms.IsTildeErrors
--
--   **Setting.** This is a predicate on four pieces of data:
--
--   - $C$, a circuit of "locations" on $N$ wires;
--   - a finite set $B$ of location labels;
--   - a natural number $\sigma$;
--   - an error assignment $\mathrm{err}$.
--
--   The circuit $C$ is a list of time steps. Each step is a list of locations. A location has:
--
--   - a kind: preparation, Hadamard, $T$, CNOT, measurement, or wait;
--   - an ordered tuple of distinct wires of length $k$, where $k = 2$ for CNOT and $k = 1$ otherwise;
--   - a classical condition.
--
--   A label $\ell = (s, j) \in \mathbb N \times \mathbb N$ refers to the $j$-th location (0-based) of step $s$. Write $C(\ell)$ for that location; it is "absent" if $s$ or $j$ is out of range.
--
--   The error assignment $\mathrm{err}$ assigns to each label either "no error" or a linear map on matrices (a superoperator) over the index set $\{0,1\}^N \times \{0,\dots,\sigma-1\}^N$. So every wire carries one qubit plus one $\sigma$-level environment symbol.
--
--   A superoperator $\Phi$ is a **channel** if there exist a finite $m$ and matrices $E_1,\dots,E_m$ with
--   $$\sum_j E_j^\dagger E_j = I \quad\text{and}\quad \Phi(\rho) = \sum_j E_j \rho E_j^\dagger \ \text{ for all } \rho.$$
--
--   **The predicate.** $\mathrm{IsTildeErrors}(C, B, \sigma, \mathrm{err})$ holds iff for every label $\ell$ both of the following hold:
--
--   1. If $C(\ell)$ is absent, then $\mathrm{err}(\ell)$ is "no error".
--   2. If $C(\ell) = l$ is a location with $k$ wires $w_0,\dots,w_{k-1}$, then there is a channel $\Psi$ on the paired index set $(\{0,1\} \times \{0,\dots,\sigma-1\})^k$ with two properties:
--      - **(a)** If $\ell \notin B$, then there is a channel $V$ on $\{0,\dots,\sigma-1\}^k$ such that $\Psi = \mathrm{id} \otimes V$. Here the space is regrouped as $\{0,1\}^k \times \{0,\dots,\sigma-1\}^k$, and $V$ acts on the environment symbols only. Formally this is the paired map with unitary $U = I$, i.e. conjugation by $I \otimes I$ after applying $\mathrm{id}\otimes V$.
--      - **(b)** $\mathrm{err}(\ell)$ is the lift of $\Psi$ to all $N$ wires along $w$.
--
--   **The lift in (b).** The space is regrouped as $(\{0,1\}\times\{0,\dots,\sigma-1\})^N$. The $(p,q)$ entry of the lifted map applied to $X$ is obtained in three steps:
--
--   - take the $k$-site submatrix of $X$ in which the sites outside $\{w_0,\dots,w_{k-1}\}$ are frozen to $p$ (rows) and $q$ (columns), while the sites $w_i$ vary;
--   - apply $\Psi$ to this submatrix;
--   - read off the entry at the restrictions $p\circ w$ and $q \circ w$.
--
--   In other words, $\Psi$ acts on the qubits and environment symbols of the location's own wires, tensored with the identity on all other wires.
--
--   **Edge cases.**
--
--   - For labels in $B$, $\Psi$ is an arbitrary channel on those $k$ paired sites.
--   - No condition is placed on labels in $B$ that are absent from $C$, beyond clause 1.
--   - If $\sigma = 0$ and $N \ge 1$, all the index sets involved are empty and the conditions on $\Psi$ and $V$ hold trivially.
--
--   ### QAlgorithms.LocalStochasticModel
--
--   A local stochastic model on $N$ qubits is a bundle of four pieces of data, with **no constraints imposed**:
--
--   - a natural number $e$, the environment dimension;
--   - a complex $e\times e$ matrix $\sigma_0$, the initial environment state;
--   - a real-valued function $\mathrm{prob}$ on finite sets $S \subseteq \mathbb N\times\mathbb N$ of location labels;
--   - for each finite set $S$ and each label $\ell$, a superoperator $\mathrm{err}_S(\ell)$ on matrices indexed by $\{0,1\}^N \times \{0,\dots,e-1\}$.
--
--   Nothing requires the following properties:
--
--   - that $\sigma_0$ is a density matrix;
--   - that $\mathrm{prob}$ is nonnegative or sums to $1$;
--   - that the $\mathrm{err}_S(\ell)$ are channels or local.
--
--   The case $e = 0$ is allowed.
--
--   ### QAlgorithms.noisyOutDist
--
--   **Inputs.**
--
--   - A location circuit $C$ on $N$ wires.
--   - A local stochastic model $M = (e, \sigma_0, \mathrm{prob}, \mathrm{err})$.
--
--   **Notation.**
--
--   - $\mathrm{locs}(C)$ is the finite set of valid labels $(s,j)$, with $s$ below the number of steps and $j$ below the length of step $s$.
--   - $m$ is the number of measurement locations of $C$.
--
--   **The definition.** $\mathrm{noisyOutDist}(C,M)$ is the real function on bit strings $r \in \{0,1\}^m$ given by
--   $$\mathrm{noisyOutDist}(C,M)(r) = \sum_{S \subseteq \mathrm{locs}(C)} \mathrm{prob}(S)\cdot \mathrm{out}_C(\mathrm{err}^S, \sigma_0)(r).$$
--   Here $\mathrm{err}^S(\ell) = \mathrm{err}_S(\ell)$ if $\ell \in S$, and "no error" otherwise.
--
--   **The output function.** $\mathrm{out}_C(\mathrm{err}',\sigma_0)(r)$ is the real part of the trace of the matrix that the noisy run of $C$ produces at the outcome record $r$.
--
--   The run starts from the classical–quantum state that assigns:
--
--   - $|0^N\rangle\langle 0^N| \otimes \sigma_0$ to the empty record;
--   - the zero matrix to every other record.
--
--   It then processes the steps in order, and the locations within each step in order. At location $(s,j)$ acting on first wire $q$, with error map $\mathcal E$ (the identity if there is no error), the update is as follows.
--
--   - **Preparation:** replace $\rho(r)$ by $\mathcal E\big(\sum_b K_b \rho(r) K_b^\dagger\big)$, where $K_b = |0\rangle\langle b|$ on qubit $q$.
--   - **Measurement:**
--     - if $r$ is non-empty with last bit $b$, the new $\rho(r)$ is $\Pi_b\, \mathcal E(\rho(r'))\, \Pi_b$, where $r'$ is $r$ with its last bit dropped and $\Pi_b = |b\rangle\langle b|$ on $q$;
--     - the new $\rho$ of the empty record is $0$.
--   - **Wait:** $\rho(r)$ becomes $\mathcal E(\rho(r))$.
--   - **Gate** (Hadamard, $T$, CNOT): $\rho(r)$ becomes $\mathcal E(U\rho(r)U^\dagger)$ if the location's condition holds, and $\mathcal E(\rho(r))$ otherwise. Here $U$ is the ideal gate on the location's wires. The condition reads the outcome bits recorded in $r$ for measurement locations in strictly earlier steps; all other outcomes are "unknown".
--
--   No normalisation is applied, and none of the properties of $M$ listed above are assumed.
--
--   ### QAlgorithms.IsLocalStochastic
--
--   **Inputs.**
--
--   - A location circuit $C$ on $N$ wires.
--   - A local stochastic model $M = (e, \sigma_0, \mathrm{prob}, \mathrm{err})$.
--   - A real function $\mathrm{bound}$ on labels.
--
--   **The predicate.** $\mathrm{IsLocalStochastic}(C, M, \mathrm{bound})$ is the conjunction of six conditions:
--
--   1. $\sigma_0$ is a density matrix: positive semidefinite with trace $1$.
--   2. $\mathrm{prob}(S) \ge 0$ for every finite set $S$ of labels.
--   3. $\mathrm{prob}(S) = 0$ whenever $S \not\subseteq \mathrm{locs}(C)$.
--   4. $\displaystyle\sum_{S\subseteq \mathrm{locs}(C)} \mathrm{prob}(S) = 1$.
--   5. **Locality.** Take any $S$, any $\ell \in S$, and suppose $C(\ell)$ is a location with wires $w_0,\dots,w_{k-1}$. Then there is a channel $\Psi$ on $\{0,1\}^k \times \{0,\dots,e-1\}$ such that $\mathrm{err}_S(\ell)$ is the lift of $\Psi$ along $w$.
--      - The $(p,q)$ entry of the lift applied to $X$ is obtained by applying $\Psi$ to the submatrix of $X$ in which the qubits outside the $w_i$ are frozen to those of $p$ (rows) and $q$ (columns).
--      - In that submatrix, the location's $k$ qubits and the **entire** shared environment vary.
--      - The entry is then read at $(p|_w, p_{\mathrm{env}})$ and $(q|_w, q_{\mathrm{env}})$.
--      - No condition is imposed for labels in $S$ that are not locations of $C$.
--   6. **Tail bound.** For every $R \subseteq \mathrm{locs}(C)$,
--   $$\sum_{\substack{S \subseteq \mathrm{locs}(C)\\ R \subseteq S}} \mathrm{prob}(S) \;\le\; \prod_{i\in R} \mathrm{bound}(i).$$
--
--   **Remarks.**
--
--   - For $R=\varnothing$, condition 6 reads $1 \le 1$.
--   - $\mathrm{bound}$ is unconstrained. If $\mathrm{bound}(i) < 0$ for some location $i$ of $C$, then condition 6 with $R=\{i\}$ cannot hold, because by condition 2 its left side is nonnegative. In that case the predicate is unsatisfiable.
--
--   ### QAlgorithms.LocCircuit.castN
--
--   Given a proof that $N = N'$ and a location circuit $C$ on $N$ wires, $\mathrm{castN}$ returns the same circuit regarded as a circuit on $N'$ wires. It has the same steps, locations, kinds, wires and conditions, transported along the equality.
--
--   ### QAlgorithms.concatCircuit
--
--   **Inputs.**
--
--   - A fault-tolerance protocol $P$ with code-block size $n$ and ancilla count $A$, so each block has $n+A$ wires.
--   - A level $L\in\mathbb N$.
--   - A location circuit $C$ on $N$ wires.
--
--   **The recursion.** $\mathrm{concatCircuit}(P,L,C)$ is a location circuit on $N(n+A)^L$ wires, defined by:
--
--   - **Level 0:** $C$ itself, recast to $N(n+A)^0 = N$ wires.
--   - **Level $L+1$:** $\mathrm{ft}_P$ applied to the level-$L$ circuit $C_L$, recast from $N(n+A)^L\cdot(n+A)$ to $N(n+A)^{L+1}$ wires.
--
--   **The compilation $\mathrm{ft}_P$.** For a circuit $C'$ on $N'$ wires:
--
--   - Logical wire $u$ becomes the block of physical wires $u(n+A)+i$, for $0 \le i < n+A$.
--   - Let $D$ be the maximum step count of $P$'s six gadgets, and let $E$ be the step count of $P$'s error-correction (EC) circuit.
--   - Each step $s$ of $C'$ is replaced by $D$ gadget steps followed by $E$ EC steps.
--
--   *Gadget step $d$* contains, for each location $l$ of step $s$ (in order), the $d$-th step of the gadget for $l$'s kind.
--
--   - If that gadget has fewer than $d+1$ steps, it contributes nothing.
--   - Its wires are mapped blockwise through $l$'s wires.
--   - Each gadget location's condition is evaluated on outcomes relabelled to global labels. The relabelling is $(s\cdot(D+E)+s',\ \text{offset}+j')$, where the offset is the total length of step $s'$ of the gadgets of the earlier locations in step $s$.
--   - If $l$ is a gate (Hadamard, $T$, CNOT), the condition is additionally conjoined with $l$'s own condition. That condition is evaluated on *decoded* outcomes: a measurement location of $C'$ gets the value $\mathrm{measDecode}$ of its measurement gadget's outcome list if all of those outcomes are known, and is unknown otherwise.
--
--   *EC step $e$* contains, for each block $q$ touched by some non-measurement location of step $s$ (in increasing order, indexed by its position $\mathrm{idx}$), the $e$-th step of the EC circuit on block $q$. Conditions are relabelled to $(s(D+E)+D+e',\ \mathrm{idx}\cdot(\text{length of EC step } e')+j')$.
--
--   ### QAlgorithms.concatDecode
--
--   **Inputs.** A protocol $P$, a level $L$, and a location circuit $C$.
--
--   **The recursion.** $\mathrm{concatDecode}(P,L,C)$ is a map from bit lists to bit lists, defined by:
--
--   - **Level 0:** the identity.
--   - **Level $L+1$:** $r \mapsto \mathrm{concatDecode}(P,L,C)\big(\mathrm{ftDecode}_P(C_L, r)\big)$, where $C_L = \mathrm{concatCircuit}(P,L,C)$.
--
--   So the outcomes of the top-level circuit are first decoded into level-$L$ outcomes, then recursively down to level $0$.
--
--   **The decoding step.** $\mathrm{ftDecode}_P(C', r)$ lists one bit for each measurement location $c$ of $C'$, in $C'$'s order of measurement locations. That bit is $\mathrm{measDecode}$ applied to the list of outcomes, read from $r$, of the measurement-gadget's measurements at their global labels in $\mathrm{ft}_P(C')$.
--
--   Here $r$ is matched positionally against the ordered list of measurement locations of $\mathrm{ft}_P(C')$. Any outcome not found, for example because $r$ is too short, is read as $0$ (false). Bits of $r$ beyond that list are ignored.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/FTCircuit.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_FaultTolerance
/-!
# The fault-tolerant circuit C′, its ExRecs, good and bad locations, the circuit C̃, local
stochastic error models, concatenation (shared definition layer)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages), §§5.1–5.2, Defs. 6, 7,
10, 12, Thms 8–10.

Layout of `C′ = ftCircuit P C` (Def. 6). Qubit `q` of `C` owns the block of physical qubits
`finProdFinEquiv (q, j)`, `j < n + A`. Time step `s` of `C` becomes `period = D + D_ec` time steps
of `C′`: a gadget phase of `D` steps (`D` the gadget depth; every location of step `s` replaced by
its gadget on the blocks of its qubits, in parallel) followed by an EC phase of `D_ec` steps (the
EC gadget on the block of every qubit whose step-`s` location is not a measurement, in parallel:
the EC between consecutive locations). Within a `C′` step the gadget instances appear in the order
of the `C` locations (resp. of the qubits). A classically controlled gate location of `C` (these
arise in `C^{(k)}`, `k ≥ 1`) becomes its gadget with every location's condition conjoined with the
location's condition on the decoded logical outcomes.
-/

namespace QAlgorithms

open scoped Matrix

namespace FTProtocol

variable (P : FTProtocol)

/-- Gottesman intro p.33 (Def. 6: "C can be divided up into time steps"): all location gadgets have
the same number of time steps, so that the gadgets of one time step of `C` run in parallel without
padding. -/
def HasUniformDepth : Prop :=
  ∀ κ : LocKind, (P.gadget κ).steps.length = (P.gadget .prep).steps.length

/-- The number of time steps of the gadget phase of `C′`: the largest gadget depth. -/
def gadgetDepth : ℕ :=
  [LocKind.prep, .had, .tgate, .cnot, .meas, .wait].foldr (fun κ acc => max (P.gadget κ).steps.length acc) 0

/-- The number of time steps of `C′` per time step of `C`. -/
def period : ℕ :=
  P.gadgetDepth + P.ec.steps.length

end FTProtocol

/-- The gadget instances of `C′`: the gadget of the `C` location `ℓ`, or the EC gadget after time
step `s` of `C` on the block of qubit `q`. -/
inductive FTInstance (N : ℕ) where
  | gadget (ℓ : ℕ × ℕ)
  | ec (s : ℕ) (q : Fin N)
  deriving DecidableEq

/-- The physical qubits of the blocks of the qubits `w` of a `C` location: block `i`, position `p`
of the gadget is block `w i`, position `p` of `C′`. -/
def blockEmb (n A : ℕ) {k N : ℕ} (w : Fin k ↪ Fin N) : Fin (k * (n + A)) ↪ Fin (N * (n + A)) :=
  ⟨fun x => finProdFinEquiv (w (finProdFinEquiv.symm x).1, (finProdFinEquiv.symm x).2), by
    intro x y h
    have h' := Prod.ext_iff.1 (finProdFinEquiv.injective h)
    exact finProdFinEquiv.symm.injective (Prod.ext (w.injective h'.1) h'.2)⟩

/-- The physical qubits of the block of qubit `q`. -/
def ecEmb (n A : ℕ) {N : ℕ} (q : Fin N) : Fin (n + A) ↪ Fin (N * (n + A)) :=
  ⟨fun p => finProdFinEquiv (q, p), fun _ _ h => (Prod.ext_iff.1 (finProdFinEquiv.injective h)).2⟩

variable {N : ℕ}

/-- The position in its `C′` step at which the gadget of the `C` location `(s, j)` starts, at local
step `d` of the gadget. -/
def gadgetOffset (P : FTProtocol) (C : LocCircuit N) (s j d : ℕ) : ℕ :=
  (((C.steps.getD s []).take j).map fun l => ((P.gadget l.kind).steps.getD d []).length).sum

/-- The id in `C′` of the location with local id `lid` of the gadget of the `C` location
`(s, j)`. -/
def gadgetGlobalId (P : FTProtocol) (C : LocCircuit N) (s j : ℕ) (lid : ℕ × ℕ) : ℕ × ℕ :=
  (s * P.period + lid.1, gadgetOffset P C s j lid.1 + lid.2)

/-- The qubits of `C` receiving an EC gadget after time step `s`: those whose step-`s` location is
not a measurement (the EC between consecutive locations, Def. 6). -/
def ecBlocks (C : LocCircuit N) (s : ℕ) : List (Fin N) :=
  (List.finRange N).filter fun q =>
    (C.steps.getD s []).any fun l => decide (l.kind ≠ .meas) && decide (q ∈ l.qubits)

/-- The id in `C′` of the location with local id `lid` of the EC gadget after step `s` on the
`idx`-th block of `ecBlocks C s`. -/
def ecGlobalId (P : FTProtocol) (s idx : ℕ) (lid : ℕ × ℕ) : ℕ × ℕ :=
  (s * P.period + P.gadgetDepth + lid.1, idx * (P.ec.steps.getD lid.1 []).length + lid.2)

/-- The decoded logical outcomes of the measurement locations of `C`, read from the outcomes `O`
of `C′` (`none` until every outcome of the measurement gadget is available). -/
def decodedOutcomes (P : FTProtocol) (C : LocCircuit N) (O : ℕ × ℕ → Option Bool) :
    ℕ × ℕ → Option Bool :=
  fun cid => match C.locAt cid with
    | some l =>
        if l.kind = .meas then
          if ((P.gadget .meas).measIds.map fun lid => O (gadgetGlobalId P C cid.1 cid.2 lid)).all
              Option.isSome then
            some (P.measDecode ((P.gadget .meas).measIds.map fun lid =>
              (O (gadgetGlobalId P C cid.1 cid.2 lid)).getD false))
          else none
        else none
    | none => none

/-- Time step `d` of the gadget phase for time step `s` of `C`, its locations tagged with their
gadget instance. -/
def gadgetPhaseStep (P : FTProtocol) (C : LocCircuit N) (s d : ℕ) :
    List (Loc (N * (P.n + P.A)) × FTInstance N) :=
  (C.steps.getD s []).zipIdx.flatMap fun p =>
    ((P.gadget p.1.kind).steps.getD d []).map fun g =>
      (⟨g.kind, g.wires.trans (blockEmb P.n P.A p.1.wires),
        fun O => g.cond (fun lid => O (gadgetGlobalId P C s p.2 lid)) &&
          (if p.1.kind.IsGate then p.1.cond (decodedOutcomes P C O) else true)⟩,
       FTInstance.gadget (s, p.2))

/-- Time step `e` of the EC phase after time step `s` of `C`, its locations tagged with their
gadget instance. -/
def ecPhaseStep (P : FTProtocol) (C : LocCircuit N) (s e : ℕ) :
    List (Loc (N * (P.n + P.A)) × FTInstance N) :=
  (ecBlocks C s).zipIdx.flatMap fun p =>
    (P.ec.steps.getD e []).map fun g =>
      (⟨g.kind, g.wires.trans (ecEmb P.n P.A p.1),
        fun O => g.cond (fun lid => O (ecGlobalId P s p.2 lid))⟩,
       FTInstance.ec s p.1)

/-- The time steps of `C′`, every location tagged with its gadget instance. -/
def ftTaggedSteps (P : FTProtocol) (C : LocCircuit N) :
    List (List (Loc (N * (P.n + P.A)) × FTInstance N)) :=
  (List.range C.steps.length).flatMap fun s =>
    (List.range P.gadgetDepth).map (gadgetPhaseStep P C s) ++
      (List.range P.ec.steps.length).map (ecPhaseStep P C s)

/-- Gottesman intro p.33 (Def. 6: "a quantum circuit `C′` constructed by replacing each location
`C_i` with a fault-tolerant gadget for `C_i`, and adding fault-tolerant error correction gadgets
between any pair of consecutive locations") and p.34 (Fig. 7): the fault-tolerant circuit for
`C`. -/
def ftCircuit (P : FTProtocol) (C : LocCircuit N) : LocCircuit (N * (P.n + P.A)) :=
  ⟨(ftTaggedSteps P C).map fun st => st.map Prod.fst⟩

/-- The gadget instance the location `id` of `C′` belongs to. -/
def ftOwner (P : FTProtocol) (C : LocCircuit N) (id : ℕ × ℕ) : Option (FTInstance N) :=
  ((ftTaggedSteps P C).getD id.1 [])[id.2]?.map Prod.snd

/-- Gottesman intro p.19 ("the final fault-tolerant measurement gadgets will produce classical
information which should … give the same outcome as the original circuit") and p.17 (classical
computation is perfect): the measurement record of `C` decoded from that of `C′`: for each
measurement location of `C` (in `C`'s record order), `measDecode` of the outcomes of its
measurement gadget; EC and other outcomes are discarded. -/
def ftDecode (P : FTProtocol) (C : LocCircuit N) (r : List Bool) : List Bool :=
  C.measIds.map fun cid => P.measDecode ((P.gadget .meas).measIds.map fun lid =>
    ((ftCircuit P C).outcomeAt r (gadgetGlobalId P C cid.1 cid.2 lid)).getD false)

/-- Gottesman intro p.34 (Def. 7) and p.38 (Def. 10): the locations of `C′` in the ExRec of the `C`
location `ℓ`: its gadget, the leading ECs (the EC after the previous step on each of its qubits,
unless `ℓ` is a preparation) and the trailing ECs (the EC after its step on each of its qubits not
in `trunc`, unless `ℓ` is a measurement). `trunc = ∅` is the full ExRec. -/
noncomputable def exRecLocs (P : FTProtocol) (C : LocCircuit N) (ℓ : ℕ × ℕ) (trunc : Finset (Fin N)) :
    Finset (ℕ × ℕ) :=
  open Classical in
  match C.locAt ℓ with
  | none => ∅
  | some l => (ftCircuit P C).locs.filter fun id =>
      match ftOwner P C id with
      | some (.gadget ℓ') => ℓ' = ℓ
      | some (.ec s q) => q ∈ l.qubits ∧
          ((l.kind ≠ .prep ∧ s + 1 = ℓ.1) ∨ (l.kind ≠ .meas ∧ s = ℓ.1 ∧ q ∉ trunc))
      | none => False

/-- Gottesman intro p.38 (Def. 10): the qubits of the `C` location `ℓ` whose trailing EC is removed
because it is the leading EC of a bad location (of the next time step) in `B`. -/
noncomputable def truncOf (C : LocCircuit N) (B : Finset (ℕ × ℕ)) (ℓ : ℕ × ℕ) : Finset (Fin N) :=
  open Classical in
  match C.locAt ℓ with
  | none => ∅
  | some l => l.qubits.filter fun q =>
      ∃ ℓ' ∈ B, ℓ'.1 = ℓ.1 + 1 ∧ ∃ l', C.locAt ℓ' = some l' ∧ q ∈ l'.qubits

/-- The bad locations among the last `k` time steps of `C`, for the set `S` of faulty locations of
`C′` (Def. 10's recursion, from the end of the circuit backwards). -/
noncomputable def badAbove (P : FTProtocol) (C : LocCircuit N) (S : Finset (ℕ × ℕ)) :
    ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | k + 1 =>
      open Classical in
      badAbove P C S k ∪
        ((Finset.range (C.steps.getD (C.steps.length - (k + 1)) []).length).image
          fun j => (C.steps.length - (k + 1), j)).filter fun ℓ =>
            P.t < (S ∩ exRecLocs P C ℓ (truncOf C (badAbove P C S k) ℓ)).card

/-- Gottesman intro p.38 (Def. 10): the set of locations of `C` whose ExRec (full or truncated) is
bad, i.e. contains more than `t` of the faulty locations `S` of `C′`; an ExRec is truncated on the
qubits whose trailing EC is a leading EC of a bad ExRec, determined from the end of the circuit
backwards. -/
noncomputable def badAssignment (P : FTProtocol) (C : LocCircuit N) (S : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  badAbove P C S C.steps.length

/-- The superoperator `Ψ` on `k` registers (of type `α`) lifted to `N` registers along `w`, the
identity on the others. -/
noncomputable def liftReg {α : Type*} {k : ℕ} (w : Fin k ↪ Fin N)
    (Ψ : Superop (Fin k → α) (Fin k → α)) : Superop (Fin N → α) (Fin N → α) :=
  fun X =>
    (liftSuperop (E := Unit) w
      (fun Y => (Ψ (Y.submatrix (fun x => (x, ())) (fun x => (x, ())))).submatrix Prod.fst Prod.fst)
      (X.submatrix Prod.fst Prod.fst)).submatrix (fun x => (x, ())) (fun x => (x, ()))

/-- A superoperator `Ψ` on the (data qubit, syndrome register) pairs of `k` qubits, lifted to the
qubits of `C` with one syndrome register per qubit as environment. -/
noncomputable def pairLift {σ k : ℕ} (w : Fin k ↪ Fin N)
    (Ψ : Superop (Fin k → Bool × Fin σ) (Fin k → Bool × Fin σ)) :
    Superop (Qubits N × (Fin N → Fin σ)) (Qubits N × (Fin N → Fin σ)) :=
  fun X =>
    (liftReg w Ψ (X.submatrix (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin σ))
      (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin σ)))).submatrix
      (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin σ)).symm
      (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin σ)).symm

/-- Gottesman intro pp.37–39 (eqs. (82), (83), Thm 8): `err` is an error assignment of a circuit
`C̃` for `C` with bad set `B` and syndrome registers `Fin σ` (one per qubit of `C`, the environment;
"`C̃` uses ancilla registers to control the types of `U′` errors"): no error off the locations; at
every location `ℓ`, after its ideal operation, a quantum operation `Ψ` on the qubits of `ℓ` and
their syndrome registers; if `ℓ ∉ B` ("include `C_i` unchanged"), `Ψ` is the identity on the qubits
tensored with a quantum operation `V` on the syndrome registers (eq. (83)); if `ℓ ∈ B`, `Ψ` is
arbitrary (the erroneous `U′` of (82), controlled by the syndrome). -/
def IsTildeErrors (C : LocCircuit N) (B : Finset (ℕ × ℕ)) (σ : ℕ)
    (err : ErrAssign N (Fin N → Fin σ)) : Prop :=
  ∀ ℓ : ℕ × ℕ, (C.locAt ℓ = none → err ℓ = none) ∧
    ∀ l : Loc N, C.locAt ℓ = some l →
      ∃ Ψ : Superop (Fin l.kind.arity → Bool × Fin σ) (Fin l.kind.arity → Bool × Fin σ),
        IsChannel Ψ ∧
        (ℓ ∉ B → ∃ V : Superop (Fin l.kind.arity → Fin σ) (Fin l.kind.arity → Fin σ),
          IsChannel V ∧ Ψ = pairedSuperop 1 V) ∧
        err ℓ = some (pairLift l.wires Ψ)

/-- Gottesman intro p.40 (Def. 12): an error model on a circuit with `N` qubits: an environment
register `Fin e` in the state `σ0`, the probability `prob S` of faults at precisely the set `S` of
locations, and the errors `err S ℓ` chosen (by an adversary) when the faulty set is `S`; they act
at the locations of `S` in chronological order and may be entangled through the environment. -/
structure LocalStochasticModel (N : ℕ) where
  e : ℕ
  σ0 : Matrix (Fin e) (Fin e) ℂ
  prob : Finset (ℕ × ℕ) → ℝ
  err : Finset (ℕ × ℕ) → ℕ × ℕ → Superop (Qubits N × Fin e) (Qubits N × Fin e)

/-- Gottesman intro p.40 (Def. 12): the output distribution of `C` under the error model: the
mixture over the faulty set `S` of the output distributions with the errors at `S`. -/
noncomputable def noisyOutDist (C : LocCircuit N) (M : LocalStochasticModel N) :
    (Fin C.measCount → Bool) → ℝ :=
  fun r => ∑ S ∈ C.locs.powerset,
    M.prob S * C.outDist (fun ℓ => if ℓ ∈ S then some (M.err S ℓ) else none) M.σ0 r

/-- Gottesman intro p.40 (Def. 12): `M` is a local stochastic error model on `C` with error bounds
`bound`: the environment state is a density matrix; `prob` is a probability distribution on the
sets of locations of `C`; each error at a faulty location is any quantum operation on that
location's qubits and the environment; and for every set `R` of locations the probability of
faults on every location of `R` (and possibly elsewhere) is at most `Π_{i ∈ R} p_i`. The side
condition `p_i < 1` of Def. 12 is a separate hypothesis of the statements (Thm 9's induced bounds
(84) may exceed 1). -/
def IsLocalStochastic (C : LocCircuit N) (M : LocalStochasticModel N) (bound : ℕ × ℕ → ℝ) : Prop :=
  IsDensityMatrix M.σ0 ∧ (∀ S, 0 ≤ M.prob S) ∧ (∀ S, ¬ S ⊆ C.locs → M.prob S = 0) ∧
    ∑ S ∈ C.locs.powerset, M.prob S = 1 ∧
    (∀ (S : Finset (ℕ × ℕ)) (ℓ : ℕ × ℕ) (l : Loc N), ℓ ∈ S → C.locAt ℓ = some l →
      IsLocError l.wires (M.err S ℓ)) ∧
    ∀ R ⊆ C.locs, ∑ S ∈ C.locs.powerset.filter (fun S => R ⊆ S), M.prob S ≤ ∏ i ∈ R, bound i

/-- Transport of a circuit along an equality of qubit numbers. -/
def LocCircuit.castN {N N' : ℕ} (h : N = N') (C : LocCircuit N) : LocCircuit N' :=
  h ▸ C

/-- Gottesman intro p.36 (§5.2: "a sequence of circuits `C^{(k)}`, `k = 1, …, L`, where each `C^{(k)}`
is a fault-tolerant simulation of `C^{(k−1)}`, with `C^{(0)} = C`") and p.42 (proof of Thm 10): the
`L`-level concatenated fault-tolerant circuit for `C`, on `N (n + A)^L` qubits. -/
def concatCircuit (P : FTProtocol) : (L : ℕ) → LocCircuit N → LocCircuit (N * (P.n + P.A) ^ L)
  | 0, C => C.castN (by simp)
  | L + 1, C => (ftCircuit P (concatCircuit P L C)).castN (by rw [pow_succ, mul_assoc])

/-- The classical decoding of the record of `C^{(L)}` to the record of `C`, level by level. -/
def concatDecode (P : FTProtocol) : (L : ℕ) → LocCircuit N → List Bool → List Bool
  | 0, _ => id
  | L + 1, C => fun r => concatDecode P L C (ftDecode P (concatCircuit P L C) r)

/-! ### Sanity tests -/

example (P : FTProtocol) : ftCircuit P (⟨[]⟩ : LocCircuit N) = ⟨[]⟩ := by
  simp [ftCircuit, ftTaggedSteps]

example (P : FTProtocol) (S : Finset (ℕ × ℕ)) : badAssignment P (⟨[]⟩ : LocCircuit N) S = ∅ := rfl

example (P : FTProtocol) (C : LocCircuit N) : concatDecode P 0 C = id := rfl

example (P : FTProtocol) (r : List Bool) : ftDecode P (⟨[]⟩ : LocCircuit N) r = [] := rfl

example (n A : ℕ) (q : Fin N) (p : Fin (n + A)) :
    blockEmb n A (Stabilizer.wire1 q) (finProdFinEquiv (0, p)) = finProdFinEquiv (q, p) := by
  show finProdFinEquiv (_, _) = _
  rw [Equiv.symm_apply_apply]
  rfl

example (C : LocCircuit N) (M : LocalStochasticModel N) (h : C.locs = ∅) (r : Fin C.measCount → Bool) :
    noisyOutDist C M r = M.prob ∅ * C.outDist (fun _ => none) M.σ0 r := by
  simp [noisyOutDist, h]

end QAlgorithms


