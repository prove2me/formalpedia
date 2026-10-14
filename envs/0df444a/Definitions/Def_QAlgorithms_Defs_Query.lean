-- Prove2me | Definitions.Def_QAlgorithms_Defs_Query
-- name    : QAlgorithms_Defs_Query
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:27:12.05844+00:00
-- url     : https://prove2.me/theorems/f618ee89-2b1c-49c1-a65a-7c3fd5fdd3c3
-- title:
--   Query oracles and query algorithms (shared definition layer)
-- statement:
--   Query oracles and query algorithms (shared definition layer)
--
--   ### QAlgorithms.xorOracle
--
--   The inputs are:
--
--   - types $\iota$ and $\kappa$ with decidable equality, where $\kappa$ carries the structure of an abelian group with operation $+$;
--   - a function $f : \iota \to \kappa$.
--
--   Finiteness of $\iota$ or $\kappa$ is not required. The output is the complex matrix $O_f$ with rows and columns indexed by pairs in $\iota \times \kappa$, with entries
--
--   $$
--   (O_f)_{(i',c'),\,(i,c)} \;=\; \begin{cases} 1 & \text{if } i' = i \text{ and } c' = c + f(i),\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   Each column $(i,c)$ has a single entry $1$, in row $(i,\, c + f(i))$. So acting on basis vectors it sends $|i, c\rangle \mapsto |i,\, c + f(i)\rangle$, where the addition is the group operation of $\kappa$; for $\kappa = $ bit strings under $+$ this is bitwise XOR. Because $c \mapsto c + f(i)$ is a bijection of $\kappa$, each row also contains exactly one $1$, so $O_f$ is a permutation matrix.
--
--   ### QAlgorithms.phaseOracle
--
--   Let $\iota$ be any index type with decidable equality; no finiteness is assumed. Let $x : \iota \to \{\text{true},\text{false}\}$ be a Boolean string indexed by $\iota$. The definition gives a complex $\iota \times \iota$ matrix $P_x$, the **phase oracle** of $x$. It is the diagonal matrix
--
--   $$
--   (P_x)_{i,i'} = \begin{cases} -1 & \text{if } i = i' \text{ and } x_i = \text{true},\\ 1 & \text{if } i = i' \text{ and } x_i = \text{false},\\ 0 & \text{if } i \neq i'.\end{cases}
--   $$
--
--   In other words, $P_x$ sends each basis vector $|i\rangle$ to $(-1)^{x_i}|i\rangle$, where true is read as $1$ and false as $0$.
--
--   ### QAlgorithms.controlledPhaseOracle
--
--   Let $\iota$ be any index type with decidable equality, and let $x : \iota \to \{\text{true},\text{false}\}$. The definition gives a complex matrix $C_x$ whose rows and columns are indexed by pairs $(i,b)$, with $i \in \iota$ and $b$ a Boolean. $C_x$ is diagonal, and its diagonal entry at $(i,b)$ is
--
--   $$
--   (C_x)_{(i,b),(i,b)} = \begin{cases} -1 & \text{if } b = \text{true} \text{ and } x_i = \text{true},\\ 1 & \text{otherwise.}\end{cases}
--   $$
--
--   All off-diagonal entries are $0$. Thus $|i,b\rangle \mapsto (-1)^{b\cdot x_i}|i,b\rangle$: the sign flips exactly when the control bit $b$ is set and $x_i$ is true.
--
--   ### QAlgorithms.QueryAlg
--
--   Fix the following data:
--
--   - finite types $\iota$ (query indices), $\kappa$ (answer values) and $W$ (workspace), each with decidable equality;
--   - a natural number $T$.
--
--   A **query algorithm** $A$ with these parameters consists of three pieces of data:
--
--   1. A vector $\mathrm{start} \in \mathbb{C}^{(\iota\times\kappa)\times W}$. This space is the Euclidean (ℓ²) space whose coordinates are indexed by triples $((i,k),w)$.
--   2. A proof that $\|\mathrm{start}\|_2 = 1$.
--   3. A family $U_0, U_1, \dots, U_T$ of $T+1$ unitary matrices on $\mathbb{C}^{(\iota\times\kappa)\times W}$, indexed by $\{0,\dots,T\}$.
--
--   Nothing else is required, and in particular nothing links $T$ to the number of oracle calls. That link comes only through how the structure is used (see `stateAt`).
--
--   If $(\iota\times\kappa)\times W$ is empty, then every vector has norm $0$. So when any of $\iota$, $\kappa$ or $W$ is empty, no query algorithm exists.
--
--   ### QAlgorithms.QueryAlg.stateAt
--
--   The inputs are:
--
--   - a query algorithm $A$, with the implicit finite types $\iota,\kappa,W$ (decidable equality) and step count $T$ as in `QueryAlg`, starting vector $\mathrm{start}$ and unitaries $U_0,\dots,U_T$;
--   - an arbitrary complex $(\iota\times\kappa)\times(\iota\times\kappa)$ matrix $O$, the "oracle". $O$ is not required to be unitary.
--
--   The definition produces a sequence of vectors $\psi_0,\dots,\psi_T \in \mathbb{C}^{(\iota\times\kappa)\times W}$, defined recursively by
--
--   $$
--   \psi_0 = U_0\,\mathrm{start}, \qquad \psi_{t+1} = U_{t+1}\,(O \otimes I_W)\,\psi_t \quad (0 \le t < T).
--   $$
--
--   Here every product is an ordinary matrix–vector product. $O\otimes I_W$ is the Kronecker product, with entries
--
--   $$
--   (O\otimes I_W)_{((a),w),((a'),w')} = O_{a,a'}\,\delta_{w,w'}.
--   $$
--
--   So $\psi_t$ is the state after $t$ applications of $O\otimes I_W$, interleaved with $U_0,\dots,U_t$.
--
--   ### QAlgorithms.QueryAlg.finalState
--
--   Take a query algorithm $A$ (implicit $\iota,\kappa,W,T$ as in `QueryAlg`) and an arbitrary complex matrix $O$ indexed by $\iota\times\kappa$. The final state is the last vector $\psi_T$ of the sequence from `stateAt`:
--
--   $$
--   \psi_T = U_T (O\otimes I_W) U_{T-1} (O\otimes I_W) \cdots U_1 (O\otimes I_W) U_0\,\mathrm{start}.
--   $$
--
--   This expression contains exactly $T$ factors of $O\otimes I_W$. When $T = 0$ it is just $U_0\,\mathrm{start}$.
--
--   ### QAlgorithms.QueryAlg.outputProb
--
--   The inputs are:
--
--   - a query algorithm $A$ (implicit $\iota,\kappa,W,T$ as in `QueryAlg`);
--   - an arbitrary complex matrix $O$ indexed by $\iota\times\kappa$;
--   - a type $\beta$ with decidable equality;
--   - an output map $\mathrm{out} : (\iota\times\kappa)\times W \to \beta$;
--   - a value $b\in\beta$.
--
--   The output probability is the real number
--
--   $$
--   \Pr_{A,O}[\mathrm{out}=b] \;=\; \sum_{z \,:\, \mathrm{out}(z)=b} \bigl|\langle e_z, \psi_T\rangle\bigr|^2 \;=\; \sum_{z \,:\, \mathrm{out}(z)=b} |(\psi_T)_z|^2 .
--   $$
--
--   Here $\psi_T$ is `finalState` of $A$ with oracle $O$, and $e_z$ is the standard basis vector at $z$. The sum runs over all basis labels $z$ whose output value is $b$.
--
--   Because $O$ is arbitrary, $\psi_T$ need not be a unit vector. The sum is then a nonnegative real number that may exceed $1$. It is a genuine probability only when $\|\psi_T\| = 1$, for example when $O$ is unitary.
--
--   ### QAlgorithms.QueryAlg.ComputesWithError
--
--   The inputs are:
--
--   - a query algorithm $A$ whose answer type is the Booleans ($\kappa = \text{Bool}$), with implicit $\iota, W, T$ as in `QueryAlg`;
--   - an output map $\mathrm{out} : (\iota\times\text{Bool})\times W \to \text{Bool}$;
--   - a finite set $D$ of Boolean strings $x : \iota\to\text{Bool}$;
--   - a function $f$ from all Boolean strings on $\iota$ to Bool;
--   - a real number $\varepsilon$.
--
--   The proposition says that for every $x \in D$,
--
--   $$
--   \Pr_{A,\,O_x}[\mathrm{out} = f(x)] \;\ge\; 1-\varepsilon .
--   $$
--
--   Here $O_x$ is the XOR oracle of $x$. It is the $0/1$ matrix with $(O_x)_{(i,c),(i',c')} = 1$ exactly when $i=i'$ and $c = c' + x_{i'}$. The addition is the additive group structure on Booleans that is in force. So $O_x$ maps $|i,c\rangle \mapsto |i, c + x_i\rangle$.
--
--   Degenerate cases:
--
--   - If $D=\emptyset$, the condition holds vacuously.
--   - If $\varepsilon \ge 1$, it holds trivially, since the left side is a sum of squared moduli and hence nonnegative.
--   - If $\varepsilon<0$, it demands a value above $1$, which is impossible when $\psi_T$ is a unit vector.
--   - $f$ is constrained only on $D$.
--
--   ### QAlgorithms.IsConstant
--
--   Let $\iota$ be any type and $x:\iota\to\text{Bool}$. $x$ is **constant** if $x_i = x_j$ for all $i,j\in\iota$. When $\iota$ is empty this holds vacuously.
--
--   ### QAlgorithms.IsBalanced
--
--   Let $\iota$ be a finite type and $x:\iota\to\text{Bool}$. $x$ is **balanced** if
--
--   $$
--   2\cdot\bigl|\{\, i\in\iota : x_i = \text{true}\,\}\bigr| \;=\; |\iota| ,
--   $$
--
--   that is, exactly half the entries are true. This is an equation of natural numbers.
--
--   - It can hold only when $|\iota|$ is even.
--   - When $\iota$ is empty it holds, since $0=0$.
--
--   ### QAlgorithms.deutschJozsaState
--
--   Let $n\in\mathbb{N}$ and $x : \{0,1\}^n \to \text{Bool}$. Here $\{0,1\}^n$ denotes the type of $n$-bit strings, functions from $\{0,\dots,n-1\}$ to Bool. The definition gives the vector
--
--   $$
--   H_n\,P_x\,H_n\,|0^n\rangle \in \mathbb{C}^{\{0,1\}^n}.
--   $$
--
--   The pieces are as follows.
--
--   - $|0^n\rangle$ is the standard basis vector at the all-false string.
--   - $P_x$ is the phase oracle: the diagonal matrix with entry $-1$ at strings $i$ where $x(i)$ is true and $+1$ elsewhere.
--   - $H_n$ is the matrix with entries
--   $$
--   (H_n)_{j,i} = \begin{cases} -(1/\sqrt2)^n & \text{if } \mathrm{dot}(i,j) = \text{true},\\ (1/\sqrt2)^n & \text{otherwise,}\end{cases}
--   $$
--   where $\mathrm{dot}(i,j) = \sum_{k<n} (i_k \wedge j_k)$ is computed with the addition on Bool that is in force.
--
--   For $n=0$ there is exactly one string, and $H_0$ is the $1\times1$ matrix $(1)$. The result is then $\pm|\,\rangle$, with the sign given by $x$ of the empty string.
--
--   ### QAlgorithms.bvInput
--
--   Let $n\in\mathbb{N}$ and $a\in\{0,1\}^n$, an $n$-bit string. The definition gives the Boolean function on $n$-bit strings
--
--   $$
--   i \;\mapsto\; \mathrm{dot}(i,a) = \sum_{k=0}^{n-1} (i_k \wedge a_k).
--   $$
--
--   The sum is taken with the addition on Bool that is in force; if that addition is exclusive-or, this is the inner product of $i$ and $a$ mod 2. For $n = 0$ the function is constantly the empty sum, the Boolean zero (false).
--
--   ### QAlgorithms.SimonPromise
--
--   Let $n\in\mathbb{N}$, let $x : \{0,1\}^n \to \{0,1\}^n$ be a function from $n$-bit strings to $n$-bit strings, and let $s\in\{0,1\}^n$. The proposition says that for all $n$-bit strings $i,j$,
--
--   $$
--   x(i) = x(j) \iff \bigl(i = j \ \text{ or } \ i = j + s\bigr).
--   $$
--
--   Here $j+s$ is the coordinatewise sum of bit strings under the addition on Bool that is in force; with exclusive-or, this is $j\oplus s$.
--
--   Degenerate cases:
--
--   - **$s$ is the zero string:** the condition says $x(i)=x(j)\iff i=j$, i.e. $x$ is injective.
--   - **$s$ is nonzero:** it requires each fibre of $x$ to be exactly a pair $\{j, j+s\}$, provided the addition is such that $i=j+s$ is symmetric in $i$ and $j$, as with XOR.
--   - **$n=0$:** there is only one string, and the condition holds for every $x$ and $s$.
--
--   ### QAlgorithms.simonRunState
--
--   This defines a vector for each natural number $n$ and each function $x : \{0,1\}^n \to \{0,1\}^n$. Here $\{0,1\}^n$ means the $n$-bit strings, indexed by positions $0,\dots,n-1$. The vector lives in the complex Euclidean space with orthonormal basis $\{|y,z\rangle : y,z \in \{0,1\}^n\}$, a two-register space. It is
--
--   $$
--   \mathrm{simonRunState}(x) \;=\; (H_n\otimes I)\,O_x\,(H_n\otimes I)\,|0^n,0^n\rangle .
--   $$
--
--   The pieces are as follows:
--
--   - $|0^n,0^n\rangle$ is the standard basis vector at the pair of all-false strings.
--   - $I$ is the identity on the second register.
--   - $H_n$ is the matrix on $\{0,1\}^n$ with entries $(H_n)_{j,i} = 2^{-n/2}(-1)^{i\cdot j}$. Here $i\cdot j = \bigoplus_k (i_k \wedge j_k)$ is the parity of the bitwise AND.
--   - $O_x$ has entry $1$ at row $(p_1,p_2)$, column $(q_1,q_2)$ exactly when $p_1=q_1$ and $p_2 = q_2 \oplus x(q_1)$, and $0$ otherwise. Here $\oplus$ is componentwise addition of bit strings, i.e. bitwise XOR. So $O_x|a,b\rangle = |a, b\oplus x(a)\rangle$.
--
--   The matrices are applied right to left: first $H_n\otimes I$, then $O_x$, then $H_n\otimes I$ again. No promise on $x$ is assumed. For $n=0$ the space is one-dimensional and every matrix involved is the $1\times 1$ matrix $(1)$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Query.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Classical
/-!
# Query oracles and query algorithms (shared definition layer)

Three oracle forms the sources distinguish (trap Q3): the standard (XOR) query
`|i, b⟩ ↦ |i, b ⊕ x_i⟩`, de Wolf's uncontrolled phase query `|i⟩ ↦ (−1)^{x_i} |i⟩`, and Childs's
controlled phase query `|i, b⟩ ↦ (−1)^{b x_i} |i, b⟩`. A `T`-query algorithm is
`U_T O U_{T−1} ⋯ U_1 O U_0` on a fixed start state, with input-independent unitaries.
-/

namespace QAlgorithms

/-- de Wolf p.29 (§2.4, "Ox : |i, b⟩ ↦ |i, b ⊕ x_i⟩"), p.35 (§3.1), p.51 (§5.3), p.60 (§6.2.2);
Childs p.106 ((21.2), (21.4)), p.133 (§26.1): the standard query to `f : ι → κ`, the permutation
matrix of `(i, y) ↦ (i, y + f i)`. With `κ = Bool` (`+` is xor) this is `O_x |i, b⟩ = |i, b ⊕ x_i⟩`;
with `κ = Fin m → Bool` it is the string query `|i, y⟩ ↦ |i, y ⊕ x_i⟩` (Simon, Shor's `O_f`, the
random-oracle query of Childs §26); with `κ = ZMod d` it is Childs's (21.4). -/
def xorOracle {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup κ] (f : ι → κ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = q.2 + f q.1 then 1 else 0

/-- de Wolf p.30 (§2.4: "`O_{x,±}`"), p.65 (§7.2): the (uncontrolled) phase query
`O_{x,±} |i⟩ = (−1)^{x_i} |i⟩`, with no target qubit. -/
def phaseOracle {ι : Type*} [DecidableEq ι] (x : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if x i then -1 else 1

/-- Childs p.106 ((21.3)): the controlled phase query `O_x |i, b⟩ = (−1)^{b x_i} |i, b⟩`. It equals
`(I ⊗ H) Ô_x (I ⊗ H)` for the XOR query `Ô_x`, but is kept separate because each statement must
use its source's oracle (trap Q3). -/
def controlledPhaseOracle {ι : Type*} [DecidableEq ι] (x : ι → Bool) :
    Matrix (ι × Bool) (ι × Bool) ℂ :=
  Matrix.diagonal fun p => if p.2 && x p.1 then -1 else 1

/-- de Wolf p.29 (§2.4), p.111 (§12.1: "`A = U_T O_x U_{T−1} ⋯ U_1 O_x U_0`, with initial state
`|0^m⟩`"); Childs p.105 (§21.1: "begins from a state that does not depend on the oracle string"),
p.106 ((21.1)), p.134 (§26.2): a `T`-query algorithm with query register `ι × κ` and workspace `W`.
The start state and the unitaries `U_0, …, U_T` are fields, fixed before any input (trap Q2); the
oracle is an argument of `stateAt`, applied as `O ⊗ I_W` between consecutive unitaries, so the
number of queries is exactly `T` (trap Q6). (De Wolf's start `|0^m⟩` with `U_0`, and Childs's
input-independent start `ψ` with `U_1, …, U_t`, give the same class.) -/
structure QueryAlg (ι κ W : Type*) [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι]
    [DecidableEq κ] [DecidableEq W] (T : ℕ) where
  /-- The input-independent initial state. -/
  start : EuclideanSpace ℂ ((ι × κ) × W)
  /-- It is a unit vector. -/
  start_unit : ‖start‖ = 1
  /-- The input-independent unitaries `U_0, …, U_T`. -/
  U : Fin (T + 1) → Matrix.unitaryGroup ((ι × κ) × W) ℂ

namespace QueryAlg

variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
  [DecidableEq W] {T : ℕ}

/-- de Wolf p.111 (§12.1): the state `|ψ_x^t⟩ = U_t O U_{t−1} ⋯ U_1 O U_0 |start⟩` after `U_t`
has been applied, for the oracle `O` (acting on the query register, identity on the
workspace). -/
noncomputable def stateAt (A : QueryAlg ι κ W T) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    Fin (T + 1) → EuclideanSpace ℂ ((ι × κ) × W) :=
  Fin.induction (act (A.U 0 : Matrix _ _ ℂ) A.start)
    (fun i ψ => act (A.U i.succ : Matrix _ _ ℂ)
      (act (Matrix.kronecker O (1 : Matrix W W ℂ)) ψ))

/-- The final state `U_T O ⋯ O U_0 |start⟩`. -/
noncomputable def finalState (A : QueryAlg ι κ W T) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    EuclideanSpace ℂ ((ι × κ) × W) :=
  A.stateAt O (Fin.last T)

/-- de Wolf p.111 (§12.1), Childs p.106 (§21.2), p.134 (§26.2): the probability that the
algorithm outputs `b`, when it measures its whole register in the computational basis and
outputs `out` of the outcome (a designated output qubit, membership in an accepting set, or a
list of output pairs). -/
noncomputable def outputProb {β : Type*} [DecidableEq β] (A : QueryAlg ι κ W T)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (out : (ι × κ) × W → β) (b : β) : ℝ :=
  probEvent (A.finalState O) fun z => out z = b

/-- de Wolf p.26 (§2.2), p.111 (§12.1: "computes f with error probability `≤ ε` for each
`x ∈ D`"): with standard queries to `x`, the algorithm computes the (partial) Boolean function
`f` on the domain `D` with worst-case error at most `ε`: for every `x ∈ D` (not on average,
trap Q5) it outputs `f x` with probability `≥ 1 − ε`. Values of `f` outside `D` are never read.
Bounded error is `ε = 1/3`. -/
def ComputesWithError (A : QueryAlg ι Bool W T) (out : (ι × Bool) × W → Bool)
    (D : Finset (ι → Bool)) (f : (ι → Bool) → Bool) (ε : ℝ) : Prop :=
  ∀ x ∈ D, A.outputProb (xorOracle x) out (f x) ≥ 1 - ε

end QueryAlg

/-- de Wolf p.30 (§2.4.1): the Deutsch–Jozsa "constant" case: all `x_i` have the same value. -/
def IsConstant {ι : Type*} (x : ι → Bool) : Prop :=
  ∀ i j, x i = x j

/-- de Wolf p.30 (§2.4.1): the Deutsch–Jozsa "balanced" case: `N/2` of the `x_i` are `0` and `N/2`
are `1`, written `2 |x| = N` without natural-number division (so for `N = 1` no input is
balanced). -/
def IsBalanced {ι : Type*} [Fintype ι] (x : ι → Bool) : Prop :=
  2 * hammingWeight x = Fintype.card ι

/-- de Wolf p.30 (§2.4.1), p.31 (§2.4.2): the final state `H^{⊗n} O_{x,±} H^{⊗n} |0ⁿ⟩` of the
Deutsch–Jozsa algorithm, before the measurement; the Bernstein–Vazirani algorithm "is exactly
the same". The input is indexed by `n`-bit strings (de Wolf identifies `{0, …, N−1}` with
`{0,1}ⁿ`). -/
noncomputable def deutschJozsaState {n : ℕ} (x : Qubits n → Bool) : EuclideanSpace ℂ (Qubits n) :=
  act (hadamardN n * phaseOracle x * hadamardN n) (zeroKet n)

/-- de Wolf p.31 (§2.4.2): the Bernstein–Vazirani input `x_i = (i · a) mod 2`. -/
def bvInput {n : ℕ} (a : Qubits n) : Qubits n → Bool :=
  fun i => dotBits i a

/-- de Wolf p.35 (§3.1), p.37 (§3.3.2): Simon's promise with mask `s`: `x_i = x_j` iff `i = j` or
`i = j ⊕ s` (`+` on bit strings is bitwise xor). The search version (§3.1) adds `s ≠ 0`; the
decision version (§3.3.2) allows `s = 0`. -/
def SimonPromise {n : ℕ} (x : Qubits n → Qubits n) (s : Qubits n) : Prop :=
  ∀ i j, x i = x j ↔ (i = j ∨ i = j + s)

/-- de Wolf p.35–36 (§3.2): one run of Simon's subroutine before the measurement: from
`|0ⁿ⟩|0ⁿ⟩`, apply `H^{⊗n}` to the first register, one string query `|i, y⟩ ↦ |i, y ⊕ x_i⟩`, and
`H^{⊗n}` to the first register. The law of the run's outcome `j` is `marginalFst` (the optional
measurement of the second register does not change it, p.36). -/
noncomputable def simonRunState {n : ℕ} (x : Qubits n → Qubits n) :
    EuclideanSpace ℂ (Qubits n × Qubits n) :=
  act (Matrix.kronecker (hadamardN n) (1 : Matrix (Qubits n) (Qubits n) ℂ) * xorOracle x *
    Matrix.kronecker (hadamardN n) (1 : Matrix (Qubits n) (Qubits n) ℂ)) (ket (0, 0))

/-! ### Sanity tests -/

example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup κ] :
    xorOracle (0 : ι → κ) = 1 := by
  ext p q
  simp [xorOracle, Matrix.one_apply, Prod.ext_iff]

/-- The standard query maps `|i, y⟩` to `|i, y + f(i)⟩`. -/
example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup κ] (f : ι → κ) (i : ι)
    (y : κ) : xorOracle f (i, y + f i) (i, y) = 1 := by
  simp [xorOracle]

theorem xorOracle_mul_neg {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup κ] (f : ι → κ) : xorOracle f * xorOracle (-f) = 1 := by
  ext ⟨i, y⟩ ⟨j, z⟩
  simp only [xorOracle, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Pi.neg_apply]
  rw [Finset.sum_eq_single (j, z + -f j)]
  · by_cases h : i = j
    · subst h; by_cases h' : y = z <;> simp [h']
    · simp [h, Prod.ext_iff]
  · rintro ⟨k, w⟩ _ hkw
    by_cases hk : k = j
    · subst hk
      have : w ≠ z + -f k := fun h => hkw (by rw [h])
      simp [this]
    · simp [hk]
  · simp

example {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Bool) :
    phaseOracle x * phaseOracle x = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; cases hx : x i <;> simp [phaseOracle, hx]
  · simp [phaseOracle, h]

/-- The controlled phase query never touches `|i, 0⟩`. -/
example {ι : Type*} [DecidableEq ι] (x : ι → Bool) (i : ι) :
    controlledPhaseOracle x (i, false) (i, false) = 1 := by
  simp [controlledPhaseOracle]

/-- A 0-query algorithm's output does not depend on the oracle. -/
example {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
    [DecidableEq W] (A : QueryAlg ι κ W 0) (O O' : Matrix (ι × κ) (ι × κ) ℂ) :
    A.finalState O = A.finalState O' := rfl

/-- One query: the final state is `U_1 (O ⊗ I) U_0 |start⟩`. -/
example {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
    [DecidableEq W] (A : QueryAlg ι κ W 1) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    A.finalState O = act (A.U 1 : Matrix _ _ ℂ)
      (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (act (A.U 0 : Matrix _ _ ℂ) A.start)) := rfl

example : IsBalanced (![true, false] : Fin 2 → Bool) ∧ ¬ IsBalanced (![true] : Fin 1 → Bool) := by
  unfold IsBalanced
  decide

/-- Simon's promise with `s = 0` says that `x` is injective. -/
example {n : ℕ} (x : Qubits n → Qubits n) : SimonPromise x 0 ↔ Function.Injective x := by
  simp only [SimonPromise, add_zero, or_self]
  exact ⟨fun h i j hij => (h i j).1 hij, fun h i j => ⟨fun hij => h hij, fun hij => hij ▸ rfl⟩⟩

end QAlgorithms


