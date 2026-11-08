-- Prove2me | Definitions.Def_QRetrieval_Adaptive_CompressionScheme
-- name    : QRetrieval_Adaptive_CompressionScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:09.304192+00:00
-- url     : https://prove2.me/theorems/3140f71b-3c71-461e-a64d-9d73bc3aba8c
-- title:
--   $(m,n,s,t)$-compression scheme with adaptive quantum retrieval, and its validity (Definition 2.1)
-- statement:
--   An **$(m,n,s,t)$-compression scheme** $S$ consists of a storage scheme and a query circuit.
--
--   1. The **storage scheme** is a function $f_S:B(m,n)\to\{0,1\}^s$.
--   2. The **query circuit** has a classical index register holding $i\in[m]$; for each $i$ it is a quantum query algorithm on an address register $[s]$, an oracle qubit $b\in\{0,1\}$ and a work register $W$: an input-independent unit start vector, unitaries $U_0,\dots,U_T$ that depend on $i$ but not on the stored string, and $T\le t$ oracle gates in between, each equal to the same oracle
--   $$
--   O_y:\ |j\rangle|b\rangle\mapsto(-1)^{y_j\cdot b}|j\rangle|b\rangle .
--   $$
--   3. At the end all registers are measured in the computational basis and a fixed map turns the outcome into a bit.
--
--   The scheme is **valid** if for every $x\in B(m,n)$ and every $i\in[m]$, running the circuit for $i$ with all oracle gates equal to $O_{f_S(x)}$ outputs $x_i$ **with probability $1$**. The quantity $s_Q(m,n,t)$ of the paper is the least $s$ for which a valid $(m,n,s,t)$-scheme exists. Only the storage scheme sees $x$: the work register, the number of queries, the start vector, the unitaries and the output map are fixed in advance, so the queries may be adaptive but the circuit cannot depend on the input.
--
--   **Formalization Note** The circuit for $i$ is a `QAlgorithms.QueryAlg (Fin s) Bool W T` (unitary throughout, one final measurement, exactly $T$ oracle gates applied as $O\otimes I_W$), with $W$ and $T\le t$ shared by all $i$, and the oracle is `QAlgorithms.controlledPhaseOracle`. The final two-outcome measurement is a computational-basis measurement followed by a classical map; any two-outcome projective measurement reduces to this by folding its change of basis into $U_T$. $s_Q$ itself is not defined: statements say "a valid scheme with $s\le\dots$ exists".
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, Definition 2.1, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QRetrieval_Adaptive_B

namespace QRetrieval.Adaptive

/-- **An `(m, n, s, t)`-compression scheme with adaptive quantum retrieval (Definition 2.1).**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, Definition 2.1, p. 4. A scheme `S` consists of

* a storage scheme `f_S : B(m, n) → {0,1}^s` (`store`);
* a query circuit `C_S`: a classical index register `I` carrying `i ∈ [m]`, arbitrary unitaries
  on the quantum registers controlled by `I`, at most `t` oracle gates `O_y`, all for the same
  string `y`, acting as `O_y : |j⟩|b⟩ ↦ (−1)^{y_j·b}|j⟩|b⟩`, and "a measurement at the end that
  yields an outcome in `{0,1}`".

Here the circuit with `I = i` is the query algorithm `query i`: an input-independent unit start
vector on the address register `Fin s`, the oracle qubit `Bool` and a work register `W`, then
`U_0, O, U_1, …, O, U_T` with exactly `T ≤ t` oracle gates (`QAlgorithms.QueryAlg`). The final
measurement is a computational-basis measurement of all registers followed by the classical map
`out i` to `{0,1}`. The scheme is **valid** (`CompressionScheme.Valid`) if for every
`x ∈ B(m, n)` and every `i ∈ [m]`, running `query i` with every oracle gate equal to
`O_{f_S(x)}` (`QAlgorithms.controlledPhaseOracle (store x)`) yields `x_i` with probability `1`.

No field except `store` depends on the string `x`: the work register, the number of queries,
the start vector, the unitaries and the output map are fixed before `x` is chosen.

**Formalization Note.**
1. "Unitary operations … controlled by the index register `I`" is encoded as one query algorithm
   per value `i` of `I` (`query i`), all sharing the work register `W` and the query count `T`.
   A per-`i` start vector is the same class as a fixed start vector followed by an `I`-controlled
   unitary.
2. "A measurement at the end that yields an outcome in `{0,1}`" is a computational-basis
   measurement of the whole register followed by a classical map `out i`; any two-outcome
   projective measurement reduces to this by folding its change of basis into `U_T`.
3. `[m]`, `{0,1}^s` are `Fin m`, `Fin s → Bool` (0-based, `true` = 1). The scheme is unitary
   until the single final measurement, as in Definition 2.1 (footnote 1 allows the *schemes of
   the proofs* to be described with intermediate measurements; they must be moved to the end). -/
structure CompressionScheme (m n s t : ℕ) where
  /-- The storage scheme `f_S : B(m, n) → {0,1}^s`. -/
  store : B m n → (Fin s → Bool)
  /-- The work register of the query circuit (independent of `x` and of `i`). -/
  W : Type
  /-- The work register is finite. -/
  [instFintypeW : Fintype W]
  /-- The work register has decidable equality. -/
  [instDecEqW : DecidableEq W]
  /-- The number of oracle gates. -/
  T : ℕ
  /-- "At most `t` oracle gates". -/
  T_le : T ≤ t
  /-- The query circuit with the index register set to `i`. -/
  query : Fin m → QAlgorithms.QueryAlg (Fin s) Bool W T
  /-- The classical post-processing of the final computational-basis measurement into `{0,1}`. -/
  out : Fin m → ((Fin s × Bool) × W → Bool)

attribute [instance] CompressionScheme.instFintypeW CompressionScheme.instDecEqW

/-- **Validity of a compression scheme (Definition 2.1, p. 4).** "A compression scheme is valid if
for all `x ∈ {0,1}^m` of Hamming weight at most `n` and all `i ∈ [m]`, the circuit `C` with the
classical register initialized to `i` and all its oracle gates as `O_{f(x)}` yields `x_i` (with
probability 1) as the outcome of the final measurement." -/
def CompressionScheme.Valid {m n s t : ℕ} (S : CompressionScheme m n s t) : Prop :=
  ∀ (x : B m n) (i : Fin m),
    (S.query i).outputProb (QAlgorithms.controlledPhaseOracle (S.store x)) (S.out i) (x.1 i) = 1

end QRetrieval.Adaptive


