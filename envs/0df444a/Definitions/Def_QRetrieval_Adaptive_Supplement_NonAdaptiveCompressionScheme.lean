-- Prove2me | Definitions.Def_QRetrieval_Adaptive_Supplement_NonAdaptiveCompressionScheme
-- name    : QRetrieval_Adaptive_Supplement_NonAdaptiveCompressionScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:58:43.784754+00:00
-- url     : https://prove2.me/theorems/bf8daae8-a6e6-4916-8cb3-ab0b31645e1c
-- title:
--   $(m,n,s,t)$-compression scheme with non-adaptive quantum retrieval, and its validity (Definition 2.1)
-- statement:
--   An **$(m,n,s,t)$-compression scheme with non-adaptive retrieval** $S$ consists of a storage scheme and a query circuit.
--
--   1. The **storage scheme** is a function $f_S:B(m,n)\to\{0,1\}^s$, where $B(m,n)$ is the set of $m$-bit strings of Hamming weight at most $n$.
--   2. The **query circuit** has a classical index register holding $i\in[m]$. For each $i$ it acts on $T$ query registers (each an address in $[s]$ and an oracle qubit) and a finite work register $W$, where $T\le t$ and $W$ are the same for all $i$: an input-independent unit start vector, a unitary $U_0$, **one** application of the product oracle gate $O_y^{\otimes T}\otimes I_W$, and a unitary $U_1$; the start vector and $U_0,U_1$ may depend on $i$ but not on the stored string.
--   3. At the end all registers are measured in the computational basis and a fixed map (depending on $i$) turns the outcome into a bit.
--
--   The scheme is **valid** if for every $x\in B(m,n)$ and every $i\in[m]$, running the circuit for $i$ with the oracle gate for $y=f_S(x)$ outputs $x_i$ **with probability $1$**:
--
--   $$
--   \Pr\bigl[\text{circuit}_i\text{ with }O_{f_S(x)}^{\otimes T}\text{ outputs }x_i\bigr]=1\qquad\text{for all }x\in B(m,n),\ i\in[m].
--   $$
--
--   The paper's quantity $s_{QN}(m,n,t)$ is the least $s$ for which a valid non-adaptive $(m,n,s,t)$-scheme exists. Only the storage map sees $x$; all $t$ probes into $y$ are made in parallel, so no probe can depend on the outcome of another.
--
--   **Formalization Note** The circuit for $i$ is a `QAlgorithms.QueryAlg (Fin T → Fin s) (Fin T → Bool) W 1` (one oracle layer, unitary until a single final measurement), with the oracle `productPhaseOracle T y`. The two-outcome measurement is a computational-basis measurement followed by a classical map; any projective two-outcome measurement reduces to this by folding its change of basis into $U_1$. Classical probes count toward $T$ as well.
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, Definition 2.1, p. 4 (and p. 2, Fig. 1b)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QRetrieval_Adaptive_B
import Definitions.Def_QRetrieval_Adaptive_Supplement_productPhaseOracle

namespace QRetrieval.Adaptive.Supplement

/-- **An `(m, n, s, t)`-compression scheme with non-adaptive quantum retrieval (Definition 2.1).**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, Definition 2.1, p. 4 (and p. 2, Fig. 1b). A scheme `S` consists of

* a storage scheme `f_S : B(m, n) → {0,1}^s` (`store`);
* a query circuit `C_S` with a classical index register `I` carrying `i ∈ [m]`, arbitrary unitaries
  controlled by `I`, and oracle gates `O_y : |j⟩|b⟩ ↦ (−1)^{y_j·b}|j⟩|b⟩`, ending in "a measurement
  at the end that yields an outcome in `{0,1}`". The query scheme is **non-adaptive**: "the query
  circuit is allowed to use a product oracle gate of the form `O_y^{⊗t′}` (for some `t′ ≤ t`), which
  appears exactly once in the circuit".

Here the circuit with `I = i` is the one-oracle-layer query algorithm `query i`
(`QAlgorithms.QueryAlg _ _ W 1`) on `T` address registers `Fin T → Fin s`, `T` oracle qubits
`Fin T → Bool` and a work register `W`: an input-independent unit start vector, a unitary `U_0`, the
product gate `O_y^{⊗T} ⊗ I_W` (`productPhaseOracle T y`) applied exactly once, a unitary `U_1`, and a
computational-basis measurement of all registers followed by the classical map `out i` to `{0,1}`.
The scheme is **valid** (`NonAdaptiveCompressionScheme.Valid`) if for every `x ∈ B(m, n)` and every
`i ∈ [m]`, running `query i` with the product gate for `y = f_S(x)` yields `x_i` with probability
`1`. The paper's `s_QN(m, n, t)` is the least `s` for which a valid such scheme exists.

No field except `store` depends on `x`: the work register, the number `T ≤ t` of parallel queries,
the start vectors, the unitaries and the output maps are fixed before `x` is chosen.

**Formalization Note.**
1. "Unitary operations … controlled by the index register `I`" is one query algorithm per value
   `i` (`query i`), all sharing `W` and `T` (a circuit using fewer queries for some `i` pads them
   with unused registers).
2. The final two-outcome measurement is a computational-basis measurement of the whole register
   followed by a classical map `out i`; any two-outcome projective measurement reduces to this by
   folding its change of basis into `U_1`. The scheme is unitary until that single measurement
   (footnote 1, p. 4, lets the proofs describe schemes with intermediate measurements, which are
   moved to the end).
3. Every probe is one of the `T ≤ t` factors of the product gate; a classical probe is a quantum
   probe whose register is in a basis state, so classical probes are counted too.
4. `[m]`, `{0,1}^s` are `Fin m`, `Fin s → Bool` (0-based, `true` = 1). -/
structure NonAdaptiveCompressionScheme (m n s t : ℕ) where
  /-- The storage scheme `f_S : B(m, n) → {0,1}^s`. -/
  store : B m n → (Fin s → Bool)
  /-- The work register of the query circuit (independent of `x` and of `i`). -/
  W : Type
  /-- The work register is finite. -/
  [instFintypeW : Fintype W]
  /-- The work register has decidable equality. -/
  [instDecEqW : DecidableEq W]
  /-- The number `t′` of parallel queries, the arity of the product oracle gate `O_y^{⊗t′}`. -/
  T : ℕ
  /-- "for some `t′ ≤ t`". -/
  T_le : T ≤ t
  /-- The query circuit with the index register set to `i`: one application of the product gate
  between two input-independent unitaries. -/
  query : Fin m → QAlgorithms.QueryAlg (Fin T → Fin s) (Fin T → Bool) W 1
  /-- The classical post-processing of the final computational-basis measurement into `{0,1}`. -/
  out : Fin m → (((Fin T → Fin s) × (Fin T → Bool)) × W → Bool)

attribute [instance] NonAdaptiveCompressionScheme.instFintypeW
  NonAdaptiveCompressionScheme.instDecEqW

/-- **Validity of a non-adaptive compression scheme (Definition 2.1, p. 4).** "A compression scheme
is valid if for all `x ∈ {0,1}^m` of Hamming weight at most `n` and all `i ∈ [m]`, the circuit `C`
with the classical register initialized to `i` and all its oracle gates as `O_{f(x)}` yields `x_i`
(with probability 1) as the outcome of the final measurement." -/
def NonAdaptiveCompressionScheme.Valid {m n s t : ℕ} (S : NonAdaptiveCompressionScheme m n s t) :
    Prop :=
  ∀ (x : B m n) (i : Fin m),
    (S.query i).outputProb (productPhaseOracle S.T (S.store x)) (S.out i) (x.1 i) = 1

end QRetrieval.Adaptive.Supplement


