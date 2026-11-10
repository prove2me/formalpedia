-- Prove2me | Definitions.Def_AgnosticImitate_Reduction_Oracle
-- name    : AgnosticImitate_Reduction_Oracle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:23:59.729492+00:00
-- url     : https://prove2.me/theorems/4a5791b9-624b-451c-a8fb-9a90df677ab8
-- title:
--   Pointwise oracle reductions, adaptive adversarial oracles and failure probability
-- statement:
--   The oracle model of Theorem 1.1 (p. 2, PDF 4: "only accesses the data distribution via … calls") and Theorem 4.1 (p. 22, PDF 24: queries and output are "pointwise functions of the oracle responses received so far"). A transcript is a sequence of answers $r_0,r_1,\dots:X\to\mathbb R$.
--
--   - **Oracle reduction** (`OracleReduction N`): $N$ calls given by maps fixed in advance, independent of $X$, $\mu$, $C$ and $g$. Call $k$ submits the query $(m_k,p'_k)$ with $m_k(x)=\texttt{mq}_k(r_0(x),\dots,r_{k-1}(x))$ and $p'_k(x)=\texttt{pq}_k(r_0(x),\dots,r_{k-1}(x))$; the output is $p(x)=\texttt{out}(r_0(x),\dots,r_{N-1}(x))$ (`weight`, `base`, `output`). `IsAdmissible`: the maps are Borel measurable, $m_k\in[0,1]$ and $p'_k,p\in[-1,1]$ whenever the answers lie in $[-1,1]$.
--   - **Correct answer** (`CallValid`): the answer $r_k$ is a predictor that is $(C,\varepsilon')$-multiaccurate for the labeled distribution with label mean $m_k g+(1-m_k)p'_k$. The label mean $g$ enters only here, so the reduction sees the data only through the oracle. A guarantee for every transcript of correct answers is a guarantee against every adaptive adversarial oracle.
--   - **Randomized oracle** (`RandOracle`, `run`): with seed space $(\Omega,P)$ and independent seeds $\omega\in\Omega^N$, the $k$-th answer is any function of the seeds of calls $0,\dots,k-1$ and its own fresh seed $\omega_k$.
--   - **Per-call failure bound** (`CallFailureBound N P δ valid`): for every call $k<N$, its failure set is measurable, and for every fixed choice of the other seeds the fresh seeds $s$ with which call $k$ is answered incorrectly have $P$-measure at most $\delta$.
--   - **Failure probability** (`failureProb`): the product measure $P^{\otimes N}$ of the seed vectors on which a stated guarantee fails.
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Theorem 1.1 (p. 2, PDF 4), §1.3 (pp. 5–6, PDF 7–8), Theorem 4.1 (p. 22, PDF 24)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Setting

noncomputable section
open MeasureTheory Classical

namespace AgnosticImitate.Reduction

/-! # Oracle reductions, adversarial adaptive oracles and failure probability

Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), *Agnostic Learning by
Imitating*, Theorem 1.1 (p. 2, PDF 4: "only accesses the data distribution via … calls"),
§1.3 (pp. 5–6, PDF 7–8) and Theorem 4.1 (p. 22, PDF 24: "queries and final output are
restricted to be pointwise functions of the oracle responses received so far").

A transcript of oracle answers is a sequence `r : ℕ → X → ℝ` (call `k` is answered by `r k`;
only the first `N` entries matter). -/

variable {X : Type*} [MeasurableSpace X]

/-- A pointwise oracle reduction with `N` calls to a multiaccuracy oracle. It is a list of maps on
answer values, fixed before the feature space, the feature distribution, the class and the
labels. Call `k` (`k = 0, …, N-1`) submits the query `(m_k, p'_k)` with
`m_k(x) = mq k (r_0(x), …, r_{k-1}(x))` and `p'_k(x) = pq k (r_0(x), …, r_{k-1}(x))`; the
output is `p(x) = out (r_0(x), …, r_{N-1}(x))`. -/
structure OracleReduction (N : ℕ) where
  /-- reweighting measure of call `k` as a function of the earlier answers' values -/
  mq : (k : ℕ) → (Fin k → ℝ) → ℝ
  /-- label-replacement predictor of call `k` as a function of the earlier answers' values -/
  pq : (k : ℕ) → (Fin k → ℝ) → ℝ
  /-- the output as a function of all `N` answers' values -/
  out : (Fin N → ℝ) → ℝ

/-- Well-formedness of a reduction: its maps are Borel measurable, the reweighting `m_k` takes
values in `[0, 1]`, and the replacement `p'_k` and the output take values in `[-1, 1]` whenever
the answers do. -/
structure OracleReduction.IsAdmissible {N : ℕ} (R : OracleReduction N) : Prop where
  measurable_mq : ∀ k, Measurable (R.mq k)
  measurable_pq : ∀ k, Measurable (R.pq k)
  measurable_out : Measurable R.out
  mq_mem : ∀ k (v : Fin k → ℝ), (∀ j, v j ∈ Set.Icc (-1 : ℝ) 1) →
    R.mq k v ∈ Set.Icc (0 : ℝ) 1
  pq_mem : ∀ k (v : Fin k → ℝ), (∀ j, v j ∈ Set.Icc (-1 : ℝ) 1) →
    R.pq k v ∈ Set.Icc (-1 : ℝ) 1
  out_mem : ∀ v : Fin N → ℝ, (∀ j, v j ∈ Set.Icc (-1 : ℝ) 1) →
    R.out v ∈ Set.Icc (-1 : ℝ) 1

/-- The reweighting measure `m_k : X → [0, 1]` of call `k` given the transcript. -/
def OracleReduction.weight {N : ℕ} (R : OracleReduction N) (r : ℕ → X → ℝ) (k : ℕ) : X → ℝ :=
  fun x => R.mq k (fun j : Fin k => r j x)

/-- The label-replacement predictor `p'_k : X → [±1]` of call `k` given the transcript. -/
def OracleReduction.base {N : ℕ} (R : OracleReduction N) (r : ℕ → X → ℝ) (k : ℕ) : X → ℝ :=
  fun x => R.pq k (fun j : Fin k => r j x)

/-- The predictor output by the reduction on the transcript `r`. -/
def OracleReduction.output {N : ℕ} (R : OracleReduction N) (r : ℕ → X → ℝ) : X → ℝ :=
  fun x => R.out (fun j : Fin N => r j x)

/-- Call `k` of the transcript is answered correctly by a `(C, ε')`-multiaccuracy oracle for the
feature distribution `μ`: the answer is a predictor that is `(C, ε')`-multiaccurate for the
labeled distribution with marginal `μ` and label mean `m_k · g + (1 - m_k) · p'_k`, where the
query `(m_k, p'_k)` is computed from the earlier answers. The label mean `g` enters only here. -/
def OracleReduction.CallValid {N : ℕ} (R : OracleReduction N) (μ : Measure X) (C : Set (X → ℝ))
    (g : X → ℝ) (ε' : ℝ) (k : ℕ) (r : ℕ → X → ℝ) : Prop :=
  IsPredictor (r k) ∧ IsMultiaccurate μ C (queryMean g (R.weight r k) (R.base r k)) (r k) ε'

/-- A randomized adaptive (adversarial) oracle on a seed space `Ω`: the answer to call `k` is any
function of the seeds of the earlier calls (hence of the whole earlier history) and of its own
fresh seed. -/
def RandOracle (Ω : Type*) (X : Type*) : Type _ :=
  (k : ℕ) → (Fin k → Ω) → Ω → X → ℝ

/-- The transcript produced by a randomized oracle over `N` calls with independent seeds
`ω : Fin N → Ω` (entries from index `N` on are `0`). -/
def RandOracle.run {Ω : Type*} {N : ℕ} (ans : RandOracle Ω X) (ω : Fin N → Ω) : ℕ → X → ℝ :=
  fun k => if h : k < N then ans k (fun j => ω ⟨j.1, j.2.trans h⟩) (ω ⟨k, h⟩) else 0

/-- "Each call fails with probability at most `δ`": for every call `k < N` and every fixed
choice of the other seeds (in particular of the earlier ones, which determine the history and
the query), the set of fresh seeds `s` for which call `k` is not answered correctly has
`P`-measure at most `δ`. The failure event of each call is measurable (an event). `valid k r`
says that call `k` of transcript `r` is answered correctly. -/
def CallFailureBound {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (P : Measure Ω) (δ : ℝ)
    (valid : ℕ → (ℕ → X → ℝ) → Prop) (ans : RandOracle Ω X) : Prop :=
  ∀ k (hk : k < N),
    MeasurableSet {ω : Fin N → Ω | ¬ valid k (ans.run ω)} ∧
    ∀ ω₀ : Fin N → Ω,
      P {s : Ω | ¬ valid k (ans.run (Function.update ω₀ ⟨k, hk⟩ s))} ≤ ENNReal.ofReal δ

/-- The failure probability of an `N`-call procedure whose guarantee on a transcript is `good`:
the product measure of the seed vectors on which the guarantee fails. -/
def failureProb {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (P : Measure Ω) (ans : RandOracle Ω X)
    (good : (ℕ → X → ℝ) → Prop) : ENNReal :=
  Measure.pi (fun _ : Fin N => P) {ω : Fin N → Ω | ¬ good (ans.run ω)}

end AgnosticImitate.Reduction


