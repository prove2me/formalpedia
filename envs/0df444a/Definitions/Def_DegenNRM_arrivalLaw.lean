-- Prove2me | Definitions.Def_DegenNRM_arrivalLaw
-- name    : DegenNRM_arrivalLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:54.728292+00:00
-- url     : https://prove2.me/theorems/89ce6dcc-327e-4af4-a3b2-592d38801af1
-- title:
--   The arrival law $F(\cdot)$, the law of a sample path, and type counts
-- statement:
--   An arrival is a pair $(j,r)$ of a type and a reward. Its law is the mixture
--   $$F=\sum_{j=1}^n p_j\,(\delta_j\otimes F_j)$$
--   on $[n]\times\mathbb R$: the type is $j$ with probability $p_j$, and given the type the reward has law $F_j$. A sample path $I=\{(\tilde r_t,\tilde a_t)\}_{t=1}^T$ of $T$ periods has the product law $F^{\otimes T}$, so the arrivals are independent and identically distributed.
--
--   For a sample path, $\tilde d_j$ denotes the number of its periods whose query is of type $j$.
--
--   The module also proves that $F$ is a probability measure.
--
--   **Formalization Note** A path of $T$ periods is a function `Fin T → Fin n × ℝ`; period $t\in[T]$ is the coordinate $t-1$.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, §2, pp.6–7, (3); §3.2, pp.12–13

import Mathlib
import Definitions.Def_DegenNRM_Instance

open MeasureTheory

namespace DegenNRM

/-- **The law `F(·)` of one arrival** (Jiang, Ma & Zhang, arXiv:2210.07996v5, §2, p.6).

An arrival is a pair `(j, r)` of a type `j` and a reward `r`: the type is `j` with probability
`p_j`, and given the type the reward has law `F_j`. So the law of an arrival is the mixture
`Σⱼ p_j · (δ_j ⊗ F_j)` on `Fin n × ℝ`. The query's size is `ã = a_j`.

**Formalization Note.** The type is recorded together with the reward (reading R3 of the
mission: the policy observes `j_t`). -/
noncomputable def arrivalLaw {m n : ℕ} (inst : Instance m n) : Measure (Fin n × ℝ) :=
  ∑ j, (inst.p j).toNNReal • (Measure.dirac j).prod (inst.F j)

instance {m n : ℕ} (inst : Instance m n) : IsProbabilityMeasure (arrivalLaw inst) := by
  constructor
  have h1 : ∑ j, (inst.p j).toNNReal = 1 := by
    rw [← NNReal.coe_inj, NNReal.coe_sum]
    simp only [Real.coe_toNNReal _ (inst.p_pos _).le, NNReal.coe_one]
    exact inst.p_sum
  simp only [arrivalLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    ← Set.univ_prod_univ, Measure.prod_prod, measure_univ, mul_one, ENNReal.smul_def,
    smul_eq_mul]
  rw [← ENNReal.ofNNReal_finsetSum, h1, ENNReal.coe_one]

/-- **The law of a sample path `I = {(r̃_t, ã_t)}_{t=1}^T`** (arXiv:2210.07996v5, (3), pp.6–7:
"(r̃_t, ã_t) follows distribution F(·) independently for each t ∈ [T]").

A sample path of `T` periods is `ω : Fin T → Fin n × ℝ`, period `t ∈ [T]` being the coordinate
`t - 1`, and its law is the product of `T` copies of `arrivalLaw`. -/
noncomputable def pathLaw {m n : ℕ} (inst : Instance m n) (T : ℕ) : Measure (Fin T → Fin n × ℝ) :=
  Measure.pi fun _ : Fin T => arrivalLaw inst

/-- **The type counts of a sample path**: `typeCount ω j` is the number of periods of `ω` whose
query is of type `j` (the `d̃_{j,t}` of §3.2, p.12–13, for the periods that `ω` covers). -/
def typeCount {n k : ℕ} (ω : Fin k → Fin n × ℝ) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun t => (ω t).1 = j).card

end DegenNRM


