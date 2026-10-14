-- Prove2me | Definitions.Def_SoftRobust_Duality_Mixture
-- name    : SoftRobust_Duality_Mixture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T18:47:08.644086+00:00
-- url     : https://prove2.me/theorems/3709a008-c827-4916-b5fe-a8e6b1e04a9a
-- title:
--   Mixture $t\mathbb Q_1 + (1-t)\mathbb Q_2$ of two probability measures (endnote 3)
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space and let $\mathcal P$ be the set of all probability measures on it. For a weight $t \in [0,1]$ and $\mathbb Q_1, \mathbb Q_2 \in \mathcal P$, the **mixture** $t\mathbb Q_1 + (1-t)\mathbb Q_2$ is the probability measure
--
--   $$
--   \big(t\mathbb Q_1 + (1-t)\mathbb Q_2\big)(A) = t\,\mathbb Q_1(A) + (1-t)\,\mathbb Q_2(A), \qquad A \in \mathcal F .
--   $$
--
--   It is again a probability measure, since its total mass is $t + (1-t) = 1$. This is the convex combination of measures that appears in the definition of a convex family of measures (endnote 3 of the paper) and of a convex penalty function on $\mathcal P$.
--
--   **Formalization Note** The weight is a nonnegative real `t : ℝ≥0` together with a proof of `t ≤ 1`; the weight $1-t$ is the truncated subtraction in `ℝ≥0`, which equals $1-t$ under that proof. A `simp` lemma records the underlying measure.
-- source:
--   Ben-Tal, Bertsimas, Brown, A Soft Robust Model for Optimization Under Ambiguity, Oper. Res. 58(4) (2010), p. 1234, endnote 3 (the mixture λℚ₁ + (1 − λ)ℚ₂)

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace SoftRobust.Duality

/-- The mixture `t ℚ₁ + (1 - t) ℚ₂` of two probability measures on a measurable space `(Ω, ℱ)`,
for a weight `t ∈ [0, 1]` (given as `t : ℝ≥0` with `t ≤ 1`). This is the convex combination of
measures used in endnote 3 of Ben-Tal, Bertsimas, Brown, *A Soft Robust Model for Optimization Under
Ambiguity*, Oper. Res. 58(4) (2010), p. 1234: `λℚ₁ + (1 − λ)ℚ₂`, i.e. the measure
`A ↦ t ℚ₁(A) + (1 − t) ℚ₂(A)`. -/
noncomputable def mix {Ω : Type*} [MeasurableSpace Ω] (t : ℝ≥0) (ht : t ≤ 1)
    (Q₁ Q₂ : ProbabilityMeasure Ω) : ProbabilityMeasure Ω :=
  ⟨(t : ℝ≥0∞) • (Q₁ : Measure Ω) + ((1 - t : ℝ≥0) : ℝ≥0∞) • (Q₂ : Measure Ω), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le ht, ENNReal.coe_one]⟩

/-- The underlying measure of `mix t ht ℚ₁ ℚ₂` is `t • ℚ₁ + (1 - t) • ℚ₂`. -/
@[simp] lemma coe_mix {Ω : Type*} [MeasurableSpace Ω] (t : ℝ≥0) (ht : t ≤ 1)
    (Q₁ Q₂ : ProbabilityMeasure Ω) :
    ((mix t ht Q₁ Q₂ : ProbabilityMeasure Ω) : Measure Ω) =
      (t : ℝ≥0∞) • (Q₁ : Measure Ω) + ((1 - t : ℝ≥0) : ℝ≥0∞) • (Q₂ : Measure Ω) := rfl

end SoftRobust.Duality


