-- Prove2me | Definitions.Def_GraphNNSphere_unif
-- name    : GraphNNSphere_unif
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:20.230507+00:00
-- url     : https://prove2.me/theorems/0d9c9561-4b81-4a8f-bb14-bc208961219c
-- title:
--   Normalized surface measure $\sigma_{d-1}$
-- statement:
--   The normalized surface measure $\sigma_{d-1}$ on $S^{d-1}$, the rotation-invariant probability measure. The data are drawn from it, and it is the default query law.
--
--   **Formalization Note** It is the published `OAI.NoiselessRegression.sphereLaw` at $E=\mathbb R^d$, the normalization of the surface measure induced by volume. For $d=0$ the sphere is empty and the measure is zero; for $d\ge 1$ it is a probability measure. The module records the finiteness instance that the product law of the sample needs.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2

import Mathlib
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_GraphNNSphere_Sph

open MeasureTheory

namespace GraphNNSphere

/-- Normalized surface measure `σ_{d-1}` on `S^{d-1}` (Lu, *Sharp Limits of Graph-Based Nearest
Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2).

**Formalization Note** This is the published `OAI.NoiselessRegression.sphereLaw` at
`E = EuclideanSpace ℝ (Fin d)`, the normalization of `Measure.toSphere volume`. It is the zero
measure for `d = 0`, where the sphere is empty, and a probability measure for `d ≥ 1`. -/
noncomputable def unif (d : ℕ) : Measure (Sph d) :=
  OAI.NoiselessRegression.sphereLaw (E := EuclideanSpace ℝ (Fin d))

instance (d : ℕ) : IsFiniteMeasure (unif d) := by
  refine ⟨?_⟩
  simp only [unif, OAI.NoiselessRegression.sphereLaw, Measure.smul_apply, smul_eq_mul]
  exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) ENNReal.one_lt_top

end GraphNNSphere


