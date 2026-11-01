-- Prove2me | Definitions.Def_SelfGuidedALP_felpObjective
-- name    : SelfGuidedALP_felpObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:48.116411+00:00
-- url     : https://prove2.me/theorems/d5b68f87-4fea-41e3-ae75-3877f50062ed
-- title:
--   The FELP objective
-- statement:
--   The objective of FELP is
--   $$
--   \beta_0+\int_\Theta B(\theta)\,\mathbb E_\nu[\varphi(s;\theta)]\,\mathrm d\theta .
--   $$
--   It is the $\nu$-average of $V(\cdot;(\beta_0,B))$.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, FELP, p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_Bspace
import Definitions.Def_SelfGuidedALP_feat

open MeasureTheory

namespace SelfGuidedALP

/-- The FELP objective `β₀ + ∫_Θ B(θ) E_ν[ϕ(s;θ)] dθ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, FELP, p.9). -/
noncomputable def felpObjective {d : ℕ} (R : RBClass d) (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (β₀ : ℝ) (B : Bspace R) : ℝ :=
  β₀ + ∫ θ in R.Θ, B θ * ∫ s, feat R.ϕ θ s ∂ν

end SelfGuidedALP


