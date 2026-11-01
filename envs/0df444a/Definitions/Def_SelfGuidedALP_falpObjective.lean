-- Prove2me | Definitions.Def_SelfGuidedALP_falpObjective
-- name    : SelfGuidedALP_falpObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:44.53018+00:00
-- url     : https://prove2.me/theorems/b00969c5-9577-4ce3-8888-7b86f57f3d87
-- title:
--   The objective of $\mathrm{FALP}_n$ and $\mathrm{FALP}^{\mathrm{SG}}_n$
-- statement:
--   The objective of the sampled programs is
--   $$
--   \beta_0+\sum_{i=1}^n\beta_i\,\mathbb E_\nu[\varphi(s;\theta^i)].
--   $$
--   It is the $\nu$-average of $V(\cdot;\beta)$.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, pp.10 and 16

import Mathlib
import Definitions.Def_SelfGuidedALP_RBClass
import Definitions.Def_SelfGuidedALP_feat

open MeasureTheory

namespace SelfGuidedALP

/-- The objective `β₀ + ∑ᵢ βᵢ E_ν[ϕ(s;θⁱ)]` of `FALP_n` and `FALP^SG_n`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, pp.10 and 16). -/
noncomputable def falpObjective {d n : ℕ} (R : RBClass d) (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (θs : Fin n → EuclideanSpace ℝ (Fin (d + 1))) (β : Fin (n + 1) → ℝ) : ℝ :=
  β 0 + ∑ i, β i.succ * ∫ s, feat R.ϕ (θs i) s ∂ν

end SelfGuidedALP


