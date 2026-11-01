-- Prove2me | Definitions.Def_SelfGuidedALP_InClassR
-- name    : SelfGuidedALP_InClassR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:27:55.724997+00:00
-- url     : https://prove2.me/theorems/0914f4db-27eb-4eee-b8e2-f6e738600857
-- title:
--   The class $\mathcal R$
-- statement:
--   The class $\mathcal R$ consists of the functions on $\mathcal S$ with a representation $V=V(\cdot;(\beta_0,B))$ with $\|B/\rho\|_{2,\rho}<\infty$.
--
--   The hypothesis $V^*\in\mathcal R$ is part of Assumption 2.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_IsRep

namespace SelfGuidedALP

/-- `V` belongs to the class `ℛ` of p.9: it has a representation `V = V(·;𝛃)` with
`‖B/ρ‖_{2,ρ} < ∞` (Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.9). -/
def InClassR {d m : ℕ} (M : MDP d m) (R : RBClass d) (V : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ β₀ B, IsRep M R V β₀ B

end SelfGuidedALP


