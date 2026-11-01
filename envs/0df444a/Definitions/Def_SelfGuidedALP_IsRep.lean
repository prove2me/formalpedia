-- Prove2me | Definitions.Def_SelfGuidedALP_IsRep
-- name    : SelfGuidedALP_IsRep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:43.009567+00:00
-- url     : https://prove2.me/theorems/5c335d30-6234-401a-ba24-f2d04069843f
-- title:
--   A representation $V=V(\cdot;\boldsymbol\beta)$ on $\mathcal S$
-- statement:
--   A pair $(\beta_0,B)$ with $B\in\mathcal B$ **represents** $V$ when $V(s)=V(s;(\beta_0,B))$ for all $s\in\mathcal S$.
--
--   The goal is stated for every representation $(\beta_0^*,B^*)$ of $V^*$.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_MDP
import Definitions.Def_SelfGuidedALP_intVFA

namespace SelfGuidedALP

/-- `(β₀, B)` with `B ∈ ℬ` represents `V` on `𝒮`: `V(s) = V(s;𝛃)` for all `s ∈ 𝒮`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.9). -/
def IsRep {d m : ℕ} (M : MDP d m) (R : RBClass d) (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (β₀ : ℝ) (B : Bspace R) : Prop :=
  ∀ s ∈ M.S, V s = intVFA R β₀ B s

end SelfGuidedALP


