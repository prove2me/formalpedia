-- Prove2me | Definitions.Def_AvoidPlast_Supplement_AvoidHardDet
-- name    : AvoidPlast_Supplement_AvoidHardDet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:58:54.161632+00:00
-- url     : https://prove2.me/theorems/783f7b5d-4ea1-49ab-909e-4372fe38b335
-- title:
--   Avoid is hard for deterministic polynomial time with success $p$
-- statement:
--   For every deterministic polynomial-time $A$ and every sufficiently large $n$, $\Pr_{x\sim\mu_n}[A(x)\text{ solves }\mathrm{Avoid}(C_x)]<p(n)$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 5.1, 5.4 ("Moreover"), pp.21, 23

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_PolyTime
import Definitions.Def_AvoidPlast_SolvesAvoid
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Supplement_pr

namespace AvoidPlast.Supplement

open AvoidPlast

/-- "`Avoid_C` cannot be solved by any polynomial-time algorithm with success `p` or more over
`μ`" (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 5.1, 5.4, the "Moreover" parts, pp.21, 23): for every deterministic
polynomial-time `A` and every sufficiently large `n`, `Pr_{x∼μ_n}[A(x) solves Avoid(C_x)] < p(n)`. -/
def AvoidHardDet (μ : ℕ → PMF (List Bool)) (C : List Bool → List Bool → List Bool)
    (ℓin ℓout : ℕ → ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ A : Machine 1, PolyTime A → ∀ᶠ n : ℕ in Filter.atTop,
    pr (μ n) (fun x => SolvesAvoid C ℓin ℓout x (output A ![x])) < p n

end AvoidPlast.Supplement


