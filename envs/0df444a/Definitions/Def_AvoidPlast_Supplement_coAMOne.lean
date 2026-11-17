-- Prove2me | Definitions.Def_AvoidPlast_Supplement_coAMOne
-- name    : AvoidPlast_Supplement_coAMOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T16:40:20.420975+00:00
-- url     : https://prove2.me/theorems/8bd172cf-b502-44e5-af7b-1f4789aef36a
-- title:
--   Acceptance of a coAM procedure (Definition 7.4)
-- statement:
--   For a coAM procedure with deterministic verifier $D(x,y,\rho,w)$, $D(x,y)=1$ iff
--   $$\Pr_{\rho\in\{0,1\}^{r_D(n)}}\bigl[\exists w\in\{0,1\}^{w_D(n)}: D(x,y,\rho,w)=0\bigr]\le1/3,\qquad n=|x|.$$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 7.4, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_prob

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `D(x, y) = 1` for a coAM procedure (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 7.4, p.41): over the coins
`ρ ∈ {0,1}^{r_D(n)}`, `Pr_ρ[∃ w ∈ {0,1}^{w_D(n)} : D(x, y, ρ, w) = 0] ≤ 1/3`, where `n = |x|` and
`D(x, y, ρ, w) = 0` means that the deterministic verifier does not accept. -/
def coAMOne (D : Machine 4) (rD wD : ℕ → ℕ) (x y : List Bool) : Prop :=
  prob (rD x.length) (fun ρ => ∃ w : List Bool, w.length = wD x.length ∧ ¬ Accepts D ![x, y, ρ, w])
    ≤ 1 / 3

end AvoidPlast.Supplement


