-- Prove2me | Definitions.Def_AvoidPlast_SolvesAvoid
-- name    : AvoidPlast_SolvesAvoid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:13.481578+00:00
-- url     : https://prove2.me/theorems/45f79001-00bf-4792-b764-edb0e5a2accb
-- title:
--   Solutions of Avoid$_C$
-- statement:
--   A string $y$ **solves Avoid$_C$** on input $x$ if $y\in\{0,1\}^{\ell_{out}(|x|)}$ and $y\notin\mathrm{Range}(C_x)$, the range being over inputs of length $\ell_{in}(|x|)$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 3.12, p.16

import Mathlib

namespace AvoidPlast

/-- `y` solves `Avoid_C` on input `x` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 3.12, p.16): `y ∈ {0,1}^{ℓout(n)}` and
`y ∉ Range(C_x)`. -/
def SolvesAvoid (C : List Bool → List Bool → List Bool) (ℓin ℓout : ℕ → ℕ) (x y : List Bool) :
    Prop :=
  y.length = ℓout x.length ∧ ∀ z : List Bool, z.length = ℓin x.length → C x z ≠ y

end AvoidPlast


