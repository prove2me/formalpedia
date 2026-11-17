-- Prove2me | Definitions.Def_AvoidPlast_Supplement_inRangeDemi
-- name    : AvoidPlast_Supplement_inRangeDemi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:05:16.123289+00:00
-- url     : https://prove2.me/theorems/7cf2f5ec-9886-489f-8d6d-eeabfb34a54f
-- title:
--   $y\in\mathrm{Range}(C_s)$
-- statement:
--   $y$ is an output of $C_s$ on some input of $n-\lambda(n)+\lceil\log t(n)\rceil$ bits.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 6.5, 6.6, pp.34–35

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_demiCs

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `y ∈ Range(C_s)` for the circuit `demiCs` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 6.5, 6.6, pp.34–35): some input
`(x, i)` of `n - λ(n) + ⌈log t(n)⌉` bits has `C_s(x, i) = y`. -/
def inRangeDemi (g : ℕ → List Bool → List Bool) (lam t : ℕ → ℕ) (n : ℕ) (s y : List Bool) : Prop :=
  ∃ z : List Bool, z.length = n - lam n + Nat.clog 2 (t n) ∧ demiCs g lam t n s z = y

end AvoidPlast.Supplement


