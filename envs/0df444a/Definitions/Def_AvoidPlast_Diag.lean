-- Prove2me | Definitions.Def_AvoidPlast_Diag
-- name    : AvoidPlast_Diag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:48:34.168872+00:00
-- url     : https://prove2.me/theorems/4e4506c7-016a-4197-bd90-5fa0a7432005
-- title:
--   The diagonalization problem Diag$_\varepsilon$
-- statement:
--   The low-space diagonalization problem:
--
--   $$\mathrm{Diag}_\varepsilon(x)=\{y\in\{0,1\}^n:\forall d\in\{0,1\}^{m_\varepsilon(n)},\ y\ne U_\varepsilon(x,d)\}.$$
--
--   It asks for a string that differs from the output on $x$ of every low-space machine.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 5.13, p.29

import Mathlib
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_U

namespace AvoidPlast

/-- The diagonalization problem (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 5.13, p.29):
`Diag_ε(x) = {y ∈ {0,1}^n : ∀ d ∈ {0,1}^{m_ε(n)}, y ≠ U_ε(x, d)}`. -/
def Diag (ε : ℝ) (x : List Bool) : Set (List Bool) :=
  {y | y.length = x.length ∧
    ∀ d : List Bool, d.length = ceilPow (ε ^ 2) x.length → y ≠ U ε x d}

end AvoidPlast


