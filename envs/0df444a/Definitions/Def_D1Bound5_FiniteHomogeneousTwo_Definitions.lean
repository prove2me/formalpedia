-- Prove2me | Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
-- name    : D1Bound5_FiniteHomogeneousTwo_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:26:23.126599+00:00
-- url     : https://prove2.me/theorems/9862c1a9-3e2e-4ce2-b0ef-ad43b61791b3
-- title:
--   Finite Homogeneous Two
-- statement:
--   An explicit integer homogeneous polynomial in two anchors. The named objects in this bundle include `finiteHomogeneousTwo`.
-- source:
--   D1Bound5/FiniteHomogeneousTwo.lean, lines 10-13, SHA-256 0f528bdfa4bbe6e6461cbf40c954a5b8c6a03faf9be9e291dd140696bc0e3dfa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- An explicit integer homogeneous polynomial in two anchors. -/
def finiteHomogeneousTwo {R : Type*} [CommRing R]
    (n : ℕ) (v : Fin (n+1) → ℤ) (x y : R) : R :=
  ∑ j, (v j : R)*x^(j : ℕ)*y^(n-(j : ℕ))





end D1Bound5
end


