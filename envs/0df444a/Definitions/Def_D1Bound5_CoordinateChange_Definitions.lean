-- Prove2me | Definitions.Def_D1Bound5_CoordinateChange_Definitions
-- name    : D1Bound5_CoordinateChange_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:27.464997+00:00
-- url     : https://prove2.me/theorems/26e17b54-ba39-49ce-9a02-3a824627d5b0
-- title:
--   Coordinate Change
-- statement:
--   Sending the new generator to omega-k changes its trace by 2k. This is an isomorphism of the entire coordinate ring. The named objects in this bundle include `QuadInt.shift`.
-- source:
--   D1Bound5/CoordinateChange.lean, lines 5-14, SHA-256 9b6bb34c1875a40d3412565a34153ddaa67227fb9054d869e7926e05c690437d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5.QuadInt

/-- Sending the new generator to omega-k changes its trace by 2k.
This is an isomorphism of the entire coordinate ring. -/
def shift (tau nu k : ℤ) :
    QuadInt (tau-2*k) (nu-tau*k+k^2) ≃+* QuadInt tau nu where
  toFun z := ⟨z.re-k*z.im,z.im⟩
  invFun z := ⟨z.re+k*z.im,z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp; ring
  map_mul' z w := by ext <;> simp <;> ring



end D1Bound5.QuadInt
end


