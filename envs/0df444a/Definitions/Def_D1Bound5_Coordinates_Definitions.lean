-- Prove2me | Definitions.Def_D1Bound5_Coordinates_Definitions
-- name    : D1Bound5_Coordinates_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:50:30.130814+00:00
-- url     : https://prove2.me/theorems/aec7688b-f800-4982-a9a8-7d8acfbeba79
-- title:
--   Coordinates
-- statement:
--   Coordinates x+y*omega with omega^2=tau*omega-nu. Both tau=0 and tau=1 are included. Identification with the full ring of integers is a separate obligation, not part of this definition. The named objects in this bundle include `QuadInt`, `QuadInt.discriminant`.
-- source:
--   D1Bound5/Coordinates.lean, lines 6-9, SHA-256 da0cb0c42a6044e813dcdaaa1831735e6baddba8fa16b037f5289e53bcfae065; D1Bound5/Coordinates.lean, lines 15-15, SHA-256 da0cb0c42a6044e813dcdaaa1831735e6baddba8fa16b037f5289e53bcfae065. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith

section
namespace D1Bound5

/-- Coordinates x+y*omega with omega^2=tau*omega-nu.
Both tau=0 and tau=1 are included. Identification with the full ring of
integers is a separate obligation, not part of this definition. -/
abbrev QuadInt (tau nu : ℤ) := QuadraticAlgebra ℤ (-nu) tau

namespace QuadInt

variable {tau nu : ℤ}

def discriminant (tau nu : ℤ) : ℤ := 4*nu-tau^2















end QuadInt
end D1Bound5
end


