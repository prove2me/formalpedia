-- Prove2me | Definitions.Def_D1Bound5_SquareTest_Definitions
-- name    : D1Bound5_SquareTest_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:51:02.030007+00:00
-- url     : https://prove2.me/theorems/23fbfbe5-e5bf-4178-bc40-c6575992421b
-- title:
--   Square Test
-- statement:
--   Exact candidate produced by three integer square roots and integer arithmetic. Every candidate is checked by multiplication before acceptance. The named objects in this bundle include `QuadInt.rootCandidate`, `QuadInt.squareRoot`, `QuadInt.hasSquareRoot`.
-- source:
--   D1Bound5/SquareTest.lean, lines 43-51, SHA-256 adcc13a33378056841f44d21785e69909232e4def68eb73ca742e5a49ce15ac3; D1Bound5/SquareTest.lean, lines 53-56, SHA-256 adcc13a33378056841f44d21785e69909232e4def68eb73ca742e5a49ce15ac3; D1Bound5/SquareTest.lean, lines 114-115, SHA-256 adcc13a33378056841f44d21785e69909232e4def68eb73ca742e5a49ce15ac3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}





/-- Exact candidate produced by three integer square roots and integer
arithmetic. Every candidate is checked by multiplication before acceptance. -/
def rootCandidate (z : QuadInt tau nu) : QuadInt tau nu :=
  let n := Int.sqrt z.norm
  let p := 2*z.re+tau*z.im
  let e := Int.sqrt (2*n+p)
  let f0 := Int.sqrt ((2*n-p)/discriminant tau nu)
  let f := if z.im < 0 then -f0 else f0
  ⟨(e-tau*f)/2,f⟩

/-- Deterministic square-root procedure, including zero. -/
def squareRoot (z : QuadInt tau nu) : Option (QuadInt tau nu) :=
  let r := rootCandidate z
  if r*r = z then some r else none







/-- The computable predicate used by later finite certificates. -/
def hasSquareRoot (z : QuadInt tau nu) : Bool := (squareRoot z).isSome









end D1Bound5.QuadInt
end


