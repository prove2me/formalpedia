-- Prove2me | Definitions.Def_D1Bound5_PairGraphNoThreeTransfer_Definitions
-- name    : D1Bound5_PairGraphNoThreeTransfer_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:54:21.24142+00:00
-- url     : https://prove2.me/theorems/9ef2804a-feb8-49c4-a154-d0ebf6682da8
-- title:
--   Pair Graph No Three Transfer
-- statement:
--   This certificate is linear in the number of vertices. It checks the actual trace coordinate for every occurrence, including zero if present. The named objects in this bundle include `pairAllTraceZeroBool`.
-- source:
--   D1Bound5/PairGraphNoThreeTransfer.lean, lines 47-50, SHA-256 10b2bdca2160b3f93442ff75882d77cb4a22b0c8e74c0b3b0b8565bc741f9adb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt



/-- This certificate is linear in the number of vertices. It checks the
actual trace coordinate for every occurrence, including zero if present. -/
def pairAllTraceZeroBool {tau nu : ℤ} (vertices : List (QuadInt tau nu)) : Bool :=
  vertices.all fun z => decide (2*z.re+tau*z.im = 0)



end D1Bound5
end


