-- Prove2me | solution 2 for APFPaper5.K2.opposite_sides_cancel
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:38:08.987193+00:00
-- url     : https://prove2.me/submissions/1301c93d-f715-423f-b965-0067e1c7acf3

import Definitions.Def_APFPaper5_K2_StateClass
import Definitions.Def_APFPaper5_K2_HoldScore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2
end APFPaper5.K2
open APFPaper5
open APFPaper5.K2
universe uI uX uD uW
variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}





/-! ### K1's table is an overlap of record lists -/





/-! ### Candidate A: the distinctions that read true, added up -/









/-! ### Candidate B: the side of each distinction -/

theorem APFPaper5.K2.opposite_sides_cancel :
    tableForm (atomTable (fun _ : Unit => (1 : ℝ)) (fun (_ : Bool) (_ : Unit) => true))
      (fun b : Bool => if b then 1 else -1) (fun b : Bool => if b then 1 else -1) = 0 := by
  simp [tableForm, atomTable, ind]

theorem solution :
    tableForm (atomTable (fun _ : Unit => (1 : ℝ)) (fun (_ : Bool) (_ : Unit) => true))
      (fun b : Bool => if b then 1 else -1) (fun b : Bool => if b then 1 else -1) = 0 := by
  simp [tableForm, atomTable, ind]


