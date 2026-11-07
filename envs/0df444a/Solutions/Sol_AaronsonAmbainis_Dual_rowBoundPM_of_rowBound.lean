-- Prove2me | solution 1 for AaronsonAmbainis.Dual.rowBoundPM_of_rowBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:46.781706+00:00
-- url     : https://prove2.me/submissions/024ee0db-c16d-4eff-aeda-c90eed93bd99

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
import Theorems.Thm_AaronsonAmbainis_rows_of_rowBound


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
namespace AaronsonAmbainis.Dual
theorem _root_.solution : RowBound → RowBoundPM := by
  intro hRB ι _ _ d f hf hdeg
  obtain ⟨a, ha0, haK, hacov⟩ := rows_of_rowBound hRB d f hf hdeg
  have hp : (0 : ℝ) ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 := by positivity
  exact ⟨a, ha0, fun x => le_trans (haK x) (by linarith), hacov⟩
end AaronsonAmbainis.Dual
