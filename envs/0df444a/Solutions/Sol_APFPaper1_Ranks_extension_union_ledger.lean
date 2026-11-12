-- Prove2me | solution 1 for APFPaper1.Ranks.extension_union_ledger
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-08T09:10:12.354321+00:00
-- url     : https://prove2.me/submissions/09207920-c7d8-445a-ba39-b1d54cf51c61

import Definitions.Def_APFPaper1_RankExtend
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical APFPaper1.Ranks

theorem solution {D : Type*} [DecidableEq D] (S : Finset D) (ds : List D) :
    extend S ds = S ∪ ds.toFinset := by
  induction ds generalizing S with
  | nil => simp [extend]
  | cons d ds ih =>
    rw [extend, ih]
    ext x
    simp [or_assoc, or_left_comm, or_comm]
