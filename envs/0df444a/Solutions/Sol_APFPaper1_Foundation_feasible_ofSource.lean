-- Prove2me | solution 1 for APFPaper1.Foundation.feasible_ofSource
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:19:14.518973+00:00
-- url     : https://prove2.me/submissions/4c95c292-6ce1-40bf-939a-6cd847db7ea8

import Definitions.Def_APFPaper1_CostLedger
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APFPaper1_LedgerOfSource
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.NNReal.Basic
set_option autoImplicit false
open Classical
open APFPaper1.Source


open APFPaper1.Foundation in
theorem solution {D P R Record : Type*} (p0 : P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) :
    Feasible (Ledger.ofSource p0 wholeResource calibration maintained sufficient usesToRealize) S ↔
      APFPaper1.Source.familyFeasible maintained sufficient usesToRealize S := by
  rfl
