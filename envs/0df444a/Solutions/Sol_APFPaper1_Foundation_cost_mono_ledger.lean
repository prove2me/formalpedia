-- Prove2me | solution 1 for APFPaper1.Foundation.cost_mono_ledger
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-09T18:24:29.850231+00:00
-- url     : https://prove2.me/submissions/15d37050-a695-4e2e-9ccb-7c0b4c888f43

import Definitions.Def_APFPaper1_CostLedger
import Theorems.Thm_APFPaper1_Foundation_cost_bounds_ledger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Foundation

theorem solution {D P Record : Type*} (L : Ledger D P Record) (S T : Finset D)
    (hST : S ⊆ T) (hT : Feasible L T) : cost L S ≤ cost L T := by
  obtain ⟨p, hp⟩ := hT
  apply le_csInf (show (costs L T).Nonempty from ⟨L.price p, p, hp, rfl⟩)
  rintro c ⟨q, hq, rfl⟩
  exact (cost_bounds_ledger L S q (L.serves_mono q S T hST hq)).2
