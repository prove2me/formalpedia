-- Prove2me | solution 1 for APFPaper1.Foundation.near_optimal_ledger
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-10T04:03:55.676004+00:00
-- url     : https://prove2.me/submissions/fe6f92b2-3c5a-4484-915e-a1e71562028b

import Definitions.Def_APFPaper1_CostLedger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Foundation

theorem solution {D P Record : Type*} (L : Ledger D P Record) (S : Finset D)
    (hS : Feasible L S) (η : ℝ) (hη : 0 < η) :
    ∃ p, L.serves p S ∧ L.price p < cost L S + η := by
  by_contra! hn
  obtain ⟨p, hp⟩ := hS
  have hle : cost L S + η ≤ cost L S := by
    apply le_csInf (show (costs L S).Nonempty from ⟨L.price p, p, hp, rfl⟩)
    rintro c ⟨q, hq, rfl⟩
    exact hn q hq
  linarith
