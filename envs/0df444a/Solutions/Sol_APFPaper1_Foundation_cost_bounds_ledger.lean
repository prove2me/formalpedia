-- Prove2me | solution 1 for APFPaper1.Foundation.cost_bounds_ledger
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-08T22:05:27.192945+00:00
-- url     : https://prove2.me/submissions/9dc7029c-1c56-4f2a-8208-dd69bb79447d

import Definitions.Def_APFPaper1_CostLedger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Foundation

theorem solution {D P Record : Type*} (L : Ledger D P Record) (S : Finset D)
    (p : P) (hp : L.serves p S) : 0 ≤ cost L S ∧ cost L S ≤ L.price p := by
  have hb : BddBelow (costs L S) := ⟨0, by rintro c ⟨q, _, rfl⟩; exact L.price_nonneg q⟩
  have hn : (costs L S).Nonempty := ⟨L.price p, p, hp, rfl⟩
  exact ⟨le_csInf hn (by rintro c ⟨q, _, rfl⟩; exact L.price_nonneg q),
    csInf_le hb ⟨p, hp, rfl⟩⟩
