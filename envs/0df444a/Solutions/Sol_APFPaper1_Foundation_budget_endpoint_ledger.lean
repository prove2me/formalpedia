-- Prove2me | solution 1 for APFPaper1.Foundation.budget_endpoint_ledger
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-13T22:23:33.83406+00:00
-- url     : https://prove2.me/submissions/7d29aae9-8a58-418e-a956-f40f049da963

import Definitions.Def_APFPaper1_WithinBudget
import Theorems.Thm_APFPaper1_Foundation_cost_bounds_ledger
import Theorems.Thm_APFPaper1_Foundation_near_optimal_ledger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Foundation

theorem solution {D P Record : Type*} (L : Ledger D P Record) (S : Finset D)
    (hS : Feasible L S) (b : ℝ) :
    WithinBudget L S b ↔ cost L S < b ∨
      (cost L S = b ∧ ∃ p, L.serves p S ∧ L.price p = cost L S) := by
  constructor
  · rintro ⟨p, hp, hb⟩
    have hlo := (cost_bounds_ledger L S p hp).2
    rcases lt_or_eq_of_le (hlo.trans hb) with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, p, hp, by linarith⟩
  · rintro (hlt | ⟨heq, p, hp, hc⟩)
    · obtain ⟨p, hp, hc⟩ := near_optimal_ledger L S hS (b - cost L S) (by linarith)
      exact ⟨p, hp, by linarith⟩
    · exact ⟨p, hp, by linarith⟩
