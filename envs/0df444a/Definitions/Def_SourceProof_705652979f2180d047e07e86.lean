-- Prove2me | Definitions.Def_SourceProof_705652979f2180d047e07e86
-- name    : SourceProof_705652979f2180d047e07e86
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:08:15.227196+00:00
-- url     : https://prove2.me/theorems/c94f23c6-4efa-4243-9bf1-9d2a73fcc07a
-- title:
--   LevyStochCalc source proof: chainingSequence_chainingSequence
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_Chaining_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Chaining

### References
- https://arxiv.org/pdf/2107.13837.pdf Lemma 6.2
- Talagrand, The generic chaining
- Vershynin, High-Dimensional Probability (section 4.2 and chapter 8)

-/

@[expose] public section

open Metric
open scoped ENNReal NNReal

variable {E : Type*} {x y : E} {A : Set E} {C C₁ C₂ : Finset E} {ε ε₁ ε₂ : ℝ≥0}

variable [PseudoEMetricSpace E]

section Sequence

variable {ε : ℕ → ℝ≥0} {C : ℕ → Finset E} {k n : ℕ}

theorem _root_.Prove2MeSourceProof.h_705652979f2180d047e07e86 (n : ℕ) (hn : n ≤ k) (m : ℕ) (hm : m ≤ n) :
    chainingSequence C (chainingSequence C x k n) n m = chainingSequence C x k m := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction l generalizing m with
  | zero => simp
  | succ l ih =>
    rw [chainingSequence_of_lt (by omega), chainingSequence_of_lt (n := m) (by omega)]
    congr 1
    simp only [← ih (m + 1) (by omega)]
    congr 1
    · congr 1
      ring
    ring
end Sequence


