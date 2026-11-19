-- Prove2me | Definitions.Def_SourceProof_fe999cb8170900d5fe5aa7da
-- name    : SourceProof_fe999cb8170900d5fe5aa7da
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:38:33.496572+00:00
-- url     : https://prove2.me/theorems/2050ceb5-e703-45dd-8f23-3fa7be77b528
-- title:
--   LevyStochCalc source proof: MeasureTheory.le_upcrossingsBefore_of_alternating
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}


theorem _root_.Prove2MeSourceProof.h_fe999cb8170900d5fe5aa7da (hab : a < b) {m : ℕ} {c : ℕ → ℕ}
    (hmono : ∀ i, i + 1 < 2 * m → c i < c (i + 1)) (hN : ∀ i < 2 * m, c i < N)
    (ha : ∀ i < m, f (c (2 * i)) ω ≤ a) (hb : ∀ i < m, b ≤ f (c (2 * i + 1)) ω) :
    m ≤ upcrossingsBefore a b f N ω := by
  rcases m with _ | m
  · simp
  have key i : i < m + 1 → i + 1 ≤ upcrossingsBefore a b f (c (2 * i + 1) + 1) ω := by
    induction i with
    | zero =>
      intro h0
      have := MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing' (f := f) (ω := ω) (N := 0) hab
        (by lia) (ha 0 h0) (hmono 0 (by lia)).le (hb 0 h0)
      lia
    | succ i ih =>
      intro hi
      have h2 := MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing' (f := f) (ω := ω)
        (N := c (2 * i + 1) + 1) hab (hmono (2 * i + 1) (by lia)) (ha (i + 1) hi)
        (hmono (2 * (i + 1)) (by lia)).le (hb (i + 1) hi)
      lia
  refine (key m (by lia)).trans ?_
  exact upcrossingsBefore_mono (f := f) hab (hN (2 * m + 1) (by lia)) ω
end MeasureTheory


