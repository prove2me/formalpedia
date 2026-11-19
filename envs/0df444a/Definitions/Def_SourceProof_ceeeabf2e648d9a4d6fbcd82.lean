-- Prove2me | Definitions.Def_SourceProof_ceeeabf2e648d9a4d6fbcd82
-- name    : SourceProof_ceeeabf2e648d9a4d6fbcd82
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:07:41.974437+00:00
-- url     : https://prove2.me/theorems/89b5fcd8-09b9-4f9d-bca9-9c8a8b85ae65
-- title:
--   LevyStochCalc source proof: MeasureTheory.mul_upcrossingsBefore_le_sum_add_posPart
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}


theorem _root_.Prove2MeSourceProof.h_ceeeabf2e648d9a4d6fbcd82 (hab : a < b) :
    (b - a) * upcrossingsBefore a b f N ω ≤
      (∑ k ∈ Finset.range N, upcrossingStrat a b f N k ω * (f (k + 1) - f k) ω) + (a - f N ω)⁺ := by
  rcases N with _ | M
  · simp [posPart, upcrossingsBefore_zero]
  let g : ℕ → Ω → ℝ := fun k ω' ↦ if k = M + 1 then max (f k ω') a else f k ω'
  have hIic i ω' : g i ω' ≤ a ↔ f i ω' ≤ a := by simp [g]; grind
  have hIci i ω' : b ≤ g i ω' ↔ b ≤ f i ω' := by simp [g]; grind
  have hga : a ≤ g (M + 1) ω := by simp [g]
  have key : (b - a) * upcrossingsBefore a b g (M + 1) ω ≤
      ∑ k ∈ Finset.range (M + 1), upcrossingStrat a b g (M + 1) k ω * (g (k + 1) - g k) ω :=
    mul_upcrossingsBefore_le (f := g) (N := M + 1) (ω := ω) hga hab
  simp_rw [MeasureTheory.upcrossingsBefore_congr hIic hIci, MeasureTheory.upcrossingStrat_congr hIic hIci] at key
  refine key.trans ?_
  rw [Finset.sum_range_succ, Finset.sum_range_succ
    (f := fun k ↦ upcrossingStrat a b f (M + 1) k ω * (f (k + 1) - f k) ω)]
  have hsum k (hk : k ∈ Finset.range M) :
      upcrossingStrat a b f (M + 1) k ω * (g (k + 1) - g k) ω
        = upcrossingStrat a b f (M + 1) k ω * (f (k + 1) - f k) ω := by simp [g]; grind
  rw [Finset.sum_congr rfl hsum, add_assoc]
  gcongr
  have hgM : g M = f M := by simp [g]
  have hgM1 : g (M + 1) ω = f (M + 1) ω + (a - f (M + 1) ω)⁺ := by simp [g, posPart]; grind
  rw [Pi.sub_apply, hgM, hgM1]
  have h11 : upcrossingStrat a b f (M + 1) M ω ≤ 1 := upcrossingStrat_le_one
  calc upcrossingStrat a b f (M + 1) M ω * (f (M + 1) ω + (a - f (M + 1) ω)⁺ - f M ω)
  _ = upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω
      + upcrossingStrat a b f (M + 1) M ω * (a - f (M + 1) ω)⁺ := by rw [Pi.sub_apply]; ring
  _ ≤ upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω + 1 * (a - f (M + 1) ω)⁺ := by
    gcongr
  _ = upcrossingStrat a b f (M + 1) M ω * (f (M + 1) - f M) ω + (a - f (M + 1) ω)⁺ := by ring
end MeasureTheory


