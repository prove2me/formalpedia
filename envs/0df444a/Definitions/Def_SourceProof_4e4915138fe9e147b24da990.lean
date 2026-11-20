-- Prove2me | Definitions.Def_SourceProof_4e4915138fe9e147b24da990
-- name    : SourceProof_4e4915138fe9e147b24da990
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:19:05.886164+00:00
-- url     : https://prove2.me/theorems/92a75a2e-45cb-4998-ae44-7b705b703563
-- title:
--   LevyStochCalc source module: SourceProof_4e4915138fe9e147b24da990
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.prod_sub_one_eq_sum` comes from the `LevyStochCalc.Poisson.ChainRule` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpSum_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump chain rule for a Poisson random measure

A product over a finite set whose factors are ordered by a key telescopes: the product minus one
is the sum, over the factors, of the product of the earlier ones times the increment of that
factor. On a set of finite reference intensity a Poisson random measure is a finite sum of unit
masses at distinct times, so the exponential of an integral against it obeys that telescoping,
which is the chain rule the exponential family needs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

section Telescope

variable {α : Type*} [DecidableEq α] {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]

omit [DecidableEq α] in
open scoped Classical in

theorem _root_.Prove2MeSourceProof.h_4e4915138fe9e147b24da990 (key : α → K) (z : α → M) :
    ∀ s : Finset α, Set.InjOn key (s : Set α) →
      (∏ p ∈ s, z p) - 1
        = ∑ p ∈ s, (∏ q ∈ s.filter (fun q => key q < key p), z q) * (z p - 1) := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hinj
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨p₀, hp₀, hmax⟩ := s.exists_max_image key hne
    have hss' : s.erase p₀ ⊂ s := Finset.erase_ssubset hp₀
    have hinj' : Set.InjOn key ((s.erase p₀ : Finset α) : Set α) := by
      refine hinj.mono ?_
      intro x hx
      exact Finset.mem_of_mem_erase hx
    have hlt : ∀ p ∈ s.erase p₀, key p < key p₀ := by
      intro p hp
      have hps : p ∈ s := Finset.mem_of_mem_erase hp
      have hne' : p ≠ p₀ := Finset.ne_of_mem_erase hp
      refine lt_of_le_of_ne (hmax p hps) fun h => hne' (hinj hps hp₀ h)
    have hfilter0 : s.filter (fun q => key q < key p₀) = s.erase p₀ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hq, hqlt⟩
        exact ⟨fun h => absurd (h ▸ hqlt) (lt_irrefl _), hq⟩
      · rintro ⟨hq1, hq2⟩
        exact ⟨hq2, hlt q (Finset.mem_erase.mpr ⟨hq1, hq2⟩)⟩
    have hfilter : ∀ p ∈ s.erase p₀,
        s.filter (fun q => key q < key p) = (s.erase p₀).filter (fun q => key q < key p) := by
      intro p hp
      ext q
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hq, hqlt⟩
        refine ⟨⟨?_, hq⟩, hqlt⟩
        rintro rfl
        exact absurd hqlt (not_lt.mpr (hlt p hp).le)
      · rintro ⟨⟨-, hq⟩, hqlt⟩
        exact ⟨hq, hqlt⟩
    have hsplit : (∑ p ∈ s, (∏ q ∈ s.filter (fun q => key q < key p), z q) * (z p - 1))
        = (∑ p ∈ s.erase p₀,
            (∏ q ∈ (s.erase p₀).filter (fun q => key q < key p), z q) * (z p - 1))
          + (∏ q ∈ s.erase p₀, z q) * (z p₀ - 1) := by
      rw [← Finset.sum_erase_add s _ hp₀, hfilter0]
      congr 1
      exact Finset.sum_congr rfl fun p hp => by rw [hfilter p hp]
    rw [hsplit, ← ih (s.erase p₀) hss' hinj', ← Finset.prod_erase_mul s z hp₀]
    ring
end Telescope

section Pathwise

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Pathwise

end LevyStochCalc.Poisson


