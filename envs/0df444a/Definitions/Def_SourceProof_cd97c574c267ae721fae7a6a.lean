-- Prove2me | Definitions.Def_SourceProof_cd97c574c267ae721fae7a6a
-- name    : SourceProof_cd97c574c267ae721fae7a6a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:27:34.724239+00:00
-- url     : https://prove2.me/theorems/416dff22-5773-436d-b6fb-23052da6ab6a
-- title:
--   LevyStochCalc source module: SourceProof_cd97c574c267ae721fae7a6a
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_forall_exp_windowSum_sub_one` comes from the `LevyStochCalc.Poisson.ChainRule` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ChainRule_F001

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

end Telescope

section Pathwise

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_cd97c574c267ae721fae7a6a (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (h : ℝ × E → ℝ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ,
      (Complex.exp (Complex.I * (windowSum N B h T ω : ℂ)) - 1
        = ∫ p in B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
            Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
              * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω))
      ∧ (Complex.exp (Complex.I * (windowSumStrict N B h T ω : ℂ)) - 1
        = ∫ p in B ∩ Set.Ioo (0 : ℝ) T ×ˢ Set.univ,
            Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
              * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω)) := by
  filter_upwards [LevyStochCalc.Poisson.ae_exists_eq_sum_dirac N hB hfin, _root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 N hB hfin,
    _root_.Prove2MeSourceProof.h_07135226a3b6eb1d82b734e1 N hB hfin] with ω hsrepex hIV hsimple
  obtain ⟨s, hs⟩ := hsrepex
  have key : ∀ (J : Set ℝ), MeasurableSet J → J ⊆ Set.Ioi 0 →
      (∀ u ∈ J, Set.Ioo (0 : ℝ) u ⊆ J) →
      Complex.exp (Complex.I * ((∫ p in B ∩ J ×ˢ Set.univ, h p ∂(N.N ω) : ℝ) : ℂ)) - 1
        = ∫ p in B ∩ J ×ˢ Set.univ,
            Complex.exp (Complex.I * (LevyStochCalc.Poisson.windowSumStrict N B h p.1 ω : ℂ))
              * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω) := by
    intro J hJm hJ0 hJ
    have hRm : MeasurableSet (B ∩ J ×ˢ Set.univ) := hB.inter (hJm.prod MeasurableSet.univ)
    have hRB : B ∩ J ×ˢ Set.univ ⊆ B := Set.inter_subset_left
    refine _root_.Prove2MeSourceProof.h_a893600c0517c19e216d57fb N hB h hJm hJ0 hJ ω
      ⟨s, LevyStochCalc.Poisson.restrict_eq_sum_dirac_of_subset hRm hRB hs⟩ ?_ ?_ hsimple
    · obtain ⟨k, hk⟩ := hIV _ hRm
      refine ⟨k, ?_⟩
      rw [Measure.restrict_apply hRm, Set.inter_eq_left.mpr hRB] at hk
      exact hk
    · intro A hA
      obtain ⟨k, hk⟩ := hIV (A ∩ (B ∩ J ×ˢ Set.univ)) (hA.inter hRm)
      refine ⟨k, ?_⟩
      rw [Measure.restrict_apply (hA.inter hRm),
        Set.inter_eq_left.mpr (Set.inter_subset_right.trans hRB)] at hk
      rw [Measure.restrict_apply hA]
      exact hk
  intro T
  exact ⟨key _ measurableSet_Ioc (fun x hx => hx.1) (fun u hu x hx => ⟨hx.1, hx.2.le.trans hu.2⟩),
    key _ measurableSet_Ioo (fun x hx => hx.1) (fun u hu x hx => ⟨hx.1, hx.2.trans hu.2⟩)⟩
end Pathwise

end LevyStochCalc.Poisson


