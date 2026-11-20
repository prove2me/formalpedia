-- Prove2me | Definitions.Def_SourceProof_a893600c0517c19e216d57fb
-- name    : SourceProof_a893600c0517c19e216d57fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:34:19.430566+00:00
-- url     : https://prove2.me/theorems/fce4559c-3dcf-4179-8e3a-99c981002a07
-- title:
--   LevyStochCalc source module: SourceProof_a893600c0517c19e216d57fb
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.exp_windowSum_sub_one_of_repr` comes from the `LevyStochCalc.Poisson.ChainRule` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ChainRule_F000
import Definitions.Def_SourceProof_4e4915138fe9e147b24da990

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

omit [MeasurableSpace.CountablyGenerated E] in
open scoped Classical in

theorem _root_.Prove2MeSourceProof.h_a893600c0517c19e216d57fb (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (h : ℝ × E → ℝ) {J : Set ℝ} (hJm : MeasurableSet J)
    (hJ0 : J ⊆ Set.Ioi 0) (hJ : ∀ u ∈ J, Set.Ioo (0 : ℝ) u ⊆ J) (ω : Ω)
    (hsrepex : ∃ s : Finset (ℝ × E), (N.N ω).restrict (B ∩ J ×ˢ Set.univ)
      = ∑ p ∈ s, ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)) {p} • Measure.dirac p)
    (hn : ∃ k : ℕ, N.N ω (B ∩ J ×ˢ Set.univ) = k)
    (hIV : Probability.IsIntegerValued ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)))
    (hsimple : ∀ t : ℝ, N.N ω (B ∩ ({t} : Set ℝ) ×ˢ Set.univ) ≤ 1) :
    Complex.exp (Complex.I * ((∫ p in B ∩ J ×ˢ Set.univ, h p ∂(N.N ω) : ℝ) : ℂ)) - 1
      = ∫ p in B ∩ J ×ˢ Set.univ,
          Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω) := by
  have hRm : MeasurableSet (B ∩ J ×ˢ Set.univ) := hB.inter (hJm.prod MeasurableSet.univ)
  obtain ⟨s, hsrep⟩ := hsrepex
  haveI : IsFiniteMeasure ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)) := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, hk]
    exact ENNReal.natCast_lt_top k
  set R : Set (ℝ × E) := B ∩ J ×ˢ Set.univ with hRdef
  set m : ℝ × E → ℝ≥0∞ := fun p => ((N.N ω).restrict R) {p} with hmdef
  have hmapp : ∀ p : ℝ × E, m p = (N.N ω) ({p} ∩ R) := fun p => by
    rw [hmdef]
    exact Measure.restrict_apply (measurableSet_singleton p)
  have hmself : ∀ p : ℝ × E, m p ≤ (N.N ω) {p} := fun p =>
    Measure.le_iff'.mp Measure.restrict_le_self {p}
  have hmle : ∀ p : ℝ × E, m p ≤ 1 := by
    intro p
    calc m p = (N.N ω) ({p} ∩ R) := hmapp p
      _ ≤ (N.N ω) (B ∩ ({p.1} : Set ℝ) ×ˢ Set.univ) := by
          refine measure_mono fun q hq => ?_
          obtain ⟨hq1, hq2⟩ := hq
          rw [Set.mem_singleton_iff] at hq1
          subst hq1
          exact ⟨hq2.1, ⟨rfl, Set.mem_univ _⟩⟩
      _ ≤ 1 := hsimple p.1
  set s₁ : Finset (ℝ × E) := s.filter (fun p => m p ≠ 0) with hs₁def
  have hs₁sub : s₁ ⊆ s := Finset.filter_subset _ _
  have hm1 : ∀ p ∈ s₁, m p = 1 := by
    intro p hp
    have hne : m p ≠ 0 := (Finset.mem_filter.mp hp).2
    obtain ⟨k, hk⟩ := hIV ({p} : Set (ℝ × E)) (measurableSet_singleton p)
    have hkm : m p = (k : ℝ≥0∞) := hk
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · exact absurd (by rw [hkm, Nat.lt_one_iff.mp hk1]; simp) hne
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        rw [hkm, this]
        norm_num
      · exfalso
        have : (2 : ℝ≥0∞) ≤ m p := by
          rw [hkm]
          exact_mod_cast hk2
        exact absurd (this.trans (hmle p)) (by norm_num)
  have hmR : ∀ p ∈ s₁, p ∈ R := by
    intro p hp
    by_contra hpR
    have : ({p} : Set (ℝ × E)) ∩ R = ∅ := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl
      exact hpR
    have hz : m p = 0 := by rw [hmapp p, this, measure_empty]
    exact (Finset.mem_filter.mp hp).2 hz
  have hinj : Set.InjOn Prod.fst (s₁ : Set (ℝ × E)) := by
    intro p hp q hq hpq
    by_contra hne
    have hp1 : m p = 1 := hm1 p hp
    have hq1 : m q = 1 := hm1 q hq
    have hpR : p ∈ R := hmR p hp
    have hqR : q ∈ R := hmR q hq
    have hdisj : Disjoint ({p} : Set (ℝ × E)) {q} := by
      simp only [Set.disjoint_singleton]
      exact hne
    have hsub : ({p} : Set (ℝ × E)) ∪ {q} ⊆ B ∩ ({p.1} : Set ℝ) ×ˢ Set.univ := by
      rintro x (hx | hx) <;> rw [Set.mem_singleton_iff] at hx <;> subst hx
      · exact ⟨hpR.1, ⟨rfl, Set.mem_univ _⟩⟩
      · exact ⟨hqR.1, ⟨hpq.symm, Set.mem_univ _⟩⟩
    have h2 : (2 : ℝ≥0∞) ≤ (N.N ω) (B ∩ ({p.1} : Set ℝ) ×ˢ Set.univ) := by
      calc (2 : ℝ≥0∞) = m p + m q := by rw [hp1, hq1]; norm_num
        _ ≤ (N.N ω) {p} + (N.N ω) {q} := add_le_add (hmself p) (hmself q)
        _ = (N.N ω) (({p} : Set (ℝ × E)) ∪ {q}) :=
            (measure_union hdisj (measurableSet_singleton q)).symm
        _ ≤ _ := measure_mono hsub
    exact absurd (h2.trans (hsimple p.1)) (by norm_num)
  -- the window sums as finite sums over the atoms
  have hsumR : ∀ (S : Set (ℝ × E)), MeasurableSet S → S ⊆ R →
      ∫ p in S, h p ∂(N.N ω) = ∑ p ∈ s₁, S.indicator h p := by
    intro S hSm hSR
    have hrw : ∫ p in S, h p ∂(N.N ω) = ∫ p, S.indicator h p ∂((N.N ω).restrict R) := by
      rw [integral_indicator hSm, Measure.restrict_restrict hSm,
        Set.inter_eq_self_of_subset_left hSR]
    rw [hrw, LevyStochCalc.Poisson.integral_of_eq_sum_dirac' hsrep]
    have hdrop : ∑ p ∈ s, (m p).toReal • S.indicator h p
        = ∑ p ∈ s₁, (m p).toReal • S.indicator h p := by
      refine (Finset.sum_subset hs₁sub ?_).symm
      intro x hx hxn
      have hz : m x = 0 := by
        by_contra hc
        exact hxn (Finset.mem_filter.mpr ⟨hx, hc⟩)
      rw [hz]
      simp
    rw [hdrop]
    exact Finset.sum_congr rfl fun p hp => by rw [hm1 p hp]; simp
  have hwindow : (∫ p in R, h p ∂(N.N ω)) = ∑ p ∈ s₁, h p := by
    rw [hsumR R hRm le_rfl]
    exact Finset.sum_congr rfl fun p hp => Set.indicator_of_mem (hmR p hp) h
  have hstrict : ∀ p ∈ s₁, LevyStochCalc.Poisson.windowSumStrict N B h p.1 ω
      = ∑ q ∈ s₁.filter (fun q => q.1 < p.1), h q := by
    intro p hp
    have hpR : p ∈ R := hmR p hp
    have hJp : Set.Ioo (0 : ℝ) p.1 ⊆ J := hJ p.1 hpR.2.1
    have hSm : MeasurableSet (B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ Set.univ) :=
      hB.inter (measurableSet_Ioo.prod MeasurableSet.univ)
    have hSR : B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ Set.univ ⊆ R := by
      intro q hq
      exact ⟨hq.1, ⟨hJp hq.2.1, Set.mem_univ _⟩⟩
    rw [LevyStochCalc.Poisson.windowSumStrict, hsumR _ hSm hSR]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqR : q ∈ R := hmR q hq
    by_cases hlt : q.1 < p.1
    · have hmem : q ∈ B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ Set.univ :=
        ⟨hqR.1, ⟨⟨hJ0 hqR.2.1, hlt⟩, Set.mem_univ _⟩⟩
      rw [if_pos hlt, Set.indicator_of_mem hmem]
    · have hnmem : q ∉ B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ Set.univ := fun hmem => hlt hmem.2.1.2
      rw [if_neg hlt, Set.indicator_of_notMem hnmem]
  -- the right-hand integral as a finite sum over the atoms
  have hRHS : ∫ p in R, Complex.exp (Complex.I * (LevyStochCalc.Poisson.windowSumStrict N B h p.1 ω : ℂ))
        * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω)
      = ∑ p ∈ s₁, Complex.exp (Complex.I * (LevyStochCalc.Poisson.windowSumStrict N B h p.1 ω : ℂ))
        * (Complex.exp (Complex.I * (h p : ℂ)) - 1) := by
    rw [show (N.N ω).restrict R = (N.N ω).restrict R from rfl,
      show ∫ p in R, Complex.exp (Complex.I * (LevyStochCalc.Poisson.windowSumStrict N B h p.1 ω : ℂ))
          * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω)
        = ∫ p, Complex.exp (Complex.I * (LevyStochCalc.Poisson.windowSumStrict N B h p.1 ω : ℂ))
          * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂((N.N ω).restrict R) from rfl,
      LevyStochCalc.Poisson.integral_of_eq_sum_dirac' hsrep]
    have hdrop : ∑ p ∈ s, (m p).toReal • (Complex.exp (Complex.I *
          (LevyStochCalc.Poisson.windowSumStrict N B h p.1 ω : ℂ)) * (Complex.exp (Complex.I * (h p : ℂ)) - 1))
        = ∑ p ∈ s₁, (m p).toReal • (Complex.exp (Complex.I *
          (LevyStochCalc.Poisson.windowSumStrict N B h p.1 ω : ℂ)) * (Complex.exp (Complex.I * (h p : ℂ)) - 1)) := by
      refine (Finset.sum_subset hs₁sub ?_).symm
      intro x hx hxn
      have hz : m x = 0 := by
        by_contra hc
        exact hxn (Finset.mem_filter.mpr ⟨hx, hc⟩)
      rw [hz]
      simp
    rw [hdrop]
    exact Finset.sum_congr rfl fun p hp => by rw [hm1 p hp]; simp
  rw [hRHS, hwindow]
  have hprod := _root_.Prove2MeSourceProof.h_4e4915138fe9e147b24da990 (M := ℂ) Prod.fst
    (fun p => Complex.exp (Complex.I * (h p : ℂ))) s₁ hinj
  rw [← Complex.exp_sum] at hprod
  have hcast : ∀ t : Finset (ℝ × E),
      ∑ p ∈ t, Complex.I * (h p : ℂ) = Complex.I * ((∑ p ∈ t, h p : ℝ) : ℂ) := by
    intro t
    rw [← Finset.mul_sum]
    norm_cast
  rw [hcast] at hprod
  rw [hprod]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Complex.exp_sum, hcast, hstrict p hp]
end Pathwise

end LevyStochCalc.Poisson


