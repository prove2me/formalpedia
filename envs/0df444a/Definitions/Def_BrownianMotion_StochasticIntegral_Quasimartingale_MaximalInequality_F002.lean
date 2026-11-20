-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F002
-- name    : BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:18:54.159174+00:00
-- url     : https://prove2.me/theorems/3c0d72a6-096b-4723-a80c-8e73bee67b39
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F001

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

variable {F : Finset ι} {t : ι} {k l : ℕ}

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name

end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

omit [LinearOrder ι] in
lemma countable_setOf_finset_coe_subset (hT : T.Countable) :
    {F : Finset ι | ↑F ⊆ T}.Countable := by
  have h1 : {F : Finset ι | ↑F ⊆ T}
      ⊆ (fun F : Finset ι ↦ (F : Set ι)) ⁻¹' {u : Set ι | u.Finite ∧ u ⊆ T} :=
    fun F hF ↦ ⟨F.finite_toSet, hF⟩
  exact ((Set.countable_setOf_finite_subset hT).preimage coe_injective).mono h1
variable [OrderBot ι]

/-- The union of the alternation events over all finite subsets of a countable set of times
below `t` has measure at most `K / ((b - a) * m)`. -/
lemma measure_biUnion_altSet_le [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (hab : a < b) (hm : 0 < m) (hT : T.Countable) (t : ι) :
    μ (⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b m)
      ≤ ENNReal.ofReal ((variationBound X 𝓕 μ t + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / m) := by
  have hcnt : {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}.Countable :=
    countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)
  have hdir : DirectedOn (Function.onFun (· ⊆ ·) fun F : Finset ι ↦ altSet X F a b m)
      {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t} :=
    fun F₁ h₁ F₂ h₂ ↦ ⟨F₁ ∪ F₂, by grind, altSet_mono subset_union_left,
      altSet_mono subset_union_right⟩
  rw [measure_biUnion_eq_iSup hcnt hdir]
  refine iSup₂_le fun F hF ↦ ?_
  have hF' : ∀ s ∈ F, s ≤ t := fun s hs ↦ (hF hs).2
  calc μ (altSet X F a b m)
  _ = ENNReal.ofReal (μ.real (altSet X F a b m)) :=
    (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  _ ≤ _ := ENNReal.ofReal_le_ofReal (measureReal_altSet_le (μ := μ) hX.adapted hX.integrable
        (hX.integral_indicator_le_variationBound t) hab hm hF')
/-- Almost surely, there is no infinite family of alternations of `X` from below `a` to above `b`
at times in a countable set `T` below `t`. -/
lemma measure_infiniteAlt [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) (hab : a < b) (hT : T.Countable) :
    μ (infiniteAlt T t X a b) = 0 := by
  suffices μ (⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b (m + 1)) = 0 by
    refine measure_mono_null ?_ this
    intro ω
    simp only [infiniteAlt, Set.subset_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
    exact fun h i ↦ h (i + 1)
  refine le_antisymm ?_ zero_le
  have hbound : ∀ m : ℕ,
      μ (⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b (m + 1))
        ≤ ENNReal.ofReal ((variationBound X 𝓕 μ t + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / (m + 1)) := by
    intro m
    refine (measure_mono (Set.iInter_subset _ m)).trans ?_
    have := measure_biUnion_altSet_le (μ := μ) hX hab (Nat.succ_pos m) hT t
    simpa using this
  have hlim : Tendsto (fun m : ℕ ↦
      ENNReal.ofReal ((variationBound X 𝓕 μ t + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / (m + 1)))
        atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have h1 : Tendsto (fun n : ℕ ↦ ((variationBound X 𝓕 μ t + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a)) / n)
        atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun m ↦ ?_
    simp [Function.comp, div_div]
  exact ge_of_tendsto' hlim hbound
lemma measure_all_infiniteAlt'' [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) (T : Set ι) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ q r, q < r → ω ∉ infiniteAlt T t X q r := by
  suffices ∀ᵐ ω ∂μ, ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T t X q r by
    filter_upwards [this] with ω hω q r hqr
    obtain ⟨q', r', hqq', hq'r', hr'r⟩ : ∃ q' r' : ℚ, q < q' ∧ q' < r' ∧ r' < r := by
      obtain ⟨r', hqr', hr'r⟩ := exists_rat_btwn hqr
      obtain ⟨q', hqq', hq'r'⟩ := exists_rat_btwn hqr'
      exact ⟨q', r', hqq', mod_cast hq'r', hr'r⟩
    exact fun h_mem ↦ hω q' r' hq'r' (infiniteAlt_mono' hqq'.le hr'r.le h_mem)
  simp_rw [ae_all_iff]
  intro q r hqr
  exact compl_mem_ae_iff.2 (measure_infiniteAlt hX (mod_cast hqr) hT)
lemma measure_all_infiniteAlt [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T T' : Set ι} (hT : T.Countable) (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ∀ q r, q < r → ω ∉ infiniteAlt T d X q r := by
  rw [ae_ball_iff hT']
  exact fun t _ ↦ measure_all_infiniteAlt'' hX T hT
lemma measure_all_infiniteAlt' [IsFiniteMeasure μ] [(atTop : Filter ι).IsCountablyGenerated]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (T : Set ι) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d, ∀ q r, q < r → ω ∉ infiniteAlt T d X q r := by
  obtain ⟨u, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  suffices ∀ᵐ ω ∂μ, ∀ n, ∀ q r, q < r → ω ∉ infiniteAlt T (u n) X q r by
    filter_upwards [this] with ω hω d q r hqr
    obtain ⟨n, hn⟩ : ∃ n, d ≤ u n := (hu.2.eventually_ge_atTop d).exists
    specialize hω n q r hqr
    exact fun h_mem ↦ hω (infiniteAlt_mono'' hn h_mem)
  rw [ae_all_iff]
  exact fun n ↦ measure_all_infiniteAlt'' hX T hT
end CountableEvents

end ProbabilityTheory


