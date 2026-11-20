-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F000
-- name    : BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:06:05.113492+00:00
-- url     : https://prove2.me/theorems/a5f7d8ea-e815-4a84-ae0e-b8921a38094c
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_LeftLimWithin_F000
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Predictable_F000
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F002
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F003
import Definitions.Def_SourceProof_dfed2a2c41cef06acf5bb665
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rohit Manokaran, Rémy Degenne
-/
@[expose] public section
open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess
namespace ProbabilityTheory
variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}
section CountableEvents
variable [OrderBot ι] {T : Set ι} {t : ι}
end CountableEvents
section RegularitySet
def regularitySet (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
  {ω | (∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r) ∧
    (∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1)}
def regularitySetRight (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
  ⋃ s ∈ T ∩ Set.Ioi d, regularitySet T X s
lemma regularitySet_anti {T : Set ι} {X : ι → Ω → ℝ} {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySet T X d₂ ⊆ regularitySet T X d₁ := by
  intro ω hω
  simp only [regularitySet, Set.mem_setOf_eq] at hω ⊢
  constructor
  · intro q r hqr
    have hω' :=  hω.1 q r hqr
    refine fun h_mem ↦ hω' ?_
    exact infiniteAlt_mono'' hd h_mem
  · obtain ⟨M, hM⟩ := hω.2
    refine ⟨M, fun s hs ↦ ?_⟩
    specialize hM s (by grind)
    grind
lemma regularitySetRight_eq_biUnion_lt
    {T : Set ι} {X : ι → Ω → ℝ} {d t : ι} (hT : ∃ u ∈ T, d < u ∧ u ≤ t) :
    regularitySetRight T X d = ⋃ d' ∈ T ∩ Set.Ioc d t, regularitySet T X d' := by
  ext ω
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop,
    Set.mem_Ioc]
  refine ⟨fun ⟨i, ⟨hiT, hdi⟩, hωi⟩ ↦ ?_, fun ⟨i, ⟨hiT, hdi, hit⟩, hωi⟩ ↦ ?_⟩
  · obtain ⟨u, huT, hud, hut⟩ := hT
    refine ⟨min i u, ?_, ?_⟩
    · grind
    · exact regularitySet_anti (by grind) hωi
  · exact ⟨i, ⟨hiT, hdi⟩, hωi⟩
lemma regularitySetRight_anti {T : Set ι} {X : ι → Ω → ℝ} {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySetRight T X d₂ ⊆ regularitySetRight T X d₁ := by
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.iUnion_subset_iff, and_imp]
  intro i hiT hd₂i ω hω
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨i, ⟨hiT, by grind⟩, hω⟩
variable [OrderBot ι]
lemma ae_mem_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) (hdT : d ∈ T) :
    ∀ᵐ ω ∂μ, ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT, _root_.Prove2MeSourceProof.h_436b1ce988647b7e9b7772ec hX hT d] with ω hω1 hω2
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2⟩
lemma ae_mem_all_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T, ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT, ae_exists_bound hX hT hT] with ω hω1 hω2 d hdT
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2 d hdT⟩
lemma ae_mem_regularitySetRight [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ∃ s ∈ T, x < s) :
    ∀ᵐ ω ∂μ, ∀ d, ω ∈ regularitySetRight T X d := by
  have h1 : ∀ᵐ ω ∂μ, ∀ s ∈ T, ω ∈ regularitySet T X s := ae_mem_all_regularitySet hX hT
  filter_upwards [h1] with ω hω d
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop]
  obtain ⟨s, hs, hsd⟩ := hTcof d
  exact ⟨s, ⟨hs, hsd⟩, hω s hs⟩
lemma measurableSet_altSet (hX : IsRealQuasimartingale 𝓕 X μ)
    (d : ι) (F : Finset ι) (hF : ∀ i ∈ F, i ≤ d) {q r : ℚ} (_hqr : q < r) (m : ℕ) :
    MeasurableSet[𝓕 d] (altSet X F q r m) := by
  have hXmeas : ∀ s ∈ F, Measurable[𝓕 d] (X s) := fun s hs ↦
    (hX.adapted s).mono (𝓕.mono (hF s hs)) le_rfl
  have hset : altSet X F (q : ℝ) (r : ℝ) m
      = ⋃ g ∈ Fintype.piFinset (fun _ : Fin (2 * m) ↦ F),
          {ω | (∀ (i : Fin (2 * m)) (h : (i : ℕ) + 1 < 2 * m), g i < g ⟨(i : ℕ) + 1, h⟩)
            ∧ (∀ i : Fin m, X (g ⟨2 * (i : ℕ), by omega⟩) ω ≤ (q : ℝ))
            ∧ (∀ i : Fin m, (r : ℝ) ≤ X (g ⟨2 * (i : ℕ) + 1, by omega⟩) ω)} := by
    ext ω
    simp only [altSet, Set.mem_setOf_eq, Set.mem_iUnion, Fintype.mem_piFinset, exists_prop]
    constructor
    · rintro ⟨c, hc1, hc2, hc3, hc4⟩
      exact ⟨fun i ↦ c (i : ℕ), fun i ↦ hc2 (i : ℕ) i.2,
        fun i h ↦ hc1 (i : ℕ) h, fun i ↦ hc3 (i : ℕ) i.2, fun i ↦ hc4 (i : ℕ) i.2⟩
    · rintro ⟨g, hgF, hg1, hg3, hg4⟩
      refine ⟨fun k ↦ if h : k < 2 * m then g ⟨k, h⟩ else ⊥, by grind, by grind, ?_, ?_⟩
      · intro i hi
        have h2i : 2 * i < 2 * m := by lia
        simp only [dif_pos h2i]
        exact hg3 ⟨i, hi⟩
      · intro i hi
        have h2i : 2 * i + 1 < 2 * m := by lia
        simp only [dif_pos h2i]
        exact hg4 ⟨i, hi⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun g hg ↦ ?_
  have hgF : ∀ i, g i ∈ F := Fintype.mem_piFinset.mp hg
  rw [Set.setOf_and]
  refine (MeasurableSet.const _).inter ?_
  rw [Set.setOf_and, Set.setOf_forall, Set.setOf_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i ↦ ?_) (MeasurableSet.iInter fun i ↦ ?_)
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ), by lia⟩) measurableSet_Iic
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ) + 1, by lia⟩) measurableSet_Ici
lemma measurableSet_infiniteAlt (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) {q r : ℚ} (hqr : q < r) :
    MeasurableSet[𝓕 d] (infiniteAlt T d X q r) := by
  unfold infiniteAlt
  refine MeasurableSet.iInter fun m ↦ MeasurableSet.biUnion ?_ fun F ↦ ?_
  · refine countable_setOf_finset_coe_subset ?_
    exact hT.mono (by grind)
  · intro hF
    refine measurableSet_altSet hX d F ?_ hqr m
    simp only [Set.subset_inter_iff, Set.mem_setOf_eq] at hF
    intro i hi
    exact hF.2 hi
lemma measurableSet_regularitySet (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySet T X d) := by
  suffices MeasurableSet[𝓕 d]
        ((⋂ (q : ℚ) (r : ℚ) (hqr : q < r), {ω | ω ∉ infiniteAlt T d X q r}) ∩
        (⋃ M : ℕ, ⋂ s ∈ T ∩ Set.Iic d, {ω | |X s ω| ≤ M + 1})) by
      convert this
      ext ω
      simp [regularitySet]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun p ↦ MeasurableSet.iInter fun q ↦ ?_
    by_cases hpq : p < q
    · simp only [hpq, Set.iInter_true]
      refine MeasurableSet.compl ?_
      exact measurableSet_infiniteAlt hX hT d hpq
    · simp [hpq]
  · refine MeasurableSet.iUnion fun M ↦ MeasurableSet.biInter (hT.mono (by grind)) fun s hs ↦ ?_
    refine measurableSet_le ?_ (by fun_prop)
    simp only [Set.mem_inter_iff, Set.mem_Iic] at hs
    refine Measurable.mono ?_ (𝓕.mono hs.2) le_rfl
    simp_rw [← Real.norm_eq_abs]
    exact (hX.stronglyAdapted s).norm.measurable
omit [OrderBot ι] in
lemma measurableSet_of_forall_gt [DenselyOrdered ι] [NoMaxOrder ι] [𝓕.IsRightContinuous]
    {t : ι} {A : Set Ω}
    (h : ∀ s, t < s → MeasurableSet[𝓕 s] A) :
    MeasurableSet[𝓕 t] A := by
  have hrc : (𝓕 t : MeasurableSpace Ω) = ⨅ j > t, 𝓕 j := by
    have h1 := 𝓕.rightCont_eq t
    rwa [Filtration.IsRightContinuous.eq] at h1
  rw [hrc, MeasurableSpace.measurableSet_iInf]
  intro j
  rw [MeasurableSpace.measurableSet_iInf]
  exact h j
lemma measurableSet_regularitySetRight [TopologicalSpace ι] [OrderClosedTopology ι]
    [DenselyOrdered ι] [NoMaxOrder ι] [𝓕.IsRightContinuous]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTd : Dense T) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySetRight T X d) := by
  refine measurableSet_of_forall_gt fun s hs ↦ ?_
  rw [regularitySetRight_eq_biUnion_lt (t := s)]
  swap
  · obtain ⟨z, hz1, hz2, hz3⟩ := hTd.exists_between hs
    exact ⟨z, hz1, hz2, hz3.le⟩
  refine MeasurableSet.biUnion ?_ fun t ht ↦ ?_
  · exact hT.mono (by grind)
  · simp only [Set.mem_inter_iff, Set.mem_Ioc] at ht
    exact 𝓕.mono ht.2.2 _ (measurableSet_regularitySet hX hT t)
lemma measurableSet_regularitySetRight'
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) :
    MeasurableSet (regularitySetRight T X d) := by
  rw [regularitySetRight]
  refine MeasurableSet.biUnion ?_ fun t ht ↦ ?_
  · exact hT.mono (by grind)
  · exact 𝓕.le _ _ (measurableSet_regularitySet hX hT t)
variable [TopologicalSpace ι] [OrderTopology ι]
omit [OrderBot ι] in
lemma right_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxd : x < d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_setOf_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    obtain ⟨M, hM⟩ := hω.2
    exact ⟨M, fun s hs => hM s hs.1 hs.2⟩
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_right hxd hfa hfb
  · refine ⟨((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
      Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
      Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind
omit [OrderBot ι] in
lemma left_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxle : x ≤ d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_setOf_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    obtain ⟨M, hM⟩ := hω.2
    exact ⟨M, fun s hs => hM s hs.1 hs.2⟩
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_left hxle hfa hfb
  · refine ⟨(M : ℝ) + 1, ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind
omit [OrderBot ι] in
lemma eventually_mem_regularitySetRight_of_mem {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight T X y := by
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop] at hω
  obtain ⟨d, ⟨hdT, hxd⟩, hω'⟩ := hω
  rw [eventually_nhdsWithin_iff]
  filter_upwards [eventually_lt_nhds hxd] with y hy hxy
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop]
  refine ⟨d, ⟨hdT, hy⟩, ?_⟩
  exact regularitySet_anti (by grind) hω'
omit [OrderBot ι] in
lemma right_limit_of_mem_regularitySetRight {T : Set ι}
    {x y : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) (hyx : y ≤ x) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi y] y) (𝓝 l) := by
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop] at hω
  obtain ⟨d, ⟨hdT, hxd⟩, hω'⟩ := hω
  exact right_limit_of_mem_regularitySet y d (by grind) hω'
omit [OrderBot ι] in
lemma eventually_right_limit_of_mem_regularitySetRight' {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi y] y) (𝓝 l) := by
  filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
  exact right_limit_of_mem_regularitySetRight hy le_rfl
omit [OrderBot ι] in
lemma left_limit_of_mem_regularitySetRight {T : Set ι}
    {x y : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) (hyx : y ≤ x) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio y] y) (𝓝 l) := by
  simp only [regularitySetRight, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, exists_prop] at hω
  obtain ⟨d, ⟨hdT, hxd⟩, hω'⟩ := hω
  exact left_limit_of_mem_regularitySet y d (by grind) hω'
omit [OrderBot ι] in
lemma eventually_left_limit_of_mem_regularitySetRight' {T : Set ι}
    {x : ι} {ω : Ω} (hω : ω ∈ regularitySetRight T X x) :
    ∀ᶠ y in 𝓝[>] x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio y] y) (𝓝 l) := by
  filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
  exact left_limit_of_mem_regularitySetRight hy le_rfl
lemma ae_right_limit [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ∃ d ∈ T, x < d) :
    ∀ᵐ ω ∂μ, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  filter_upwards [ae_mem_all_regularitySet hX hT] with ω hω
  intro x
  obtain ⟨d, hdT, hxd⟩ := hTcof x
  exact right_limit_of_mem_regularitySet x d hxd (hω d hdT)
lemma ae_left_limit [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ∃ d ∈ T, x ≤ d) :
    ∀ᵐ ω ∂μ, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  filter_upwards [ae_mem_all_regularitySet hX hT] with ω hω
  intro x
  obtain ⟨d, hdT, hxle⟩ := hTcof x
  exact left_limit_of_mem_regularitySet x d hxle (hω d hdT)
end RegularitySet
variable [TopologicalSpace ι] [OrderBot ι] [OrderTopology ι]
  [DenselyOrdered ι] [NoMaxOrder ι] 
section PathRegularization
variable {T : Set ι} {h r : ι → ℝ} {x : ι}
omit [OrderBot ι] in
lemma tendsto_rightLim_nhdsLT (hTd : Dense T)
    (hr : ∀ᶠ y in 𝓝[<] x, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {L : ℝ}
    (hL : Tendsto h (𝓝[T ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto r (𝓝[<] x) (𝓝 L) := by
  by_cases hex : ∃ u, u < x
  swap
  · have hempty : Set.Iio x = ∅ := Set.eq_empty_iff_forall_notMem.2
      (fun u hu ↦ hex ⟨u, hu⟩)
    rw [nhdsWithin, hempty, Filter.principal_empty, inf_bot_eq]
    exact tendsto_bot
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T, h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt hex).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hvx, hr] with y hy hr
  have hne := nhdsWithin_Ioi_inter_neBot hTd y
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto hr ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hy.2] with s hs hsT
  exact hv ⟨hy.1.trans hs.1, hs.2⟩ hsT
omit [OrderBot ι] in
lemma tendsto_rightLim_comp_of_lt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {u : ℕ → ι} {L : ℝ}
    (hux : ∀ k, u k < x) (hutend : Tendsto u atTop (𝓝 x))
    (hL : Tendsto h (𝓝[T' ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T', h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt ⟨u 0, hux 0⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Ioi v :=
    hutend (IsOpen.mem_nhds isOpen_Ioi hvx)
  filter_upwards [hevk] with k hk
  have hne := nhdsWithin_Ioi_inter_neBot hTd (u k)
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto (hr (u k)) ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT (hux k)] with s hs hsT
  exact hv ⟨hk.trans hs.1, hs.2⟩ (hTT' hsT)
omit [OrderBot ι] in
lemma tendsto_rightLim_comp_of_gt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y))) {u : ℕ → ι} {L : ℝ}
    (hux : ∀ k, x < u k) (hutend : Tendsto u atTop (𝓝 x))
    (hL : Tendsto h (𝓝[T' ∩ Set.Ioi x] x) (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[>] x ⊓ 𝓟 T', h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsGT_basis x).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Iio v :=
    hutend (IsOpen.mem_nhds isOpen_Iio hvx)
  filter_upwards [hevk] with k hk
  have hne := nhdsWithin_Ioi_inter_neBot hTd (u k)
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto (hr (u k)) ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hk] with s hs hsT
  exact hv ⟨(hux k).trans hs.1, hs.2⟩ (hTT' hsT)
end PathRegularization
section Accumulation
omit [OrderBot ι] [NoMaxOrder ι] in
lemma exists_seq_gt_tendsto_of_not_countable [TopologicalSpace.SeparableSpace ι]
    {A : Set ι} (hA : ¬ A.Countable) :
    ∃ (p : ι) (u : ℕ → ι), (∀ k, u k ∈ A) ∧ (∀ k, p < u k) ∧
      Tendsto u atTop (𝓝 p) := by
  have : SecondCountableTopology ι := .of_separableSpace_orderTopology _
  have h := countable_setOf_isolated_right_within (s := A)
  have hsub : ¬ A ⊆ {x | x ∈ A ∧ 𝓝[A ∩ Set.Ioi x] x = ⊥} := by
    intro hcon
    exact hA (h.mono hcon)
  rw [Set.not_subset] at hsub
  obtain ⟨p, hpA, hpiso⟩ := hsub
  simp only [Set.mem_setOf_eq, not_and] at hpiso
  have : (𝓝[A ∩ Set.Ioi p] p).NeBot := ⟨hpiso hpA⟩
  obtain ⟨u, hu⟩ := exists_seq_tendsto (𝓝[A ∩ Set.Ioi p] p)
  simp only [tendsto_nhdsWithin_iff, Set.mem_inter_iff, Set.mem_Ioi, eventually_atTop] at hu
  obtain ⟨hu_tendsto, a, hu⟩ := hu
  refine ⟨p, fun k ↦ u (a + k), fun k ↦ (hu (a + k) (by grind)).1,
    fun k ↦ (hu (a + k) (by grind)).2, ?_⟩
  simp_rw [add_comm a]
  exact (tendsto_add_atTop_iff_nat a).mpr hu_tendsto
end Accumulation
open Function
omit [OrderBot ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight
    {T : Set ι} {x : ι} {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 (rightLimWithin (X · ω) T x)) := by
  have h := right_limit_of_mem_regularitySetRight hmem le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_rightLimWithin_of_tendsto h
omit [OrderBot ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma tendsto_nhdsLT_leftLimWithin_of_mem_regularitySetRight
    {T : Set ι} {x : ι} {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 (leftLimWithin (X · ω) T x)) := by
  have h := left_limit_of_mem_regularitySetRight hmem le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_leftLimWithin_of_tendsto h
omit [OrderBot ι] in
lemma rightContinuous_rightLimWithin_of_mem_regularitySetRight
    {T : Set ι} (hTd : Dense T) {x : ι}
    {ω : Ω} (hmem : ω ∈ regularitySetRight T X x) :
    ContinuousWithinAt (rightLimWithin (X · ω) T) (Set.Ici x) x := by
  refine continuousWithinAt_rightLimWithin_Ici_of_dense hTd ?_ ?_
  · have h := right_limit_of_mem_regularitySetRight hmem le_rfl
    rw [Set.inter_comm] at h
    exact tendsto_rightLimWithin_of_tendsto h
  · have h_ev_mem : ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight T X y :=
      eventually_mem_regularitySetRight_of_mem hmem
    filter_upwards [h_ev_mem] with y hy
    rw [Set.inter_comm]
    exact tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hy
omit [OrderBot ι] in
lemma measurableSet_tendsto_nhdsGT [FirstCountableTopology ι] [𝓕.IsRightContinuous]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet[𝓕 t] {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} := by
  refine measurableSet_of_forall_gt fun s hts ↦ ?_
  let S : Set ι := (T ∩ Set.Ioi t) ∩ Set.Iio s
  have hScount : S.Countable := hT.mono (Set.inter_subset_left.trans Set.inter_subset_left)
  have hSlt x (hx : x ∈ S) : x < s := by unfold S at hx; exact hx.2
  have hSmem : S ∈ 𝓝[T ∩ Set.Ioi t] t :=
    Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hts)))
  have : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
  have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact hSmem)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable[𝓕 s] (X s') := (hX s').mono (𝓕.mono (hSlt s' s'.2).le) le_rfl
  exact @MeasureTheory.measurableSet_exists_tendsto S ℝ Ω (𝓕 s) _ _ _ _ _ _ l₀ _ _ hf
omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma measurableSet_tendsto_nhdsGT' [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} := by
  let S : Set ι := (T ∩ Set.Ioi t)
  have hScount : S.Countable := hT.mono (Set.inter_subset_left)
  have : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
  have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact self_mem_nhdsWithin)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable (X s') := (hX s').mono (𝓕.le _) le_rfl
  exact MeasureTheory.measurableSet_exists_tendsto hf
omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma measurableSet_tendsto_nhdsLT [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    MeasurableSet[𝓕 t] {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio t] t) (𝓝 l)} := by
  let S : Set ι := T ∩ Set.Iio t
  have hScount : S.Countable := hT.mono Set.inter_subset_left
  have hSlt x (hx : x ∈ S) : x < t := by unfold S at hx; exact hx.2
  have hSmem : S ∈ 𝓝[T ∩ Set.Iio t] t := self_mem_nhdsWithin
  haveI : Countable S := hScount.to_subtype
  set l₀ : Filter S := Filter.comap ((↑) : S → ι) (𝓝[T ∩ Set.Iio t] t) with hl₀
  haveI : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
  have hmap : Filter.map ((↑) : S → ι) l₀ = 𝓝[T ∩ Set.Iio t] t :=
    Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact hSmem)
  have hset : {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio t] t) (𝓝 l)}
      = {ω | ∃ c, Tendsto (fun s' : S ↦ X s' ω) l₀ (𝓝 c)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun c ↦ ?_
    rw [← hmap]
    exact tendsto_map'_iff
  rw [hset]
  have hf (s' : S) : Measurable[𝓕 t] (X s') := (hX s').mono (𝓕.mono (hSlt s' s'.2).le) le_rfl
  exact @MeasureTheory.measurableSet_exists_tendsto S ℝ Ω (𝓕 t) _ _ _ _ _ _ l₀ _ _ hf
end ProbabilityTheory


