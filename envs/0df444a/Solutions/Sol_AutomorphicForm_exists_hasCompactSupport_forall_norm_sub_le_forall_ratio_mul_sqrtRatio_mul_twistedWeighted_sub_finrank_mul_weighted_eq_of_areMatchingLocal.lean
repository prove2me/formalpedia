-- Prove2me | solution 1 for AutomorphicForm.exists_hasCompactSupport_forall_norm_sub_le_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_sub_finrank_mul_weighted_eq_of_areMatchingLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/521468a9-0aff-526b-aff2-1e80d6c3b8c1

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_eq_of_norm_sub_le_mul_norm_one_sub_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_sub_finrank_mul_weighted_eq_of_areMatchingLocal
import Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_ratio_mul_sqrtRatio_mul_eq_neg_two_mul_halfWeighted_of_isWeightedOrbitalIntegral
import Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_exists_isCompact_forall_halfWeighted_ne_zero_mem_and_forall_exists_nhds_halfWeighted_eq_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_hasCompactSupport_forall_norm_sub_le_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_sub_finrank_mul_weighted_eq_of_areMatchingLocal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace LocDiscPatch

open Filter Topology Metric

variable {F : Type*} [NormedField F] [IsUltrametricDist F] [ProperSpace F]

theorem units_norm_pos (a : Fˣ) : 0 < ‖(a : F)‖ := norm_pos_iff.2 a.ne_zero

theorem norm_eq_of_norm_sub_lt {a a' : F} (h : ‖a' - a‖ < ‖a‖) : ‖a'‖ = ‖a‖ := by
  apply le_antisymm
  · have h1 : ‖a'‖ = ‖(a' - a) + a‖ := by rw [sub_add_cancel]
    rw [h1]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le le_rfl)
  · by_contra hlt
    push_neg at hlt
    have h2 : ‖a‖ = ‖(a - a') + a'‖ := by rw [sub_add_cancel]
    have h3 : ‖a - a'‖ < ‖a‖ := by rwa [norm_sub_rev]
    have := (IsUltrametricDist.norm_add_le_max (a - a') a')
    rw [← h2] at this
    exact absurd (this.trans_lt (max_lt h3 hlt)) (lt_irrefl _)

theorem exists_radius_of_mem_nhds_one {U : Set Fˣ} (hU : U ∈ 𝓝 (1 : Fˣ)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 2⁻¹ ∧ ∀ t : Fˣ, ‖(t : F) - 1‖ ≤ r → t ∈ U := by
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  rw [Units.val_one, Metric.mem_nhds_iff] at hW
  obtain ⟨ε, hε, hεW⟩ := hW
  refine ⟨min (ε / 2) 2⁻¹, by positivity, min_le_right _ _, fun t ht => hWU ?_⟩
  show (t : F) ∈ W
  apply hεW
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt ht (lt_of_le_of_lt (min_le_left _ _) (by linarith))

theorem isCompact_preimage_closedBall_one {r : ℝ} (hr1 : r < 1) :
    IsCompact ((Units.val : Fˣ → F) ⁻¹' closedBall (1 : F) r) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, Set.image_preimage_eq_inter_range]
  have hsub : closedBall (1 : F) r ⊆ Set.range (Units.val : Fˣ → F) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, zero_sub, norm_neg, norm_one] at hx
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  rw [Set.inter_eq_left.2 hsub]
  exact isCompact_closedBall _ _

theorem isCompact_annulus {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) :
    IsCompact {a : Fˣ | c₁ ≤ ‖(a : F)‖ ∧ ‖(a : F)‖ ≤ c₂} := by
  have hset : {a : Fˣ | c₁ ≤ ‖(a : F)‖ ∧ ‖(a : F)‖ ≤ c₂} =
      (Units.val : Fˣ → F) ⁻¹' {x : F | c₁ ≤ ‖x‖ ∧ ‖x‖ ≤ c₂} := rfl
  rw [hset, Units.isEmbedding_val₀.isCompact_iff, Set.image_preimage_eq_inter_range]
  have hsub : {x : F | c₁ ≤ ‖x‖ ∧ ‖x‖ ≤ c₂} ⊆ Set.range (Units.val : Fˣ → F) := by
    intro x hx
    have hx1 : c₁ ≤ ‖x‖ := hx.1
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hx1
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  rw [Set.inter_eq_left.2 hsub]
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : F) c₂)
  · exact isClosed_Icc.preimage continuous_norm
  · intro x hx
    rw [mem_closedBall, dist_zero_right]
    exact hx.2

theorem isOpen_annulus {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    IsOpen {a : Fˣ | c₁ ≤ ‖(a : F)‖ ∧ ‖(a : F)‖ ≤ c₂} := by
  have h1 : IsOpen {x : F | c₁ ≤ ‖x‖} := by
    have : {x : F | c₁ ≤ ‖x‖} = (ball (0 : F) c₁)ᶜ := by
      ext x; simp [mem_ball, dist_zero_right, not_lt]
    rw [this]
    exact (IsUltrametricDist.isClosed_ball (0 : F) c₁).isOpen_compl
  have h2 : IsOpen {x : F | ‖x‖ ≤ c₂} := by
    have : {x : F | ‖x‖ ≤ c₂} = closedBall (0 : F) c₂ := by
      ext x; simp [mem_closedBall, dist_zero_right]
    rw [this]
    exact IsUltrametricDist.isOpen_closedBall (0 : F) hc₂.ne'
  exact (h1.preimage Units.continuous_val).inter (h2.preimage Units.continuous_val)

theorem continuousAt_of_exists_nhds {X : Type*} [TopologicalSpace X] {f : X → ℂ} {p : X}
    (h : ∃ V ∈ 𝓝 p, ∀ q ∈ V, f q = f p) : ContinuousAt f p := by
  obtain ⟨V, hV, hVf⟩ := h
  exact (continuousAt_const (y := f p)).congr (Filter.eventually_of_mem hV fun q hq => (hVf q hq).symm)

theorem patch (ΨR ΨL : Fˣ × Fˣ → ℂ) (U : Set Fˣ) (hU : U ∈ 𝓝 (1 : Fˣ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hRcs : HasCompactSupport ΨR)
    (hRlc : ∀ p : Fˣ × Fˣ, p.2 ≠ 1 → ∃ V ∈ 𝓝 p, ∀ q ∈ V, ΨR q = ΨR p)
    (hLcells : ∀ a a' t t' : Fˣ, t ∈ U →
      ‖(a' : F) - (a : F)‖ ≤ ρ * ‖(a : F)‖ →
      ‖(t' : F) - (t : F)‖ ≤ ρ * ‖(1 : F) - (t : F)‖ → ΨL (a', t') = ΨL (a, t))
    (hLgerm : ∃ C : ℝ, ∀ a t : Fˣ,
      ‖ΨL (a, t) - ΨL (a, 1)‖ ≤ C * ‖(1 : F) - (t : F)‖ * (1 + |Real.log ‖(1 : F) - (t : F)‖|))
    (Q : Fˣ → Fˣ → ℂ → Prop)
    (hRQ : ∀ a t : Fˣ, t ≠ 1 → Q a t (ΨR (a, t)))
    (hLQ : ∀ a t : Fˣ, t ≠ 1 → t ∈ U → Q a t (ΨL (a, t))) :
    ∃ Ψ : Fˣ × Fˣ → ℂ, HasCompactSupport Ψ ∧
      (∀ p : Fˣ × Fˣ, p.2 ≠ 1 → ∃ V ∈ 𝓝 p, ∀ q ∈ V, Ψ q = Ψ p) ∧
      (∃ U' ∈ 𝓝 (1 : Fˣ), ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ a a' t t' : Fˣ, t ∈ U' →
        ‖(a' : F) - (a : F)‖ ≤ ρ' * ‖(a : F)‖ →
        ‖(t' : F) - (t : F)‖ ≤ ρ' * ‖(1 : F) - (t : F)‖ → Ψ (a', t') = Ψ (a, t)) ∧
      (∃ C : ℝ, ∀ a t : Fˣ,
        ‖Ψ (a, t) - Ψ (a, 1)‖ ≤ C * ‖(1 : F) - (t : F)‖ * (1 + |Real.log ‖(1 : F) - (t : F)‖|)) ∧
      ∀ a t : Fˣ, t ≠ 1 → Q a t (Ψ (a, t)) := by
  classical
  obtain ⟨CL, hCL⟩ := hLgerm
  have h1U : (1 : Fˣ) ∈ U := mem_of_mem_nhds hU

  obtain ⟨r₁, hr₁, hr₁h, hr₁U⟩ := exists_radius_of_mem_nhds_one hU
  have hr₁1 : r₁ < 1 := lt_of_le_of_lt hr₁h (by norm_num)
  set U₁ : Set Fˣ := (Units.val : Fˣ → F) ⁻¹' closedBall (1 : F) r₁ with hU₁def
  have memU₁ : ∀ t : Fˣ, t ∈ U₁ ↔ ‖(t : F) - 1‖ ≤ r₁ := fun t => by
    simp [hU₁def, mem_closedBall, dist_eq_norm]
  have hU₁U : U₁ ⊆ U := fun t ht => hr₁U t ((memU₁ t).1 ht)
  have h1U₁ : (1 : Fˣ) ∈ U₁ := (memU₁ 1).2 (by simp [hr₁.le])
  have hU₁open : IsOpen U₁ := (IsUltrametricDist.isOpen_closedBall (1 : F) hr₁.ne').preimage Units.continuous_val
  have hU₁cpt : IsCompact U₁ := isCompact_preimage_closedBall_one hr₁1
  have hU₁nhds : U₁ ∈ 𝓝 (1 : Fˣ) := hU₁open.mem_nhds h1U₁

  obtain ⟨c₂, hc₂⟩ := hRcs.exists_bound_of_continuousOn
    (f := fun p : Fˣ × Fˣ => ((p.1 : Fˣ) : F)) (Units.continuous_val.comp continuous_fst).continuousOn
  obtain ⟨c₃, hc₃⟩ := hRcs.exists_bound_of_continuousOn
    (f := fun p : Fˣ × Fˣ => ((p.1⁻¹ : Fˣ) : F)) (Units.continuous_coe_inv.comp continuous_fst).continuousOn
  set c₁ : ℝ := (max c₃ 1)⁻¹ with hc₁def
  set c₂' : ℝ := max c₂ 1 with hc₂'def
  have hc₁ : 0 < c₁ := by positivity
  have hc₂' : 0 < c₂' := by positivity
  set A₀ : Set Fˣ := {a : Fˣ | c₁ ≤ ‖(a : F)‖ ∧ ‖(a : F)‖ ≤ c₂'} with hA₀def
  have hA₀K : ∀ p ∈ tsupport ΨR, p.1 ∈ A₀ := by
    intro p hp
    refine ⟨?_, (hc₂ p hp).trans (le_max_left _ _)⟩
    have hinv : ‖((p.1⁻¹ : Fˣ) : F)‖ ≤ max c₃ 1 := (hc₃ p hp).trans (le_max_left _ _)
    have hpos := units_norm_pos p.1
    rw [Units.val_inv_eq_inv_val, norm_inv] at hinv
    rw [hc₁def]
    exact inv_le_of_inv_le₀ hpos hinv
  have hA₀cpt : IsCompact A₀ := isCompact_annulus hc₁
  have hA₀open : IsOpen A₀ := isOpen_annulus hc₁ hc₂'
  have hR0 : ∀ a t : Fˣ, a ∉ A₀ → ΨR (a, t) = 0 := fun a t ha =>
    image_eq_zero_of_notMem_tsupport fun h => ha (hA₀K (a, t) h)

  set D : Set (Fˣ × Fˣ) := A₀ ×ˢ U₁ with hDdef
  have hDopen : IsOpen D := hA₀open.prod hU₁open
  have hDclosed : IsClosed D := hA₀cpt.isClosed.prod hU₁cpt.isClosed
  let Ψ : Fˣ × Fˣ → ℂ := fun p => if p ∈ D then ΨL p else ΨR p
  have hΨD : ∀ p, p ∈ D → Ψ p = ΨL p := fun p hp => if_pos hp
  have hΨnD : ∀ p, p ∉ D → Ψ p = ΨR p := fun p hp => if_neg hp
  refine ⟨Ψ, ?_, ?_, ⟨U₁, hU₁nhds, min ρ 2⁻¹, by positivity, ?_⟩, ?_, ?_⟩
  ·
    refine HasCompactSupport.intro (hRcs.union (hA₀cpt.prod hU₁cpt)) fun p hp => ?_
    rw [Set.mem_union, not_or] at hp
    rw [hΨnD p hp.2]
    exact image_eq_zero_of_notMem_tsupport hp.1
  ·
    rintro ⟨a, t⟩ ht
    have ht' : (t : F) ≠ 1 := fun h => ht (Units.val_eq_one.1 h)
    by_cases hD : (a, t) ∈ D
    · have hO1 : IsOpen {q : Fˣ × Fˣ | ‖(q.1 : F) - (a : F)‖ < ρ * ‖(a : F)‖} :=
        isOpen_lt (continuous_norm.comp ((Units.continuous_val.comp continuous_fst).sub continuous_const))
          continuous_const
      have hO2 : IsOpen {q : Fˣ × Fˣ | ‖(q.2 : F) - (t : F)‖ < ρ * ‖(1 : F) - (t : F)‖} :=
        isOpen_lt (continuous_norm.comp ((Units.continuous_val.comp continuous_snd).sub continuous_const))
          continuous_const
      have hm1 : (a, t) ∈ {q : Fˣ × Fˣ | ‖(q.1 : F) - (a : F)‖ < ρ * ‖(a : F)‖} := by
        show ‖(a : F) - (a : F)‖ < ρ * ‖(a : F)‖
        rw [sub_self, norm_zero]; exact mul_pos hρ (units_norm_pos a)
      have hm2 : (a, t) ∈ {q : Fˣ × Fˣ | ‖(q.2 : F) - (t : F)‖ < ρ * ‖(1 : F) - (t : F)‖} := by
        show ‖(t : F) - (t : F)‖ < ρ * ‖(1 : F) - (t : F)‖
        rw [sub_self, norm_zero]; exact mul_pos hρ (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm ht')))
      refine ⟨D ∩ ({q : Fˣ × Fˣ | ‖(q.1 : F) - (a : F)‖ < ρ * ‖(a : F)‖} ∩
          {q : Fˣ × Fˣ | ‖(q.2 : F) - (t : F)‖ < ρ * ‖(1 : F) - (t : F)‖}),
        (hDopen.inter (hO1.inter hO2)).mem_nhds ⟨hD, hm1, hm2⟩, ?_⟩
      rintro ⟨a', t'⟩ ⟨hqD, hqa, hqt⟩
      rw [hΨD _ hqD, hΨD _ hD]
      exact hLcells a a' t t' (hU₁U hD.2) (le_of_lt hqa) (le_of_lt hqt)
    · obtain ⟨V, hV, hVR⟩ := hRlc (a, t) ht
      refine ⟨Dᶜ ∩ V, Filter.inter_mem (hDclosed.isOpen_compl.mem_nhds hD) hV, ?_⟩
      rintro q ⟨hqD, hqV⟩
      rw [hΨnD _ hqD, hΨnD _ hD]
      exact hVR q hqV
  ·
    intro a a' t t' ht ha' ht'
    have hρ' : min ρ 2⁻¹ ≤ ρ := min_le_left _ _
    have ha'ρ : ‖(a' : F) - (a : F)‖ ≤ ρ * ‖(a : F)‖ :=
      ha'.trans (mul_le_mul_of_nonneg_right hρ' (norm_nonneg _))
    have ht'ρ : ‖(t' : F) - (t : F)‖ ≤ ρ * ‖(1 : F) - (t : F)‖ :=
      ht'.trans (mul_le_mul_of_nonneg_right hρ' (norm_nonneg _))
    have htr : ‖(t : F) - 1‖ ≤ r₁ := (memU₁ t).1 ht
    have ht'U₁ : t' ∈ U₁ := by
      rw [memU₁]
      have e : (t' : F) - 1 = ((t' : F) - t) + ((t : F) - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ htr)
      refine ht'.trans ?_
      rw [norm_sub_rev]
      calc min ρ 2⁻¹ * ‖(t : F) - 1‖ ≤ 1 * ‖(t : F) - 1‖ :=
            mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (by norm_num)) (norm_nonneg _)
        _ ≤ r₁ := by rw [one_mul]; exact htr
    have hnorm : ‖(a' : F)‖ = ‖(a : F)‖ := by
      apply norm_eq_of_norm_sub_lt
      refine lt_of_le_of_lt ha' ?_
      calc min ρ 2⁻¹ * ‖(a : F)‖ ≤ 2⁻¹ * ‖(a : F)‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ < ‖(a : F)‖ := by linarith [units_norm_pos a]
    by_cases haA : a ∈ A₀
    · have ha'A : a' ∈ A₀ := by simp only [hA₀def, Set.mem_setOf_eq, hnorm] at haA ⊢; exact haA
      rw [hΨD _ ⟨ha'A, ht'U₁⟩, hΨD _ ⟨haA, ht⟩]
      exact hLcells a a' t t' (hU₁U ht) ha'ρ ht'ρ
    · have ha'A : a' ∉ A₀ := by simp only [hA₀def, Set.mem_setOf_eq, hnorm] at haA ⊢; exact haA
      rw [hΨnD _ (fun h => ha'A h.1), hΨnD _ (fun h => haA h.1), hR0 a' t' ha'A, hR0 a t haA]
  ·
    have hg : Continuous fun a : Fˣ => ΨL (a, 1) := by
      refine continuous_iff_continuousAt.2 fun a => continuousAt_of_exists_nhds ?_
      have hO : IsOpen {a' : Fˣ | ‖(a' : F) - (a : F)‖ < ρ * ‖(a : F)‖} :=
        isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
      have hm : a ∈ {a' : Fˣ | ‖(a' : F) - (a : F)‖ < ρ * ‖(a : F)‖} := by
        show ‖(a : F) - (a : F)‖ < ρ * ‖(a : F)‖
        rw [sub_self, norm_zero]; exact mul_pos hρ (units_norm_pos a)
      refine ⟨{a' : Fˣ | ‖(a' : F) - (a : F)‖ < ρ * ‖(a : F)‖}, hO.mem_nhds hm, fun a' ha' => ?_⟩
      exact hLcells a a' 1 1 h1U (le_of_lt ha') (by simp)
    obtain ⟨ML, hML⟩ := hA₀cpt.exists_bound_of_continuousOn hg.continuousOn
    set E : Set (Fˣ × Fˣ) := tsupport ΨR ∩ {p | r₁ ≤ ‖(p.2 : F) - 1‖} with hEdef
    have hEcpt : IsCompact E := hRcs.inter_right
      (isClosed_le continuous_const (continuous_norm.comp ((Units.continuous_val.comp continuous_snd).sub continuous_const)))
    have hEcont : ContinuousOn ΨR E := by
      intro p hp
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_of_exists_nhds
      apply hRlc p
      intro h1
      have : r₁ ≤ ‖((p.2 : Fˣ) : F) - 1‖ := hp.2
      rw [h1, Units.val_one, sub_self, norm_zero] at this
      linarith
    obtain ⟨MR, hMR⟩ := hEcpt.exists_bound_of_continuousOn hEcont
    set M : ℝ := max ML 0 + max MR 0 with hMdef
    have hM0 : 0 ≤ M := by positivity
    refine ⟨max CL 0 + M / r₁, fun a t => ?_⟩
    have hX : 0 ≤ ‖(1 : F) - (t : F)‖ * (1 + |Real.log ‖(1 : F) - (t : F)‖|) := by positivity
    have hC0 : 0 ≤ max CL 0 + M / r₁ := by positivity
    by_cases haA : a ∈ A₀
    · have h1D : (a, (1 : Fˣ)) ∈ D := ⟨haA, h1U₁⟩
      by_cases htU : t ∈ U₁
      · rw [hΨD _ ⟨haA, htU⟩, hΨD _ h1D]
        refine (hCL a t).trans ?_
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_add_of_nonneg_right (by positivity))) hX
      · rw [hΨnD _ (fun h => htU h.2), hΨD _ h1D]
        have hRb : ‖ΨR (a, t)‖ ≤ max MR 0 := by
          by_cases hsupp : (a, t) ∈ tsupport ΨR
          · refine (hMR (a, t) ⟨hsupp, ?_⟩).trans (le_max_left _ _)
            show r₁ ≤ ‖(t : F) - 1‖
            exact le_of_not_ge fun h => htU ((memU₁ t).2 h)
          · rw [image_eq_zero_of_notMem_tsupport hsupp, norm_zero]; exact le_max_right _ _
        have hLb : ‖ΨL (a, 1)‖ ≤ max ML 0 := (hML a haA).trans (le_max_left _ _)
        have hrt : r₁ ≤ ‖(1 : F) - (t : F)‖ := by
          rw [norm_sub_rev]; exact le_of_not_ge fun h => htU ((memU₁ t).2 h)
        have hlog : 1 ≤ 1 + |Real.log ‖(1 : F) - (t : F)‖| := by
          linarith [abs_nonneg (Real.log ‖(1 : F) - (t : F)‖)]
        calc ‖ΨR (a, t) - ΨL (a, 1)‖ ≤ ‖ΨR (a, t)‖ + ‖ΨL (a, 1)‖ := norm_sub_le _ _
          _ ≤ M := by rw [hMdef]; linarith
          _ = (M / r₁) * r₁ * 1 := by field_simp
          _ ≤ (M / r₁) * ‖(1 : F) - (t : F)‖ * (1 + |Real.log ‖(1 : F) - (t : F)‖|) := by
              apply mul_le_mul _ hlog zero_le_one (by positivity)
              exact mul_le_mul_of_nonneg_left hrt (by positivity)
          _ ≤ (max CL 0 + M / r₁) * ‖(1 : F) - (t : F)‖ * (1 + |Real.log ‖(1 : F) - (t : F)‖|) := by
              rw [mul_assoc, mul_assoc]
              exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hX
    · rw [hΨnD _ (fun h => haA h.1), hΨnD _ (fun h => haA h.1), hR0 a t haA, hR0 a 1 haA, sub_self,
        norm_zero]
      rw [mul_assoc]; exact mul_nonneg hC0 hX
  ·
    intro a t ht
    by_cases hD : (a, t) ∈ D
    · rw [hΨD _ hD]; exact hLQ a t ht (hU₁U hD.2)
    · rw [hΨnD _ hD]; exact hRQ a t ht

end LocDiscPatch

namespace R3pAux

open Filter Topology Metric

variable {F : Type*} [NormedField F] [IsUltrametricDist F] [ProperSpace F]

theorem exists_nhds_ratio_sqrtRatio_eq (a t : Fˣ) (ht : t ≠ 1) :
    ∃ V ∈ 𝓝 (a, t), ∀ p : Fˣ × Fˣ, p ∈ V →
      AutomorphicForm.LocalWeightedOrbital.ratio (fun x : F => ‖x‖) p.1 (p.1 * p.2) =
        AutomorphicForm.LocalWeightedOrbital.ratio (fun x : F => ‖x‖) a (a * t) ∧
      AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : F => ‖x‖) p.1 (p.1 * p.2) =
        AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : F => ‖x‖) a (a * t) := by
  have hratio : ∀ b s : Fˣ, AutomorphicForm.LocalWeightedOrbital.ratio (fun x : F => ‖x‖) b (b * s) =
      ‖(1 : F) - (s : F)‖ := by
    intro b s
    simp only [AutomorphicForm.LocalWeightedOrbital.ratio, Units.val_mul]
    rw [mul_comm ((b : F)) (s : F), mul_assoc, Units.mul_inv, mul_one]
  have hsqrt : ∀ b s : Fˣ, AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : F => ‖x‖) b (b * s) =
      Real.sqrt (‖(s : F)‖⁻¹) := by
    intro b s
    simp only [AutomorphicForm.LocalWeightedOrbital.sqrtRatio, Units.val_mul, norm_mul]
    have hb : ‖(b : F)‖ ≠ 0 := norm_ne_zero_iff.mpr b.ne_zero
    rw [div_mul_eq_div_div, div_self hb, one_div]
  have ht' : (t : F) ≠ 1 := fun h => ht (Units.val_eq_one.1 h)
  have h1t : 0 < ‖(1 : F) - (t : F)‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm ht'))
  have h0t : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  set W : Set (Fˣ × Fˣ) := {p | ‖(p.2 : F) - (t : F)‖ < min ‖(1 : F) - (t : F)‖ ‖(t : F)‖} with hW
  have hWo : IsOpen W :=
    isOpen_lt (continuous_norm.comp ((Units.continuous_val.comp continuous_snd).sub continuous_const))
      continuous_const
  have hmem : (a, t) ∈ W := by
    show ‖(t : F) - (t : F)‖ < min ‖(1 : F) - (t : F)‖ ‖(t : F)‖
    rw [sub_self, norm_zero]; exact lt_min h1t h0t
  refine ⟨W, hWo.mem_nhds hmem, fun p hp => ?_⟩
  have hp1 : ‖(p.2 : F) - (t : F)‖ < ‖(1 : F) - (t : F)‖ := lt_of_lt_of_le hp (min_le_left _ _)
  have hp2 : ‖(p.2 : F) - (t : F)‖ < ‖(t : F)‖ := lt_of_lt_of_le hp (min_le_right _ _)
  have e1 : ‖(1 : F) - (p.2 : F)‖ = ‖(1 : F) - (t : F)‖ := by
    apply LocDiscPatch.norm_eq_of_norm_sub_lt
    have : (1 : F) - (p.2 : F) - ((1 : F) - (t : F)) = -((p.2 : F) - (t : F)) := by ring
    rw [this, norm_neg]; exact hp1
  have e2 : ‖(p.2 : F)‖ = ‖(t : F)‖ := LocDiscPatch.norm_eq_of_norm_sub_lt hp2
  exact ⟨by rw [hratio, hratio, e1], by rw [hsqrt, hsqrt, e2]⟩

end R3pAux

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f) :
    ∃ Ψ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, HasCompactSupport Ψ ∧
      (∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Ψ q = Ψ p) ∧
      (∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
        ‖Ψ (a, t) - Ψ (a, 1)‖ ≤ C * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ *
          (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|)) ∧
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 →
        ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a (a * t)))
            (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a (a * t)))),
          @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a (a * t))) τ →
          τ {x | (x : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1 →
        ∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a (a * t)) τ f J →
          ((∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) *
                (J' - (Module.finrank K L : ℂ) * J) = Ψ (a, t)) ∧
          ((¬ ∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) *
                (0 - (Module.finrank K L : ℂ) * J) = Ψ (a, t))) := by

  classical
  letI mF : MeasurableSpace (v.adicCompletion K) := borel _
  haveI bF : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  letI glF : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v

  have hOc : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hOo : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    (NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v
  obtain ⟨μ, hμH, hμ1⟩ : ∃ μ : Measure (v.adicCompletion K), μ.IsAddHaarMeasure ∧
      μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
    have h0 : (Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ 0 :=
      (hOo.measure_pos Measure.addHaar ⟨0, (v.adicCompletionIntegers K).zero_mem⟩).ne'
    have htop : (Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ ⊤ :=
      hOc.measure_lt_top.ne
    refine ⟨((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
        (Measure.addHaar : Measure (v.adicCompletion K)), ?_, ?_⟩
    · exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)
    · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]
  haveI := hμH

  obtain ⟨ΨL, U, hU, ρ, hρ, hLcells, hLgerm, hLQ⟩ :=
    AutomorphicForm.exists_nhds_forall_eq_of_norm_sub_le_mul_norm_one_sub_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_sub_finrank_mul_weighted_eq_of_areMatchingLocal
      K L σ hgen hdeg v φ hφ f hf hmatch
  obtain ⟨⟨SH, hSHc, hH0⟩, hHlc⟩ :=
    AutomorphicForm.LocalWeightedOrbital.exists_isCompact_forall_halfWeighted_ne_zero_mem_and_forall_exists_nhds_halfWeighted_eq_of_isLocalTestFn K v μ f hf
  obtain ⟨Φ, hΦlc, ⟨SΦ, hSΦc, hΦ0⟩, hΦval⟩ :=
    AutomorphicForm.exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn K L σ hgen hdeg v φ hφ
  have hdict := AutomorphicForm.LocalWeightedOrbital.ratio_mul_sqrtRatio_mul_eq_neg_two_mul_halfWeighted_of_isWeightedOrbitalIntegral
    K v μ hμ1 f hf

  let ΨR : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ := fun p =>
    if p.2 = 1 then 0 else ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) p.1 (p.1 * p.2) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) p.1 (p.1 * p.2) : ℝ) : ℂ) * Φ p + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : v.adicCompletion K => ‖x‖) f p.1 (p.1 * p.2)
  have hΨR : ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 →
      ΨR (a, t) = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * Φ (a, t) + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : v.adicCompletion K => ‖x‖) f a (a * t) := by
    intro a t ht
    simp only [ΨR, if_neg ht]
  have hΨR1 : ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 = 1 → ΨR p = 0 := by
    intro p hp
    simp only [ΨR, if_pos hp]

  let Q : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → ℂ → Prop := fun a t z =>
    ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a (a * t)))
        (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a (a * t)))),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a (a * t))) τ →
      τ {x | (x : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1 →
    ∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a (a * t)) τ f J →
      ((∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
          AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
            AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
        ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
          τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
        ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
          ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * (J' - (Module.finrank K L : ℂ) * J) = z) ∧
      ((¬ ∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
          AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
            AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) →
          ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * (0 - (Module.finrank K L : ℂ) * J) = z))

  have hRQ : ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → Q a t (ΨR (a, t)) := by
    intro a t ht τ hτ hτ1 J hJ
    have hat : a ≠ a * t := by
      intro h
      apply ht
      have h' : a * t = a * 1 := by rw [mul_one]; exact h.symm
      exact mul_left_cancel h'
    have hJd : ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * J = -2 * AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : v.adicCompletion K => ‖x‖) f a (a * t) := hdict a (a * t) hat τ hτ hτ1 J hJ
    rw [hΨR a t ht]
    refine ⟨fun α β hαβ τ' hτ' hτ'1 J' hJ' => ?_, fun hno => ?_⟩
    · have hJ'Φ : J' = Φ (a, t) := (hΦval a t ht).1 α β hαβ τ' hτ' hτ'1 J' hJ'
      calc ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * (J' - (Module.finrank K L : ℂ) * J)
          = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * J' - (Module.finrank K L : ℂ) * (((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * J) := by ring
        _ = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * Φ (a, t) + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : v.adicCompletion K => ‖x‖) f a (a * t) := by
          rw [hJd, hJ'Φ]; ring
    · have hΦ0' : Φ (a, t) = 0 := (hΦval a t ht).2 hno
      calc ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * (0 - (Module.finrank K L : ℂ) * J)
          = -((Module.finrank K L : ℂ) * (((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * J)) := by ring
        _ = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) * AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * Φ (a, t) + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : v.adicCompletion K => ‖x‖) f a (a * t) := by
          rw [hJd, hΦ0']; ring
  have hLQ' : ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U → Q a t (ΨL (a, t)) :=
    fun a t ht htU => hLQ a t ht htU

  have hRcs : HasCompactSupport ΨR := by
    refine HasCompactSupport.intro (hSΦc.union hSHc) fun p hp => ?_
    rw [Set.mem_union, not_or] at hp
    by_cases hp2 : p.2 = 1
    · exact hΨR1 p hp2
    · have h1 : Φ (p.1, p.2) = 0 := by
        by_contra h
        exact hp.1 (hΦ0 p.1 p.2 hp2 h)
      have h2 : AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : v.adicCompletion K => ‖x‖) f p.1 (p.1 * p.2) = 0 := by
        by_contra h
        exact hp.2 (hH0 p.1 p.2 h)
      rw [show p = (p.1, p.2) from rfl, hΨR p.1 p.2 hp2, h1, h2, mul_zero, mul_zero, add_zero]

  have hRlc : ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 →
      ∃ V ∈ nhds p, ∀ q ∈ V, ΨR q = ΨR p := by
    rintro ⟨a, t⟩ ht
    obtain ⟨V₁, hV₁, hV₁Φ⟩ := hΦlc (a, t) ht
    obtain ⟨V₂, hV₂, hV₂H⟩ := hHlc a t ht
    obtain ⟨V₃, hV₃, hV₃rs⟩ := R3pAux.exists_nhds_ratio_sqrtRatio_eq a t ht
    have hO : IsOpen {q : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ | q.2 ≠ 1} :=
      isOpen_ne_fun continuous_snd continuous_const
    refine ⟨{q | q.2 ≠ 1} ∩ (V₁ ∩ (V₂ ∩ V₃)),
      Filter.inter_mem (hO.mem_nhds ht) (Filter.inter_mem hV₁ (Filter.inter_mem hV₂ hV₃)), ?_⟩
    intro q hq
    obtain ⟨hqt, hq₁, hq₂, hq₃⟩ := hq
    have hqt' : q.2 ≠ 1 := hqt
    obtain ⟨e1, e2⟩ := hV₃rs q hq₃
    rw [show q = (q.1, q.2) from rfl, hΨR q.1 q.2 hqt', hΨR a t ht, ← show q = (q.1, q.2) from rfl, hV₁Φ q hq₁,
      hV₂H q hq₂, e1, e2]

  obtain ⟨Ψ, hcs, hlc, -, hgerm, hQ⟩ :=
    LocDiscPatch.patch ΨR ΨL U hU ρ hρ hRcs hRlc hLcells hLgerm Q hRQ hLQ'
  exact ⟨Ψ, hcs, hlc, hgerm, fun a t ht => hQ a t ht⟩

end S_AutomorphicForm_exists_hasCompactSupport_forall_norm_sub_le_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_sub_finrank_mul_weighted_eq_of_areMatchingLocal
end P2MW
export P2MW.S_AutomorphicForm_exists_hasCompactSupport_forall_norm_sub_le_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_sub_finrank_mul_weighted_eq_of_areMatchingLocal (solution)
