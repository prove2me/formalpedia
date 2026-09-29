-- Prove2me | solution 1 for AutomorphicForm.exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1c91ee85-0abc-5afe-b7c0-2d34159fdcfd

import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Set NumberField IsDedekindDomain NumberField.TateGlobal Matrix
open scoped ENNReal NNReal Pointwise TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mCentralCovolQuat

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant]
  (Γ : Subgroup G) [Countable Γ]
  (φ : G → ℝ) (s : ℝ → G)

theorem isFundamentalDomain_smul_of_comm {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) (g : G)
    (hg : ∀ γ ∈ Γ, γ * g = g * γ) : IsFundamentalDomain Γ (g • Ω) μ := by
  refine hΩ.image_of_equiv (MulAction.toPerm g)
    (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving (Equiv.refl _) fun γ x => ?_
  show g • ((γ : G) * x) = (γ : G) * (g • x)
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, hg γ γ.2]

def slabMeasure (Ω : Set G) : Measure ℝ := Measure.map φ (μ.restrict Ω)

variable {μ φ}

theorem slabMeasure_apply (hφ : Measurable φ) (Ω : Set G) {B : Set ℝ} (hB : MeasurableSet B) :
    slabMeasure μ φ Ω B = μ (φ ⁻¹' B ∩ Ω) := by
  rw [slabMeasure, Measure.map_apply hφ hB, Measure.restrict_apply (hφ hB)]

theorem slabMeasure_mono (Ω : Set G) {B B' : Set ℝ} (h : B ⊆ B') :
    slabMeasure μ φ Ω B ≤ slabMeasure μ φ Ω B' := measure_mono h

variable {Γ s}

theorem preimage_smul_preimage_eq (hφmul : ∀ x y, φ (x * y) = φ x + φ y)
    (hΓ : ∀ γ ∈ Γ, φ γ = 0) (B : Set ℝ) (γ : Γ) :
    (fun x : G => γ • x) ⁻¹' (φ ⁻¹' B) = φ ⁻¹' B := by
  ext x
  simp only [mem_preimage, Subgroup.smul_def, smul_eq_mul, hφmul, hΓ γ γ.2, zero_add]

theorem slabMeasure_preimage_const_add (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) (t : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    slabMeasure μ φ Ω ((fun x => t + x) ⁻¹' B) = slabMeasure μ φ Ω B := by
  have hB' : MeasurableSet ((fun x => t + x) ⁻¹' B) := measurable_const_add t hB
  rw [slabMeasure_apply hφ Ω hB', slabMeasure_apply hφ Ω hB]

  have hpre : φ ⁻¹' ((fun x => t + x) ⁻¹' B) = (fun h => s t * h) ⁻¹' (φ ⁻¹' B) := by
    ext x
    simp only [mem_preimage, hφmul, hs]
  have hΩ' : IsFundamentalDomain Γ (s t • Ω) μ := isFundamentalDomain_smul_of_comm μ Γ hΩ (s t) (hcomm t)
  have hinj : Function.Injective fun h : G => s t * h := mul_right_injective (s t)
  have hpreΩ : (fun h => s t * h) ⁻¹' (s t • Ω) = Ω := by
    rw [← image_smul]
    exact hinj.preimage_image Ω
  calc μ (φ ⁻¹' ((fun x => t + x) ⁻¹' B) ∩ Ω)
      = μ ((fun h => s t * h) ⁻¹' (φ ⁻¹' B ∩ s t • Ω)) := by
        rw [preimage_inter, hpre, hpreΩ]
    _ = μ (φ ⁻¹' B ∩ s t • Ω) := measure_preimage_mul μ (s t) _
    _ = μ (φ ⁻¹' B ∩ Ω) :=
        hΩ'.measure_set_eq hΩ (hφ hB) (preimage_smul_preimage_eq hφmul hΓ B)

theorem isAddLeftInvariant_slabMeasure (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) :
    (slabMeasure μ φ Ω).IsAddLeftInvariant := by
  refine ⟨fun t => Measure.ext fun B hB => ?_⟩
  rw [Measure.map_apply (measurable_const_add t) hB]
  exact slabMeasure_preimage_const_add hφ hφmul hΓ hs hcomm hΩ t hB

theorem isFiniteMeasureOnCompacts_slabMeasure (hφ : Measurable φ) {Ω : Set G}
    (hfin : ∀ R : ℝ, μ (φ ⁻¹' Icc (-R) R ∩ Ω) < ⊤) :
    IsFiniteMeasureOnCompacts (slabMeasure μ φ Ω) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hK.isBounded
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
  calc slabMeasure μ φ Ω K ≤ slabMeasure μ φ Ω (Icc (-R) R) := measure_mono hR
    _ = μ (φ ⁻¹' Icc (-R) R ∩ Ω) := slabMeasure_apply hφ Ω measurableSet_Icc
    _ < ⊤ := hfin R

theorem exists_measure_preimage_Icc_inter_eq (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω₀ : Set G} (hΩ₀ : IsFundamentalDomain Γ Ω₀ μ)
    (hfin : ∀ R : ℝ, μ (φ ⁻¹' Icc (-R) R ∩ Ω₀) < ⊤) :
    ∃ c : ℝ≥0, (μ ≠ 0 → c ≠ 0) ∧
      ∀ Ω : Set G, IsFundamentalDomain Γ Ω μ → ∀ a b : ℝ,
        μ (φ ⁻¹' Icc a b ∩ Ω) = (c : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  set m : Measure ℝ := slabMeasure μ φ Ω₀ with hm
  haveI : m.IsAddLeftInvariant := isAddLeftInvariant_slabMeasure hφ hφmul hΓ hs hcomm hΩ₀
  haveI : IsFiniteMeasureOnCompacts m := isFiniteMeasureOnCompacts_slabMeasure hφ hfin
  have hIcc : ∀ a b : ℝ, m (Icc a b) = (m.addHaarScalarFactor volume : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
    intro a b
    have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure m volume
      (s := Icc a b) (by rw [closure_Icc]; exact isCompact_Icc)
    rw [h, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul]
  refine ⟨m.addHaarScalarFactor volume, fun hμ hc => ?_, fun Ω hΩ a b => ?_⟩
  ·
    apply hΩ₀.measure_ne_zero hμ
    have huniv : m univ = 0 := by
      have hcov : (univ : Set ℝ) = ⋃ n : ℕ, Icc (-(n : ℝ)) n := by
        refine (eq_univ_of_forall fun x => mem_iUnion.2 ?_).symm
        obtain ⟨n, hn⟩ := exists_nat_ge |x|
        exact ⟨n, abs_le.1 hn⟩
      rw [hcov]
      refine measure_iUnion_null fun n => ?_
      rw [hIcc, hc, ENNReal.coe_zero, zero_mul]
    have := slabMeasure_apply (μ := μ) hφ Ω₀ MeasurableSet.univ
    rw [preimage_univ, univ_inter] at this
    rw [← this]
    exact huniv
  · rw [← hΩ₀.measure_set_eq hΩ (hφ measurableSet_Icc) (preimage_smul_preimage_eq hφmul hΓ _),
      ← slabMeasure_apply hφ Ω₀ measurableSet_Icc]
    exact hIcc a b

theorem measure_preimage_inter_lt_top_of_subset_iUnion_smul [IsFiniteMeasureOnCompacts μ]
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) {A C : Set G} (hC : IsCompact C)
    (hAC : A ⊆ ⋃ γ : Γ, γ • C) : μ (A ∩ Ω) < ⊤ := by
  calc μ (A ∩ Ω) ≤ μ ((⋃ γ : Γ, γ • C) ∩ Ω) := measure_mono (inter_subset_inter_left _ hAC)
    _ = μ (⋃ γ : Γ, γ • C ∩ Ω) := by rw [iUnion_inter]
    _ ≤ ∑' γ : Γ, μ (γ • C ∩ Ω) := measure_iUnion_le _
    _ = μ C := (hΩ.measure_eq_tsum C).symm
    _ < ⊤ := hC.measure_lt_top

theorem measure_preimage_Icc_inter_lt_top_of_one (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) {a₀ b₀ : ℝ} (hab₀ : a₀ < b₀)
    (hfin₀ : μ (φ ⁻¹' Icc a₀ b₀ ∩ Ω) < ⊤) (R : ℝ) :
    μ (φ ⁻¹' Icc (-R) R ∩ Ω) < ⊤ := by
  set m : Measure ℝ := slabMeasure μ φ Ω with hm
  have hm₀ : m (Icc a₀ b₀) < ⊤ := by rwa [hm, slabMeasure_apply hφ Ω measurableSet_Icc]

  have htrans : ∀ t : ℝ, m (Icc (a₀ + t) (b₀ + t)) = m (Icc a₀ b₀) := by
    intro t
    have h := slabMeasure_preimage_const_add hφ hφmul hΓ hs hcomm hΩ (-t) (measurableSet_Icc (a := a₀) (b := b₀))
    rw [Set.preimage_const_add_Icc, sub_neg_eq_add, sub_neg_eq_add] at h
    exact h

  set w : ℝ := b₀ - a₀ with hw
  have hw0 : 0 < w := sub_pos.2 hab₀
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (R + |a₀|) / w + 1 ≤ M := exists_nat_ge _
  have hcov : Icc (-R) R ⊆ ⋃ k ∈ Finset.Icc (-(M : ℤ)) M, Icc (a₀ + (k : ℝ) * w) (b₀ + (k : ℝ) * w) := by
    intro x hx
    set k : ℤ := ⌊(x - a₀) / w⌋ with hk
    have hk1 : (k : ℝ) ≤ (x - a₀) / w := Int.floor_le _
    have hk2 : (x - a₀) / w < k + 1 := Int.lt_floor_add_one _
    have hxR : |x| ≤ R := abs_le.2 hx
    have hbound : |(x - a₀) / w| ≤ (R + |a₀|) / w := by
      rw [abs_div, abs_of_pos hw0]
      exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by linarith)) hw0.le
    have hkabs : |(k : ℝ)| ≤ (R + |a₀|) / w + 1 := by
      rw [abs_le]
      constructor
      · have := (abs_le.1 hbound).1
        linarith
      · have := (abs_le.1 hbound).2
        linarith
    have hkM : -(M : ℤ) ≤ k ∧ k ≤ M := by
      have h := abs_le.1 (hkabs.trans hM)
      constructor
      · have h1 : ((-(M : ℤ) : ℤ) : ℝ) ≤ (k : ℝ) := by push_cast; exact h.1
        exact Int.cast_le.1 h1
      · have h2 : ((k : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by push_cast; exact h.2
        exact Int.cast_le.1 h2
    refine mem_iUnion₂.2 ⟨k, Finset.mem_Icc.2 hkM, ?_⟩
    have h1 : (k : ℝ) * w ≤ x - a₀ := (le_div_iff₀ hw0).1 hk1
    have h2 : x - a₀ < ((k : ℝ) + 1) * w := (div_lt_iff₀ hw0).1 hk2
    constructor <;> [linarith; (rw [hw] at h2 ⊢; linarith)]
  calc μ (φ ⁻¹' Icc (-R) R ∩ Ω) = m (Icc (-R) R) := (slabMeasure_apply hφ Ω measurableSet_Icc).symm
    _ ≤ m (⋃ k ∈ Finset.Icc (-(M : ℤ)) M, Icc (a₀ + (k : ℝ) * w) (b₀ + (k : ℝ) * w)) := measure_mono hcov
    _ ≤ ∑ k ∈ Finset.Icc (-(M : ℤ)) M, m (Icc (a₀ + (k : ℝ) * w) (b₀ + (k : ℝ) * w)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ k ∈ Finset.Icc (-(M : ℤ)) M, m (Icc a₀ b₀) := Finset.sum_congr rfl fun k _ => htrans _
    _ < ⊤ := ENNReal.sum_lt_top.2 fun _ _ => hm₀

end Abstract

section Ideles

variable (F : Type) [Field F] [NumberField F]

theorem countable_numberField : Countable F :=
  (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance

theorem ideleNorm_principal (a : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
  simp only [ideleNorm]
  rw [RingHom.toMonoidHom_eq_coe] at h
  rw [h]
  rfl

def basePlace : InfinitePlace F := Classical.arbitrary _

variable {F} in
open scoped Classical in

def toCompletion (w : InfinitePlace F) (r : ℝ) : w.Completion :=
  if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm r
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm r

variable {F} in
theorem isometry_ringEquiv_symm {A B : Type*} [NormedField A] [NormedField B] (e : A ≃+* B)
    (he : Isometry e) : Isometry e.symm := fun a b => by
  rw [← he.edist_eq, e.apply_symm_apply, e.apply_symm_apply]

variable {F} in
theorem isometry_toCompletion (w : InfinitePlace F) : Isometry (toCompletion w) := by
  by_cases hw : w.IsReal
  · have h : Isometry (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm :=
      isometry_ringEquiv_symm _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
    intro a b
    simp only [toCompletion, dif_pos hw]
    exact h.edist_eq a b
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have h : Isometry (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm :=
      isometry_ringEquiv_symm _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
    intro a b
    simp only [toCompletion, dif_neg hw]
    exact (h.comp Complex.isometry_ofReal).edist_eq a b

variable {F} in
theorem toCompletion_zero (w : InfinitePlace F) : toCompletion w 0 = 0 := by
  by_cases hw : w.IsReal
  · simp only [toCompletion, dif_pos hw, map_zero]
  · simp only [toCompletion, dif_neg hw, Complex.ofReal_zero, map_zero]

variable {F} in
theorem norm_toCompletion (w : InfinitePlace F) (r : ℝ) : ‖toCompletion w r‖ = |r| := by
  rw [(isometry_toCompletion w).norm_map_of_map_zero (toCompletion_zero w), Real.norm_eq_abs]

variable {F} in
theorem continuous_toCompletion (w : InfinitePlace F) : Continuous (toCompletion w) :=
  (isometry_toCompletion w).continuous

variable {F} in
theorem toCompletion_ne_zero (w : InfinitePlace F) {r : ℝ} (hr : r ≠ 0) : toCompletion w r ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_toCompletion]
  exact abs_ne_zero.mpr hr

variable {F} in

def expUnit (w : InfinitePlace F) (t : ℝ) : (w.Completion)ˣ :=
  Units.mk0 (toCompletion w (Real.exp (t / w.mult))) (toCompletion_ne_zero w (Real.exp_pos _).ne')

variable {F} in
theorem norm_expUnit (w : InfinitePlace F) (t : ℝ) :
    ‖((expUnit w t : (w.Completion)ˣ) : w.Completion)‖ = Real.exp (t / w.mult) := by
  rw [expUnit, Units.val_mk0, norm_toCompletion, abs_of_pos (Real.exp_pos _)]

variable {F} in
theorem continuous_expUnit (w : InfinitePlace F) : Continuous (expUnit w) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_toCompletion w).comp (Real.continuous_exp.comp (continuous_id.div_const _))
  · have : (fun t => ((expUnit w t)⁻¹ : (w.Completion)ˣ) : ℝ → w.Completion) =
        fun t => (toCompletion w (Real.exp (t / w.mult)))⁻¹ := by
      funext t; rfl
    rw [this]
    exact ((continuous_toCompletion w).comp
      (Real.continuous_exp.comp (continuous_id.div_const _))).inv₀
      fun t => toCompletion_ne_zero w (Real.exp_pos _).ne'

def archSection (t : ℝ) : (AdeleRing (𝓞 F) F)ˣ :=
  archUnitHom (basePlace F) (expUnit (basePlace F) t)

theorem continuous_archSection : Continuous (archSection F) := by
  classical
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h1 : Continuous fun t => ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) :
        (basePlace F).Completion) := Units.continuous_val.comp (continuous_expUnit _)
    have : (Units.val ∘ archSection F) = fun t =>
        ((Function.update (1 : InfiniteAdeleRing F) (basePlace F)
          ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) : (basePlace F).Completion), 1) :
            InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := by
      funext t; rfl
    rw [this]
    exact (continuous_const.update (basePlace F) h1).prodMk continuous_const
  · have h1 : Continuous fun t => (((expUnit (basePlace F) t)⁻¹ : ((basePlace F).Completion)ˣ) :
        (basePlace F).Completion) := Units.continuous_coe_inv.comp (continuous_expUnit _)
    have : (fun t => ((archSection F t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : ℝ → AdeleRing (𝓞 F) F) = fun t =>
        ((Function.update (1 : InfiniteAdeleRing F) (basePlace F)
          (((expUnit (basePlace F) t)⁻¹ : ((basePlace F).Completion)ˣ) : (basePlace F).Completion), 1) :
            InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := by
      funext t; rfl
    rw [this]
    exact (continuous_const.update (basePlace F) h1).prodMk continuous_const

theorem ideleNorm_archSection (t : ℝ) : ideleNorm F (archSection F t) = Real.exp t := by
  classical
  have h2 : ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl
  have h := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F
    (archSection F t) h2
  simp only [ideleNorm]
  rw [h, Finset.prod_eq_single (basePlace F)]
  · rw [show ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 (basePlace F) =
        ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) : (basePlace F).Completion) from
        NumberField.AdelicVolume.archCentralUnit_fst_self _ _,
      norm_expUnit, ← Real.exp_nat_mul, mul_div_cancel₀]
    exact Nat.cast_ne_zero.mpr (InfinitePlace.mult_pos (w := basePlace F)).ne'
  · intro w _ hw
    rw [show ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 from
      NumberField.AdelicVolume.archCentralUnit_fst_of_ne _ _ hw, norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ _) h

end Ideles

section Topology

p2m_open "AutomorphicForm~continuous_sigmaTensor"
open scoped TensorProduct TensorProduct.RightActions

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra K A]

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor A K L σ)

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) =>
      t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL A K L σ).inv
  have : ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

omit [IsTopologicalRing A] in
theorem continuous_includeRight :
    Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  have h : Continuous fun a : A => a • (1 : L ⊗[K] A) := continuous_id.fun_smul continuous_const
  refine h.congr fun a => ?_
  rw [← Algebra.algebraMap_eq_smul_one]
  rfl

omit [IsTopologicalRing A] in
theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) A =>
    M.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom)
  exact continuous_id.matrix_map (continuous_includeRight A K L)

end Topology

section Algebra

p2m_open "AutomorphicForm~continuous_sigmaTensor"
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (B : Type) [CommRing B] [Algebra K B]

theorem sigmaTensor_includeLeft (σ : L ≃ₐ[K] L) (l : L) :
    sigmaTensor K L B σ (l ⊗ₜ[K] (1 : B)) = σ l ⊗ₜ[K] (1 : B) := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem sigmaGL_map_includeLeft (σ : L ≃ₐ[K] L) (g : GL (Fin 2) L) :
    sigmaGL K L B σ (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] B) g) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] B)
        (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show sigmaTensor K L B σ (Algebra.TensorProduct.includeLeftRingHom (g i j)) =
    Algebra.TensorProduct.includeLeftRingHom ((σ : L →+* L) (g i j))
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    sigmaTensor_includeLeft]
  rfl

theorem sigmaGL_toTensorGL (σ : L ≃ₐ[K] L) (g : GL (Fin 2) B) :
    sigmaGL K L B σ (toTensorGL K L B g) = toTensorGL K L B g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show sigmaTensor K L B σ ((Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) (g i j)) =
    (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) (g i j)
  rw [Algebra.TensorProduct.includeRight_apply]
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

variable {K L B} in
theorem scalar_mul_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem toTensorGL_scalar (z : Bˣ) :
    toTensorGL K L B (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) : B →* L ⊗[K] B) z) := by
  show Matrix.GeneralLinearGroup.map
    ((Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B).toRingHom)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = _
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Units.coe_map,
    MonoidHom.coe_coe]
  split_ifs <;> simp

theorem det_scalar_two {R : Type*} [CommRing R] (z : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z * z := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two]

theorem map_mem_twistedCentralizer (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] B)ˣ)
    (g : GL (Fin 2) L) (hg : g ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀) :
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] B) g ∈
      twistedCentralizer K L B σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] B) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  rw [mem_sigmaCentralizer_iff] at hg ⊢
  rw [sigmaGL_map_includeLeft, ← map_inv, mul_assoc, mul_assoc, scalar_mul_comm c, ← mul_assoc,
    ← mul_assoc, ← map_mul, ← map_mul, hg]

theorem toTensorGL_scalar_mem_twistedCentralizer (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] B)) (z : Bˣ) :
    toTensorGL K L B (Matrix.GeneralLinearGroup.scalar (Fin 2) z) ∈ twistedCentralizer K L B σ δ := by
  rw [mem_sigmaCentralizer_iff, sigmaGL_toTensorGL, toTensorGL_scalar, scalar_mul_comm, mul_assoc,
    mul_inv_cancel, mul_one]

end Algebra

section Setting

p2m_open "AutomorphicForm~continuous_sigmaTensor"
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

abbrev inclA : L →+* L ⊗[K] AdeleRing (𝓞 K) K := Algebra.TensorProduct.includeLeftRingHom

abbrev Emap : L ⊗[K] AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map (inclA K L) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c

abbrev Tw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δA K L δ₀ c)

abbrev ΓTw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (Tw K L σ δ₀ c) :=
  ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
    (Matrix.GeneralLinearGroup.map (inclA K L))).subgroupOf (Tw K L σ δ₀ c)

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

def normDet (t : Tw K L σ δ₀ c) : ℝ :=
  ideleNorm L (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
    (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))

def logNormDet (t : Tw K L σ δ₀ c) : ℝ := Real.log (normDet K L σ δ₀ c t)

theorem normDet_pos (t : Tw K L σ δ₀ c) : 0 < normDet K L σ δ₀ c t := ideleNorm_pos _

theorem normDet_mul (s t : Tw K L σ δ₀ c) :
    normDet K L σ δ₀ c (s * t) = normDet K L σ δ₀ c s * normDet K L σ δ₀ c t := by
  simp only [normDet, Subgroup.coe_mul, map_mul, ideleNorm]
  push_cast
  ring

theorem normDet_inv (t : Tw K L σ δ₀ c) : normDet K L σ δ₀ c t⁻¹ = (normDet K L σ δ₀ c t)⁻¹ := by
  simp only [normDet, Subgroup.coe_inv, map_inv, ideleNorm]
  push_cast
  ring

theorem logNormDet_mul (s t : Tw K L σ δ₀ c) :
    logNormDet K L σ δ₀ c (s * t) = logNormDet K L σ δ₀ c s + logNormDet K L σ δ₀ c t := by
  simp only [logNormDet, normDet_mul]
  exact Real.log_mul (normDet_pos K L σ δ₀ c s).ne' (normDet_pos K L σ δ₀ c t).ne'

theorem continuous_logNormDet : Continuous (logNormDet K L σ δ₀ c) := by
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  have hE : Continuous fun g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
      Matrix.GeneralLinearGroup.map (n := Fin 2) (Emap K L) g :=
    (baseChangeGLEquiv K L).continuous.congr fun g => rfl
  have hν : Continuous (normDet K L σ δ₀ c) :=
    (NumberField.TateGlobal.continuous_ideleNorm L).comp
      (Matrix.GeneralLinearGroup.continuous_det.comp (hE.comp continuous_subtype_val))
  exact hν.log fun t => (normDet_pos K L σ δ₀ c t).ne'

theorem logNormDet_of_mem (γ : Tw K L σ δ₀ c) (hγ : γ ∈ ΓTw K L σ δ₀ c) :
    logNormDet K L σ δ₀ c γ = 0 := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
  obtain ⟨g, -, hg⟩ := hγ
  have hTS := (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).2.2 g
  simp only [logNormDet, normDet]
  rw [← hg, hTS]
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L g) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
        (Matrix.GeneralLinearGroup.det g) := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.val_det_apply]
    show ((Matrix.GeneralLinearGroup.map (algebraMap L (AdeleRing (𝓞 L) L)) g :
      GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).det = _
    rw [show ((Matrix.GeneralLinearGroup.map (algebraMap L (AdeleRing (𝓞 L) L)) g :
      GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
        (algebraMap L (AdeleRing (𝓞 L) L)).mapMatrix (g : Matrix (Fin 2) (Fin 2) L) from rfl,
      ← RingHom.map_det]
  rw [hdet, ideleNorm_principal L, Real.log_one]

def twSection (t : ℝ) : Tw K L σ δ₀ c :=
  ⟨toTensorGL K L (AdeleRing (𝓞 K) K) (Matrix.GeneralLinearGroup.scalar (Fin 2)
      (archSection K (t / (2 * Module.finrank K L)))),
    toTensorGL_scalar_mem_twistedCentralizer K L (AdeleRing (𝓞 K) K) σ _ _⟩

theorem coe_twSection (t : ℝ) :
    ((twSection K L σ δ₀ c t : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
      toTensorGL K L (AdeleRing (𝓞 K) K) (Matrix.GeneralLinearGroup.scalar (Fin 2)
        (archSection K (t / (2 * Module.finrank K L)))) := rfl

theorem continuous_twSection : Continuous (twSection K L σ δ₀ c) := by
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  refine Continuous.subtype_mk ?_ _
  refine (continuous_toTensorGL (AdeleRing (𝓞 K) K) K L).comp ?_
  have hsc : Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) :
      (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (AdeleRing (𝓞 K) K)) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have h1 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => fun _ : Fin 2 => (z : AdeleRing (𝓞 K) K) :=
        continuous_pi fun _ => Units.continuous_val
      exact h1.matrix_diagonal.congr fun z => (Matrix.scalar_apply (z : AdeleRing (𝓞 K) K)).symm
    · have h1 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => fun _ : Fin 2 =>
          ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) :=
        continuous_pi fun _ => Units.continuous_coe_inv
      exact h1.matrix_diagonal.congr fun z =>
        (Matrix.scalar_apply ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).symm
  exact hsc.comp ((continuous_archSection K).comp (continuous_id.div_const _))

theorem twSection_comm (t : ℝ) (g : Tw K L σ δ₀ c) :
    g * twSection K L σ δ₀ c t = twSection K L σ δ₀ c t * g := by
  apply Subtype.ext
  show (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * _ = _ * (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
  rw [coe_twSection, toTensorGL_scalar, scalar_mul_comm]

theorem det_map_baseChange (s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β s) =
      AutomorphicForm.TransversalMeasure.idelesBaseChange K L (Matrix.GeneralLinearGroup.det s) := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, AutomorphicForm.TransversalMeasure.idelesBaseChange,
    M4aHerbrand.GenuineDescent.genuineBaseChange_β, RingHom.map_det]

theorem logNormDet_twSection (t : ℝ) : logNormDet K L σ δ₀ c (twSection K L σ δ₀ c t) = t := by
  have hTS := (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).2.1
  simp only [logNormDet, normDet, coe_twSection]
  rw [hTS, det_map_baseChange, NumberField.TateGlobal.ideleNorm_idelesBaseChange, det_scalar_two,
    ideleNorm_mul, ideleNorm_archSection, ← Real.exp_add, ← Real.exp_nat_mul, Real.log_exp]
  have hn : (Module.finrank K L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  field_simp
  ring

scoped instance countable_ΓTw : Countable (ΓTw K L σ δ₀ c) := by
  haveI := countable_numberField L
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  haveI : Countable (GL (Fin 2) L) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L))
      fun g h hgh => Units.ext hgh
  let f : sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀ → ΓTw K L σ δ₀ c :=
    fun g => ⟨⟨Matrix.GeneralLinearGroup.map (inclA K L) g,
      map_mem_twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ₀ c g g.2⟩, by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        exact ⟨g, g.2, rfl⟩⟩
  refine Function.Surjective.countable (f := f) fun γ => ?_
  have hγ := γ.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
  obtain ⟨g, hg, hgγ⟩ := hγ
  refine ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext ?_)⟩
  exact hgγ

end Setting

section Main

p2m_open "AutomorphicForm~continuous_sigmaTensor"
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (δA K L δ₀ c) =
      toTensorGL K L (AdeleRing (𝓞 K) K) (centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (τ' : Measure (Tw K L σ δ₀ c)) [τ'.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D' : Set (Tw K L σ δ₀ c), IsFundamentalDomain (ΓTw K L σ δ₀ c).op D' τ' →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ' (D' ∩ {t | ideleNorm L
            (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by

  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_tensor K L (AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_tensor K L (AdeleRing (𝓞 K) K)
  haveI := isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (Tw K L σ δ₀ c) := ⟨rfl⟩
  have hclosed := isClosed_twistedCentralizer (AdeleRing (𝓞 K) K) K L σ (δA K L δ₀ c)
  haveI : LocallyCompactSpace (Tw K L σ δ₀ c) := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

  by_cases hex : ∃ D₀ : Set (Tw K L σ δ₀ c), IsFundamentalDomain (ΓTw K L σ δ₀ c).op D₀ τ'
  swap
  · refine ⟨1, one_ne_zero, ENNReal.one_ne_top, fun D' hD' => absurd ⟨D', hD'⟩ hex⟩
  obtain ⟨D₀, hD₀⟩ := hex

  haveI : τ'.IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
      K L h2 σ hgen (δA K L δ₀ c) u hN τ' inferInstance
  set ν : Measure (Tw K L σ δ₀ c) := τ'.inv with hν
  haveI : ν.IsHaarMeasure := by
    obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Tw K L σ δ₀ c)) := inferInstance
    refine Measure.isHaarMeasure_of_isCompact_nonempty_interior ν (K₀ : Set (Tw K L σ δ₀ c))
      K₀.isCompact K₀.interior_nonempty ?_ ?_
    · rw [hν, Measure.inv_apply]
      have hsub : (interior (K₀ : Set (Tw K L σ δ₀ c)))⁻¹ ⊆ (K₀ : Set (Tw K L σ δ₀ c))⁻¹ :=
        Set.inv_subset_inv.2 interior_subset
      have hpos : 0 < τ' (interior (K₀ : Set (Tw K L σ δ₀ c)))⁻¹ :=
        (isOpen_interior.inv).measure_pos τ' (K₀.interior_nonempty.inv)
      exact (hpos.trans_le (measure_mono hsub)).ne'
    · rw [hν, Measure.inv_apply]
      exact K₀.isCompact.inv.measure_lt_top.ne

  set fm : Tw K L σ δ₀ c ≃ᵐ Tw K L σ δ₀ c := (Homeomorph.inv (Tw K L σ δ₀ c)).toMeasurableEquiv
    with hfm_def
  have hfm : ∀ t : Tw K L σ δ₀ c, fm t = t⁻¹ := fun _ => rfl
  have hmap : Measure.map fm τ' = ν := by
    rw [hν, Measure.inv_def]
    rfl
  have hqmp : Measure.QuasiMeasurePreserving fm.symm ν τ' := by
    refine ⟨fm.symm.measurable, ?_⟩
    rw [← hmap, MeasurableEquiv.map_symm_map]
  let eqΓ : ΓTw K L σ δ₀ c ≃ (ΓTw K L σ δ₀ c).op :=
    { toFun := fun g => ⟨MulOpposite.op ((g : Tw K L σ δ₀ c)⁻¹), by
        rw [Subgroup.mem_op, MulOpposite.unop_op]
        exact Subgroup.inv_mem _ g.2⟩
      invFun := fun x => ⟨(MulOpposite.unop (x : (Tw K L σ δ₀ c)ᵐᵒᵖ))⁻¹, by
        refine Subgroup.inv_mem _ ?_
        have hx := x.2
        rw [Subgroup.mem_op] at hx
        exact hx⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp only [MulOpposite.unop_op, inv_inv]
      right_inv := fun x => by
        apply Subtype.ext
        apply MulOpposite.unop_injective
        simp only [MulOpposite.unop_op, inv_inv] }
  have heqΓ : ∀ (g : ΓTw K L σ δ₀ c) (t : Tw K L σ δ₀ c),
      (eqΓ g • t : Tw K L σ δ₀ c) = t * (g : Tw K L σ δ₀ c)⁻¹ := by
    intro g t
    rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
    rfl
  have hleftFD : ∀ D : Set (Tw K L σ δ₀ c), IsFundamentalDomain (ΓTw K L σ δ₀ c).op D τ' →
      IsFundamentalDomain (ΓTw K L σ δ₀ c) (fm '' D) ν := by
    intro D hD
    refine hD.image_of_equiv fm.toEquiv hqmp eqΓ (fun g x => ?_)
    show fm (eqΓ g • x) = g • fm x
    rw [hfm, hfm, heqΓ, Subgroup.smul_def, smul_eq_mul, _root_.mul_inv_rev, inv_inv]

  have hφ : Measurable (logNormDet K L σ δ₀ c) := (continuous_logNormDet K L σ δ₀ c).measurable
  have hφmul := logNormDet_mul K L σ δ₀ c
  have hΓ : ∀ γ ∈ ΓTw K L σ δ₀ c, logNormDet K L σ δ₀ c γ = 0 := logNormDet_of_mem K L σ δ₀ c
  have hs := logNormDet_twSection K L σ δ₀ c
  have hcomm : ∀ (t : ℝ), ∀ γ ∈ ΓTw K L σ δ₀ c,
      γ * twSection K L σ δ₀ c t = twSection K L σ δ₀ c t * γ :=
    fun t γ _ => twSection_comm K L σ δ₀ c t γ

  set Ω₀ : Set (Tw K L σ δ₀ c) := fm '' D₀ with hΩ₀def
  have hΩ₀ : IsFundamentalDomain (ΓTw K L σ δ₀ c) Ω₀ ν := hleftFD D₀ hD₀
  obtain ⟨CF, hCFc, hCF⟩ :=
    AutomorphicForm.exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ c u hN hns
  have hCF' : ∀ t : Tw K L σ δ₀ c, normDet K L σ δ₀ c t = 1 →
      ∃ γ ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀, ∃ k ∈ CF,
        (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
          Matrix.GeneralLinearGroup.map (inclA K L) γ * (k : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    hCF
  clear hCF
  set C₁ : Set (Tw K L σ δ₀ c) :=
    (fun p : ℝ × Tw K L σ δ₀ c => twSection K L σ δ₀ c p.1 * p.2) '' (Set.Icc (0 : ℝ) 1 ×ˢ CF)
    with hC₁def
  have hC₁c : IsCompact C₁ :=
    (isCompact_Icc.prod hCFc).image
      (((continuous_twSection K L σ δ₀ c).comp continuous_fst).mul continuous_snd)
  have hcover : logNormDet K L σ δ₀ c ⁻¹' Set.Icc (0 : ℝ) 1 ⊆ ⋃ γ : ΓTw K L σ δ₀ c, γ • C₁ := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : Tw K L σ δ₀ c,
        y = (twSection K L σ δ₀ c (logNormDet K L σ δ₀ c x))⁻¹ * x := ⟨_, rfl⟩
    have hy0 : logNormDet K L σ δ₀ c y = 0 := by
      have h1 : logNormDet K L σ δ₀ c (twSection K L σ δ₀ c (logNormDet K L σ δ₀ c x) * y) =
          logNormDet K L σ δ₀ c x := by rw [hy, mul_inv_cancel_left]
      rw [hφmul, hs] at h1
      linarith
    have hy1 : normDet K L σ δ₀ c y = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (normDet_pos K L σ δ₀ c y) hy0
    obtain ⟨g, hg, k, hk, hyk⟩ := hCF' y hy1
    let γ : ΓTw K L σ δ₀ c := ⟨⟨Matrix.GeneralLinearGroup.map (inclA K L) g,
      map_mem_twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ₀ c g hg⟩, by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        exact ⟨g, hg, rfl⟩⟩
    have hyγk : y = (γ : Tw K L σ δ₀ c) * k := Subtype.ext hyk
    refine Set.mem_iUnion.2 ⟨γ, ?_⟩
    rw [Subgroup.smul_def, Set.mem_smul_set]
    refine ⟨twSection K L σ δ₀ c (logNormDet K L σ δ₀ c x) * k, ⟨(logNormDet K L σ δ₀ c x, k),
      ⟨hx, hk⟩, rfl⟩, ?_⟩
    show (γ : Tw K L σ δ₀ c) * (twSection K L σ δ₀ c (logNormDet K L σ δ₀ c x) * k) = x
    rw [← mul_assoc, hcomm _ (γ : Tw K L σ δ₀ c) γ.2, mul_assoc, ← hyγk, hy, mul_inv_cancel_left]
  have hfin₀ : ν (logNormDet K L σ δ₀ c ⁻¹' Set.Icc (0 : ℝ) 1 ∩ Ω₀) < ⊤ :=
    measure_preimage_inter_lt_top_of_subset_iUnion_smul (μ := ν) (Γ := ΓTw K L σ δ₀ c) hΩ₀ hC₁c hcover
  have hfinR := measure_preimage_Icc_inter_lt_top_of_one (μ := ν) (Γ := ΓTw K L σ δ₀ c)
    (φ := logNormDet K L σ δ₀ c) (s := twSection K L σ δ₀ c) hφ hφmul hΓ hs hcomm hΩ₀
    zero_lt_one hfin₀

  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_measure_preimage_Icc_inter_eq (μ := ν) (Γ := ΓTw K L σ δ₀ c)
    (φ := logNormDet K L σ δ₀ c) (s := twSection K L σ δ₀ c) hφ hφmul hΓ hs hcomm hΩ₀ hfinR
  have hν0 : ν ≠ 0 :=
    Measure.measure_univ_ne_zero.1 (IsOpen.measure_ne_zero ν isOpen_univ univ_nonempty)
  refine ⟨c₀, ENNReal.coe_ne_zero.2 (hc₀0 hν0), ENNReal.coe_ne_top, fun D' hD' a b ha hab => ?_⟩

  have hb : 0 < b := ha.trans_le hab
  have hFD : IsFundamentalDomain (ΓTw K L σ δ₀ c) (fm '' D') ν := hleftFD D' hD'
  have key := hc₀ (fm '' D') hFD (Real.log b⁻¹) (Real.log a⁻¹)
  have hset : D' ∩ {t : Tw K L σ δ₀ c | ideleNorm L
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
        (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b} =
      fm ⁻¹' (logNormDet K L σ δ₀ c ⁻¹' Set.Icc (Real.log b⁻¹) (Real.log a⁻¹) ∩ fm '' D') := by
    rw [Set.preimage_inter, fm.injective.preimage_image, Set.inter_comm]
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hfm, Set.mem_Icc]
    show normDet K L σ δ₀ c t ∈ Set.Icc a b ↔ _
    rw [logNormDet, normDet_inv, Set.mem_Icc,
      Real.log_le_log_iff (inv_pos.2 hb) (inv_pos.2 (normDet_pos K L σ δ₀ c t)),
      Real.log_le_log_iff (inv_pos.2 (normDet_pos K L σ δ₀ c t)) (inv_pos.2 ha),
      inv_le_inv₀ hb (normDet_pos K L σ δ₀ c t), inv_le_inv₀ (normDet_pos K L σ δ₀ c t) ha, and_comm]
  calc τ' (D' ∩ {t : Tw K L σ δ₀ c | ideleNorm L
          (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
            (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b})
      = τ' (fm ⁻¹' (logNormDet K L σ δ₀ c ⁻¹' Set.Icc (Real.log b⁻¹) (Real.log a⁻¹) ∩ fm '' D')) := by
        rw [hset]
    _ = Measure.map fm τ' (logNormDet K L σ δ₀ c ⁻¹' Set.Icc (Real.log b⁻¹) (Real.log a⁻¹) ∩ fm '' D') :=
        (MeasurableEquiv.map_apply fm _).symm
    _ = (c₀ : ℝ≥0∞) * ENNReal.ofReal (Real.log a⁻¹ - Real.log b⁻¹) := by rw [hmap]; exact key
    _ = c₀ * ENNReal.ofReal (Real.log (b / a)) := by
        rw [Real.log_inv, Real.log_inv, Real.log_div hb.ne' ha.ne']
        ring_nf

end Main

end P2mCentralCovolQuat
p2m_reactivate "P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two.P2mCentralCovolQuat"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two.P2mCentralCovolQuat"

open MeasureTheory NumberField
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    [τ'.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
        IsFundamentalDomain
          (((AutomorphicForm.sigmaCentralizer
              (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
              (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom :
                  L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
            (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom :
                    L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det
              (Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) :=
  P2mCentralCovolQuat.main K L h2 σ hgen δ₀ c u hN hns τ'

end S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two (solution)
