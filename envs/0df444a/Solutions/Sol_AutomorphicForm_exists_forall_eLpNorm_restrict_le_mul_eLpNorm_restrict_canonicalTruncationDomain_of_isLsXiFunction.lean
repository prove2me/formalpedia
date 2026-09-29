-- Prove2me | solution 1 for AutomorphicForm.exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4266f42e-caa7-5113-800b-ae3aa88e37b6

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal AutomorphicForm
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace SN4Proof

theorem tsum_indicator_smul_set_le_card {Γ X : Type*} [Group Γ] [MulAction Γ X] (A : Set X) (Q : Finset Γ)
    (hQ : ∀ δ : Γ, (∃ a ∈ A, δ • a ∈ A) → δ ∈ Q) (x : X) :
    ∑' γ : Γ, (γ • A).indicator (fun _ => (1 : ℝ≥0∞)) x ≤ Q.card := by
  classical
  by_cases hP : ∃ γ₁ : Γ, x ∈ γ₁ • A
  · obtain ⟨γ₁, hγ₁⟩ := hP
    set W : Finset Γ := Q.image fun δ => γ₁ * δ⁻¹ with hW
    have hsub : ∀ γ : Γ, x ∈ γ • A → γ ∈ W := by
      intro γ hγ
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hγ hγ₁
      have hδ : γ⁻¹ * γ₁ ∈ Q := hQ _ ⟨γ₁⁻¹ • x, hγ₁, by rw [mul_smul, smul_inv_smul]; exact hγ⟩
      rw [hW, Finset.mem_image]
      exact ⟨γ⁻¹ * γ₁, hδ, by group⟩
    calc ∑' γ : Γ, (γ • A).indicator (fun _ => (1 : ℝ≥0∞)) x
        ≤ ∑' γ : Γ, (W : Set Γ).indicator (fun _ => (1 : ℝ≥0∞)) γ := by
          refine ENNReal.tsum_le_tsum fun γ => ?_
          by_cases hγ : x ∈ γ • A
          · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (Finset.mem_coe.mpr (hsub γ hγ))]
          · rw [Set.indicator_of_notMem hγ]; exact bot_le
      _ = ∑ γ ∈ W, (1 : ℝ≥0∞) := by
          rw [tsum_eq_sum (s := W) (fun γ hγ => Set.indicator_of_notMem (fun h => hγ (Finset.mem_coe.mp h)) _)]
          exact Finset.sum_congr rfl fun γ hγ => Set.indicator_of_mem (Finset.mem_coe.mpr hγ) _
      _ = W.card := by simp
      _ ≤ Q.card := by exact_mod_cast Finset.card_image_le
  · push_neg at hP
    have : ∀ γ : Γ, (γ • A).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 := fun γ => Set.indicator_of_notMem (hP γ) _
    simp [this]

end SN4Proof

namespace SN4Proof

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]

theorem smulInvariantMeasure_restrict (Γ : Subgroup G) [MeasurableConstSMul ↥Γ G]
    (μ : Measure G) [SMulInvariantMeasure ↥Γ G μ] {S : Set G} (hS : MeasurableSet S)
    (hΓS : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' S = S) :
    SMulInvariantMeasure ↥Γ G (μ.restrict S) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓS γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hS)

end Group

section Adelic

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

abbrev dn (g : AdelicGL2 (𝓞 F) F) : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det g)

abbrev slab (F : Type) [Field F] [NumberField F] (a b : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

abbrev Γp (F : Type) [Field F] [NumberField F] : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range

scoped instance instCountableΓ : Countable ↥(Γp F) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (GL (Fin 2) F) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F)).countable

theorem dn_mul (g h : AdelicGL2 (𝓞 F) F) : dn (g * h) = dn g * dn h := by
  show ideleNorm F _ = _
  rw [_root_.map_mul, ideleNorm_mul]

theorem dn_subtype_mul (γ : ↥(Γp F)) (g : AdelicGL2 (𝓞 F) F) : dn ((γ : AdelicGL2 (𝓞 F) F) * g) = dn g := by
  obtain ⟨_, γ', rfl⟩ := γ
  rw [dn_mul]
  show ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ')) * dn g = dn g
  rw [AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab F a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F a b

theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp F) (AdelicGL2 (𝓞 F) F) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b)) :=
  smulInvariantMeasure_restrict (Γp F) _ (measurableSet_slab a b) fun γ => by
    ext w
    show dn ((γ : AdelicGL2 (𝓞 F) F) * w) ∈ Set.Icc a b ↔ dn w ∈ Set.Icc a b
    rw [dn_subtype_mul γ w]

theorem dn_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    dn (centralScalar (𝓞 F) F z * g) = ideleNorm F z ^ 2 * dn g := by
  rw [dn_mul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z * z := by
    apply Units.ext
    simp [centralScalar, Matrix.GeneralLinearGroup.scalar]
    ring
  show ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z)) = _
  rw [hdet, ideleNorm_mul, sq]

theorem setLIntegral_le_card_mul_of_subset_slab {a b : ℝ} {Φ₀ A : Set (AdelicGL2 (𝓞 F) F)}
    (hFD : IsFundamentalDomain ↥(Γp F) Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b)))
    (hΦ₀ : Φ₀ ⊆ slab F a b) (hA : A ⊆ slab F a b) (hAm : MeasurableSet A)
    (G : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hGm : AEMeasurable G (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hG : ∀ (γ : ↥(Γp F)) (w : AdelicGL2 (𝓞 F) F), G (γ • w) = G w)
    (Q : Finset ↥(Γp F)) (hQ : ∀ δ : ↥(Γp F), (∃ x ∈ A, δ • x ∈ A) → δ ∈ Q) :
    ∫⁻ w in A, G w ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤
      (Q.card : ℝ≥0∞) * ∫⁻ w in Φ₀, G w ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := smulInvariantMeasure_slab (F := F) a b
  set ν := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b) with hν
  have hmeas_smul : ∀ γ : ↥(Γp F), MeasurableSet (γ • A) := fun γ => by
    have : γ • A = (fun w => γ⁻¹ • w) ⁻¹' A := by
      ext w; rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]
    rw [this]; exact hAm.preimage (measurable_const_smul _)
  calc ∫⁻ w in A, G w ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫⁻ w in A, G w ∂ν := by rw [hν, Measure.restrict_restrict_of_subset hA]
    _ = ∑' γ : ↥(Γp F), ∫⁻ w in γ • A ∩ Φ₀, G (γ⁻¹ • w) ∂ν := hFD.setLIntegral_eq_tsum' G A
    _ = ∑' γ : ↥(Γp F), ∫⁻ w in Φ₀, (γ • A).indicator G w ∂ν := by
        refine tsum_congr fun γ => ?_
        simp_rw [hG]
        rw [lintegral_indicator (hmeas_smul γ), Measure.restrict_restrict (hmeas_smul γ)]
    _ = ∫⁻ w in Φ₀, ∑' γ : ↥(Γp F), (γ • A).indicator G w ∂ν := by
        rw [lintegral_tsum]
        intro γ
        refine (hGm.mono_measure ?_).indicator (hmeas_smul γ)
        exact (Measure.restrict_le_self).trans Measure.restrict_le_self
    _ ≤ ∫⁻ w in Φ₀, (Q.card : ℝ≥0∞) * G w ∂ν := by
        refine lintegral_mono fun w => ?_
        have hpt : ∀ γ : ↥(Γp F), (γ • A).indicator G w = (γ • A).indicator (fun _ => (1 : ℝ≥0∞)) w * G w := by
          intro γ; by_cases h : w ∈ γ • A <;> simp [h]
        simp_rw [hpt]
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul_left (tsum_indicator_smul_set_le_card A Q hQ w) _
    _ = (Q.card : ℝ≥0∞) * ∫⁻ w in Φ₀, G w ∂ν := by
        rw [lintegral_const_mul'' _ (hGm.mono_measure ((Measure.restrict_le_self).trans Measure.restrict_le_self))]
    _ = (Q.card : ℝ≥0∞) * ∫⁻ w in Φ₀, G w ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [hν, Measure.restrict_restrict_of_subset hΦ₀]

end Adelic

end SN4Proof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction.SN4Proof"

namespace SN4Proof

def posUnit (t : ℝ) (ht : 0 < t) : ℝ≥0ˣ :=
  Units.mk0 ⟨t, ht.le⟩ (by
    intro h
    have h' := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [NNReal.coe_mk, NNReal.coe_zero] at h'
    exact ht.ne' h')

theorem posUnit_val (t : ℝ) (ht : 0 < t) : (((posUnit t ht : ℝ≥0ˣ) : ℝ≥0) : ℝ) = t := rfl

end SN4Proof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction.SN4Proof"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

open SN4Proof in
theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    ∃ c : ℝ≥0, ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ ξK b →
      AEStronglyMeasurable b (adelicGLHaar (Fin 2) (𝓞 K) K) →
      eLpNorm b 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) ≤
        (c : ℝ≥0∞) * eLpNorm b 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (canonicalTruncationDomain K α β)) := by
  classical
  obtain ⟨-, -, -, hΦS, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  obtain ⟨s, hs, hsn, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
  have hβ : 0 < β := hα.trans hαβ

  set ζ : ℝ≥0ˣ → AdelicGL2 (𝓞 K) K := fun r => centralScalar (𝓞 K) K (s r) with hζ
  set V : ℝ≥0ˣ → Set (AdelicGL2 (𝓞 K) K) := fun r => {g | dn (ζ r * g) ∈ Set.Ioo α β} with hV
  have hVo : ∀ r, IsOpen (V r) := fun r =>
    isOpen_Ioo.preimage ((NumberField.TateGlobal.continuous_ideleNorm_det K).comp (continuous_mul_left (ζ r)))
  have hcov : C ⊆ ⋃ r, V r := by
    intro g _
    have hg : 0 < dn g := ideleNorm_pos _
    have hm : 0 < Real.sqrt (α * β) := Real.sqrt_pos.mpr (mul_pos hα hβ)
    have htpos : 0 < Real.sqrt (Real.sqrt (α * β) / dn g) := Real.sqrt_pos.mpr (div_pos hm hg)
    refine Set.mem_iUnion.mpr ⟨posUnit _ htpos, ?_⟩
    show dn (centralScalar (𝓞 K) K (s (posUnit _ htpos)) * g) ∈ Set.Ioo α β
    rw [dn_centralScalar_mul, hsn, posUnit_val, Real.sq_sqrt (div_pos hm hg).le, div_mul_cancel₀ _ hg.ne']
    constructor
    · rw [Real.lt_sqrt hα.le]; nlinarith
    · rw [Real.sqrt_lt' hβ]; nlinarith
  obtain ⟨R, hR⟩ := hC.elim_finite_subcover V hVo hcov

  have hfin : ∀ r : ℝ≥0ˣ, {δ : GL (Fin 2) K |
      globalPoints (𝓞 K) K δ ∈ ((fun g => ζ r * g) '' C) * ((fun g => ζ r * g) '' C)⁻¹}.Finite := by
    intro r
    have hc1 : IsCompact ((fun g => ζ r * g) '' C) := hC.image (continuous_mul_left _)
    have hcpt : IsCompact (((fun g => ζ r * g) '' C) * ((fun g => ζ r * g) '' C)⁻¹) := hc1.mul hc1.inv
    have h := AutomorphicForm.adelicKernelLocalFiniteness K _ hcpt 1 1
    simpa only [inv_one, one_mul, mul_one] using h
  set Q : ℝ≥0ˣ → Finset ↥(Γp K) := fun r =>
    ((hfin r).toFinset).image (MonoidHom.rangeRestrict (globalPoints (𝓞 K) K)) with hQdef
  have hQ : ∀ r, ∀ δ : ↥(Γp K), (∃ x ∈ (fun g => ζ r * g) '' (C ∩ V r), δ • x ∈ (fun g => ζ r * g) '' (C ∩ V r)) →
      δ ∈ Q r := by
    rintro r ⟨_, δ', rfl⟩ ⟨x, hx, hδx⟩
    have hsub : (fun g => ζ r * g) '' (C ∩ V r) ⊆ (fun g => ζ r * g) '' C := Set.image_mono Set.inter_subset_left
    rw [hQdef, Finset.mem_image]
    refine ⟨δ', (hfin r).mem_toFinset.mpr ?_, rfl⟩
    refine Set.mem_mul.mpr ⟨_, hsub hδx, x⁻¹, Set.inv_mem_inv.mpr (hsub hx), ?_⟩
    show globalPoints (𝓞 K) K δ' * x * x⁻¹ = globalPoints (𝓞 K) K δ'
    rw [mul_inv_cancel_right]

  set κ : ℝ≥0ˣ → ℝ≥0∞ := fun r => ‖(((ξK ⟨s r, Subgroup.mem_top _⟩)⁻¹ : ℂˣ) : ℂ)‖ₑ ^ (2 : ℝ) with hκ
  have hκtop : ∀ r, κ r ≠ ⊤ := fun r => ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top
  set Ctot : ℝ≥0∞ := ∑ r ∈ R, κ r * ((Q r).card : ℝ≥0∞) with hCtot
  have hCtop : Ctot ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun r _ => ENNReal.mul_ne_top (hκtop r) (ENNReal.natCast_ne_top _)
  refine ⟨(Ctot ^ (1 / 2 : ℝ)).toNNReal, fun b hb hbm => ?_⟩
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set G : AdelicGL2 (𝓞 K) K → ℝ≥0∞ := fun g => ‖b g‖ₑ ^ (2 : ℝ) with hG
  have hGm : AEMeasurable G μ := by
    rw [hG]; exact (hbm.enorm.pow_const _)
  have hGγ : ∀ (γ : ↥(Γp K)) (w : AdelicGL2 (𝓞 K) K), G (γ • w) = G w := by
    rintro ⟨_, γ', rfl⟩ w
    show ‖b (globalPoints (𝓞 K) K γ' * w)‖ₑ ^ (2 : ℝ) = ‖b w‖ₑ ^ (2 : ℝ)
    rw [hb.left_invariant]
  have hGζ : ∀ (r : ℝ≥0ˣ) (g : AdelicGL2 (𝓞 K) K), G g = κ r * G (ζ r * g) := by
    intro r g
    have h := hb.central_transform ⟨s r, Subgroup.mem_top _⟩ g
    have hbg : b g = (((ξK ⟨s r, Subgroup.mem_top _⟩)⁻¹ : ℂˣ) : ℂ) * b (ζ r * g) := by
      show b g = _ * b (centralScalar (𝓞 K) K (s r) * g)
      rw [h, ← mul_assoc, Units.inv_mul, one_mul]
    show ‖b g‖ₑ ^ (2 : ℝ) = ‖(((ξK ⟨s r, Subgroup.mem_top _⟩)⁻¹ : ℂˣ) : ℂ)‖ₑ ^ (2 : ℝ) * ‖b (ζ r * g)‖ₑ ^ (2 : ℝ)
    rw [hbg, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

  have hpiece : ∀ r : ℝ≥0ˣ, ∫⁻ g in C ∩ V r, G g ∂μ ≤ κ r * ((Q r).card : ℝ≥0∞) * ∫⁻ g in canonicalTruncationDomain K α β, G g ∂μ := by
    intro r
    have hA : (fun g => ζ r * g) '' (C ∩ V r) ⊆ slab K α β := by
      rintro _ ⟨g, ⟨-, hg⟩, rfl⟩
      exact Set.Ioo_subset_Icc_self hg
    have hAm : MeasurableSet ((fun g => ζ r * g) '' (C ∩ V r)) := by
      rw [Set.image_mul_left]
      exact (hC.isClosed.measurableSet.inter (hVo r).measurableSet).preimage (measurable_const_mul _)
    calc ∫⁻ g in C ∩ V r, G g ∂μ = ∫⁻ g in C ∩ V r, κ r * G (ζ r * g) ∂μ := by
          refine lintegral_congr fun g => hGζ r g
      _ = κ r * ∫⁻ g in C ∩ V r, G (ζ r * g) ∂μ := lintegral_const_mul' _ _ (hκtop r)
      _ = κ r * ∫⁻ h in (fun g => ζ r * g) '' (C ∩ V r), G h ∂μ := by
          rw [(measurePreserving_mul_left μ (ζ r)).setLIntegral_comp_emb (measurableEmbedding_mulLeft (ζ r)) G _]
      _ ≤ κ r * (((Q r).card : ℝ≥0∞) * ∫⁻ g in canonicalTruncationDomain K α β, G g ∂μ) := by
          gcongr
          exact setLIntegral_le_card_mul_of_subset_slab hFD hΦS hA hAm G hGm hGγ (Q r) (hQ r)
      _ = κ r * ((Q r).card : ℝ≥0∞) * ∫⁻ g in canonicalTruncationDomain K α β, G g ∂μ := by rw [mul_assoc]

  have hmain : ∫⁻ g in C, G g ∂μ ≤ Ctot * ∫⁻ g in canonicalTruncationDomain K α β, G g ∂μ := by
    calc ∫⁻ g in C, G g ∂μ ≤ ∫⁻ g in ⋃ r : ↥R, (C ∩ V r), G g ∂μ := by
          refine lintegral_mono_set fun g hg => ?_
          obtain ⟨r, hr, hv⟩ := Set.mem_iUnion₂.mp (hR hg)
          exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hg, hv⟩
      _ ≤ ∑' r : ↥R, ∫⁻ g in C ∩ V r, G g ∂μ := lintegral_iUnion_le _ _
      _ = ∑ r ∈ R, ∫⁻ g in C ∩ V r, G g ∂μ := by
          rw [tsum_fintype, Finset.sum_coe_sort R fun r => ∫⁻ g in C ∩ V r, G g ∂μ]
      _ ≤ ∑ r ∈ R, κ r * ((Q r).card : ℝ≥0∞) * ∫⁻ g in canonicalTruncationDomain K α β, G g ∂μ :=
          Finset.sum_le_sum fun r _ => hpiece r
      _ = Ctot * ∫⁻ g in canonicalTruncationDomain K α β, G g ∂μ := by rw [hCtot, Finset.sum_mul]

  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, h2]
  have hcoe : (((Ctot ^ (1 / 2 : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) = Ctot ^ (1 / 2 : ℝ) :=
    ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCtop)
  rw [hcoe]
  calc (∫⁻ g in C, ‖b g‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      ≤ (Ctot * ∫⁻ g in canonicalTruncationDomain K α β, ‖b g‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hmain (by norm_num)
    _ = Ctot ^ (1 / 2 : ℝ) * (∫⁻ g in canonicalTruncationDomain K α β, ‖b g‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

end
end S_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction (solution)
