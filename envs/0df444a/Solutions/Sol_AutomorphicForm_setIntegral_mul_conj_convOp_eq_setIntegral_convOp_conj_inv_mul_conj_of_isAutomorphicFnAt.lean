-- Prove2me | solution 1 for AutomorphicForm.setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/76d993ae-1ed1-5769-8717-ef8fb60e44d0

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan

import Theorems.Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open scoped Pointwise ENNReal
open AutomorphicForm

theorem T6B.iSup_ofReal_min_natCast (r : ℝ) (hr : 0 ≤ r) :
    (⨆ n : ℕ, ENNReal.ofReal (min r n)) = ENNReal.ofReal r := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  refine le_iSup_of_le ⌈r⌉₊ ?_
  rw [min_eq_left (Nat.le_ceil r)]

theorem T6B.setLIntegral_ofReal_norm_sq_comp_mul_eq (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦfin : adelicGLHaar (Fin 2) (𝓞 K) K Φ < ⊤)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : AEStronglyMeasurable u (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
    (h : AdelicGL2 (𝓞 K) K) (hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det h) = 1) :
    ∫⁻ x in Φ, ENNReal.ofReal (‖u (x * h)‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ x in Φ, ENNReal.ofReal (‖u x‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) := isFiniteMeasure_restrict.2 hΦfin.ne
  have huh : AEStronglyMeasurable (fun x => u (x * h)) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    hu.comp_quasiMeasurePreserving (measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 K) K) h).quasiMeasurePreserving
  have hmeas_min : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∀ n : ℕ, AEStronglyMeasurable (fun x => min (‖v x‖ ^ 2) (n : ℝ))
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) := fun v hv n =>
    ((continuous_id.pow 2).min continuous_const).comp_aestronglyMeasurable hv.restrict.norm
  have hnn : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ) (n : ℕ) (x : AdelicGL2 (𝓞 K) K), 0 ≤ min (‖v x‖ ^ 2) (n : ℝ) :=
    fun v n x => le_min (sq_nonneg _) (Nat.cast_nonneg n)
  have hint : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∀ n : ℕ, Integrable (fun x => min (‖v x‖ ^ 2) (n : ℝ)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
    fun v hv n => Integrable.of_bound (hmeas_min v hv n) n (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn v n x)]; exact min_le_right _ _)

  have key : ∀ n : ℕ, ∫⁻ x in Φ, ENNReal.ofReal (min (‖u (x * h)‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ x in Φ, ENNReal.ofReal (min (‖u x‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro n
    have hB := AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
      K α β Φ hΦs hΦ h hh (fun x => ((min (‖u x‖ ^ 2) (n : ℝ) : ℝ) : ℂ)) (fun γ g => by rw [hΓ γ g])
    rw [integral_complex_ofReal, integral_complex_ofReal] at hB
    have hR : ∫ x in Φ, min (‖u (x * h)‖ ^ 2) (n : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ x in Φ, min (‖u x‖ ^ 2) (n : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by exact_mod_cast hB
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _ huh n) (Filter.Eventually.of_forall (hnn _ n)),
      ← ofReal_integral_eq_lintegral_ofReal (hint _ hu n) (Filter.Eventually.of_forall (hnn _ n)), hR]

  have hsup : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∫⁻ x in Φ, ENNReal.ofReal (‖v x‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ⨆ n : ℕ, ∫⁻ x in Φ, ENNReal.ofReal (min (‖v x‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro v hv
    rw [← lintegral_iSup' (fun n => (hmeas_min v hv n).aemeasurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => fun a b hab =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hab)))]
    exact lintegral_congr fun x => (T6B.iSup_ofReal_min_natCast _ (sq_nonneg _)).symm
  rw [hsup _ huh, hsup _ hu]
  exact iSup_congr key

namespace Ws31
namespace Adjoint

theorem setIntegral_mul_conj_comp_mul_eq (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (v w : AdelicGL2 (𝓞 K) K → ℂ)
    (hvΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), v (globalPoints (𝓞 K) K γ * g) = v g)
    (hwΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), w (globalPoints (𝓞 K) K γ * g) = w g)
    (hvZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      v (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * v g)
    (hwZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      w (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * w g)
    (x : AdelicGL2 (𝓞 K) K) :
    ∫ g in Φ, v g * conj (w (g * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in Φ, v (g * x⁻¹) * conj (w g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  set F : AdelicGL2 (𝓞 K) K → ℂ := fun g => v (g * x⁻¹) * conj (w g) with hF
  have hFΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), F (globalPoints (𝓞 K) K γ * g) = F g := by
    intro γ g; simp only [hF, mul_assoc, hvΓ, hwΓ]

  have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hr : 0 < 1 / NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) := one_div_pos.2 hd
  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K _ (Real.sqrt_pos.2 hr)
  have hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * x)) = 1 := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar K, pow_two,
      NumberField.TateGlobal.ideleNorm_mul, hz, Real.mul_self_sqrt hr.le, one_div_mul_cancel hd.ne']
  have hξ2 : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      conj (((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) * ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = 1 := by
    intro z
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hξu, one_pow, Complex.ofReal_one]

  have h1 : ∀ g, F (g * (centralScalar (𝓞 K) K z * x)) = v g * conj (w (g * x)) := by
    intro g
    have e1 : g * (centralScalar (𝓞 K) K z * x) * x⁻¹ = centralScalar (𝓞 K) K z * g := by
      rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, mul_centralScalar_comm]
    have e2 : g * (centralScalar (𝓞 K) K z * x) = centralScalar (𝓞 K) K z * (g * x) := by
      rw [← mul_assoc, mul_centralScalar_comm, mul_assoc]
    simp only [hF]
    rw [e1, e2, hvZ, hwZ, map_mul]
    calc ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * v g * (conj (((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) * conj (w (g * x)))
        = (conj (((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) * ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) * (v g * conj (w (g * x))) := by ring
      _ = v g * conj (w (g * x)) := by rw [hξ2, one_mul]
  have key := AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
    K α β Φ hΦs hΦ _ hh F hFΓ
  simp only [h1] at key
  rw [key]

end Ws31.Adjoint

namespace Ws31
namespace Adjoint

theorem setLIntegral_norm_sq_comp_mul_eq_of_central (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦfin : adelicGLHaar (Fin 2) (𝓞 K) K Φ < ⊤)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : AEStronglyMeasurable u (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
    (hZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      u (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g)
    (x : AdelicGL2 (𝓞 K) K) :
    ∫⁻ g in Φ, ENNReal.ofReal (‖u (g * x)‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ g in Φ, ENNReal.ofReal (‖u g‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hr : 0 < 1 / NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) := one_div_pos.2 hd
  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K _ (Real.sqrt_pos.2 hr)
  have hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * x)) = 1 := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar K, pow_two,
      NumberField.TateGlobal.ideleNorm_mul, hz, Real.mul_self_sqrt hr.le, one_div_mul_cancel hd.ne']
  have hpt : ∀ g : AdelicGL2 (𝓞 K) K, ‖u (g * (centralScalar (𝓞 K) K z * x))‖ = ‖u (g * x)‖ := by
    intro g
    rw [← mul_assoc, mul_centralScalar_comm, mul_assoc, hZ, norm_mul, hξu z, one_mul]
  rw [← T6B.setLIntegral_ofReal_norm_sq_comp_mul_eq K α β Φ hΦs hΦ hΦfin u hu hΓ _ hh]
  exact lintegral_congr fun g => by rw [hpt]

end Ws31.Adjoint

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (v w : AdelicGL2 (𝓞 K) K → ℂ)
    (_hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v)
    (_hw : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK w)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, v g * conj (convOp K f w g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K (fun x => conj (f x⁻¹)) v g * conj (w g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsInvInvariant :=
    MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (adelicGLHaar (Fin 2) (𝓞 K) K)
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ
  have hfin : μ Φ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict Φ) := isFiniteMeasure_restrict.2 hfin.ne

  have hvL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 _hv
  have hwL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 _hw
  have hvΓ := hvL.1.left_invariant
  have hwΓ := hwL.1.left_invariant
  have hvZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      v (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * v g :=
    fun z g => hvL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hwZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      w (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * w g :=
    fun z g => hwL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hvm : AEStronglyMeasurable v μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK v _hv
  have hwm : AEStronglyMeasurable w μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK w _hw

  have FUB : ∀ (a b : AdelicGL2 (𝓞 K) K → ℂ),
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK a →
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK b →
      ∀ (h : AdelicGL2 (𝓞 K) K → ℂ), Continuous h → HasCompactSupport h →
      ∫ g in Φ, (∫ x, a (g * x) * h x ∂μ) * conj (b g) ∂μ = ∫ x, h x * ∫ g in Φ, a (g * x) * conj (b g) ∂μ ∂μ := by
    intro a b ha hb h hh hhc
    have haL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 ha
    have hbL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hb
    have ham : AEStronglyMeasurable a μ :=
      AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK a ha
    have hbm : AEStronglyMeasurable b μ :=
      AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK b hb
    have haΓ := haL.1.left_invariant
    have haZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        a (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * a g :=
      fun z g => haL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
    have ha2 : MemLp a 2 (μ.restrict Φ) := haL.2
    have hb2 : MemLp b 2 (μ.restrict Φ) := hbL.2

    have hIa : Integrable (fun g => ‖a g‖ ^ 2) (μ.restrict Φ) := (memLp_two_iff_integrable_sq_norm ham.restrict).1 ha2
    have hIb : Integrable (fun g => ‖b g‖ ^ 2) (μ.restrict Φ) := (memLp_two_iff_integrable_sq_norm hbm.restrict).1 hb2
    have hmass : ∀ x : AdelicGL2 (𝓞 K) K,
        ∫⁻ g in Φ, ENNReal.ofReal (‖a (g * x)‖ ^ 2) ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖a g‖ ^ 2) ∂μ :=
      fun x => Ws31.Adjoint.setLIntegral_norm_sq_comp_mul_eq_of_central K α β Φ hslab hFD hfin ξK hξu a ham haΓ haZ x
    have haxm : ∀ x : AdelicGL2 (𝓞 K) K, AEStronglyMeasurable (fun g => a (g * x)) μ := fun x =>
      ham.comp_quasiMeasurePreserving (measurePreserving_mul_right μ x).quasiMeasurePreserving
    have hIax : ∀ x : AdelicGL2 (𝓞 K) K, Integrable (fun g => ‖a (g * x)‖ ^ 2) (μ.restrict Φ) := by
      intro x
      refine ⟨((haxm x).restrict.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
      show ∫⁻ g in Φ, ‖‖a (g * x)‖ ^ 2‖ₑ ∂μ < ⊤
      have h1 : ∫⁻ g in Φ, ‖‖a (g * x)‖ ^ 2‖ₑ ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖a (g * x)‖ ^ 2) ∂μ :=
        lintegral_congr fun g => Real.enorm_eq_ofReal (sq_nonneg _)
      have h2 : ∫⁻ g in Φ, ‖‖a g‖ ^ 2‖ₑ ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖a g‖ ^ 2) ∂μ :=
        lintegral_congr fun g => Real.enorm_eq_ofReal (sq_nonneg _)
      rw [h1, hmass x, ← h2]
      exact hIa.2
    have hax : ∀ x : AdelicGL2 (𝓞 K) K, MemLp (fun g => a (g * x)) 2 (μ.restrict Φ) := fun x =>
      (memLp_two_iff_integrable_sq_norm (haxm x).restrict).2 (hIax x)
    have hmassR : ∀ x : AdelicGL2 (𝓞 K) K, ∫ g in Φ, ‖a (g * x)‖ ^ 2 ∂μ = ∫ g in Φ, ‖a g‖ ^ 2 ∂μ := by
      intro x
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun g => sq_nonneg _) (hIax x).1,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun g => sq_nonneg _) hIa.1, hmass x]

    set G : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K → ℂ := fun p => a (p.1 * p.2) * h p.2 * conj (b p.1) with hG
    have hq : Measure.QuasiMeasurePreserving (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => p.1 * p.2)
        ((μ.restrict Φ).prod μ) μ :=
      Measure.quasiMeasurePreserving_snd.comp (measurePreserving_prod_mul (μ.restrict Φ) μ).quasiMeasurePreserving
    have hGm : AEStronglyMeasurable G ((μ.restrict Φ).prod μ) :=
      ((ham.comp_quasiMeasurePreserving hq).mul (hh.comp continuous_snd).aestronglyMeasurable).mul
        (Complex.continuous_conj.comp_aestronglyMeasurable hbm.restrict.comp_fst)
    have hconjb : MemLp (fun g => conj (b g)) 2 (μ.restrict Φ) :=
      hb2.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hbm.restrict)
        (Filter.Eventually.of_forall fun g => (RCLike.norm_conj _).symm)
    have hGi : Integrable G ((μ.restrict Φ).prod μ) := by
      refine (integrable_prod_iff' hGm).2 ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
      · have h1 : Integrable ((fun g => a (g * x)) * fun g => conj (b g)) (μ.restrict Φ) :=
          (hax x).integrable_mul hconjb
        have := h1.mul_const (h x)
        refine this.congr (Filter.Eventually.of_forall fun g => ?_)
        show a (g * x) * conj (b g) * h x = a (g * x) * h x * conj (b g)
        ring
      ·
        have hbound : ∀ x, ∫ g, ‖G (g, x)‖ ∂(μ.restrict Φ) ≤
            ‖h x‖ * ((∫ g in Φ, ‖a g‖ ^ 2 ∂μ) + ∫ g in Φ, ‖b g‖ ^ 2 ∂μ) := by
          intro x
          have hpt : ∀ g, ‖G (g, x)‖ ≤ ‖h x‖ * (‖a (g * x)‖ ^ 2 + ‖b g‖ ^ 2) := by
            intro g
            simp only [hG, norm_mul, RCLike.norm_conj]
            have : ‖a (g * x)‖ * ‖b g‖ ≤ ‖a (g * x)‖ ^ 2 + ‖b g‖ ^ 2 := by
              nlinarith [sq_nonneg (‖a (g * x)‖ - ‖b g‖), norm_nonneg (a (g * x)), norm_nonneg (b g)]
            calc ‖a (g * x)‖ * ‖h x‖ * ‖b g‖ = ‖h x‖ * (‖a (g * x)‖ * ‖b g‖) := by ring
              _ ≤ ‖h x‖ * (‖a (g * x)‖ ^ 2 + ‖b g‖ ^ 2) := by gcongr
          calc ∫ g, ‖G (g, x)‖ ∂(μ.restrict Φ) ≤ ∫ g, ‖h x‖ * (‖a (g * x)‖ ^ 2 + ‖b g‖ ^ 2) ∂(μ.restrict Φ) :=
                integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => norm_nonneg _)
                  (((hIax x).add hIb).const_mul _) (Filter.Eventually.of_forall hpt)
            _ = ‖h x‖ * ((∫ g in Φ, ‖a g‖ ^ 2 ∂μ) + ∫ g in Φ, ‖b g‖ ^ 2 ∂μ) := by
                rw [integral_const_mul, integral_add (hIax x) hIb, hmassR x]
        have hmeasI : AEStronglyMeasurable (fun x => ∫ g, ‖G (g, x)‖ ∂(μ.restrict Φ)) μ := by
          have := hGm.prod_swap.norm
          exact this.integral_prod_right'
        refine Integrable.mono' ((hh.norm.integrable_of_hasCompactSupport hhc.norm).mul_const
          ((∫ g in Φ, ‖a g‖ ^ 2 ∂μ) + ∫ g in Φ, ‖b g‖ ^ 2 ∂μ)) hmeasI (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun g => norm_nonneg _)]
        exact hbound x

    have hL : ∀ g, (∫ x, a (g * x) * h x ∂μ) * conj (b g) = ∫ x, G (g, x) ∂μ := by
      intro g
      rw [← integral_mul_const]
    have hR : ∀ x, (∫ g in Φ, G (g, x) ∂μ) = h x * ∫ g in Φ, a (g * x) * conj (b g) ∂μ := by
      intro x
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show a (g * x) * h x * conj (b g) = h x * (a (g * x) * conj (b g))
      ring
    simp_rw [hL]
    rw [integral_integral_swap (f := fun g x => G (g, x)) hGi]
    simp_rw [hR]

  have TRANS : ∀ x : AdelicGL2 (𝓞 K) K,
      ∫ g in Φ, v g * conj (w (g * x)) ∂μ = ∫ g in Φ, v (g * x⁻¹) * conj (w g) ∂μ :=
    fun x => Ws31.Adjoint.setIntegral_mul_conj_comp_mul_eq K α β Φ hslab hFD ξK hξu v w hvΓ hwΓ hvZ hwZ x

  have hstar_c : Continuous (fun x : AdelicGL2 (𝓞 K) K => conj (f x⁻¹)) :=
    (Complex.continuous_conj.comp (_hf.comp continuous_inv))
  have hstar_cs : HasCompactSupport (fun x : AdelicGL2 (𝓞 K) K => conj (f x⁻¹)) :=
    (_hfc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))).comp_left (map_zero _)
  calc ∫ g in Φ, v g * conj (convOp K f w g) ∂μ
      = conj (∫ g in Φ, (∫ x, w (g * x) * f x ∂μ) * conj (v g) ∂μ) := by
        rw [← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [map_mul, Complex.conj_conj, convOp_apply, rightConv_apply, hμ]
        ring
    _ = conj (∫ x, f x * ∫ g in Φ, w (g * x) * conj (v g) ∂μ ∂μ) := by rw [FUB w v _hw _hv f _hf _hfc]
    _ = ∫ x, conj (f x) * ∫ g in Φ, v g * conj (w (g * x)) ∂μ ∂μ := by
        rw [← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show conj (f x * ∫ g in Φ, w (g * x) * conj (v g) ∂μ) = conj (f x) * ∫ g in Φ, v g * conj (w (g * x)) ∂μ
        rw [map_mul, ← integral_conj]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show conj (w (g * x) * conj (v g)) = v g * conj (w (g * x))
        rw [map_mul, Complex.conj_conj, mul_comm]
    _ = ∫ x, conj (f x) * ∫ g in Φ, v (g * x⁻¹) * conj (w g) ∂μ ∂μ := by
        simp only [TRANS]
    _ = ∫ x, conj (f x⁻¹) * ∫ g in Φ, v (g * x) * conj (w g) ∂μ ∂μ := by
        rw [← integral_inv_eq_self (fun x => conj (f x⁻¹) * ∫ g in Φ, v (g * x) * conj (w g) ∂μ) ]
        simp only [inv_inv]
    _ = ∫ g in Φ, (∫ x, v (g * x) * conj (f x⁻¹) ∂μ) * conj (w g) ∂μ := by
        rw [FUB v w _hv _hw _ hstar_c hstar_cs]
    _ = ∫ g in Φ, convOp K (fun x => conj (f x⁻¹)) v g * conj (w g) ∂μ := by
        simp only [convOp_apply, rightConv_apply, hμ]

end S_AutomorphicForm_setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt (solution)
