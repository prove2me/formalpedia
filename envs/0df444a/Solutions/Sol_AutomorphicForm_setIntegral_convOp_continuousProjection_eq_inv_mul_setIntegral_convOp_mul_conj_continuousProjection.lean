-- Prove2me | solution 1 for AutomorphicForm.setIntegral_convOp_continuousProjection_eq_inv_mul_setIntegral_convOp_mul_conj_continuousProjection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/08e17bad-58a7-5058-8952-19bf49ae3abd

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
import Theorems.Thm_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
import Theorems.Thm_NumberField_TateGlobal_exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_convOp_continuousProjection_eq_inv_mul_setIntegral_convOp_mul_conj_continuousProjection
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
      K α β Φ hΦs hΦ h hh (fun x => ((min (‖u x‖ ^ 2) (n : ℝ) : ℝ) : ℂ)) (fun γ g => by beta_reduce; rw [hΓ γ g])
    beta_reduce at hB
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

namespace Ws31
namespace PairForm

theorem norm_integral_mul_conj_le {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (φ ψ : X → ℂ) (hφ : MemLp φ 2 ν) (hψ : MemLp ψ 2 ν) :
    ‖∫ x, φ x * conj (ψ x) ∂ν‖ ≤ (eLpNorm φ 2 ν).toReal * (eLpNorm ψ 2 ν).toReal := by
  have h1 : ∫ x, φ x * conj (ψ x) ∂ν = inner ℂ (hψ.toLp ψ) (hφ.toLp φ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hφ.coeFn_toLp, hψ.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply, mul_comm]
  rw [h1]
  calc ‖inner ℂ (hψ.toLp ψ) (hφ.toLp φ)‖ ≤ ‖hψ.toLp ψ‖ * ‖hφ.toLp φ‖ := norm_inner_le_norm _ _
    _ = (eLpNorm φ 2 ν).toReal * (eLpNorm ψ 2 ν).toReal := by rw [Lp.norm_toLp, Lp.norm_toLp, mul_comm]

theorem comp_mul_mem_residualSpan (K : Type) [Field K] [NumberField K]
    (Z : Subgroup (AdeleRing (𝓞 K) K)ˣ) (ξ : Z →* ℂˣ) (r : AdelicGL2 (𝓞 K) K → ℂ)
    (hr : r ∈ AutomorphicForm.residualSpan (𝓞 K) K Z ξ) (y : AdelicGL2 (𝓞 K) K) :
    (fun g => r (g * y)) ∈ AutomorphicForm.residualSpan (𝓞 K) K Z ξ := by
  let T : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => g * y)
  have hT : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, T u = fun g => u (g * y) := fun u => rfl
  have hle : Submodule.map T (AutomorphicForm.residualSpan (𝓞 K) K Z ξ) ≤
      AutomorphicForm.residualSpan (𝓞 K) K Z ξ := by
    unfold AutomorphicForm.residualSpan
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro φ ⟨χ, hχ, rfl⟩
    have e : T (AutomorphicForm.chiDet (𝓞 K) K χ) =
        ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • AutomorphicForm.chiDet (𝓞 K) K χ := by
      funext g
      show AutomorphicForm.chiDet (𝓞 K) K χ (g * y) =
        ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * AutomorphicForm.chiDet (𝓞 K) K χ g
      simp only [AutomorphicForm.chiDet, map_mul, Units.val_mul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, hχ, rfl⟩)
  rw [← hT]
  exact hle (Submodule.mem_map_of_mem hr)

theorem band_toReal_pos (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK) :
    0 < (νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal := by
  obtain ⟨C, hC, hband⟩ :=
    NumberField.TateGlobal.exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log K νZK
  have h2 : {z : (AdeleRing (𝓞 K) K)ˣ | NumberField.TateGlobal.ideleNorm K
        (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β} =
      {z | NumberField.TateGlobal.ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β)} := by
    ext z
    simp only [Set.mem_setOf_eq]
    have hu := NumberField.TateGlobal.ideleNorm_pos z
    rw [det_centralScalar K, pow_two, NumberField.TateGlobal.ideleNorm_mul, Set.mem_Icc, Set.mem_Icc]
    have hN : Real.sqrt (NumberField.TateGlobal.ideleNorm K z * NumberField.TateGlobal.ideleNorm K z) =
        NumberField.TateGlobal.ideleNorm K z := Real.sqrt_mul_self hu.le
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := Real.sqrt_le_sqrt h1; rwa [hN] at this
      · have := Real.sqrt_le_sqrt h2; rwa [hN] at this
    · rintro ⟨h1, h2⟩
      have hβ : 0 ≤ β := by
        have : 0 < Real.sqrt β := hu.trans_le h2
        exact (Real.sqrt_pos.1 this).le
      refine ⟨?_, ?_⟩
      · have := mul_self_le_mul_self (Real.sqrt_nonneg α) h1
        rwa [Real.mul_self_sqrt hα.le] at this
      · have := mul_self_le_mul_self hu.le h2
        rwa [Real.mul_self_sqrt hβ] at this
  rw [h2, hband ΩK hΩK _ _ (Real.sqrt_pos.2 hα) (Real.sqrt_le_sqrt hαβ.le)]
  have hlt : Real.sqrt α < Real.sqrt β := Real.sqrt_lt_sqrt hα.le hαβ
  have hpos : 0 < C * Real.log (Real.sqrt β / Real.sqrt α) :=
    mul_pos hC (Real.log_pos ((one_lt_div (Real.sqrt_pos.2 hα)).2 hlt))
  rw [ENNReal.toReal_ofReal hpos.le]
  exact hpos

theorem isAutomorphicFnAt_comp_mul (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) (y : AdelicGL2 (𝓞 K) K) :
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (fun g => u (g * y)) := by
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
  have huL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
  have huΓ := huL.1.left_invariant
  have huZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      u (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g :=
    fun z g => huL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hum : AEStronglyMeasurable u μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK u hu
  have hu2 : MemLp u 2 (μ.restrict Φ) := huL.2
  have hIu : Integrable (fun g => ‖u g‖ ^ 2) (μ.restrict Φ) :=
    (memLp_two_iff_integrable_sq_norm hum.restrict).1 hu2
  have hmass : ∫⁻ g in Φ, ENNReal.ofReal (‖u (g * y)‖ ^ 2) ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖u g‖ ^ 2) ∂μ :=
    Ws31.Adjoint.setLIntegral_norm_sq_comp_mul_eq_of_central K α β Φ hslab hFD hfin ξK hξu u hum huΓ huZ y
  have huym : AEStronglyMeasurable (fun g => u (g * y)) μ :=
    hum.comp_quasiMeasurePreserving (measurePreserving_mul_right μ y).quasiMeasurePreserving
  have hIuy : Integrable (fun g => ‖u (g * y)‖ ^ 2) (μ.restrict Φ) := by
    refine ⟨(huym.restrict.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
    show ∫⁻ g in Φ, ‖‖u (g * y)‖ ^ 2‖ₑ ∂μ < ⊤
    have h1 : ∫⁻ g in Φ, ‖‖u (g * y)‖ ^ 2‖ₑ ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖u (g * y)‖ ^ 2) ∂μ :=
      lintegral_congr fun g => Real.enorm_eq_ofReal (sq_nonneg _)
    have h2 : ∫⁻ g in Φ, ‖‖u g‖ ^ 2‖ₑ ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖u g‖ ^ 2) ∂μ :=
      lintegral_congr fun g => Real.enorm_eq_ofReal (sq_nonneg _)
    rw [h1, hmass, ← h2]
    exact hIu.2
  have huy2 : MemLp (fun g => u (g * y)) 2 (μ.restrict Φ) :=
    (memLp_two_iff_integrable_sq_norm huym.restrict).2 hIuy
  refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, huy2⟩
  · beta_reduce
    rw [mul_assoc]
    exact huΓ γ (g * y)
  · beta_reduce
    rw [mul_assoc]
    exact huL.1.central_transform z (g * y)

theorem fubini_pairing (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (a b : AdelicGL2 (𝓞 K) K → ℂ) (ha : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK a) (hb : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK b)
    (h : AdelicGL2 (𝓞 K) K → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (∫ x, a (g * x) * h x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * conj (b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x, h x * ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        a (g * x) * conj (b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
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

end Ws31.PairForm

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    letI := adeleBorel (𝓞 K) K
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)) (_hC : IsCompact C)
      (A : Set (AdelicGL2 (𝓞 K) K)) (_hA : A ⊆ C) (_hAm : MeasurableSet A)
      (B : Set (AdelicGL2 (𝓞 K) K)) (_hB : B ⊆ C) (_hBm : MeasurableSet B)
      (ucA urA ueA : AdelicGL2 (𝓞 K) K → ℂ)
      (_hucA : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ucA) (_huc0A : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 ucA g = 0))
      (_hurA : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK urA)
      (_hurcA : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (urA - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hueA : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ueA)
      (_hueoA : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ueA g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsumA : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator (A.indicator fun _ => (1 : ℂ))
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] ucA + urA + ueA)
      (ucB urB ueB : AdelicGL2 (𝓞 K) K → ℂ)
      (_hucB : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ucB) (_huc0B : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 ucB g = 0))
      (_hurB : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK urB)
      (_hurcB : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (urB - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hueB : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ueB)
      (_hueoB : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ueB g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsumB : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator (B.indicator fun _ => (1 : ℂ))
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] ucB + urB + ueB)
,
    ∫ x in A, convOp K f ueB x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) =
      (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ))⁻¹ *
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K f ueB g * conj (ueA g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  intro C hC A hA hAm B hB hBm ucA urA ueA hucA huc0A hurA hurcA hueA hueoA hsumA
    ucB urB ueB hucB huc0B hurB hurcB hueB hueoB hsumB
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
  set P := productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K) with hP

  have hstar_c : Continuous (fun x : AdelicGL2 (𝓞 K) K => conj (f x⁻¹)) :=
    (Complex.continuous_conj.comp (_hf.comp continuous_inv))
  have hstar_cs : HasCompactSupport (fun x : AdelicGL2 (𝓞 K) K => conj (f x⁻¹)) :=
    (_hfc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))).comp_left (map_zero _)

  have hw : IsAutomorphicFnAt K P ξK (convOp K f ueB) :=
    AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
      K α β hα hαβ ξK hξc hξu ueB hueB f _hf _hfc
  have hwL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hw
  have hw2 : MemLp (convOp K f ueB) 2 (μ.restrict Φ) := hwL.2
  have hwm : AEStronglyMeasurable (convOp K f ueB) μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK _ hw
  have hconjw : MemLp (fun g => conj (convOp K f ueB g)) 2 (μ.restrict Φ) :=
    hw2.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hwm.restrict)
      (Filter.Eventually.of_forall fun g => (RCLike.norm_conj _).symm)
  have hint : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K P ξK u →
      Integrable (fun g => u g * conj (convOp K f ueB g)) (μ.restrict Φ) :=
    fun u hu => ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu).2.integrable_mul hconjw

  have hΨm : Measurable (A.indicator fun _ => (1 : ℂ)) := measurable_const.indicator hAm
  have hΨc : ∃ C' : Set (AdelicGL2 (𝓞 K) K), IsCompact C' ∧ ∀ y ∉ C', A.indicator (fun _ => (1 : ℂ)) y = 0 :=
    ⟨C, hC, fun y hy => Set.indicator_of_notMem (fun h => hy (hA h)) _⟩
  have hΨb : ∃ B' : ℝ, ∀ y, ‖A.indicator (fun _ => (1 : ℂ)) y‖ ≤ B' :=
    ⟨1, fun y => by by_cases hy : y ∈ A <;> simp [hy]⟩
  have hU := AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
    K α β hα hαβ νZK ΩK hΩK ξK hξc hξt hξu (A.indicator fun _ => (1 : ℂ)) hΨm hΨc hΨb (convOp K f ueB) hw

  have hsplit : ∫ g in Φ, (ucA + urA + ueA) g * conj (convOp K f ueB g) ∂μ =
      (∫ g in Φ, ucA g * conj (convOp K f ueB g) ∂μ) + (∫ g in Φ, urA g * conj (convOp K f ueB g) ∂μ)
        + ∫ g in Φ, ueA g * conj (convOp K f ueB g) ∂μ := by
    have e : ∀ g, (ucA + urA + ueA) g * conj (convOp K f ueB g) =
        (ucA g * conj (convOp K f ueB g) + urA g * conj (convOp K f ueB g))
          + ueA g * conj (convOp K f ueB g) := by
      intro g; simp only [Pi.add_apply]; ring
    simp_rw [e]
    have h12 : Integrable (fun g => ucA g * conj (convOp K f ueB g) + urA g * conj (convOp K f ueB g))
        (μ.restrict Φ) := (hint ucA hucA).add (hint urA hurA)
    rw [integral_add h12 (hint ueA hueA), integral_add (hint ucA hucA) (hint urA hurA)]

  have hc0 : ∫ g in Φ, ucA g * conj (convOp K f ueB g) ∂μ = 0 := by
    have hadj := AutomorphicForm.setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
      K α β hα hαβ ξK hξc hξu ucA ueB hucA hueB f _hf _hfc
    refine hadj.trans ?_
    have hhA : IsAutomorphicFnAt K P ξK (convOp K (fun x => conj (f x⁻¹)) ucA) :=
      AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
        K α β hα hαβ ξK hξc hξu ucA hucA _ hstar_c hstar_cs
    have hct := AutomorphicForm.constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt
      K α β hα hαβ ξK hξc ucA hucA _ hstar_c hstar_cs huc0A
    have h0 : ∫ g in Φ, ueB g * conj (convOp K (fun x => conj (f x⁻¹)) ucA g) ∂μ = 0 :=
      hueoB _ hhA (Or.inl (Filter.Eventually.of_forall hct))
    calc ∫ g in Φ, convOp K (fun x => conj (f x⁻¹)) ucA g * conj (ueB g) ∂μ
        = conj (∫ g in Φ, ueB g * conj (convOp K (fun x => conj (f x⁻¹)) ucA g) ∂μ) := by
          rw [← integral_conj]
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          dsimp only
          rw [map_mul, Complex.conj_conj, mul_comm]
      _ = 0 := by rw [h0, map_zero]

  have hr0 : ∀ r : AdelicGL2 (𝓞 K) K → ℂ, r ∈ AutomorphicForm.residualSpan (𝓞 K) K P.Z ξK →
      IsAutomorphicFnAt K P ξK r → ∫ g in Φ, r g * conj (convOp K f ueB g) ∂μ = 0 := by
    intro r hrS hrA
    have hrL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hrA
    have hueBL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hueB
    have hrZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        r (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * r g :=
      fun z g => hrL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
    have hueBZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        ueB (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ueB g :=
      fun z g => hueBL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
    have hinner : ∀ x : AdelicGL2 (𝓞 K) K, ∫ g in Φ, ueB (g * x) * conj (r g) ∂μ = 0 := by
      intro x
      have T := Ws31.Adjoint.setIntegral_mul_conj_comp_mul_eq K α β Φ hslab hFD ξK hξu ueB r
        hueBL.1.left_invariant hrL.1.left_invariant hueBZ hrZ x⁻¹
      rw [inv_inv] at T
      rw [← T]
      exact hueoB (fun g => r (g * x⁻¹))
        (Ws31.PairForm.isAutomorphicFnAt_comp_mul K α β hα hαβ ξK hξu r hrA x⁻¹)
        (Or.inr (Ws31.PairForm.comp_mul_mem_residualSpan K _ ξK r hrS x⁻¹))
    have hF := Ws31.PairForm.fubini_pairing K α β hα hαβ ξK hξu ueB r hueB hrA f _hf _hfc
    calc ∫ g in Φ, r g * conj (convOp K f ueB g) ∂μ
        = conj (∫ g in Φ, (∫ x, ueB (g * x) * f x ∂μ) * conj (r g) ∂μ) := by
          rw [← integral_conj]
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          simp only [map_mul, Complex.conj_conj, convOp_apply, rightConv_apply, hμ]
          ring
      _ = conj (∫ x, f x * ∫ g in Φ, ueB (g * x) * conj (r g) ∂μ ∂μ) := by rw [hF]
      _ = 0 := by simp only [hinner, mul_zero, integral_zero, map_zero]

  have hr_zero : ∫ g in Φ, urA g * conj (convOp K f ueB g) ∂μ = 0 := by
    have hurL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hurA
    have hbound : ∀ ε : ℝ, 0 < ε → ‖∫ g in Φ, urA g * conj (convOp K f ueB g) ∂μ‖ ≤
        ε * (eLpNorm (convOp K f ueB) 2 (μ.restrict Φ)).toReal := by
      intro ε hε
      obtain ⟨r, hrS, hrA, hrε⟩ := hurcA ε hε
      have hrL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hrA
      have hd2 : MemLp (urA - r) 2 (μ.restrict Φ) := hurL.2.sub hrL.2
      have hId : Integrable (fun g => (urA - r) g * conj (convOp K f ueB g)) (μ.restrict Φ) :=
        hd2.integrable_mul hconjw
      have hIr : Integrable (fun g => r g * conj (convOp K f ueB g)) (μ.restrict Φ) := hint r hrA
      have hsplit2 : ∫ g in Φ, urA g * conj (convOp K f ueB g) ∂μ =
          (∫ g in Φ, (urA - r) g * conj (convOp K f ueB g) ∂μ) + ∫ g in Φ, r g * conj (convOp K f ueB g) ∂μ := by
        rw [← integral_add hId hIr]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [Pi.sub_apply]
        ring
      rw [hsplit2, hr0 r hrS hrA, add_zero]
      calc ‖∫ g in Φ, (urA - r) g * conj (convOp K f ueB g) ∂μ‖
          ≤ (eLpNorm (urA - r) 2 (μ.restrict Φ)).toReal * (eLpNorm (convOp K f ueB) 2 (μ.restrict Φ)).toReal :=
            Ws31.PairForm.norm_integral_mul_conj_le _ _ _ hd2 hw2
        _ ≤ ε * (eLpNorm (convOp K f ueB) 2 (μ.restrict Φ)).toReal :=
            mul_le_mul_of_nonneg_right (ENNReal.toReal_lt_of_lt_ofReal hrε).le ENNReal.toReal_nonneg
    have hM0 : 0 ≤ (eLpNorm (convOp K f ueB) 2 (μ.restrict Φ)).toReal := ENNReal.toReal_nonneg
    have hI0 : ‖∫ g in Φ, urA g * conj (convOp K f ueB g) ∂μ‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hM1 : 0 < (eLpNorm (convOp K f ueB) 2 (μ.restrict Φ)).toReal + 1 := by linarith
      have := hbound (ε / ((eLpNorm (convOp K f ueB) 2 (μ.restrict Φ)).toReal + 1)) (div_pos hε hM1)
      refine this.trans ?_
      rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ hM1]
      nlinarith
    exact norm_le_zero_iff.1 hI0

  have hkey : ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
        ∫ g in Φ, A.indicator (fun _ => (1 : ℂ)) g * conj (convOp K f ueB g) ∂μ
      = ∫ g in Φ, ueA g * conj (convOp K f ueB g) ∂μ := by
    refine hU.symm.trans ?_
    calc _ = ∫ g in Φ, (ucA + urA + ueA) g * conj (convOp K f ueB g) ∂μ :=
          integral_congr_ae (hsumA.mono fun g hg => congrArg (fun t => t * conj (convOp K f ueB g)) hg)
      _ = _ := hsplit
      _ = ∫ g in Φ, ueA g * conj (convOp K f ueB g) ∂μ := by rw [hc0, hr_zero, zero_add, zero_add]

  have hbpos := Ws31.PairForm.band_toReal_pos K α β hα hαβ νZK ΩK hΩK
  have hb0 : ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hbpos.ne'

  have hLHS : ∫ x in A, convOp K f ueB x ∂(μ.restrict Φ) =
      ∫ g in Φ, A.indicator (fun _ => (1 : ℂ)) g * convOp K f ueB g ∂μ := by
    rw [← integral_indicator hAm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ A <;> simp [hg]

  have hkey' : ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) * ∫ g in Φ, A.indicator (fun _ => (1 : ℂ)) g * convOp K f ueB g ∂μ
      = ∫ g in Φ, convOp K f ueB g * conj (ueA g) ∂μ := by
    have e1 : ∫ g in Φ, A.indicator (fun _ => (1 : ℂ)) g * convOp K f ueB g ∂μ
        = conj (∫ g in Φ, A.indicator (fun _ => (1 : ℂ)) g * conj (convOp K f ueB g) ∂μ) := by
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      by_cases hg : g ∈ A <;> simp [hg]
    have e2 : ∫ g in Φ, convOp K f ueB g * conj (ueA g) ∂μ
        = conj (∫ g in Φ, ueA g * conj (convOp K f ueB g) ∂μ) := by
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      dsimp only
      rw [map_mul, Complex.conj_conj, mul_comm]
    rw [e1, e2, ← hkey, map_mul, Complex.conj_ofReal]
  rw [hLHS, ← hkey', ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]

end S_AutomorphicForm_setIntegral_convOp_continuousProjection_eq_inv_mul_setIntegral_convOp_mul_conj_continuousProjection
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_convOp_continuousProjection_eq_inv_mul_setIntegral_convOp_mul_conj_continuousProjection (solution)
