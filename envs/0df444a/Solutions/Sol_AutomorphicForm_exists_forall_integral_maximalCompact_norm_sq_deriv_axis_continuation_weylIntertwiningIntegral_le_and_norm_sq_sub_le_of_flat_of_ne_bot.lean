-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integral_maximalCompact_norm_sq_deriv_axis_continuation_weylIntertwiningIntegral_le_and_norm_sq_sub_le_of_flat_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/642dad37-11f6-5af8-8fac-8af4f7522935

import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight
import Theorems.Thm_NumberField_TateGlobal_exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq
import Theorems.Thm_MeasureTheory_integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le
import Theorems.Thm_AutomorphicForm_exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integral_maximalCompact_norm_sq_deriv_axis_continuation_weylIntertwiningIntegral_le_and_norm_sq_sub_le_of_flat_of_ne_bot
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support"
p2m_attr_erase "simp" "RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace R4ScattPar

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.TateGlobal
open LanglandsTunnell.Converse NumberField.AdelicVolume

variable {K : Type} [Field K] [NumberField K]

theorem norm_extensionEmbedding (v : InfinitePlace K) (x : v.Completion) : ‖extensionEmbedding v x‖ = ‖x‖ :=
  (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) x

theorem exists_extensionEmbedding_eq_ofReal (v : InfinitePlace K) (r : ℝ) :
    ∃ x : v.Completion, extensionEmbedding v x = (r : ℂ) := by
  by_cases hv : v.IsReal
  · obtain ⟨x, hx⟩ := surjective_extensionEmbeddingOfIsReal hv r
    exact ⟨x, by rw [← extensionEmbeddingOfIsReal_apply hv, hx]⟩
  · have hc : v.IsComplex := not_isReal_iff_isComplex.mp hv
    obtain ⟨x, hx⟩ := surjective_extensionEmbedding_of_isComplex hc (r : ℂ)
    exact ⟨x, hx⟩

theorem exists_unit_extensionEmbedding_eq (v : InfinitePlace K) {r : ℝ} (hr : 0 < r) :
    ∃ x : (v.Completion)ˣ, extensionEmbedding v (x : v.Completion) = (r : ℂ) := by
  obtain ⟨x, hx⟩ := exists_extensionEmbedding_eq_ofReal v r
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx
    exact hr.ne' (by exact_mod_cast hx.symm)
  exact ⟨Units.mk0 x hx0, hx⟩

theorem ideleNorm_archUnitHom (v : InfinitePlace K) (x : (v.Completion)ˣ) :
    ideleNorm K (archUnitHom v x) = ‖(x : v.Completion)‖ ^ v.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _
      (by rw [archUnitHom_apply]; exact archCentralUnit_snd v x),
    Finset.prod_eq_single v]
  · rw [archUnitHom_apply, archCentralUnit_fst_self]
  · intro w _ hw
    rw [archUnitHom_apply, archCentralUnit_fst_of_ne _ _ hw, norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ v) h

theorem ofReal_pow_cpow {r : ℝ} (hr : 0 < r) (n : ℕ) (w : ℂ) :
    (((r ^ n : ℝ)) : ℂ) ^ w = (r : ℂ) ^ ((n : ℂ) * w) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hrn : ((r ^ n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_pos hr n).ne'
  rw [Complex.cpow_def_of_ne_zero hrn, Complex.cpow_def_of_ne_zero hr0, ← Complex.ofReal_log (pow_pos hr n).le,
    Real.log_pow, ← Complex.ofReal_log hr.le]
  push_cast; ring_nf

theorem ofReal_exp_cpow (t : ℝ) (c : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ c = Complex.exp (t * c) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
  · rw [Complex.ofReal_im]; exact neg_lt_zero.mpr Real.pi_pos
  · rw [Complex.ofReal_im]; exact Real.pi_pos.le

theorem eq_zero_of_forall_cpow_eq_one {z : ℂ} (h : ∀ r : ℝ, 0 < r → (r : ℂ) ^ z = 1) : z = 0 := by
  have hexp : ∀ t : ℝ, Complex.exp ((t : ℂ) * z) = 1 := fun t => by
    rw [← ofReal_exp_cpow]; exact h _ (Real.exp_pos t)
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * z)) (Complex.exp ((0 : ℝ) * z) * (1 * z)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * z) (1 * z) 0 := (Complex.ofRealCLM.hasDerivAt).mul_const z
    exact (Complex.hasDerivAt_exp _).comp (0 : ℝ) h1
  have hc : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * z)) 0 0 := by
    have : (fun t : ℝ => Complex.exp ((t : ℂ) * z)) = fun _ => (1 : ℂ) := funext hexp
    rw [this]; exact hasDerivAt_const 0 1
  have := hd.unique hc
  simpa using this

theorem cpow_exponent_unique {a b : ℂ} (h : ∀ r : ℝ, 0 < r → (r : ℂ) ^ a = (r : ℂ) ^ b) : a = b := by
  have : a - b = 0 := eq_zero_of_forall_cpow_eq_one fun r hr => by
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hr.ne'), h r hr, div_self]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
  exact sub_eq_zero.mp this

theorem u_eq_of_isArchCompAt {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : InfinitePlace K} {u : ℂ} {a : ℤ}
    (hA : IsArchCompAt K μ v u a) {τ : ℝ}
    (hτ : ∀ (x : (v.Completion)ˣ),
        0 < (extensionEmbedding v (x : v.Completion)).re →
        (extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I)) :
    u = (τ : ℂ) * Complex.I := by
  have hm : (v.mult : ℂ) ≠ 0 := by exact_mod_cast (mult_pos (w := v)).ne'
  suffices h : (v.mult : ℂ) * u = (v.mult : ℂ) * ((τ : ℂ) * Complex.I) from mul_left_cancel₀ hm h
  refine cpow_exponent_unique fun r hr => ?_
  obtain ⟨x, hx⟩ := exists_unit_extensionEmbedding_eq v hr
  have hnx : ‖(x : v.Completion)‖ = r := by
    rw [← norm_extensionEmbedding, hx, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have h1 := hA x
  have h2 := hτ x (by rw [hx, Complex.ofReal_re]; exact hr) (by rw [hx, Complex.ofReal_im])
  rw [h1, hnx, hx, ideleNorm_archUnitHom, hnx, div_self (Complex.ofReal_ne_zero.mpr hr.ne'), one_zpow, mul_one,
    ofReal_pow_cpow hr] at h2
  exact h2

end R4ScattPar

namespace R4ScattTw

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open FLT.SmoothVectors
open scoped ComplexConjugate

variable {K : Type} [Field K] [NumberField K]

theorem det_fst_eq (g : AdelicGL2 (𝓞 K) K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 =
      ((glArch (𝓞 K) K g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) _).det := by
  show (adeleArch (𝓞 K) K) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) = _
  rw [RingHom.map_det]
  rfl

theorem det_snd_eq (g : AdelicGL2 (𝓞 K) K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 =
      ((glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _).det := by
  show (adeleFin (𝓞 K) K) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) = _
  rw [RingHom.map_det]
  rfl

theorem det_mem_integral_of_isLevelZeroMatrix {N : Ideal (𝓞 K)}
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hm : IsLevelZeroMatrix (𝓞 K) K N m) :
    m.det ∈ integralFiniteAdeles (𝓞 K) K := by
  rw [Matrix.det_fin_two]
  exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hm.integral 0 0) (hm.integral 1 1))
    (mul_mem_integralFiniteAdeles (hm.integral 0 1) (hm.integral 1 0))

theorem det_fst_eq_one_of_mem_finiteAdelicGL2Subgroup {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ finiteAdelicGL2Subgroup K) :
    ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  rw [det_fst_eq, (mem_finiteAdelicGL2Subgroup_iff K u).mp hu]
  simp

theorem finitePartUnits_det_mem_unitIdeles_of_mem_levelZero {N : Ideal (𝓞 K)} {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelZero (𝓞 K) K N) :
    NumberField.AdeleRing.finitePartUnits (𝓞 K) K (Matrix.GeneralLinearGroup.det u) ∈
      IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K := by
  rw [mem_levelZero_iff, mem_finiteLevelZero_iff] at hu
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have h := det_mem_integral_of_isLevelZeroMatrix hu.1 v
    rw [NumberField.AdeleRing.val_finitePartUnits, det_snd_eq]
    exact h
  · have h := det_mem_integral_of_isLevelZeroMatrix hu.2 v
    have : ((NumberField.AdeleRing.finitePartUnits (𝓞 K) K (Matrix.GeneralLinearGroup.det u))⁻¹ :
        (FiniteAdeleRing (𝓞 K) K)ˣ) = NumberField.AdeleRing.finitePartUnits (𝓞 K) K
          (Matrix.GeneralLinearGroup.det u⁻¹) := by
      rw [map_inv, map_inv]
    rw [this, NumberField.AdeleRing.val_finitePartUnits, det_snd_eq, map_inv]
    exact h

theorem principalLevel_le_levelZero (N : Ideal (𝓞 K)) :
    principalLevel (𝓞 K) K N ≤ levelZero (𝓞 K) K N :=
  (principalLevel_le_levelOne (𝓞 K) K N).trans (levelOne_le_levelZero (𝓞 K) K N)

theorem levelZero_le_levelZero_top (N : Ideal (𝓞 K)) :
    levelZero (𝓞 K) K N ≤ levelZero (𝓞 K) K ⊤ := by
  intro g hg
  rw [mem_levelZero_iff, mem_finiteLevelZero_iff] at hg ⊢
  refine ⟨⟨hg.1.integral, ?_⟩, ⟨hg.2.integral, ?_⟩⟩
  · exact fun v => (idealBound_top v).symm ▸ valued_apply_le_one (hg.1.integral 1 0) v
  · exact fun v => (idealBound_top v).symm ▸ valued_apply_le_one (hg.2.integral 1 0) v

section Eta

variable (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hηc : Continuous η)
  (hηu : ∀ v : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt η v)
include hηc hηu

theorem eta_det_eq_one {N : Ideal (𝓞 K)} {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelZero (𝓞 K) K N) (huf : u ∈ finiteAdelicGL2Subgroup K) :
    η (Matrix.GeneralLinearGroup.det u) = 1 :=
  NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous K η hηc ∅
    (fun v _ => hηu v) _ (det_fst_eq_one_of_mem_finiteAdelicGL2Subgroup huf) (fun v hv => absurd hv (by simp))
    (finitePartUnits_det_mem_unitIdeles_of_mem_levelZero hu)

theorem chiDet_mul_eq_of_mem {N : Ideal (𝓞 K)} {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelZero (𝓞 K) K N) (huf : u ∈ finiteAdelicGL2Subgroup K) (g : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K η (g * u) = chiDet (𝓞 K) K η g := by
  rw [chiDet_mul]
  unfold chiDet
  rw [eta_det_eq_one η hηc hηu hu huf, Units.val_one, mul_one]

theorem isKfSmooth_chiDet : IsKfSmooth K (chiDet (𝓞 K) K η) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨(levelZero (𝓞 K) K ⊤).subgroupOf (finiteAdelicGL2Subgroup K), ?_, ?_⟩
  · exact (isOpen_levelZero (𝓞 K) K top_ne_bot).preimage continuous_subtype_val
  · intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    rw [Subgroup.smul_def]
    exact RightTranslationFn.ext fun g => chiDet_mul_eq_of_mem η hηc hηu hu u.2 g

theorem isKfSmooth_fnTwist' {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsKfSmooth K φ) :
    IsKfSmooth K (fnTwist K η φ) :=
  isKfSmooth_fnTwist K η (isKfSmooth_chiDet η hηc hηu) hφ

theorem fnTwist_level {N : Ideal (𝓞 K)} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g)
    (g : AdelicGL2 (𝓞 K) K) (u : AdelicGL2 (𝓞 K) K)
    (hu : u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    fnTwist K η φ (g * u) = fnTwist K η φ g := by
  have hu' := Subgroup.mem_inf.mp hu
  simp only [fnTwist_apply]
  rw [chiDet_mul_eq_of_mem η hηc hηu (principalLevel_le_levelZero N hu'.1) hu'.2 g, hφ g u hu]

end Eta

theorem chiDet_borel_mul (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {b : AdelicGL2 (𝓞 K) K}
    (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K η (b * g) =
      ((η (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
        ((η (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * chiDet (𝓞 K) K η g := by
  rw [chiDet_mul]
  congr 1
  unfold chiDet
  rw [det_borel_eq_diag_mul hb, map_mul, Units.val_mul]

theorem isInducedSection_fnTwist (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) :
    IsInducedSection (𝓞 K) K (χ₁ * η) (χ₂ * η) (fnTwist K η φ) := by
  intro b hb g
  simp only [fnTwist_apply, MonoidHom.mul_apply, Units.val_mul]
  rw [chiDet_borel_mul η hb g, hφ b hb g]
  ring

theorem etaFst_mul (μ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) :
    etaFst (μ * η) α hα s = etaFst μ α hα s * η := by
  show μ * η * cpowChar α hα (s + 1 / 2) = μ * cpowChar α hα (s + 1 / 2) * η
  exact mul_right_comm μ η _

theorem etaSnd_mul (ν η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) :
    etaSnd (ν * η) α hα s = etaSnd ν α hα s * η := by
  show ν * η * cpowChar α hα (-(s + 1 / 2)) = ν * cpowChar α hα (-(s + 1 / 2)) * η
  exact mul_right_comm ν η _

def mulChiOn {X : Type*} (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (p : X → AdelicGL2 (𝓞 K) K) :
    (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun h := fun x => chiDet (𝓞 K) K η (p x) * h x
  map_add' h₁ h₂ := by funext x; simp [mul_add]
  map_smul' c h := by funext x; simp; ring

theorem mulChiOn_apply {X : Type*} (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (p : X → AdelicGL2 (𝓞 K) K) (h : X → ℂ)
    (x : X) : mulChiOn η p h x = chiDet (𝓞 K) K η (p x) * h x := rfl

theorem isArchKFinite_fnTwist (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchKFinite K φ) : IsArchKFinite K (fnTwist K η φ) := by
  classical
  intro w
  obtain ⟨s₀, hs₀⟩ := hφ w
  refine ⟨s₀.image (mulChiOn η id), fun k hk => ?_⟩
  have hmem := hs₀ k hk
  have heq : (fun x => fnTwist K η φ (x * k)) = chiDet (𝓞 K) K η k • mulChiOn η id (fun x => φ (x * k)) := by
    funext x
    simp only [fnTwist_apply, Pi.smul_apply, smul_eq_mul, mulChiOn_apply, id, chiDet_mul]
    ring
  rw [heq, Finset.coe_image]
  refine Submodule.smul_mem _ _ ?_
  rw [Submodule.span_image]
  exact Submodule.mem_map_of_mem hmem

theorem fnTwist_Ku (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ) (w : InfinitePlace K)
    (hφ : ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) :
    ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => fnTwist K η (φ s) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W := by
  obtain ⟨W, hW, hmem⟩ := hφ
  let L := mulChiOn (X := ↥(archRowIsometrySubgroup K w)) η (fun k => (k : AdelicGL2 (𝓞 K) K))
  haveI := hW
  refine ⟨W.map L, inferInstance, fun s g => ?_⟩
  have heq : (fun k : ↥(archRowIsometrySubgroup K w) => fnTwist K η (φ s) (g * (k : AdelicGL2 (𝓞 K) K))) =
      chiDet (𝓞 K) K η g • L (fun k => φ s (g * (k : AdelicGL2 (𝓞 K) K))) := by
    funext k
    simp only [fnTwist_apply, Pi.smul_apply, smul_eq_mul, L, mulChiOn_apply, chiDet_mul]
    ring
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hmem s g))

theorem fnTwist_mem_typeSubmodule (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {H W : Type*} [Group H]
    [AddCommGroup W] [Module ℂ W]
    (ι : H →* AdelicGL2 (𝓞 K) K) (hι : ∀ k, Matrix.GeneralLinearGroup.det (ι k) = 1)
    (ρ : Representation ℂ H W) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : f ∈ typeSubmodule ι ρ) :
    fnTwist K η f ∈ typeSubmodule ι ρ := by
  have hchi : ∀ (x : AdelicGL2 (𝓞 K) K) (k : H), chiDet (𝓞 K) K η (x * ι k) = chiDet (𝓞 K) K η x := by
    intro x k
    rw [chiDet_mul]; unfold chiDet; rw [hι k, map_one, Units.val_one, mul_one]
  refine Submodule.span_induction (p := fun f _ => fnTwist K η f ∈ typeSubmodule ι ρ) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : IsRightEquivariant ι ρ (mulChiOn η id ∘ₗ T) := by
      intro k' v' x
      show chiDet (𝓞 K) K η x * T (ρ k' v') x = chiDet (𝓞 K) K η (x * ι k') * T v' (x * ι k')
      rw [hT k' v' x, hchi]
    exact mem_typeSubmodule_of_isRightEquivariant hS v
  · show fnTwist K η 0 ∈ _
    rw [show (0 : AdelicGL2 (𝓞 K) K → ℂ) = fun _ => 0 from rfl, fnTwist_zero]; exact (typeSubmodule ι ρ).zero_mem
  · intro f g _ _ hu hw
    have : fnTwist K η (f + g) = fnTwist K η f + fnTwist K η g := by
      funext x; simp [fnTwist_apply, mul_add]
    rw [this]; exact (typeSubmodule ι ρ).add_mem hu hw
  · intro c f _ hu
    have : fnTwist K η (c • f) = c • fnTwist K η f := by
      funext x; simp [fnTwist_apply]; ring
    rw [this]; exact (typeSubmodule ι ρ).smul_mem c hu

omit [NumberField K] in
theorem det_apply_infinitePlace (M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (w' : InfinitePlace K) :
    M.det w' = (M.map (fun x : InfiniteAdeleRing K => x w')).det :=
  RingHom.map_det (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w') M

theorem det_rowIsometryInclAt₀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ K w k) = 1 := by
  have hk : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((AutomorphicForm.mem_rowIsometrySubgroup₀_iff (K := w.Completion)).mp k.2).1
  have h1 : glArch (𝓞 K) K (rowIsometryInclAt₀ K w k) = archGLIncl K w (k : GL (Fin 2) w.Completion) := by
    rw [rowIsometryInclAt₀_apply, show adelicArchGLInclAt K w = (adelicArchGLIncl K).comp (archGLIncl K w) from rfl,
      MonoidHom.comp_apply, glArch_adelicArchGLIncl]
  have h2 : glFin (𝓞 K) K (rowIsometryInclAt₀ K w k) = 1 := by
    rw [rowIsometryInclAt₀_apply, show adelicArchGLInclAt K w = (adelicArchGLIncl K).comp (archGLIncl K w) from rfl,
      MonoidHom.comp_apply, glFin_adelicArchGLIncl]
  refine Units.ext (Prod.ext ?_ ?_)
  · rw [det_fst_eq]
    refine funext fun w' => (det_apply_infinitePlace _ w').trans ?_
    have hM : ∀ x : AdelicGL2 (𝓞 K) K, ((glArch (𝓞 K) K x : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map (fun y : InfiniteAdeleRing K => y w') =
        ((archComponent K w' (glArch (𝓞 K) K x)) : Matrix (Fin 2) (Fin 2) _) :=
      fun x => Matrix.ext fun i j => by rw [Matrix.map_apply]; exact (archComponent_apply K w' _ i j).symm
    rw [hM, h1]
    show _ = (1 : w'.Completion)
    by_cases h : w' = w
    · subst h; rw [archComponent_archGLIncl_self]; exact hk
    · rw [archComponent_archGLIncl_of_ne K h]; simp
  · rw [det_snd_eq, h2]
    simp; rfl

theorem fnTwist_mem_archCutSubmodule (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (tys : ArchTypeFamily K)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : f ∈ archCutSubmodule K tys) : fnTwist K η f ∈ archCutSubmodule K tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _ (motive := fun f => fnTwist K η f ∈
      ⨆ i : Fin (tys.card w), archTypeSubmoduleAt K w (tys.rep w i)) (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archTypeSubmoduleAt K w (tys.rep w j)) i
      (fnTwist_mem_typeSubmodule η _ (det_rowIsometryInclAt₀ w) _ hfi)
  · show fnTwist K η (fun _ => 0) ∈ _
    rw [fnTwist_zero]; exact Submodule.zero_mem _
  · intro f g hu hw
    have : fnTwist K η (f + g) = fnTwist K η f + fnTwist K η g := by
      funext x; simp [fnTwist_apply, mul_add]
    rw [this]; exact Submodule.add_mem _ hu hw

theorem continuous_chiDet (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hηc : Continuous η) :
    Continuous (chiDet (𝓞 K) K η) := by
  unfold chiDet
  exact Units.continuous_val.comp (hηc.comp (Matrix.GeneralLinearGroup.continuous_det))

theorem continuous_fnTwist_family (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hηc : Continuous η)
    {φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ} (h : Continuous fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2) :
    Continuous fun p : ℂ × AdelicGL2 (𝓞 K) K => fnTwist K η (φ p.1) p.2 :=
  ((continuous_chiDet η hηc).comp continuous_snd).mul h

theorem continuousOn_fnTwist_family (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hηc : Continuous η)
    {E : ℂ → AdelicGL2 (𝓞 K) K → ℂ} {S : Set (ℂ × AdelicGL2 (𝓞 K) K)}
    (h : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E p.1 p.2) S) :
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => fnTwist K η (E p.1) p.2) S :=
  ((continuous_chiDet η hηc).comp continuous_snd).continuousOn.mul h

theorem differentiable_fnTwist_family (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    {φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ} (g : AdelicGL2 (𝓞 K) K) (h : Differentiable ℂ fun s => φ s g) :
    Differentiable ℂ fun s => fnTwist K η (φ s) g :=
  (differentiable_const _).mul h

theorem analyticOnNhd_fnTwist_family (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    {E : ℂ → AdelicGL2 (𝓞 K) K → ℂ} {O : Set ℂ} (g : AdelicGL2 (𝓞 K) K) (h : AnalyticOnNhd ℂ (fun s => E s g) O) :
    AnalyticOnNhd ℂ (fun s => fnTwist K η (E s) g) O :=
  fun s hs => analyticAt_const.mul (h s hs)

theorem deriv_fnTwist_family (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (E : ℂ → AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (s : ℂ) :
    deriv (fun s => fnTwist K η (E s) g) s = chiDet (𝓞 K) K η g * deriv (fun s => E s g) s := by
  simp only [fnTwist_apply]
  exact deriv_const_mul_field _

theorem chiDet_unipotentGL2_mul (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K η (unipotentGL2 x * g) = chiDet (𝓞 K) K η g := by
  rw [chiDet_borel_mul η (unipotentGL2_mem_borelSubgroup x) g, borelDiagFst_unipotentGL2, borelDiagSnd_unipotentGL2]
  simp

theorem chiDet_weyl_unipotent_mul (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 K) K η)
    (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K η (adelicWeyl (𝓞 K) K * unipotentGL2 x * g) = chiDet (𝓞 K) K η g := by
  rw [mul_assoc, show adelicWeyl (𝓞 K) K = globalPoints (𝓞 K) K gl2Weyl from rfl,
    chiDet_globalPoints_mul K η hη, chiDet_unipotentGL2_mul]

theorem chiDet_weyl_inv_unipotent_mul (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 K) K η)
    (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K η ((adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 x * g) = chiDet (𝓞 K) K η g := by
  rw [mul_assoc, show (adelicWeyl (𝓞 K) K)⁻¹ = globalPoints (𝓞 K) K gl2Weyl⁻¹ from (map_inv _ _).symm,
    chiDet_globalPoints_mul K η hη, chiDet_unipotentGL2_mul]

theorem weylIntertwiningIntegral_fnTwist [MeasurableSpace (AdeleRing (𝓞 K) K)]
    (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 K) K η)
    (m : Measure (AdeleRing (𝓞 K) K)) (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    weylIntertwiningIntegral (𝓞 K) K m (fnTwist K η φ) g =
      chiDet (𝓞 K) K η g * weylIntertwiningIntegral (𝓞 K) K m φ g := by
  unfold weylIntertwiningIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fnTwist_apply, chiDet_weyl_inv_unipotent_mul η hη]

theorem tsum_fnTwist_weyl (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 K) K η)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    ∑' ξ : K, fnTwist K η φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g) =
      chiDet (𝓞 K) K η g * ∑' ξ : K, φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  simp only [fnTwist_apply, chiDet_weyl_unipotent_mul η hη]

theorem norm_fnTwist (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hηu : IsUnitaryChar (𝓞 K) K η)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ‖fnTwist K η φ g‖ = ‖φ g‖ := by
  rw [fnTwist_apply, norm_mul]
  unfold chiDet
  rw [hηu, one_mul]

theorem norm_chiDet (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hηu : IsUnitaryChar (𝓞 K) K η) (g : AdelicGL2 (𝓞 K) K) :
    ‖chiDet (𝓞 K) K η g‖ = 1 := hηu _

end R4ScattTw

namespace R4ScattWin

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.TateGlobal
open NumberField.AdelicVolume AutomorphicForm.WindowedSiegel Matrix
open scoped NNReal

variable {K : Type} [Field K] [NumberField K]

theorem glArch_archAt (w : InfinitePlace K) (y : GL (Fin 2) w.Completion) :
    glArch (𝓞 K) K (adelicArchGLInclAt K w y) = archGLIncl K w y := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]

theorem glFin_archAt (w : InfinitePlace K) (y : GL (Fin 2) w.Completion) :
    glFin (𝓞 K) K (adelicArchGLInclAt K w y) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

theorem archAt_fst_self (w : InfinitePlace K) (y : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt K w y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w =
      (y : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  show (archComponent K w (glArch (𝓞 K) K (adelicArchGLInclAt K w y)) : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
  rw [glArch_archAt, archComponent_archGLIncl_self]

theorem archAt_fst_of_ne {v w : InfinitePlace K} (hv : v ≠ w) (y : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt K w y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 v =
      (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  show (archComponent K v (glArch (𝓞 K) K (adelicArchGLInclAt K w y)) : Matrix (Fin 2) (Fin 2) v.Completion) i j = _
  rw [glArch_archAt, archComponent_archGLIncl_of_ne K hv, Units.val_one]

theorem archAt_snd (w : InfinitePlace K) (y : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt K w y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j := by
  show (glFin (𝓞 K) K (adelicArchGLInclAt K w y) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j = _
  rw [glFin_archAt, Units.val_one]

theorem eq_of_forall_archComponent_eq (a b : GL (Fin 2) (InfiniteAdeleRing K))
    (h : ∀ v : InfinitePlace K, archComponent K v a = archComponent K v b) : a = b := by
  apply Units.ext
  refine Matrix.ext fun i j => funext fun v => ?_
  exact congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion) i j) (h v)

theorem archAt_mul_eq_mul_archAt_conj (w : InfinitePlace K) (x : GL (Fin 2) w.Completion) (y : AdelicGL2 (𝓞 K) K) :
    adelicArchGLInclAt K w x * y =
      y * adelicArchGLInclAt K w
        ((archComponent K w (glArch (𝓞 K) K y))⁻¹ * x * archComponent K w (glArch (𝓞 K) K y)) := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, map_mul, glArch_archAt, glArch_archAt]
    apply eq_of_forall_archComponent_eq
    intro v
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self, archComponent_archGLIncl_self, ← mul_assoc, ← mul_assoc,
        mul_inv_cancel, one_mul]
    · rw [archComponent_archGLIncl_of_ne K hv, archComponent_archGLIncl_of_ne K hv, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_archAt, glFin_archAt, one_mul, mul_one]

theorem commute_archAt_of_archComponent_eq_one (w : InfinitePlace K) (x : GL (Fin 2) w.Completion)
    (y : AdelicGL2 (𝓞 K) K) (hy : archComponent K w (glArch (𝓞 K) K y) = 1) :
    Commute y (adelicArchGLInclAt K w x) := by
  have h := archAt_mul_eq_mul_archAt_conj w x y
  rw [hy, inv_one, one_mul, mul_one] at h
  exact h.symm

theorem archAt_mem_adelicBorel (w : InfinitePlace K) {b : GL (Fin 2) w.Completion}
    (hb : (b : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) :
    adelicArchGLInclAt K w b ∈ adelicBorel (𝓞 K) K := by
  show ((adelicArchGLInclAt K w b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
  refine Prod.ext (funext fun v => ?_) ?_
  · by_cases hv : v = w
    · subst hv
      rw [archAt_fst_self, hb]
      rfl
    · rw [archAt_fst_of_ne hv, Matrix.one_apply_ne (by decide)]
      rfl
  · rw [archAt_snd, Matrix.one_apply_ne (by decide)]
    rfl

theorem borelDiagFst_archAt (w : InfinitePlace K) (b : GL (Fin 2) w.Completion)
    (hmem : adelicArchGLInclAt K w b ∈ adelicBorel (𝓞 K) K) (a : (w.Completion)ˣ)
    (ha : (b : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = a) :
    borelDiagFst (⟨adelicArchGLInclAt K w b, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = archUnitHom w a := by
  apply Units.ext
  rw [borelDiagFst_apply_val, archUnitHom_apply]
  show ((adelicArchGLInclAt K w b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = _
  refine Prod.ext (funext fun v => ?_) ?_
  · by_cases hv : v = w
    · subst hv
      rw [archAt_fst_self, archCentralUnit_fst_self, ha]
    · rw [archAt_fst_of_ne hv, archCentralUnit_fst_of_ne _ _ hv, Matrix.one_apply_eq]
  · rw [archAt_snd, archCentralUnit_snd, Matrix.one_apply_eq]

theorem borelDiagSnd_archAt (w : InfinitePlace K) (b : GL (Fin 2) w.Completion)
    (hmem : adelicArchGLInclAt K w b ∈ adelicBorel (𝓞 K) K) (d : (w.Completion)ˣ)
    (hd : (b : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = d) :
    borelDiagSnd (⟨adelicArchGLInclAt K w b, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = archUnitHom w d := by
  apply Units.ext
  rw [borelDiagSnd_apply_val, archUnitHom_apply]
  show ((adelicArchGLInclAt K w b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = _
  refine Prod.ext (funext fun v => ?_) ?_
  · by_cases hv : v = w
    · subst hv
      rw [archAt_fst_self, archCentralUnit_fst_self, hd]
    · rw [archAt_fst_of_ne hv, archCentralUnit_fst_of_ne _ _ hv, Matrix.one_apply_eq]
  · rw [archAt_snd, archCentralUnit_snd, Matrix.one_apply_eq]

theorem induced_archAt {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {F : AdelicGL2 (𝓞 K) K → ℂ}
    (hF : IsInducedSection (𝓞 K) K χ₁ χ₂ F) (w : InfinitePlace K) (b : GL (Fin 2) w.Completion)
    (hb : (b : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) (a d : (w.Completion)ˣ)
    (ha : (b : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = a) (hd : (b : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = d)
    (g : AdelicGL2 (𝓞 K) K) :
    F (adelicArchGLInclAt K w b * g) =
      ((χ₁ (archUnitHom w a) : ℂˣ) : ℂ) * ((χ₂ (archUnitHom w d) : ℂˣ) : ℂ) * F g := by
  have hmem := archAt_mem_adelicBorel (K := K) w hb
  rw [hF _ hmem g, borelDiagFst_archAt w b hmem a ha, borelDiagSnd_archAt w b hmem d hd]

private theorem _root_.R4ScattWin.ideleNorm_archUnitHom (v : InfinitePlace K) (x : (v.Completion)ˣ) :
    ideleNorm K (archUnitHom v x) = ‖(x : v.Completion)‖ ^ v.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _
      (by rw [archUnitHom_apply]; exact archCentralUnit_snd v x),
    Finset.prod_eq_single v]
  · rw [archUnitHom_apply, archCentralUnit_fst_self]
  · intro w _ hw
    rw [archUnitHom_apply, archCentralUnit_fst_of_ne _ _ hw, norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ v) h

p2m_export "R4ScattWin" "ideleNorm_archUnitHom"

section Scalar

variable {L : Type*} [NormedField L]

def scalarGL (z : Lˣ) : GL (Fin 2) L := Units.map (Matrix.scalar (Fin 2) : L →+* Matrix (Fin 2) (Fin 2) L).toMonoidHom z

theorem scalarGL_apply (z : Lˣ) (i j : Fin 2) :
    ((scalarGL z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = if i = j then (z : L) else 0 := by
  show (Matrix.scalar (Fin 2) (z : L)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem scalarGL_commute (z : Lˣ) (M : GL (Fin 2) L) : Commute (scalarGL z) M := by
  rw [Commute, SemiconjBy, ← Units.val_inj, Units.val_mul, Units.val_mul]
  exact Matrix.scalar_commute (z : L) (fun r' => mul_comm _ _) _

theorem isRowIsometry_scalarGL {z : Lˣ} (hz : ‖(z : L)‖ = 1) : IsRowIsometry (scalarGL z) := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [Matrix.det_fin_two, scalarGL_apply, scalarGL_apply, scalarGL_apply, scalarGL_apply]
    simp [hz]
  · rw [scalarGL_apply, scalarGL_apply, scalarGL_apply, scalarGL_apply]
    simp [norm_mul, hz]

theorem det_scalarGL (z : Lˣ) :
    ((scalarGL z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = (z : L) ^ 2 := by
  rw [Matrix.det_fin_two, scalarGL_apply, scalarGL_apply, scalarGL_apply, scalarGL_apply]
  simp; ring

end Scalar

section Complex

variable {w : InfinitePlace K} (hw : w.IsComplex)

theorem norm_ringEquiv (x : w.Completion) : ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ := by
  rw [ringEquivComplexOfIsComplex_apply]
  exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem extensionEmbedding_symm (r : ℂ) :
    extensionEmbedding w ((ringEquivComplexOfIsComplex hw).symm r) = r := by
  rw [← ringEquivComplexOfIsComplex_apply hw, RingEquiv.apply_symm_apply]

theorem norm_symm (r : ℂ) : ‖(ringEquivComplexOfIsComplex hw).symm r‖ = ‖r‖ := by
  rw [← norm_ringEquiv hw, RingEquiv.apply_symm_apply]

include hw in

theorem exists_sq_eq_det {κ : GL (Fin 2) w.Completion} (hκ : IsRowIsometry κ) :
    ∃ z : (w.Completion)ˣ, ‖(z : w.Completion)‖ = 1 ∧
      (z : w.Completion) ^ 2 = ((κ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) _).det := by
  set c : ℂ := ringEquivComplexOfIsComplex hw ((κ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) _).det with hc
  have hc1 : ‖c‖ = 1 := by rw [hc, norm_ringEquiv]; exact hκ.1
  set d : ℂ := c ^ ((2 : ℕ)⁻¹ : ℂ) with hd
  have hd2 : d ^ 2 = c := Complex.cpow_nat_inv_pow c two_ne_zero
  have hd1 : ‖d‖ = 1 := by
    have : ‖d‖ ^ 2 = 1 := by rw [← norm_pow, hd2, hc1]
    nlinarith [norm_nonneg d]
  have hd0 : (ringEquivComplexOfIsComplex hw).symm d ≠ 0 := by
    intro h; have := congrArg (‖·‖) h; simp only [norm_symm, hd1, norm_zero] at this; exact one_ne_zero this
  refine ⟨Units.mk0 _ hd0, ?_, ?_⟩
  · rw [Units.val_mk0, norm_symm, hd1]
  · rw [Units.val_mk0, ← map_pow, hd2, hc, RingEquiv.symm_apply_apply]

include hw in

theorem exists_scalar_mul_eq {κ : GL (Fin 2) w.Completion} (hκ : IsRowIsometry κ) :
    ∃ (z : (w.Completion)ˣ) (s : rowIsometrySubgroup₀ w.Completion), ‖(z : w.Completion)‖ = 1 ∧
      scalarGL z * (s : GL (Fin 2) w.Completion) = κ := by
  obtain ⟨z, hz1, hz2⟩ := exists_sq_eq_det hw hκ
  have hs : (scalarGL z)⁻¹ * κ ∈ rowIsometrySubgroup₀ w.Completion := by
    rw [AutomorphicForm.mem_rowIsometrySubgroup₀_iff]
    refine ⟨?_, (isRowIsometry_scalarGL hz1).inv.mul hκ⟩
    rw [Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv, Matrix.det_nonsing_inv, det_scalarGL, ← hz2,
      Ring.inverse_mul_cancel]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (Units.ne_zero z))
  exact ⟨z, ⟨_, hs⟩, hz1, mul_inv_cancel_left _ _⟩

end Complex

theorem comp_mul_mem_iSup {ι : Type*} (T : ι → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (a : AdelicGL2 (𝓞 K) K)
    (ha : ∀ i (f : AdelicGL2 (𝓞 K) K → ℂ), f ∈ T i → (fun x => f (x * a)) ∈ T i)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : f ∈ ⨆ i, T i) : (fun x => f (x * a)) ∈ ⨆ i, T i := by
  refine Submodule.iSup_induction _ (motive := fun f => (fun x => f (x * a)) ∈ ⨆ i, T i) hf ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup T i (ha i f hfi)
  · exact Submodule.zero_mem _
  · intro f g hu hv
    exact Submodule.add_mem _ hu hv

theorem exists_forall_abs_sub_le (K : Type) [Field K] [NumberField K] (tys : ArchTypeFamily K) :
    ∃ n₀ : ℕ, ∀ (w : InfinitePlace K) (hw : w.IsComplex) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (φ : AdelicGL2 (𝓞 K) K → ℂ), IsInducedSection (𝓞 K) K χ₁ χ₂ φ → Continuous φ →
      φ ∈ archCutSubmodule K tys → φ ≠ 0 →
      ∀ (m₁ m₂ : ℤ),
      (∀ x : (w.Completion)ˣ, ‖extensionEmbedding w (x : w.Completion)‖ = 1 →
        ((χ₁ (archUnitHom w x) : ℂˣ) : ℂ) = (extensionEmbedding w (x : w.Completion)) ^ m₁) →
      (∀ x : (w.Completion)ˣ, ‖extensionEmbedding w (x : w.Completion)‖ = 1 →
        ((χ₂ (archUnitHom w x) : ℂˣ) : ℂ) = (extensionEmbedding w (x : w.Completion)) ^ m₂) →
      |m₁ - m₂| ≤ (n₀ : ℤ) := by
  obtain ⟨n₀, hn₀⟩ :=
    AutomorphicForm.exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt K tys
  refine ⟨n₀, fun w hw χ₁ χ₂ φ hφ hφc hφty hφ0 m₁ m₂ h₁ h₂ => ?_⟩

  obtain ⟨g, hg⟩ := Function.ne_iff.mp hφ0
  obtain ⟨b, k, hb, -, hka, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
  have hk0 : φ k ≠ 0 := by
    intro h; apply hg; rw [hφ b hb k, h, mul_zero]; rfl

  set κ : GL (Fin 2) w.Completion := archComponent K w (glArch (𝓞 K) K k) with hκ
  obtain ⟨z, s, hz1, hzs⟩ := exists_scalar_mul_eq hw (hka w)
  set y : AdelicGL2 (𝓞 K) K := k * (adelicArchGLInclAt K w κ)⁻¹ with hy
  have hy1 : archComponent K w (glArch (𝓞 K) K y) = 1 := by
    rw [hy, map_mul, map_inv, map_mul, map_inv, glArch_archAt, archComponent_archGLIncl_self, mul_inv_cancel]
  have hkdec : k = y * adelicArchGLInclAt K w (scalarGL z) * rowIsometryInclAt₀ K w s := by
    rw [rowIsometryInclAt₀_apply, hy, mul_assoc, mul_assoc, ← map_mul, ← map_inv, ← map_mul, hzs, inv_mul_cancel,
      map_one, mul_one]

  set T : Fin (tys.card w) → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := fun i => archTypeSubmoduleAt K w (tys.rep w i)
    with hT
  have hφw : φ ∈ ⨆ i, T i := (mem_archCutSubmodule_iff K tys φ).mp hφty w
  have hs' : (fun x => φ (x * rowIsometryInclAt₀ K w s)) ∈ ⨆ i, T i :=
    comp_mul_mem_iSup T _ (fun i f hf => comp_mul_mem_typeSubmodule hf s) hφw
  have hz' : (fun x => φ (x * adelicArchGLInclAt K w (scalarGL z) * rowIsometryInclAt₀ K w s)) ∈ ⨆ i, T i := by
    refine comp_mul_mem_iSup T (adelicArchGLInclAt K w (scalarGL z)) (fun i f hf => ?_) hs'
    refine comp_mul_mem_typeSubmodule_of_commute hf _ fun k' => ?_
    rw [rowIsometryInclAt₀_apply]
    exact (scalarGL_commute z (k' : GL (Fin 2) w.Completion)).map (adelicArchGLInclAt K w)
  have hy' : (fun x => φ (x * y * adelicArchGLInclAt K w (scalarGL z) * rowIsometryInclAt₀ K w s)) ∈ ⨆ i, T i := by
    refine comp_mul_mem_iSup T y (fun i f hf => ?_) hz'
    refine comp_mul_mem_typeSubmodule_of_commute hf _ fun k' => ?_
    rw [rowIsometryInclAt₀_apply]
    exact commute_archAt_of_archComponent_eq_one w _ y hy1
  set f : AdelicGL2 (𝓞 K) K → ℂ := fun x => φ (x * k) with hf
  have hfeq : f = fun x => φ (x * y * adelicArchGLInclAt K w (scalarGL z) * rowIsometryInclAt₀ K w s) := by
    funext x; simp only [hf, hkdec, mul_assoc]
  have hfmem : f ∈ ⨆ i, T i := hfeq ▸ hy'
  have hfc : Continuous f := hφc.comp (continuous_mul_const k)
  have hf1 : f 1 ≠ 0 := by rw [hf]; simpa using hk0

  set e := ringEquivComplexOfIsComplex hw with he
  have hcirc : ∀ ζ : ℂˣ, ‖(ζ : ℂ)‖ = 1 → f (1 * archCircleAt hw ζ) = (ζ : ℂ) ^ (m₁ - m₂) * f 1 := by
    intro ζ hζ
    have hζ0 : (ζ : ℂ) ≠ 0 := Units.ne_zero ζ
    set a : (w.Completion)ˣ := Units.map e.symm.toRingHom.toMonoidHom ζ with ha
    have hav : (a : w.Completion) = e.symm ζ := rfl
    have hainv : ((a⁻¹ : (w.Completion)ˣ) : w.Completion) = e.symm ((ζ⁻¹ : ℂˣ) : ℂ) := by
      rw [ha, ← map_inv]; rfl
    have hea : extensionEmbedding w (a : w.Completion) = ζ := by rw [hav, he, extensionEmbedding_symm]
    have heainv : extensionEmbedding w ((a⁻¹ : (w.Completion)ˣ) : w.Completion) = ((ζ⁻¹ : ℂˣ) : ℂ) := by
      rw [hainv, he, extensionEmbedding_symm]
    have hcirc_eq : archCircleAt hw ζ = adelicArchGLInclAt K w (glEquivOfRingEquiv e.symm (circleGL2 ζ)) := rfl
    have hb10 : ((glEquivOfRingEquiv e.symm (circleGL2 ζ) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
      rw [glEquivOfRingEquiv_apply_entry]; simp [circleGL2]
    have hb00 : ((glEquivOfRingEquiv e.symm (circleGL2 ζ) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = a := by
      rw [glEquivOfRingEquiv_apply_entry, hav]; simp [circleGL2]
    have hb11 : ((glEquivOfRingEquiv e.symm (circleGL2 ζ) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = ((a⁻¹ : (w.Completion)ˣ) : w.Completion) := by
      rw [glEquivOfRingEquiv_apply_entry, hainv]; simp [circleGL2]
    have hχ₁ : ((χ₁ (archUnitHom w a) : ℂˣ) : ℂ) = (ζ : ℂ) ^ m₁ := by
      rw [h₁ a (by rw [hea]; exact hζ), hea]
    have hχ₂ : ((χ₂ (archUnitHom w a⁻¹) : ℂˣ) : ℂ) = (ζ : ℂ) ^ (-m₂) := by
      rw [h₂ a⁻¹ (by rw [heainv, Units.val_inv_eq_inv_val, norm_inv, hζ, inv_one]), heainv,
        Units.val_inv_eq_inv_val, _root_.inv_zpow']
    rw [one_mul, hf]
    simp only []
    rw [hcirc_eq, induced_archAt hφ w _ hb10 a a⁻¹ hb00 hb11 k, hχ₁, hχ₂, one_mul, ← zpow_add₀ hζ0, sub_eq_add_neg]
  exact hn₀ w hw f hfc hfmem 1 (m₁ - m₂) hcirc hf1

end R4ScattWin

namespace R4ScattMain

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open Set
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable {K : Type} [Field K] [NumberField K]

theorem integral_norm_sq_eq_of {X : Type*} [MeasurableSpace X] {m : Measure X} {f : X → ℂ} {P : ℝ}
    (hf : ∫ k, f k * conj (f k) ∂m = (P : ℂ)) : ∫ k, ‖f k‖ ^ 2 ∂m = P := by
  have h : ∀ k, f k * conj (f k) = ((‖f k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [h] at hf
  have h2 : ∫ k, ((‖f k‖ ^ 2 : ℝ) : ℂ) ∂m = ((∫ k, ‖f k‖ ^ 2 ∂m : ℝ) : ℂ) := integral_ofReal
  rw [h2] at hf
  exact_mod_cast hf

theorem isUnitaryChar_mul {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 K) K μ)
    (hν : IsUnitaryChar (𝓞 K) K ν) : IsUnitaryChar (𝓞 K) K (μ * ν) := fun x => by
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ, hν, one_mul]

theorem isIdeleClassChar_mul {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hμ : IsIdeleClassChar (𝓞 K) K μ)
    (hν : IsIdeleClassChar (𝓞 K) K ν) : IsIdeleClassChar (𝓞 K) K (μ * ν) := fun u => by
  rw [MonoidHom.mul_apply, hμ, hν, one_mul]

theorem continuous_coe_mul {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hμ : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
    (hν : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((μ * ν) z : ℂˣ) : ℂ) := by
  simp only [MonoidHom.mul_apply, Units.val_mul]; exact hμ.mul hν

theorem continuous_coe_of_continuous {η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hη : Continuous η) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((η z : ℂˣ) : ℂ) :=
  Units.continuous_val.comp hη

theorem archParam_mul {μ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {τμ τη : InfinitePlace K → ℝ}
    (hμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τμ v : ℝ) : ℂ) * Complex.I))
    (hη : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar η v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τη v : ℝ) : ℂ) * Complex.I)) :
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (μ * η) v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ ((((fun v => τμ v + τη v) v : ℝ) : ℂ) * Complex.I) := by
  intro v x h1 h2
  have h0 : (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ideleNorm_pos _).ne'
  rw [show archLocalChar (μ * η) v x = archLocalChar μ v x * archLocalChar η v x from rfl, Units.val_mul,
    hμ v x h1 h2, hη v x h1 h2, ← Complex.cpow_add _ _ h0]
  congr 1; push_cast; ring

theorem archWeight_mul {μ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {mμ mη : InfinitePlace K → ℤ}
    (hμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (mμ v))
    (hη : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar η v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (mη v)) :
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar (μ * η) v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ ((fun v => mμ v + mη v) v) := by
  intro v x h1
  have h0 : extensionEmbedding v (x : v.Completion) ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
  rw [show archLocalChar (μ * η) v x = archLocalChar μ v x * archLocalChar η v x from rfl, Units.val_mul,
    hμ v x h1, hη v x h1, ← zpow_add₀ h0]

theorem abs_two_mul_add_le {t t' τ δ : ℝ} (hτ : τ ∈ uIcc t t') :
    |2 * τ + δ| ≤ |2 * t + δ| + |2 * t' + δ| := by
  rcases mem_uIcc.mp hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · calc |2 * τ + δ| ≤ max |2 * t + δ| |2 * t' + δ| := abs_le_max_abs_abs (by linarith) (by linarith)
      _ ≤ |2 * t + δ| + |2 * t' + δ| := max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _)
  · calc |2 * τ + δ| ≤ max |2 * t' + δ| |2 * t + δ| := abs_le_max_abs_abs (by linarith) (by linarith)
      _ ≤ |2 * t + δ| + |2 * t' + δ| := by
        rw [max_comm]; exact max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _)

theorem norm_two_mul_I_add_ofReal_mul_I (t δ : ℝ) :
    ‖2 * (t : ℂ) * Complex.I + ((δ : ℝ) : ℂ) * Complex.I‖ = |2 * t + δ| := by
  rw [show 2 * (t : ℂ) * Complex.I + ((δ : ℝ) : ℂ) * Complex.I = ((2 * t + δ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem main (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (tysF : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type)
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (v : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysF)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (uμ uν : ιE → InfinitePlace K → ℂ) (aμ aν : ιE → InfinitePlace K → ℤ)
      (_hμA : ∀ (e : ιE) (v : InfinitePlace K), LanglandsTunnell.Converse.IsArchCompAt K (μ e) v (uμ e v) (aμ e v))
      (_hνA : ∀ (e : ιE) (v : InfinitePlace K), LanglandsTunnell.Converse.IsArchCompAt K (ν e) v (uν e v) (aν e v))
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g)),
    ∃ A : ℕ, ∃ d : ℝ, 0 ≤ d ∧ ∀ (e : ιE) (j : Fin (nE e)) (t t' : ℝ),
      (∫ k, ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
            deriv (fun s : ℂ => NE e j s (k : AdelicGL2 (𝓞 K) K)) ((t : ℂ) * Complex.I)‖ ^ 2
          ∂(maximalCompactHaar K)) ≤
        (d * (1 + ∑ v : InfinitePlace K, ‖2 * (t : ℂ) * Complex.I + (uμ e v - uν e v)‖) ^ A) ^ 2 ∧
      (∫ k, ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) -
            ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ^ 2
          ∂(maximalCompactHaar K)) ≤
        (d * ((1 + ∑ v : InfinitePlace K, ‖2 * (t : ℂ) * Complex.I + (uμ e v - uν e v)‖) +
              (1 + ∑ v : InfinitePlace K, ‖2 * (t' : ℂ) * Complex.I + (uμ e v - uν e v)‖)) ^ A * |t - t'|) ^ 2 := by
  intro αm hαm ιE μ ν hμ hν hμic hνic hμc hνc nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon
    uμ uν aμ aν hμA hνA OE EE NE hEE
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  letI mU : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K)ˣ := ⟨rfl⟩
  have hαn : ∀ x, ((αm x : ℝˣ) : ℝ) = ideleNorm K x := fun x => rfl

  set S₀ : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors _hN).toFinset with hS₀def
  have hS₀ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S₀ := fun v hv => by
    rw [hS₀def, Set.Finite.mem_toFinset]; exact hv

  obtain ⟨nρ, ρs, hρs⟩ :=
    AutomorphicForm.exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
      K S₀ N hS₀

  obtain ⟨n₀, hn₀⟩ := R4ScattWin.exists_forall_abs_sub_le K tysF

  obtain ⟨B, Ξ, hB0, hΞfin, hΞprop, hTN⟩ :=
    NumberField.TateGlobal.exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq
      K S₀ nρ ρs n₀
  haveI : Fintype ↥Ξ := hΞfin.fintype

  let ξK : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) :=
    fun ξ => ξ.comp (Subgroup.subtype ⊤)
  have hξKt : ∀ ξ₀ : ↥Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ξ₀.1 ⟨z, Subgroup.mem_top z⟩ = 1 := by
    rintro ξ₀ _ ⟨u, rfl⟩
    exact (hΞprop _ ξ₀.2).2.1 u
  have hξKw : ∀ ξ₀ : ↥Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ξ₀.1 ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((ideleNorm K z) ^ (0 : ℝ) : ℝ) := by
    intro ξ₀ z
    rw [Real.rpow_zero]
    exact (hΞprop _ ξ₀.2).1 z
  have h247 := fun ξ₀ : ↥Ξ =>
    AutomorphicForm.exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight
      K S₀ (ξK ξ₀.1) (hΞprop _ ξ₀.2).2.2 (hξKt ξ₀) N hS₀ tysF 0 (hξKw ξ₀)
  choose Cof Aof hCpos hgrow using h247
  set Amax : ℕ := ∑ ξ₀ : ↥Ξ, Aof ξ₀ with hAmax
  set Cmax : ℝ := ∑ ξ₀ : ↥Ξ, Cof ξ₀ with hCmax
  have hAle : ∀ ξ₀ : ↥Ξ, Aof ξ₀ ≤ Amax := fun ξ₀ =>
    Finset.single_le_sum (f := Aof) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ξ₀)
  have hCle : ∀ ξ₀ : ↥Ξ, Cof ξ₀ ≤ Cmax := fun ξ₀ =>
    Finset.single_le_sum (f := Cof) (fun ξ _ => (hCpos ξ).le) (Finset.mem_univ ξ₀)
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun ξ _ => (hCpos ξ).le
  set d : ℝ := Cmax * B ^ Amax with hd
  have hd0 : 0 ≤ d := mul_nonneg hCmax0 (pow_nonneg hB0 _)
  refine ⟨Amax, d, hd0, fun e j t₁ t₂ => ?_⟩

  set φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ := φE e j with hφdef
  have hφc0 : Continuous (φ 0) := (hφEjc e j).comp (Continuous.prodMk_right (0 : ℂ))
  have hP : ∫ k, ‖φ 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by
    have h := hφEon e j j
    rw [if_pos rfl] at h
    exact integral_norm_sq_eq_of (by exact_mod_cast h)
  have hφ0 : φ 0 ≠ 0 := by
    intro h
    have : ∫ k, ‖φ 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 0 := by
      simp [h]
    rw [this] at hP; exact zero_ne_one hP

  obtain ⟨τμ, mμ, hτμ, hmμ, hrμ⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (μ e) (hμ e) (hμc e)
  obtain ⟨τν, mν, hτν, hmν, hrν⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (ν e) (hν e) (hνc e)

  have huμ : ∀ v, uμ e v = (τμ v : ℂ) * Complex.I := fun v => R4ScattPar.u_eq_of_isArchCompAt (hμA e v) (hτμ v)
  have huν : ∀ v, uν e v = (τν v : ℂ) * Complex.I := fun v => R4ScattPar.u_eq_of_isArchCompAt (hνA e v) (hτν v)
  set Λ : ℝ → ℝ := fun t => 1 + ∑ v : InfinitePlace K, ‖2 * (t : ℂ) * Complex.I + (uμ e v - uν e v)‖ with hΛ
  have hΛeq : ∀ t, Λ t = 1 + ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)| := by
    intro t
    simp only [hΛ]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [huμ, huν, ← sub_mul, ← Complex.ofReal_sub, norm_two_mul_I_add_ofReal_mul_I]
  have hΛ1 : ∀ t, 1 ≤ Λ t := fun t => by
    rw [hΛeq]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => abs_nonneg _)

  have hdiff : ∀ v : InfinitePlace K, v.IsComplex → |mμ v - mν v| ≤ (n₀ : ℤ) := by
    intro v hv
    refine hn₀ v hv (etaFst (μ e) αm hαm 0) (etaSnd (ν e) αm hαm 0) (φ 0) (hφE e j 0) hφc0 (hφEty e j 0) hφ0
      (mμ v) (mν v) (fun x hx => ?_) (fun x hx => ?_)
    · have h1 : ((αm (archUnitHom v x) : ℝˣ) : ℝ) = 1 := by
        rw [hαn, R4ScattPar.ideleNorm_archUnitHom, ← R4ScattPar.norm_extensionEmbedding, hx, one_pow]
      rw [etaFst_apply, Units.val_mul, cpowChar_apply_val, h1, Complex.ofReal_one, Complex.one_cpow, mul_one]
      exact hmμ v x hx
    · have h1 : ((αm (archUnitHom v x) : ℝˣ) : ℝ) = 1 := by
        rw [hαn, R4ScattPar.ideleNorm_archUnitHom, ← R4ScattPar.norm_extensionEmbedding, hx, one_pow]
      rw [etaSnd_apply, Units.val_mul, cpowChar_apply_val, h1, Complex.ofReal_one, Complex.one_cpow, mul_one]
      exact hmν v x hx

  obtain ⟨hunr, r, r', hρ⟩ := hρs hαm (μ e) (ν e) 0 (φ 0) (hφE e j 0) hφ0 (hφElev e j 0)

  obtain ⟨η, τη, mη, hηu, hηic, hηc, hηunr, hτη, hmη, hηreal, hΞmem, -, -, hgauge⟩ :=
    hTN (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) hunr ⟨r, r', hρ⟩ τμ τν hτμ hτν mμ mν hmμ hmν
      (fun v hv => ⟨hrμ v hv, hrν v hv⟩) hdiff
  set ξ₀ : ↥Ξ := ⟨μ e * ν e * η ^ 2, hΞmem⟩ with hξ₀
  have hηc' : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((η z : ℂˣ) : ℂ) := continuous_coe_of_continuous hηc

  set ψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s => fnTwist K η (φ s) with hψ
  set E' : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s => fnTwist K η (EE e j s) with hE'
  set N' : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s => fnTwist K η (NE e j s) with hN'
  obtain ⟨hO, hOpc, hOax, hOhp, hEa, hNa, hEc, hNc, hEeq, hNeq⟩ := hEE e j
  have hgrow_e := hgrow ξ₀ hαm (μ e * η) (ν e * η) (isUnitaryChar_mul (hμ e) hηu) (isUnitaryChar_mul (hν e) hηu)
    (isIdeleClassChar_mul (hμic e) hηic) (isIdeleClassChar_mul (hνic e) hηic)
    (continuous_coe_mul (hμc e) hηc') (continuous_coe_mul (hνc e) hηc')
    (fun z => by
      rw [Real.rpow_zero, Complex.ofReal_one, mul_one]
      show ((((μ e * η) z : ℂˣ)) : ℂ) * (((ν e * η) z : ℂˣ) : ℂ) = (((μ e * ν e * η ^ 2) z : ℂˣ) : ℂ)
      simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]; ring)
    (fun v => τμ v + τη v) (fun v => τν v + τη v) (archParam_mul hτμ hτη) (archParam_mul hτν hτη)
    (fun v => mμ v + mη v) (fun v => mν v + mη v) (archWeight_mul hmμ hmη) (archWeight_mul hmν hmη)
    ψ
    (fun s => by rw [hψ, R4ScattTw.etaFst_mul, R4ScattTw.etaSnd_mul]; exact R4ScattTw.isInducedSection_fnTwist η (hφE e j s))
    (fun s => R4ScattTw.isArchKFinite_fnTwist η (hφEK e j s))
    (fun s => R4ScattTw.isKfSmooth_fnTwist' η hηc hηunr (hφEf e j s))
    (R4ScattTw.continuous_fnTwist_family η hηc (hφEjc e j))
    (fun g => R4ScattTw.differentiable_fnTwist_family η g (hφEhol e j g))
    (fun v => R4ScattTw.fnTwist_Ku η φ v (hφEKu e j v))
    (fun s k => by simp only [hψ, fnTwist_apply, hφdef, hφEflat e j s k])
    (fun s g u hu => R4ScattTw.fnTwist_level η hηc hηunr (hφElev e j s) g u hu)
    (fun s => R4ScattTw.fnTwist_mem_archCutSubmodule η tysF (hφEty e j s))
    (by
      have : ∀ k : adelicMaximalCompact K, ‖ψ 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 = ‖φ 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 :=
        fun k => by rw [hψ, R4ScattTw.norm_fnTwist η hηu]
      simp_rw [this]; exact hP.le)
    (OE e j) E' N'
    ⟨hO, hOpc, hOax, hOhp,
      fun g => R4ScattTw.analyticOnNhd_fnTwist_family η g (hEa g),
      fun g => R4ScattTw.analyticOnNhd_fnTwist_family η g (hNa g),
      R4ScattTw.continuousOn_fnTwist_family η hηc hEc,
      R4ScattTw.continuousOn_fnTwist_family η hηc hNc,
      fun s hs g => by
        rw [hE', hψ]
        simp only []
        rw [R4ScattTw.tsum_fnTwist_weyl η hηic, fnTwist_apply, fnTwist_apply, hEeq s hs g, mul_add],
      fun s hs g => by
        rw [hN', hψ]
        simp only []
        rw [R4ScattTw.weylIntertwiningIntegral_fnTwist η hηic, fnTwist_apply, hNeq s hs g]⟩

  set cK : ℂ := ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ with hcK
  set D : ℝ → ℝ := fun y => ∑ v : InfinitePlace K,
      (|y + (τμ v + τη v)| + |y - (τν v + τη v)| + |((mμ v + mη v : ℤ) : ℝ)| + |((mν v + mη v : ℤ) : ℝ)|) with hD
  have hD0 : ∀ y, 0 ≤ D y := fun y => Finset.sum_nonneg fun v _ => by positivity
  have hDΛ : ∀ y : ℝ, 1 + D y ≤ B * Λ y := fun y => by
    rw [hΛeq]
    have h := hgauge y
    simp only [hD]
    push_cast at h ⊢
    exact h
  have hcl1 : ∀ τ : ℝ,
      (∫ k, ‖cK * deriv (fun s : ℂ => NE e j s (k : AdelicGL2 (𝓞 K) K)) ((τ : ℂ) * Complex.I)‖ ^ 2
          ∂(maximalCompactHaar K)) ≤ (d * Λ τ ^ Amax) ^ 2 := by
    intro τ
    have h1 := hgrow_e τ
    have hint : (∫ k, ‖cK * deriv (fun s : ℂ => N' s (k : AdelicGL2 (𝓞 K) K)) ((τ : ℂ) * Complex.I)‖ ^ 2
          ∂(maximalCompactHaar K)) =
        ∫ k, ‖cK * deriv (fun s : ℂ => NE e j s (k : AdelicGL2 (𝓞 K) K)) ((τ : ℂ) * Complex.I)‖ ^ 2
          ∂(maximalCompactHaar K) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [hN']
      rw [R4ScattTw.deriv_fnTwist_family, mul_left_comm, norm_mul, R4ScattTw.norm_chiDet η hηu, one_mul]
    rw [hint] at h1
    refine h1.trans ?_
    change (Cof ξ₀ * (1 + D τ) ^ Aof ξ₀) ^ 2 ≤ _
    have h2 : Cof ξ₀ * (1 + D τ) ^ Aof ξ₀ ≤ d * Λ τ ^ Amax := by
      have h1D : 1 ≤ 1 + D τ := le_add_of_nonneg_right (hD0 τ)
      calc Cof ξ₀ * (1 + D τ) ^ Aof ξ₀ ≤ Cof ξ₀ * (1 + D τ) ^ Amax :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1D (hAle ξ₀)) (hCpos ξ₀).le
        _ ≤ Cmax * (B * Λ τ) ^ Amax :=
            mul_le_mul (hCle ξ₀) (pow_le_pow_left₀ (by linarith [hD0 τ]) (hDΛ τ) _) (by positivity) hCmax0
        _ = d * Λ τ ^ Amax := by rw [hd, mul_pow]; ring
    have h3 : 0 ≤ Cof ξ₀ * (1 + D τ) ^ Aof ξ₀ := mul_nonneg (hCpos ξ₀).le (pow_nonneg (by linarith [hD0 τ]) _)
    exact pow_le_pow_left₀ h3 h2 2
  refine ⟨hcl1 t₁, ?_⟩

  have hΛ0 : ∀ t, 0 ≤ Λ t := fun t => zero_le_one.trans (hΛ1 t)
  have hΛseg : ∀ τ ∈ uIcc t₁ t₂, Λ τ ≤ Λ t₁ + Λ t₂ := by
    intro τ hτ
    rw [hΛeq, hΛeq, hΛeq, add_add_add_comm, ← Finset.sum_add_distrib]
    have : ∑ v : InfinitePlace K, |2 * τ + (τμ v - τν v)| ≤
        ∑ v : InfinitePlace K, (|2 * t₁ + (τμ v - τν v)| + |2 * t₂ + (τμ v - τν v)|) :=
      Finset.sum_le_sum fun v _ => abs_two_mul_add_le hτ
    linarith
  set Nn : ℂ → adelicMaximalCompact K → ℂ := fun s k => cK * NE e j s (k : AdelicGL2 (𝓞 K) K) with hNn
  have hNna : ∀ k : adelicMaximalCompact K, AnalyticOnNhd ℂ (fun s => Nn s k) (OE e j) := fun k =>
    fun s hs => analyticAt_const.mul (hNa _ s hs)
  have hNnc : ContinuousOn (fun p : ℂ × adelicMaximalCompact K => Nn p.1 p.2) ((OE e j) ×ˢ Set.univ) := by
    have h1 : Continuous fun p : ℂ × adelicMaximalCompact K => ((p.1, (p.2 : AdelicGL2 (𝓞 K) K)) :
        ℂ × AdelicGL2 (𝓞 K) K) := by fun_prop
    have h2 : ContinuousOn (fun p : ℂ × adelicMaximalCompact K => NE e j p.1 (p.2 : AdelicGL2 (𝓞 K) K))
        ((OE e j) ×ˢ Set.univ) := hNc.comp h1.continuousOn (fun p hp => ⟨hp.1, mem_univ _⟩)
    exact continuousOn_const.mul h2
  have hderiv : ∀ (k : adelicMaximalCompact K) (τ : ℝ),
      deriv (fun s => Nn s k) ((τ : ℂ) * Complex.I) =
        cK * deriv (fun s : ℂ => NE e j s (k : AdelicGL2 (𝓞 K) K)) ((τ : ℂ) * Complex.I) := by
    intro k τ
    have hax : ((τ : ℂ) * Complex.I) ∈ OE e j := hOax (by simp)
    exact deriv_const_mul _ ((hNa _ _ hax).differentiableAt)
  have hBseg : ∀ τ ∈ Set.uIcc t₁ t₂,
      ∫ k, ‖deriv (fun s : ℂ => Nn s k) ((τ : ℂ) * Complex.I)‖ ^ 2 ∂(maximalCompactHaar K) ≤
        (d * (Λ t₁ + Λ t₂) ^ Amax) ^ 2 := by
    intro τ hτ
    simp_rw [hderiv]
    refine (hcl1 τ).trans ?_
    have h1 : d * Λ τ ^ Amax ≤ d * (Λ t₁ + Λ t₂) ^ Amax :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΛ0 τ) (hΛseg τ hτ) Amax) hd0
    exact pow_le_pow_left₀ (by have := hΛ0 τ; positivity) h1 2
  have := MeasureTheory.integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le
    (maximalCompactHaar K) (OE e j) hO hOax Nn hNna hNnc t₁ t₂ (d * (Λ t₁ + Λ t₂) ^ Amax) hBseg
  simpa only [hNn, mul_assoc d] using this

end R4ScattMain

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (N : Ideal (𝓞 F)) (_hN : N ≠ ⊥) (tysF : ArchTypeFamily F) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type)
      (μ ν : ιE → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 F) F (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν e z : ℂˣ) : ℂ))
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 F) F (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite F (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth F (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 F) F), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (v : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F v) => φE e j s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact F),
        φE e j s (k : AdelicGL2 (𝓞 F) F) = φE e j 0 (k : AdelicGL2 (𝓞 F) F))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule F tysF)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 F) F) * conj (φE e j 0 (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F) =
        if i = j then 1 else 0)
      (uμ uν : ιE → InfinitePlace F → ℂ) (aμ aν : ιE → InfinitePlace F → ℤ)
      (_hμA : ∀ (e : ιE) (v : InfinitePlace F), LanglandsTunnell.Converse.IsArchCompAt F (μ e) v (uμ e v) (aμ e v))
      (_hνA : ∀ (e : ιE) (v : InfinitePlace F), LanglandsTunnell.Converse.IsArchCompAt F (ν e) v (uν e v) (aν e v))
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        EE e j s g = φE e j s g + ∑' ξ : F, φE e j s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        NE e j s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φE e j s) g)),
    ∃ A : ℕ, ∃ d : ℝ, 0 ≤ d ∧ ∀ (e : ιE) (j : Fin (nE e)) (t t' : ℝ),
      (∫ k, ‖((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
            deriv (fun s : ℂ => NE e j s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ^ 2
          ∂(maximalCompactHaar F)) ≤
        (d * (1 + ∑ v : InfinitePlace F, ‖2 * (t : ℂ) * Complex.I + (uμ e v - uν e v)‖) ^ A) ^ 2 ∧
      (∫ k, ‖((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) -
            ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * NE e j ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ^ 2
          ∂(maximalCompactHaar F)) ≤
        (d * ((1 + ∑ v : InfinitePlace F, ‖2 * (t : ℂ) * Complex.I + (uμ e v - uν e v)‖) +
              (1 + ∑ v : InfinitePlace F, ‖2 * (t' : ℂ) * Complex.I + (uμ e v - uν e v)‖)) ^ A * |t - t'|) ^ 2 := by
  exact R4ScattMain.main F N _hN tysF

end

end S_AutomorphicForm_exists_forall_integral_maximalCompact_norm_sq_deriv_axis_continuation_weylIntertwiningIntegral_le_and_norm_sq_sub_le_of_flat_of_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integral_maximalCompact_norm_sq_deriv_axis_continuation_weylIntertwiningIntegral_le_and_norm_sq_sub_le_of_flat_of_ne_bot (solution)
