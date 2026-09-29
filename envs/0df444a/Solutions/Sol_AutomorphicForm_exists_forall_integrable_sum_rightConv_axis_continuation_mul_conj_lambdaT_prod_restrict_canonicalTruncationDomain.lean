-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integrable_sum_rightConv_axis_continuation_mul_conj_lambdaT_prod_restrict_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6fd0e2de-9c58-56fe-a3b1-604f169fd97f

import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain_of_flat
import Theorems.Thm_AutomorphicForm_forall_exists_forall_norm_lambdaT_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_neg_of_mem_canonicalTruncationDomain_of_flat
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integrable_sum_rightConv_axis_continuation_mul_conj_lambdaT_prod_restrict_canonicalTruncationDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

theorem L1B.dsum_bound {n : ℕ} (a : Fin n → Fin n → ℂ) (u v : Fin n → ℂ) (Ba Buv : ℝ)
    (ha : ∀ i j, ‖a i j‖ ≤ Ba) (huv : ∀ i j, ‖u i‖ * ‖v j‖ ≤ Buv) (hBa : 0 ≤ Ba) :
    ‖∑ i, ∑ j, a i j * (u i * conj (v j))‖ ≤ ((n : ℕ) : ℝ) ^ 2 * (Ba * Buv) := by
  calc ‖∑ i, ∑ j, a i j * (u i * conj (v j))‖
      ≤ ∑ i, ‖∑ j, a i j * (u i * conj (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖a i j * (u i * conj (v j))‖ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, Ba * Buv := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        exact mul_le_mul (ha i j) (huv i j) (by positivity) hBa
    _ = ((n : ℕ) : ℝ) ^ 2 * (Ba * Buv) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring

theorem L1B.final_bound (n A B₀ : ℕ) (Ca Kc P W S : ℝ) (hCa : 0 ≤ Ca) (hKc : 0 ≤ Kc)
    (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hS : S ≤ ((n : ℕ) : ℝ) ^ 2 * (Ca * (1 + P) ^ (-((A + B₀ : ℕ) : ℝ)) * (Kc * (1 + (P + W)) ^ A))) :
    S ≤ ((n : ℕ) : ℝ) ^ 2 * (Ca * Kc) * (1 + W) ^ A * (1 + P) ^ (-(B₀ : ℝ)) := by
  refine hS.trans ?_
  have h1P : 0 < 1 + P := by positivity
  have hPW : (1 + (P + W)) ^ A ≤ ((1 + W) * (1 + P)) ^ A :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hW hP]) _
  have hkey : (1 + P) ^ (-((A + B₀ : ℕ) : ℝ)) * (1 + P) ^ A = (1 + P) ^ (-(B₀ : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add h1P]
    congr 1; push_cast; ring
  have hr : 0 ≤ (1 + P) ^ (-((A + B₀ : ℕ) : ℝ)) := Real.rpow_nonneg h1P.le _
  calc ((n : ℕ) : ℝ) ^ 2 * (Ca * (1 + P) ^ (-((A + B₀ : ℕ) : ℝ)) * (Kc * (1 + (P + W)) ^ A))
      ≤ ((n : ℕ) : ℝ) ^ 2 * (Ca * (1 + P) ^ (-((A + B₀ : ℕ) : ℝ)) * (Kc * ((1 + W) * (1 + P)) ^ A)) := by
        gcongr
    _ = ((n : ℕ) : ℝ) ^ 2 * (Ca * Kc) * (1 + W) ^ A *
          ((1 + P) ^ (-((A + B₀ : ℕ) : ℝ)) * (1 + P) ^ A) := by
        rw [mul_pow]; ring
    _ = _ := by rw [hkey]

theorem L1B.rpow_le_max (p : ℝ) {h x T : ℝ} (hh : 0 < h) (hhx : h ≤ x) (hxT : x ≤ T) :
    x ^ p ≤ max (h ^ p) (T ^ p) := by
  rcases le_or_gt 0 p with hp | hp
  · exact le_max_of_le_right (Real.rpow_le_rpow (hh.le.trans hhx) hxT hp)
  · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos hh hhx hp.le)

theorem L1B.prod_bound (CG CD h₀ T Q H BG Ei Lj : ℝ) (AG AD Nc : ℕ)
    (hCG : 0 ≤ CG) (hCD : 0 ≤ CD) (hh₀ : 0 < h₀) (hH : h₀ ≤ H) (hQ : 0 ≤ Q) (hN : BG ≤ (Nc : ℝ))
    (hLj0 : 0 ≤ Lj)
    (hEi : Ei ≤ CG * (1 + Q) ^ AG * H ^ BG)
    (hlow : H ≤ T → Lj ≤ CG * (1 + Q) ^ AG * H ^ BG)
    (hhigh : T < H → Lj ≤ CD * (1 + Q) ^ AD * H ^ (-(Nc : ℝ))) :
    Ei * Lj ≤ (CG * CG * (max (h₀ ^ BG) (T ^ BG)) ^ 2 + CG * CD * h₀ ^ (BG - Nc)) *
      (1 + Q) ^ (AG + AG + AD) := by
  have h1Q : 1 ≤ 1 + Q := by linarith
  have hHpos : 0 < H := hh₀.trans_le hH
  have hHB : 0 ≤ H ^ BG := Real.rpow_nonneg hHpos.le _
  have hM0 : 0 ≤ max (h₀ ^ BG) (T ^ BG) := le_max_of_le_left (Real.rpow_nonneg hh₀.le _)
  have hK1 : 0 ≤ CG * CG * (max (h₀ ^ BG) (T ^ BG)) ^ 2 := by positivity
  have hK2 : 0 ≤ CG * CD * h₀ ^ (BG - Nc) := by
    have := Real.rpow_nonneg hh₀.le (BG - Nc); positivity
  have hX : 0 ≤ (1 + Q) ^ (AG + AG + AD) := by positivity
  rcases le_or_gt H T with hle | hlt
  · have hL := hlow hle
    have hHM : H ^ BG ≤ max (h₀ ^ BG) (T ^ BG) := L1B.rpow_le_max BG hh₀ hH hle
    have hR0 : 0 ≤ CG * (1 + Q) ^ AG * H ^ BG := by positivity
    calc Ei * Lj ≤ (CG * (1 + Q) ^ AG * H ^ BG) * (CG * (1 + Q) ^ AG * H ^ BG) :=
          mul_le_mul hEi hL hLj0 hR0
      _ = CG * CG * (H ^ BG) ^ 2 * (1 + Q) ^ (AG + AG) := by ring
      _ ≤ CG * CG * (max (h₀ ^ BG) (T ^ BG)) ^ 2 * (1 + Q) ^ (AG + AG + AD) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHB hHM 2) (by positivity))
            (pow_le_pow_right₀ h1Q (by omega)) (by positivity) hK1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK2) hX
  · have hL := hhigh hlt
    have hHneg : H ^ BG * H ^ (-(Nc : ℝ)) = H ^ (BG - Nc) := by
      rw [sub_eq_add_neg, Real.rpow_add hHpos]
    have hh : H ^ (BG - Nc) ≤ h₀ ^ (BG - Nc) :=
      Real.rpow_le_rpow_of_nonpos hh₀ hH (sub_nonpos.2 hN)
    have hR0 : 0 ≤ CG * (1 + Q) ^ AG * H ^ BG := by positivity
    calc Ei * Lj ≤ (CG * (1 + Q) ^ AG * H ^ BG) * (CD * (1 + Q) ^ AD * H ^ (-(Nc : ℝ))) :=
          mul_le_mul hEi hL hLj0 hR0
      _ = CG * CD * (H ^ BG * H ^ (-(Nc : ℝ))) * (1 + Q) ^ (AG + AD) := by ring
      _ = CG * CD * H ^ (BG - Nc) * (1 + Q) ^ (AG + AD) := by rw [hHneg]
      _ ≤ CG * CD * h₀ ^ (BG - Nc) * (1 + Q) ^ (AG + AG + AD) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hh (by positivity))
            (pow_le_pow_right₀ h1Q (by omega)) (by positivity) hK2
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK1) hX

theorem L1B.summable_of_le {ιE : Type*} (nE : ιE → ℕ) (D₀ : ℕ) (hcard : ∀ e, nE e ≤ D₀) (c : ℝ) (hc : 0 ≤ c)
    (A : ℕ) (W : ιE → ℝ) (W₀ : ℝ) (hW0 : ∀ e, 0 ≤ W e) (hW : ∀ e, 0 < nE e → W e ≤ W₀)
    (V : ℝ) (hV : 0 ≤ V) (I : ιE → ℝ) (hI : ∀ e, 0 ≤ I e) (hs : Summable fun e => if 0 < nE e then I e else 0)
    (g : ιE → ℝ) (hg0 : ∀ e, 0 ≤ g e)
    (hg : ∀ e, g e ≤ ((nE e : ℕ) : ℝ) ^ 2 * c * (1 + W e) ^ A * (V * I e)) :
    Summable g := by
  refine Summable.of_nonneg_of_le hg0 (fun e => (hg e).trans ?_)
    (hs.mul_left (((D₀ : ℕ) : ℝ) ^ 2 * c * (1 + W₀) ^ A * V))
  by_cases hpos : 0 < nE e
  · rw [if_pos hpos]
    have h1 := hI e; have h2 := hW e hpos; have h3 := hW0 e
    have h4 : ((nE e : ℕ) : ℝ) ≤ ((D₀ : ℕ) : ℝ) := by exact_mod_cast hcard e
    calc ((nE e : ℕ) : ℝ) ^ 2 * c * (1 + W e) ^ A * (V * I e)
        = ((nE e : ℕ) : ℝ) ^ 2 * c * (1 + W e) ^ A * V * I e := by ring
      _ ≤ ((D₀ : ℕ) : ℝ) ^ 2 * c * (1 + W₀) ^ A * V * I e := by gcongr
  · have h0 : nE e = 0 := Nat.eq_zero_of_not_pos hpos
    rw [if_neg hpos, h0]
    simp

theorem L1B.measurable_lambdaT {Q G : Type*} [MeasurableSpace Q] [Group G] [MeasurableSpace G]
    (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (E : ℝ → G → ℂ)
    (hE : Measurable fun p : ℝ × G => E p.1 p.2)
    (hCT : Measurable fun p : ℝ × G => constantTerm μ u (E p.1) p.2)
    (hH : MeasurableSet (highSet H T)) :
    Measurable fun p : ℝ × G => lambdaT μ u H T (E p.1) p.2 := by
  have heq : (fun p : ℝ × G => lambdaT μ u H T (E p.1) p.2) =
      fun p => E p.1 p.2 - {q : ℝ × G | q.2 ∈ highSet H T}.indicator
        (fun q => constantTerm μ u (E q.1) q.2) p := by
    funext p
    rfl
  rw [heq]
  exact hE.sub (hCT.indicator (measurable_snd hH))

theorem L1B.measurable_kernel {G : Type*} [MeasurableSpace G] {n : ℕ}
    (a : Fin n → Fin n → ℝ × G → ℂ) (u : Fin n → ℝ × G → ℂ) (L : Fin n → ℝ × G → ℂ)
    (ha : ∀ i j, Measurable (a i j)) (hu : ∀ i, Measurable (u i)) (hL : ∀ j, Measurable (L j)) :
    Measurable fun p : ℝ × G => ∑ i, ∑ j, a i j p * (u i p * conj (L j p)) := by
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (ha i j).mul ((hu i).mul (Complex.continuous_conj.measurable.comp (hL j)))

theorem L1B.integrable_and_integral_le {G : Type*} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν]
    (Φ : Set G) (hΦ : ∀ᵐ p ∂((volume : Measure ℝ).prod ν), p.2 ∈ Φ)
    (F : ℝ × G → ℂ) (hF : Measurable F) (c : ℝ) (prof : ℝ → ℝ) (hprof : Integrable prof)
    (hb : ∀ p : ℝ × G, p.2 ∈ Φ → ‖F p‖ ≤ c * prof p.1) :
    Integrable F ((volume : Measure ℝ).prod ν) ∧
      ∫ p, ‖F p‖ ∂((volume : Measure ℝ).prod ν) ≤ c * (ν.real Set.univ * ∫ t, prof t) := by
  have hG : Integrable (fun p : ℝ × G => c * prof p.1) ((volume : Measure ℝ).prod ν) :=
    (hprof.comp_fst ν).const_mul c
  have hae : ∀ᵐ p ∂((volume : Measure ℝ).prod ν), ‖F p‖ ≤ c * prof p.1 :=
    hΦ.mono fun p hp => hb p hp
  have hI : Integrable F ((volume : Measure ℝ).prod ν) := hG.mono' hF.aestronglyMeasurable hae
  refine ⟨hI, ?_⟩
  calc ∫ p, ‖F p‖ ∂((volume : Measure ℝ).prod ν)
      ≤ ∫ p, c * prof p.1 ∂((volume : Measure ℝ).prod ν) := integral_mono_ae hI.norm hG hae
    _ = c * (ν.real Set.univ * ∫ t, prof t) := by
        rw [integral_const_mul, integral_fun_fst, smul_eq_mul]

theorem L1B.ae_snd_mem {G : Type*} [MeasurableSpace G] {μG : Measure G} {Φ S : Set G}
    (hnull : NullMeasurableSet Φ (μG.restrict S)) (hsub : Φ ⊆ S) (ρ : Measure ℝ) :
    ∀ᵐ p ∂(ρ.prod (μG.restrict Φ)), p.2 ∈ Φ := by
  have h : NullMeasurableSet Φ (μG.restrict Φ) :=
    hnull.mono_ac (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hsub le_rfl))
  have h2 : ∀ᵐ x ∂(μG.restrict Φ), x ∈ Φ :=
    (ae_restrict_iff₀ h).2 (Filter.Eventually.of_forall fun _ => id)
  exact Measure.quasiMeasurePreserving_snd.ae h2

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
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
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ e : ιE, Integrable (fun p : ℝ × AdelicGL2 (𝓞 K) K => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((p.1 : ℂ) * Complex.I))) p.2)))
          ((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))) ∧
      (Summable fun e : ιE => ∫ p : ℝ × AdelicGL2 (𝓞 K) K, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((p.1 : ℂ) * Complex.I))) p.2))‖
          ∂((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))) := by

  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _iC μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf
    hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE f hf hfc hfact hbi harch
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K

  have hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) := by
    intro z; rw [Real.rpow_zero]; exact hξu z
  have hμν' : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
      ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) : ℂ) =
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    intro e z
    rw [Real.rpow_zero, Complex.ofReal_one, mul_one, ← Units.val_mul, hμν e z]
  have hpairs' : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
      IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
      IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
      ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
      IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
      Continuous φ₀ → IsArchKFinite K φ₀ →
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
      φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
      ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z := by
    intro μ' ν' h1 h2 h3 h4 h5 h6 h7
    refine hpairs μ' ν' h1 h2 h3 h4 h5 h6 (fun z => Units.ext ?_)
    have h := h7 z
    rw [Real.rpow_zero, Complex.ofReal_one, mul_one] at h
    rw [Units.val_mul]; exact h

  obtain ⟨D₀, τμ, τν, mμ, mν, M₀, nρ, ρs, B₀, hcard, hτ, hm, hM₀, -, hsum⟩ :=
    AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2 K α β hα hαβ ΦK
      cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK (fun _ => 0) (fun _ _ => 0) 0 hξw hαm ιE μ ν
      hμ hν hμic hνic hμc hνc hμν' hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan
      hpairs' OE EE NE hEE
  obtain ⟨hint, hsumm, -⟩ := hsum B₀ le_rfl

  obtain ⟨CG, AG, BG, hCG, hG⟩ :=
    AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain_of_flat
      K SK ξK hξc hξt N hN tysK 0 hξw α β hα hαβ
  obtain ⟨CD, AD, hCD, hD⟩ :=
    AutomorphicForm.forall_exists_forall_norm_lambdaT_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_neg_of_mem_canonicalTruncationDomain_of_flat
      K SK ξK hξc hξt N hN tysK 0 hξw α β hα hαβ ΦK ⌈BG⌉₊

  obtain ⟨h₀, hh₀, hfloor, -⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
      K α β hα hαβ

  obtain ⟨Ca, hCa, ha⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn K SK ξK hξc hξt N hN tysK 0 hξw
      f hf hfc hfact (AG + AG + AD + B₀)

  have hnorm : ∀ (e : ιE) (j : Fin (nE e)),
      ∫ k, ‖φE e j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1 := by
    intro e j
    have h := hφEon e j j
    rw [if_pos rfl] at h
    have hk : ∀ g : AdelicGL2 (𝓞 K) K, φE e j 0 g * conj (φE e j 0 g) = ((‖φE e j 0 g‖ ^ 2 : ℝ) : ℂ) := fun g => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    simp_rw [hk] at h
    rw [integral_complex_ofReal] at h
    exact (Complex.ofReal_eq_one.mp h).le

  have hab : ∀ (e : ιE) (i j : Fin (nE e)),
      (Continuous fun t : ℝ =>
        ∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
          conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
      ∀ t : ℝ,
      ‖∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
          conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤
        Ca * (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-((AG + AG + AD + B₀ : ℕ) : ℝ)) := by
    intro e i j
    obtain ⟨a', hd, -, hb⟩ := ha hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν' e)
      (τμ e) (τν e) (fun v z h1 h2 => (hτ e v z h1 h2).1) (fun v z h1 h2 => (hτ e v z h1 h2).2)
      (φE e i) (φE e j) (hφE e i) (hφE e j) (hφEK e i) (hφEK e j) (hφEf e i) (hφEf e j)
      (hφEjc e i) (hφEjc e j) (hφEhol e i) (hφEhol e j) (hφEKu e i) (hφEKu e j)
      (hφEflat e i) (hφEflat e j) (hφElev e i) (hφElev e j) (hφEty e i) (hφEty e j) (hnorm e i) (hnorm e j)
    have hc : Continuous _ := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
    simp only [zero_div, Real.rpow_zero, Complex.ofReal_one, mul_one] at hc hb
    exact ⟨hc, fun t => le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hb t)⟩

  have hax : ∀ t : ℝ, ((t : ℂ) * Complex.I) ∈ {s : ℂ | s.re = 0} := fun t => by simp
  have hιc : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => (((p.1 : ℂ) * Complex.I), p.2) :=
    ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk continuous_snd
  have hEc : ∀ (e : ιE) (i : Fin (nE e)),
      Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => EE e i ((p.1 : ℂ) * Complex.I) p.2 := by
    intro e i
    obtain ⟨-, -, haxs, -, -, -, hEjc, -⟩ := hEE e i
    exact hEjc.comp_continuous hιc fun p => ⟨haxs (hax p.1), Set.mem_univ _⟩
  have hCTc : ∀ (e : ιE) (j : Fin (nE e)), Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K =>
      AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
        (fun t => AutomorphicForm.unipotentGL2 t) (EE e j ((p.1 : ℂ) * Complex.I)) p.2 := by
    intro e j
    obtain ⟨hO, hOc, haxs, hhalf, hEa, hNa, hEjc, hNjc, hEq, hNq⟩ := hEE e j
    have hE' : ∀ z : ℂ, 1 / 2 < z.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j z g = AutomorphicForm.pseudoEisenstein K (φE e j z) g := fun z hz g => by
      rw [hEq z hz g, AutomorphicForm.pseudoEisenstein_apply]
    have hct := (AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family K hαm (μ e) (ν e)
      (hμ e) (hν e) (hμic e) (hνic e) (φE e j) (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j)
      (hφEKu e j) (OE e j) (EE e j) (NE e j) hO hOc hhalf hEa hNa hEjc hNjc hE' hNq).2.1
    exact hct.comp_continuous hιc fun p => ⟨haxs (hax p.1), Set.mem_univ _⟩
  have hHm : Measurable (NumberField.AdelicHeight.adelicHeight K) :=
    (NumberField.AdelicHeight.continuous_adelicHeight K).measurable

  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    isFiniteMeasure_restrict.2 hfin.ne
  have hae : ∀ᵐ p ∂((volume : Measure ℝ).prod
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))),
      p.2 ∈ AutomorphicForm.canonicalTruncationDomain K α β :=
    L1B.ae_snd_mem hFD.nullMeasurableSet hslab _
  refine ⟨0, fun R _ => ?_⟩

  have hS' : MeasurableSet (highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)) :=
    measurableSet_lt measurable_const hHm
  have hsplit : ∀ (e : ιE) (t : ℝ),
      ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ)) =
        ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|) +
          ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)) := fun e t => by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have hprod : ∀ (e : ιE) (i j : Fin (nE e)) (t : ℝ), ∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β,
      ‖EE e i ((t : ℂ) * Complex.I) x‖ * ‖(@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((t : ℂ) * Complex.I))) x‖ ≤
        (CG * CG * (max (h₀ ^ BG) (Real.exp R ^ BG)) ^ 2 + CG * CD * h₀ ^ (BG - ⌈BG⌉₊)) *
          (1 + (∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|) +
            ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)))) ^ (AG + AG + AD) := by
    intro e i j t x hx
    have hGe : ∀ i' : Fin (nE e), ‖EE e i' ((t : ℂ) * Complex.I) x‖ ≤
        CG * (1 + (∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|) +
            ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)))) ^ AG *
          NumberField.AdelicHeight.adelicHeight K x ^ BG := fun i' => by
      have h := hG hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν' e)
        (τμ e) (τν e) (fun v z h1 h2 => (hτ e v z h1 h2).1) (fun v z h1 h2 => (hτ e v z h1 h2).2)
        (mμ e) (mν e) (fun v z h1 => (hm e v z h1).1) (fun v z h1 => (hm e v z h1).2)
        (φE e i') (hφE e i') (hφEK e i') (hφEf e i') (hφEjc e i') (hφEhol e i') (hφEKu e i') (hφEflat e i')
        (hφElev e i') (hφEty e i') (hnorm e i') (OE e i') (EE e i') (NE e i') (hEE e i') t x hx
      rwa [hsplit e t] at h
    refine L1B.prod_bound CG CD h₀ (Real.exp R) _ _ BG _ _ AG AD ⌈BG⌉₊ hCG.le hCD.le hh₀ (hfloor x hx)
      (by positivity) (Nat.le_ceil BG) (norm_nonneg _) (hGe i) (fun hle => ?_) (fun hlt => ?_)
    · rw [AutomorphicForm.lambdaT_apply_of_le _ _ hle]
      exact hGe j
    · have h := hD hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν' e)
        (τμ e) (τν e) (fun v z h1 h2 => (hτ e v z h1 h2).1) (fun v z h1 h2 => (hτ e v z h1 h2).2)
        (mμ e) (mν e) (fun v z h1 => (hm e v z h1).1) (fun v z h1 => (hm e v z h1).2)
        (φE e j) (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j) (hφEflat e j)
        (hφElev e j) (hφEty e j) (hnorm e j) (OE e j) (EE e j) (NE e j) (hEE e j) t R x hx hlt
      rwa [hsplit e t] at h
  have hKc : 0 ≤ CG * CG * (max (h₀ ^ BG) (Real.exp R ^ BG)) ^ 2 + CG * CD * h₀ ^ (BG - ⌈BG⌉₊) := by
    have h1 := Real.rpow_nonneg hh₀.le (BG - ⌈BG⌉₊)
    have h2 := sq_nonneg (max (h₀ ^ BG) (Real.exp R ^ BG))
    have := hCG.le; have := hCD.le
    positivity

  have key : ∀ (e : ιE) (p : ℝ × AdelicGL2 (𝓞 K) K), p.2 ∈ AutomorphicForm.canonicalTruncationDomain K α β →
      ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((p.1 : ℂ) * Complex.I))) p.2))‖ ≤
        ((nE e : ℕ) : ℝ) ^ 2 * (Ca * (CG * CG * (max (h₀ ^ BG) (Real.exp R ^ BG)) ^ 2 + CG * CD * h₀ ^ (BG - ⌈BG⌉₊))) *
          (1 + ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ))) ^ (AG + AG + AD) *
          (1 + ∑ v : InfinitePlace K, (|p.1 + τμ e v| + |p.1 - τν e v|)) ^ (-(B₀ : ℝ)) := by
    intro e p hp
    have hds := L1B.dsum_bound _ _ _ _ _ (fun i j => (hab e i j).2 p.1) (fun i j => hprod e i j p.1 p.2 hp)
      (mul_nonneg hCa.le (Real.rpow_nonneg (by positivity) _))
    exact L1B.final_bound (nE e) (AG + AG + AD) B₀ Ca _ _ _ _ hCa.le hKc (by positivity) (by positivity) hds

  have hmeas : ∀ e : ιE, Measurable fun p : ℝ × AdelicGL2 (𝓞 K) K => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((p.1 : ℂ) * Complex.I))) p.2)) := by
    intro e
    refine L1B.measurable_kernel _ _ _ (fun i j => ((hab e i j).1.comp continuous_fst).measurable)
      (fun i => (hEc e i).measurable) (fun j => ?_)
    exact L1B.measurable_lambdaT _ _ _ _ (fun t => EE e j ((t : ℂ) * Complex.I)) (hEc e j).measurable
      (hCTc e j).measurable hS'

  have hFI := fun e : ιE => L1B.integrable_and_integral_le _ _ hae _ (hmeas e) _ _ (hint e) (key e)
  refine ⟨fun e => (hFI e).1, ?_⟩

  have hW0 : ∀ e : ιE, 0 ≤ ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)) := fun e => by positivity
  have hWle : ∀ e : ιE, 0 < nE e → ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)) ≤
      ∑ _v : InfinitePlace K, ((M₀ : ℝ) + (M₀ : ℝ)) := fun e he =>
    Finset.sum_le_sum fun v _ => by
      have h1 : (|mμ e v| : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast (hM₀ e he v).1
      have h2 : (|mν e v| : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast (hM₀ e he v).2
      exact add_le_add h1 h2
  have hIe : ∀ e : ιE, 0 ≤ ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B₀ : ℝ)) := fun e =>
    integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  exact L1B.summable_of_le nE D₀ hcard _ (mul_nonneg hCa.le hKc) (AG + AG + AD)
    (fun e => ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ))) _ hW0 hWle
    _ ENNReal.toReal_nonneg _ hIe hsumm _ (fun e => integral_nonneg fun _ => norm_nonneg _) (fun e => (hFI e).2)

end S_AutomorphicForm_exists_forall_integrable_sum_rightConv_axis_continuation_mul_conj_lambdaT_prod_restrict_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integrable_sum_rightConv_axis_continuation_mul_conj_lambdaT_prod_restrict_canonicalTruncationDomain (solution)
