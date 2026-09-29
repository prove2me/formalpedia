-- Prove2me | solution 1 for AutomorphicForm.finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/177c8507-c9e7-5a4c-abbf-5bb91371cc1a

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
import Theorems.Thm_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers
import Theorems.Thm_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_AutomorphicForm_setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_central_transfer
import Theorems.Thm_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_of_odd
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar
import Theorems.Thm_NumberField_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_setIntegral_comp_idelicNorm_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply AutomorphicForm.cpowChar_apply_val ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel toTensorGL normString IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedOrbitalIntegralOn AdelicGL2 globalPoints centralScalar sigmaAdelicAct sigmaCentralizer centralCell ellipticCell adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_central_transfer mem_range_idelicNorm_of_isNormOf_centralScalar_of_odd exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar"
namespace CentralLedgerK
p2m_open "AutomorphicForm"

section Reps

variable {K : Type*} [Field K]

theorem scalar_mem_centralCell (a : Kˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ centralCell K := by
  refine ⟨(a : K), ?_⟩
  show Matrix.scalar (Fin 2) (a : K) = (a : K) • (1 : Matrix (Fin 2) (Fin 2) K)
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem exists_eq_scalar_of_mem_centralCell {γ : GL (Fin 2) K} (hγ : γ ∈ centralCell K) :
    ∃ b : Kˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) b := by
  obtain ⟨c, hc⟩ := hγ
  have hc0 : c ≠ 0 := by
    intro h0
    apply (Matrix.isUnits_det_units γ).ne_zero
    rw [hc, h0, zero_smul, Matrix.det_zero]
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  show (γ : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c
  rw [hc]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem scalar_mul_comm (c : Kˣ) (g : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : K) * (g : Matrix (Fin 2) (Fin 2) K) =
    (g : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (c : K)
  exact (Matrix.scalar_commute (c : K) (fun r => Commute.all _ r) _).eq

private theorem _root_.AutomorphicForm.CentralLedgerK.conj_scalar (c : Kˣ) (h : GL (Fin 2) K) :
    h⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * h = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

p2m_export "AutomorphicForm.CentralLedgerK" "conj_scalar"
private theorem _root_.AutomorphicForm.CentralLedgerK.scalar_injective : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL (Fin 2) K) := by
  intro a b h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using Units.ext this

p2m_export "AutomorphicForm.CentralLedgerK" "scalar_injective"
variable (RK : Set (GL (Fin 2) K))
  (hRKsub : RK ⊆ centralCell K ∪ ellipticCell K)
  (hRK : ∀ γ ∈ centralCell K ∪ ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
    γ₀ ∈ RK ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))

include hRK in

theorem exists_inter_centralCell_eq_singleton :
    ∃ b : Kˣ, RK ∩ centralCell K = {Matrix.GeneralLinearGroup.scalar (Fin 2) b} := by

  have h1c : (1 : GL (Fin 2) K) ∈ centralCell K := by
    have := scalar_mem_centralCell (K := K) 1
    rwa [map_one] at this
  obtain ⟨γc, ⟨hγcR, h, a, hγc⟩, huniq⟩ := hRK 1 (Or.inl h1c)

  have hγc' : γc = Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ := by
    have h1 : h⁻¹ * γc * h = Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ := by
      have := hγc
      rw [map_inv]
      rw [eq_comm, mul_eq_one_iff_inv_eq] at this
      exact this.symm
    calc γc = h * (h⁻¹ * γc * h) * h⁻¹ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ := by rw [h1, ← scalar_mul_comm, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨a⁻¹, Set.eq_singleton_iff_unique_mem.2 ⟨⟨hγc' ▸ hγcR, scalar_mem_centralCell _⟩, ?_⟩⟩
  rintro γ ⟨hγR, hγC⟩
  obtain ⟨b, rfl⟩ := exists_eq_scalar_of_mem_centralCell hγC

  rw [← hγc']
  refine huniq _ ⟨hγR, 1, b⁻¹, ?_⟩
  rw [inv_one, one_mul, mul_one, ← map_mul, inv_mul_cancel, map_one]

theorem card_stabilizer_scalar_eq_one (b : Kˣ) :
    Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
      Matrix.GeneralLinearGroup.scalar (Fin 2) a * Matrix.GeneralLinearGroup.scalar (Fin 2) b =
        h⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) b * h} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨1, 1, by rw [map_one, one_mul, inv_one, one_mul, mul_one]⟩, ?_⟩
  rintro ⟨a, h, ha⟩
  refine Subtype.ext ?_
  rw [conj_scalar, ← map_mul] at ha
  have := scalar_injective ha
  simpa using this

end Reps

section Integrand

variable (K : Type) [Field K] [NumberField K]

theorem conj_globalPoints_scalar_mul_centralScalar (b : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    x⁻¹ * globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) b) * (centralScalar (𝓞 K) K z * x) =
      globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) b) * centralScalar (𝓞 K) K z := by
  have hgp : globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) b) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b) := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    show algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.GeneralLinearGroup.scalar (Fin 2) b : Matrix (Fin 2) (Fin 2) K) i j) =
      ((Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b) :
          GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [hgp]
  show x⁻¹ * centralScalar (𝓞 K) K _ * (centralScalar (𝓞 K) K z * x) = _
  rw [← mul_assoc (x⁻¹ * centralScalar (𝓞 K) K _), mul_assoc x⁻¹, ← map_mul]
  set c := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b * z
  have hcomm : centralScalar (𝓞 K) K c * x = x * centralScalar (𝓞 K) K c := by
    refine Units.ext ?_
    show Matrix.scalar (Fin 2) (c : AdeleRing (𝓞 K) K) * (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (c : AdeleRing (𝓞 K) K)
    exact (Matrix.scalar_commute (c : AdeleRing (𝓞 K) K) (fun r => Commute.all _ r) _).eq
  rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem setIntegral_conj_central_eq (b : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (Ψ : Set (AdelicGL2 (𝓞 K) K))
    (f : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ x in Ψ, f (x⁻¹ * globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) b) *
        (centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((adelicGLHaar (Fin 2) (𝓞 K) K).real Ψ : ℂ) *
        f (globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) b) * centralScalar (𝓞 K) K z) := by
  simp only [conj_globalPoints_scalar_mul_centralScalar]
  rw [setIntegral_const, Complex.real_smul]

end Integrand

section Covolume

variable (K : Type) [Field K] [NumberField K]

theorem map_centralizer_scalar_eq_range (b : Kˣ) :
    (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) b} : Set (GL (Fin 2) K))).map
        (globalPoints (𝓞 K) K) =
      (globalPoints (𝓞 K) K).range := by
  have htop : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) b} : Set (GL (Fin 2) K)) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact (scalar_mul_comm b g).symm
  rw [htop, ← MonoidHom.range_eq_map]

theorem exists_covolume_const (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (AdelicGL2 (𝓞 K) K),
        Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
        IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
          ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) →
        adelicGLHaar (Fin 2) (𝓞 K) K Φ = C * ENNReal.ofReal (Real.log (b / a)) := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K Φ₀ ≠ ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K α β hα hαβ Φ₀ hΦ₀
    rw [Set.inter_eq_self_of_subset_left hΦ₀s] at h
    exact h.ne
  obtain ⟨C, hC0, hCt, -, hC⟩ :=
    NumberField.AdelicHaar.exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log (Fin 2) K
      (adelicGLHaar (Fin 2) (𝓞 K) K) α β hα hαβ Φ₀ hΦ₀s hΦ₀ hfin
  exact ⟨C, hC0, hCt, hC⟩

end Covolume

section KSide

variable (K : Type) [Field K] [NumberField K]

theorem central_term_eq (α β : ℝ) (b : Kˣ) (Ψ : Set (AdelicGL2 (𝓞 K) K))
    (C : ℝ≥0∞) (hΨ : adelicGLHaar (Fin 2) (𝓞 K) K Ψ = C * ENNReal.ofReal (Real.log (β / α)))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] (ν : Measure (AdeleRing (𝓞 K) K)ˣ)
    (ξ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ) :
    ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
        Matrix.GeneralLinearGroup.scalar (Fin 2) a * Matrix.GeneralLinearGroup.scalar (Fin 2) b =
          h⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) b * h} : ℕ) : ℂ)⁻¹ *
      ∫ z, ξ z * (∫ x in Ψ, f (x⁻¹ * globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) b) *
        (centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂ν =
      ((C * ENNReal.ofReal (Real.log (β / α))).toReal : ℂ) *
        ∫ z, ξ z * f (globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) b) *
          centralScalar (𝓞 K) K z) ∂ν := by
  rw [card_stabilizer_scalar_eq_one, Nat.cast_one, inv_one, one_mul]
  simp only [setIntegral_conj_central_eq, measureReal_def, hΨ]
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

end KSide

end AutomorphicForm.CentralLedgerK

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel toTensorGL normString IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedOrbitalIntegralOn AdelicGL2 globalPoints centralScalar sigmaAdelicAct sigmaCentralizer centralCell ellipticCell adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_central_transfer mem_range_idelicNorm_of_isNormOf_centralScalar_of_odd exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar"
namespace CentralLedgerL
p2m_open "AutomorphicForm"

open LT.TwistedNorm

section GL2

variable {K : Type*} [Field K]

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

theorem scalar_mul_comm (c : Kˣ) (g : GL (Fin 2) K) : sc c * g = g * sc c := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (c : K) * (g : Matrix (Fin 2) (Fin 2) K) =
    (g : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (c : K)
  exact (Matrix.scalar_commute (c : K) (fun r => Commute.all _ r) _).eq

theorem conj_scalar (c : Kˣ) (h : GL (Fin 2) K) : h⁻¹ * sc c * h = sc c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conj_scalar_mul (c : Kˣ) (g h k : GL (Fin 2) K) :
    h⁻¹ * (sc c * g) * k = sc c * (h⁻¹ * g * k) := by
  rw [← mul_assoc h⁻¹, ← scalar_mul_comm c h⁻¹]
  simp only [mul_assoc]

theorem scalar_injective : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL (Fin 2) K) := by
  intro a b h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using Units.ext this

theorem map_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (c : Aˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : A →* B) c) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem eq_scalar_of_isConj {γ : GL (Fin 2) K} {b : Kˣ} (h : IsConj γ (sc b)) : γ = sc b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h

  calc γ = c⁻¹ * (c * γ * c⁻¹) * c := by group
    _ = sc b := by rw [hc, conj_scalar]

theorem det_scalar_two (b : Kˣ) : Matrix.GeneralLinearGroup.det (sc b) = b ^ 2 := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

end GL2

section Enum

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)
local notation "σ'" => Matrix.GeneralLinearGroup.map (σ : L →+* L)
local notation "Nσ" => sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L)
local notation "ιF" => Units.map ((algebraMap F L : F →+* L) : F →* L)

variable (F L) in

abbrev nu : Lˣ →* Fˣ := Units.map (Algebra.norm F : L →* F)

omit [FiniteDimensional F L] [IsGalois F L] in
theorem map_scalar_units (u : Lˣ) : σ' (sc u) = sc (Units.map ((σ : L →+* L) : L →* L) u) :=
  map_scalar _ _

omit [FiniteDimensional F L] [IsGalois F L] in

theorem sigmaPartialNorm_scalar_mul (u : Lˣ) (δ : GL (Fin 2) L) (r : ℕ) :
    sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (sc u * δ) r =
      sc (sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) u r) *
        sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul,
        map_scalar_units, map_mul]
      rw [← mul_assoc, mul_assoc (sc u) δ, ← scalar_mul_comm, ← mul_assoc, ← map_mul, mul_assoc]

theorem scalar_algebraMap_norm (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ) :
    sc (ιF (nu F L u)) = sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) := by
  congr 1
  refine Units.ext ?_
  rw [Units.coe_map, coe_sigmaNormPow_units_eq_algebraMap_norm hgen u]
  rfl

theorem sigmaNormPow_scalar_mul (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ)
    (δ : GL (Fin 2) L) : Nσ (sc u * δ) = sc (ιF (nu F L u)) * Nσ δ := by
  rw [sigmaNormPow_def, sigmaPartialNorm_scalar_mul, ← sigmaNormPow_def, ← sigmaNormPow_def,
    scalar_algebraMap_norm hgen]

theorem sigmaNormPow_sigmaConj (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (h δ : GL (Fin 2) L) :
    Nσ (h⁻¹ * δ * σ' h) = h⁻¹ * Nσ δ * h :=
  sigmaNormPow_sigmaConj_generalLinearGroup (fun a => iterate_finrank_apply_of_generator hgen a) h δ

theorem sigmaNormPow_eq_scalar_of_normClassMap_eq (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {b : Fˣ}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (sc b)) :
    Nσ δ = sc (ιF b) := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at h
  have hrep : normRep hgen δ = sc b := eq_scalar_of_isConj h
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  rw [hrep, map_scalar] at hP

  calc Nσ δ = P * (P⁻¹ * Nσ δ * P) * P⁻¹ := by group
    _ = sc (ιF b) := by
        rw [hP]
        have := conj_scalar (Units.map ((algebraMap F L : F →+* L) : F →* L) b) P⁻¹
        rwa [inv_inv] at this

theorem normClassMap_eq_of_sigmaNormPow_eq_scalar (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {b : Fˣ} (h : Nσ δ = sc (ιF b)) :
    normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (sc b) := by
  refine normClassMap_mk_eq_of_isNormRep hgen ⟨1, ?_⟩
  rw [inv_one, one_mul, mul_one, h, map_scalar]

theorem nu_eq_one_of_rel (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {b : Fˣ} (hδ : Nσ δ = sc (ιF b)) {u : Lˣ}
    (h : ∃ k : GL (Fin 2) L, sc u * δ = k⁻¹ * δ * σ' k) : nu F L u = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 := congrArg (fun x => Nσ x) hk
  rw [sigmaNormPow_scalar_mul hgen, sigmaNormPow_sigmaConj hgen, hδ, conj_scalar, ← map_mul] at h1
  have h2 : ιF (nu F L u) * ιF b = ιF b := scalar_injective h1
  rw [mul_eq_right] at h2

  refine Units.ext ?_
  have h3 := congrArg (fun x : Lˣ => (x : L)) h2
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one, map_eq_one_iff _ (algebraMap F L).injective]
    at h3
  simpa using h3

omit [FiniteDimensional F L] [IsGalois F L] in
theorem coe_R_apply (w : Lˣ) :
    ((((Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ) w : Lˣ)) : L) = σ (w : L) / (w : L) := by
  rw [MonoidHom.div_apply, Units.val_div_eq_div_val, Units.coe_map, MonoidHom.id_apply]
  rfl

theorem mk_eq_one_of_nu_eq_one (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {u : Lˣ}
    (h : nu F L u = 1) :
    (QuotientGroup.mk u : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range) = 1 := by
  haveI : IsCyclic (L ≃ₐ[F] L) := ⟨⟨σ, hgen⟩⟩
  have h1 : Algebra.norm F ((u : Lˣ) : L) = 1 := by
    have := congrArg (fun x : Fˣ => (x : F)) h
    simpa only [Units.coe_map, MonoidHom.coe_coe, Units.val_one] using this
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one hgen h1
  rw [← QuotientGroup.mk_one, eq_comm, QuotientGroup.eq, inv_one, one_mul]
  refine ⟨y⁻¹, Units.ext ?_⟩
  rw [coe_R_apply, ← hy]
  have hy0 : (y : L) ≠ 0 := y.ne_zero
  have hσy0 : σ (y : L) ≠ 0 := by simp [hy0]
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  field_simp

theorem card_weights_eq_one (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {b : Fˣ} (hδ : Nσ δ = sc (ιF b)) :
    Nat.card {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
        ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
          Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ =
            h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨1, 1, QuotientGroup.mk_one _, 1, by rw [map_one, one_mul, inv_one, one_mul, map_one, mul_one]⟩, ?_⟩
  rintro ⟨q, u, rfl, hu⟩
  exact Subtype.ext (mk_eq_one_of_nu_eq_one hgen (nu_eq_one_of_rel hgen hδ hu))

theorem exists_rel_of_norm_eq_mul (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ δ₁ : GL (Fin 2) L} {b b₁ : Fˣ} (hδ : Nσ δ = sc (ιF b)) (hδ₁ : Nσ δ₁ = sc (ιF b₁))
    {v : Lˣ} (hv : b₁ = b * nu F L v) :
    ∃ h : GL (Fin 2) L, δ₁ = sc v * (h⁻¹ * δ * σ' h) := by
  have hN : Nσ (sc v * δ) = Nσ δ₁ := by
    rw [sigmaNormPow_scalar_mul hgen, hδ, hδ₁, hv, map_mul, map_mul]
    exact scalar_mul_comm _ _
  obtain ⟨h, hh⟩ := LT.TwistedNorm.exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers hgen hN
  exact ⟨h, by rw [hh, conj_scalar_mul]⟩

theorem exists_nu_eq_of_odd (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (hodd : Odd (Module.finrank F L)) {δ : GL (Fin 2) L} {b : Fˣ} (hδ : Nσ δ = sc (ιF b)) :
    ∃ v : Lˣ, b = nu F L v := by
  obtain ⟨m, hm⟩ := hodd

  have hdet := congrArg Matrix.GeneralLinearGroup.det hδ
  rw [det_sigmaNormPow, det_scalar_two] at hdet
  have hdet' : ιF (nu F L (Matrix.GeneralLinearGroup.det δ)) = ιF b ^ 2 := by
    rw [← hdet]
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact (coe_sigmaNormPow_units_eq_algebraMap_norm hgen _).symm
  have hinj : Function.Injective (Units.map ((algebraMap F L : F →+* L) : F →* L)) := by
    intro x y hxy
    refine Units.ext ((algebraMap F L).injective ?_)
    have := congrArg (fun z : Lˣ => (z : L)) hxy
    simpa only [Units.coe_map, MonoidHom.coe_coe] using this
  have h2 : nu F L (Matrix.GeneralLinearGroup.det δ) = b ^ 2 := hinj (by rw [hdet', map_pow])

  have hℓ : nu F L (ιF b) = b ^ Module.finrank F L := by
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
    exact Algebra.norm_algebraMap (b : F)
  refine ⟨ιF b * ((Matrix.GeneralLinearGroup.det δ) ^ m)⁻¹, ?_⟩
  rw [map_mul, map_inv, map_pow, hℓ, h2, hm, ← pow_mul, pow_succ, mul_comm (b ^ (2 * m)) b,
    mul_inv_cancel_right]

omit [FiniteDimensional F L] [IsGalois F L] in

def antidiag (b : Fˣ) : GL (Fin 2) L :=
  ⟨!![0, 1; algebraMap F L b, 0], !![0, (algebraMap F L b)⁻¹; 1, 0],
    by
      have hb : algebraMap F L (b : F) ≠ 0 := by simp [b.ne_zero]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb],
    by
      have hb : algebraMap F L (b : F) ≠ 0 := by simp [b.ne_zero]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb]⟩

omit [FiniteDimensional F L] [IsGalois F L] in
theorem map_antidiag (b : Fˣ) : σ' (antidiag (L := L) b) = antidiag b := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [antidiag]

omit [FiniteDimensional F L] [IsGalois F L] in
theorem antidiag_mul_antidiag (b : Fˣ) : antidiag (L := L) b * antidiag b = sc (ιF b) := by
  ext i j
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;>
    simp [antidiag, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

omit [FiniteDimensional F L] [IsGalois F L] in

theorem exists_sigmaNormPow_eq_scalar_of_two (h2 : Module.finrank F L = 2) (b : Fˣ) :
    ∃ δ : GL (Fin 2) L, Nσ δ = sc (ιF b) := by
  refine ⟨antidiag b, ?_⟩
  rw [h2, sigmaNormPow_def, sigmaPartialNorm_succ', sigmaPartialNorm_one, map_antidiag,
    antidiag_mul_antidiag]

end Enum

section Scalars

variable (K : Type) [Field K] [NumberField K]

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

theorem globalPoints_scalar (a : Kˣ) :
    AutomorphicForm.globalPoints (𝓞 K) K (sc a) =
      AutomorphicForm.centralScalar (𝓞 K) K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) :=
  map_scalar _ _

theorem continuous_centralScalar : Continuous (AutomorphicForm.centralScalar (𝓞 K) K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_val).matrix_diagonal).congr fun u => ?_
    rfl
  · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_coe_inv).matrix_diagonal).congr fun u => ?_
    change (Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
      (((AutomorphicForm.centralScalar (𝓞 K) K u)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    rw [← map_inv]
    rfl

theorem isClosedEmbedding_centralScalar : Topology.IsClosedEmbedding (AutomorphicForm.centralScalar (𝓞 K) K) := by

  let p : AutomorphicForm.AdelicGL2 (𝓞 K) K → AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    fun g => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0,
      MulOpposite.op (((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0))
  have hp : Continuous p := by
    refine Continuous.prodMk ?_ ?_
    · exact Units.continuous_val.matrix_elem 0 0
    · exact MulOpposite.continuous_op.comp (Units.continuous_coe_inv.matrix_elem 0 0)
  have hcomp : p ∘ AutomorphicForm.centralScalar (𝓞 K) K = Units.embedProduct (AdeleRing (𝓞 K) K) := by
    funext u
    change ((((AutomorphicForm.centralScalar (𝓞 K) K u : AutomorphicForm.AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0,
      MulOpposite.op (((((AutomorphicForm.centralScalar (𝓞 K) K u)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0)) =
      ((u : AdeleRing (𝓞 K) K), MulOpposite.op (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K))
    rw [← map_inv]
    rfl
  have hind : Topology.IsInducing (AutomorphicForm.centralScalar (𝓞 K) K) := by
    refine Topology.IsInducing.of_comp (continuous_centralScalar K) hp ?_
    rw [hcomp]
    exact Units.isInducing_embedProduct
  have hinj : Function.Injective (AutomorphicForm.centralScalar (𝓞 K) K) := by
    intro a b h
    have := congrArg (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) h
    refine Units.ext ?_
    simpa [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
  refine ⟨⟨hind, hinj⟩, ?_⟩

  have hrange : Set.range (AutomorphicForm.centralScalar (𝓞 K) K) =
      {g : AutomorphicForm.AdelicGL2 (𝓞 K) K |
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
          (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1} := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    · rintro ⟨h01, h10, h00⟩
      set a : AdeleRing (𝓞 K) K := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 with ha
      have hg : (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = Matrix.diagonal fun _ => a := by
        ext i j
        fin_cases i <;> fin_cases j
        · simp [ha]
        · simpa using h01
        · simpa using h10
        · simp only [Matrix.diagonal_apply_eq]
          exact h00.symm.trans ha
      have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = a * a := by
        rw [hg, Matrix.det_diagonal, Fin.prod_univ_two]
      have ha : IsUnit a := by
        have hu : IsUnit (a * a) := hdet ▸ (Matrix.isUnits_det_units g)
        exact isUnit_of_mul_isUnit_left hu
      refine ⟨ha.unit, Units.ext ?_⟩
      rw [hg]
      ext i j
      simp [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [hrange]
  refine IsClosed.inter (isClosed_eq (Units.continuous_val.matrix_elem 0 1)
    continuous_const) (IsClosed.inter (isClosed_eq (Units.continuous_val.matrix_elem 1 0)
    continuous_const) (isClosed_eq (Units.continuous_val.matrix_elem 0 0)
    (Units.continuous_val.matrix_elem 1 1)))

end Scalars

section Constants

theorem finalAlgebra (c₀ : NNReal) (κ ℓ CK : ℝ) (n : ℕ) (X Y : ℂ) (hκ : κ ≠ 0) (hℓ : ℓ ≠ 0)
    (hY : c₀ ≠ 0 → Y = 0) (hn : n = 0 → X = 0) :
    (((c₀ : ℝ) / ℓ * CK : ℝ) : ℂ) * X =
      (((c₀ : ℝ) * κ / (ℓ * ((max 1 n : ℕ) : ℝ)) : ℝ) : ℂ) * ((CK : ℂ) * (((n : ℂ) / (κ : ℂ)) * (X + Y))) := by
  by_cases h0 : n = 0
  · subst h0
    rw [hn rfl]
    simp
  by_cases hc : c₀ = 0
  · subst hc
    simp
  rw [hY hc, add_zero, max_eq_right (Nat.one_le_iff_ne_zero.mpr h0)]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast h0
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  push_cast
  field_simp

end Constants

end AutomorphicForm.CentralLedgerL

end

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open NumberField.AdelicLevel _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer.AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (RL : Set (GL (Fin 2) L))
    (hRLsub : RL ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ})
    (hRL : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ RL ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h))
    (ΨL : GL (Fin 2) L → Set (AdelicGL2 (𝓞 L) L))
    (hΨLs : ∀ δ₀ ∈ RL, ΨL δ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨL : ∀ δ₀ ∈ RL, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (ΨL δ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (RK : Set (GL (Fin 2) K))
    (hRKsub : RK ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hRK : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ RK ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (ΨK : GL (Fin 2) K → Set (AdelicGL2 (𝓞 K) K))
    (hΨKs : ∀ γ₀ ∈ RK, ΨK γ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨK : ∀ γ₀ ∈ RK, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K))
      (ΨK γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (c₀ : NNReal) (κ : ℝ) (hκ : 0 < κ)
    (hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal κ *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hcent : ∀ (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u) →
      ∀ (τ : Measure (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))))
        (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
        τ.IsHaarMeasure → τ'.IsHaarMeasure →
      ∀ C : ENNReal, C ≠ 0 → C ≠ ⊤ →
        (∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
          IsFundamentalDomain
            (((AutomorphicForm.sigmaCentralizer
                (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
                (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom :
                    L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
              (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
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
              C * ENNReal.ofReal (Real.log (b / a))) →
        (∀ D : Set (Subgroup.centralizer
            ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))),
          IsFundamentalDomain
            (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
              (Subgroup.centralizer
                ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K)))).op D τ →
          ∀ a b : ℝ, 0 < a → a ≤ b →
            τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
              (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a))) →
      ∀ I I' : ℂ,
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ.symm
          (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
            (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
            (adelicGLHaar (Fin 2) (𝓞 L) L))
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
          (φ ∘ Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I' →
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I' = I)
    (hcvan : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
      (¬ ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ.symm
            (AutomorphicForm.centralScalar (𝓞 K) K u) δ) →
      ∀ τ : Measure (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))),
        τ.IsHaarMeasure →
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I = 0) :
    (RL ∩ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.centralCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk γ} ∩
      Function.support (fun δ₀ : GL (Fin 2) L =>
        ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
            ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
              Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
                h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
          ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL)).Finite ∧
    (∑ᶠ δ₀ ∈ RL ∩ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.centralCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk γ},
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL) =
      (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) *
        ∑ ξK ∈ Ξ, ∑ᶠ γ₀ ∈ RK ∩ AutomorphicForm.centralCell K,
          ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
              Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
            ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK := by
  classical

  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ.symm, hgen⟩⟩
  have hℓpos : 0 < Module.finrank K L := hprime.pos
  have hℓ0 : (Module.finrank K L : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  let N : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
  let ιK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
  let ιF : Kˣ →* Lˣ := Units.map ((algebraMap K L : K →+* L) : K →* L)
  let χL : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)
  let χ : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    fun ξ u => ((ξ ⟨u, Subgroup.mem_top u⟩ : ℂˣ) : ℂ)
  let F : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun u => f (centralScalar (𝓞 K) K u)
  have hFc : Continuous F := hf.comp (CentralLedgerL.continuous_centralScalar K)
  have hFs : HasCompactSupport F :=
    hfc.comp_isClosedEmbedding (CentralLedgerL.isClosedEmbedding_centralScalar K)
  let I : Kˣ → ℂ := fun t => ∫ z in Θ, χL z * F (ιK t * N z) ∂νZL

  let Nσ : GL (Fin 2) L → GL (Fin 2) L :=
    LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) (Module.finrank K L)

  let Nm : Subgroup Kˣ := (Units.map (Algebra.norm K : L →* K)).range

  set SL : Set (GL (Fin 2) L) := {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
      γ ∈ AutomorphicForm.centralCell K ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
        ConjClasses.mk γ} with hSL
  have hSL_of : ∀ {δ : GL (Fin 2) L} {b : Kˣ},
      Nσ δ = Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF b) → δ ∈ SL := fun {δ b} h =>
    ⟨_, CentralLedgerK.scalar_mem_centralCell b, CentralLedgerL.normClassMap_eq_of_sigmaNormPow_eq_scalar hgen h⟩
  have hSL_to : ∀ {δ : GL (Fin 2) L}, δ ∈ SL → ∃ b : Kˣ,
      Nσ δ = Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF b) := by
    rintro δ ⟨γ, hγ, hδ⟩
    obtain ⟨b, rfl⟩ := CentralLedgerK.exists_eq_scalar_of_mem_centralCell hγ
    exact ⟨b, CentralLedgerL.sigmaNormPow_eq_scalar_of_normClassMap_eq hgen hδ⟩

  let bL : GL (Fin 2) L → Kˣ := fun δ =>
    if h : ∃ b : Kˣ, Nσ δ = Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF b) then h.choose else 1
  have hbL : ∀ {δ : GL (Fin 2) L}, δ ∈ SL → Nσ δ = Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF (bL δ)) := by
    intro δ hδ
    have h := hSL_to hδ
    simp only [bL, dif_pos h]
    exact h.choose_spec
  have hbLnc : ∀ {δ : GL (Fin 2) L}, δ ∈ SL →
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
        ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) (bL δ)) := fun hδ =>
    CentralLedgerL.normClassMap_eq_of_sigmaNormPow_eq_scalar hgen (hbL hδ)
  have hιF_inj : Function.Injective ιF := by
    intro x y hxy
    refine Units.ext ((algebraMap K L).injective ?_)
    have := congrArg (fun z : Lˣ => (z : L)) hxy
    simpa only [ιF, Units.coe_map, MonoidHom.coe_coe] using this

  have hSL_big : ∀ {δ : GL (Fin 2) L}, δ ∈ SL → δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
      (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ} := by
    rintro δ ⟨γ, hγ, hδ⟩
    exact ⟨γ, Or.inr hγ, hδ⟩

  have huniq : ∀ {δ₀ δ₁ : GL (Fin 2) L}, δ₀ ∈ RL → δ₁ ∈ RL → δ₁ ∈ SL →
      (∃ (h : GL (Fin 2) L) (u : Lˣ), δ₁ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h)) → δ₀ = δ₁ := by
    intro δ₀ δ₁ h₀ h₁ h₁S hrel
    obtain ⟨d, -, hd⟩ := hRL δ₁ (hSL_big h₁S)
    have e₀ : δ₀ = d := hd δ₀ ⟨h₀, hrel⟩
    have e₁ : δ₁ = d := hd δ₁ ⟨h₁, 1, 1, by rw [map_one, one_mul, inv_one, one_mul, map_one, mul_one]⟩
    rw [e₀, e₁]

  have hkey : ∀ {δ₀ δ₁ : GL (Fin 2) L}, δ₀ ∈ RL ∩ SL → δ₁ ∈ RL ∩ SL →
      (QuotientGroup.mk (bL δ₀) : Kˣ ⧸ Nm) = QuotientGroup.mk (bL δ₁) → δ₀ = δ₁ := by
    intro δ₀ δ₁ h₀ h₁ heq
    rw [QuotientGroup.eq] at heq
    obtain ⟨v, hv⟩ := heq
    have hv' : bL δ₁ = bL δ₀ * CentralLedgerL.nu K L v := by
      change Units.map (Algebra.norm K : L →* K) v = (bL δ₀)⁻¹ * bL δ₁ at hv
      rw [CentralLedgerL.nu, hv, mul_inv_cancel_left]
    obtain ⟨h, hh⟩ := CentralLedgerL.exists_rel_of_norm_eq_mul hgen (hbL h₀.2) (hbL h₁.2) hv'
    exact huniq h₀.1 h₁.1 h₁.2 ⟨h, v, hh⟩

  have hcover : ∀ (δ : GL (Fin 2) L) (b : Kˣ), Nσ δ = Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF b) →
      ∃ δ₀ ∈ RL ∩ SL, (QuotientGroup.mk (bL δ₀) : Kˣ ⧸ Nm) = QuotientGroup.mk b := by
    intro δ b hδ
    obtain ⟨δ₀, ⟨h₀, h, u, hrel⟩, -⟩ := hRL δ (hSL_big (hSL_of hδ))

    have hN0 : Nσ δ₀ = Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF ((CentralLedgerL.nu K L u)⁻¹ * b)) := by
      have h1 : Nσ δ = Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF (CentralLedgerL.nu K L u)) *
          (h⁻¹ * Nσ δ₀ * h) := by
        simp only [Nσ]
        rw [hrel, CentralLedgerL.sigmaNormPow_scalar_mul hgen, CentralLedgerL.sigmaNormPow_sigmaConj hgen]
      have h2 : h⁻¹ * Nσ δ₀ * h =
          Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF ((CentralLedgerL.nu K L u)⁻¹ * b)) := by
        rw [map_mul, map_inv, map_mul, map_inv]
        exact eq_inv_mul_of_mul_eq (h1.symm.trans hδ)

      calc Nσ δ₀ = h * (h⁻¹ * Nσ δ₀ * h) * h⁻¹ := by group
        _ = _ := by
          rw [h2]
          have := CentralLedgerL.conj_scalar (ιF ((CentralLedgerL.nu K L u)⁻¹ * b)) h⁻¹
          rwa [inv_inv] at this
    have h₀S : δ₀ ∈ SL := hSL_of hN0
    refine ⟨δ₀, ⟨h₀, h₀S⟩, ?_⟩
    have hb0 : bL δ₀ = (CentralLedgerL.nu K L u)⁻¹ * b :=
      hιF_inj (CentralLedgerL.scalar_injective ((hbL h₀S).symm.trans hN0))
    rw [QuotientGroup.eq, hb0, mul_inv_rev, inv_inv, inv_mul_cancel_comm]
    exact ⟨u, rfl⟩

  let rep : Kˣ ⧸ Nm → Kˣ := fun q =>
    if h : ∃ δ : GL (Fin 2) L, δ ∈ RL ∩ SL ∧ (QuotientGroup.mk (bL δ) : Kˣ ⧸ Nm) = q then bL h.choose
    else Quotient.out q
  have hrep_mk : ∀ q, (QuotientGroup.mk (rep q) : Kˣ ⧸ Nm) = q := by
    intro q
    by_cases h : ∃ δ : GL (Fin 2) L, δ ∈ RL ∩ SL ∧ (QuotientGroup.mk (bL δ) : Kˣ ⧸ Nm) = q
    · simp only [rep, dif_pos h]
      exact h.choose_spec.2
    · simp only [rep, dif_neg h]
      exact QuotientGroup.out_eq' q
  have hrep_b : ∀ {δ : GL (Fin 2) L}, δ ∈ RL ∩ SL → rep (QuotientGroup.mk (bL δ)) = bL δ := by
    intro δ hδ
    have h : ∃ δ' : GL (Fin 2) L, δ' ∈ RL ∩ SL ∧
        (QuotientGroup.mk (bL δ') : Kˣ ⧸ Nm) = QuotientGroup.mk (bL δ) := ⟨δ, hδ, rfl⟩
    simp only [rep, dif_pos h]
    rw [hkey h.choose_spec.1 hδ h.choose_spec.2]
  let T : Set Kˣ := Set.range rep
  have hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b := by
    intro a
    refine ⟨rep (QuotientGroup.mk a), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · have h := hrep_mk (QuotientGroup.mk a)
      rw [QuotientGroup.eq] at h
      obtain ⟨v, hv⟩ := h
      exact ⟨v, by rw [hv, mul_inv_cancel_left]⟩
    · rintro t ⟨⟨q, rfl⟩, v, hv⟩
      have : (QuotientGroup.mk a : Kˣ ⧸ Nm) = QuotientGroup.mk (rep q) := by
        rw [QuotientGroup.eq]
        exact ⟨v⁻¹, by rw [map_inv, hv, mul_inv_rev, inv_mul_cancel_right]⟩
      rw [this, hrep_mk]
  have himgT : bL '' (RL ∩ SL) ⊆ T := by
    rintro _ ⟨δ, hδ, rfl⟩
    exact ⟨_, hrep_b hδ⟩
  have hinjOn : Set.InjOn bL (RL ∩ SL) := fun δ₀ h₀ δ₁ h₁ heq => hkey h₀ h₁ (by rw [heq])

  clear_value SL bL rep

  obtain ⟨hfinT, hchar, hempty⟩ :=
    NumberField.sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_setIntegral_comp_idelicNorm_eq_mul
      K L σ.symm hgen νZL νZK Θ hΘ κ hκ (fun g hg => (hκi g hg).2) ξL hξc hξt Ξ hΞ F hFc hFs T hT

  obtain ⟨bK, hbK⟩ := CentralLedgerK.exists_inter_centralCell_eq_singleton RK hRK
  have hbKmem : Matrix.GeneralLinearGroup.scalar (Fin 2) bK ∈ RK := by
    have : Matrix.GeneralLinearGroup.scalar (Fin 2) bK ∈ RK ∩ centralCell K := by
      rw [hbK]; exact Set.mem_singleton _
    exact this.1
  have hFD0 : IsFundamentalDomain (globalPoints (𝓞 K) K).range (ΨK (Matrix.GeneralLinearGroup.scalar (Fin 2) bK))
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by
    have := hΨK _ hbKmem
    rwa [CentralLedgerK.map_centralizer_scalar_eq_range] at this
  obtain ⟨C_H, hC0, hCt, hC_H⟩ := CentralLedgerK.exists_covolume_const K α β hα hαβ _ (hΨKs _ hbKmem) hFD0
  have hvolK : adelicGLHaar (Fin 2) (𝓞 K) K (ΨK (Matrix.GeneralLinearGroup.scalar (Fin 2) bK)) =
      C_H * ENNReal.ofReal (Real.log (β / α)) := hC_H α β hα hαβ.le _ (hΨKs _ hbKmem) hFD0

  have hlog : 0 < Real.log (β / α) := Real.log_pos ((one_lt_div hα).2 hαβ)
  set CK : ℝ := (C_H * ENNReal.ofReal (Real.log (β / α))).toReal with hCK
  have hCKpos : 0 < CK := by
    rw [hCK, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlog.le]
    exact mul_pos (ENNReal.toReal_pos hC0 hCt) hlog

  have hKξ : ∀ ξ ∈ Ξ,
      (∑ᶠ γ₀ ∈ RK ∩ AutomorphicForm.centralCell K,
          ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
              Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
            ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK) =
        (CK : ℂ) * ∫ u, χ ξ u * F u ∂νZK := by
    intro ξ hξ
    rw [hbK, finsum_mem_singleton,
      CentralLedgerK.central_term_eq K α β bK _ C_H hvolK νZK (χ ξ) f]
    congr 1
    have h1 : ∀ z : (AdeleRing (𝓞 K) K)ˣ, globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) bK) *
        centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K (ιK bK * z) := fun z => by
      rw [map_mul, CentralLedgerL.globalPoints_scalar]
    simp_rw [h1]
    have h2 := integral_mul_left_eq_self (μ := νZK) (fun z => χ ξ ((ιK bK)⁻¹ * z) * F z) (ιK bK)
    simp only [inv_mul_cancel_left] at h2
    have htriv : ξ ⟨(ιK bK)⁻¹, Subgroup.mem_top _⟩ = 1 := by
      have := ((hΞ ξ).1 hξ).2.1 (ιK bK⁻¹) ⟨bK⁻¹, rfl⟩
      rwa [map_inv] at this
    calc ∫ z, χ ξ z * f (centralScalar (𝓞 K) K (ιK bK * z)) ∂νZK
        = ∫ z, χ ξ ((ιK bK)⁻¹ * z) * F z ∂νZK := h2
      _ = ∫ u, χ ξ u * F u ∂νZK := by
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          show χ ξ ((ιK bK)⁻¹ * z) * F z = χ ξ z * F z
          congr 1
          change ((ξ ⟨(ιK bK)⁻¹ * z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)
          have hmul : (⟨(ιK bK)⁻¹ * z, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
              ⟨(ιK bK)⁻¹, Subgroup.mem_top _⟩ * ⟨z, Subgroup.mem_top z⟩ := rfl
          rw [hmul, map_mul, htriv, one_mul]
  have hK : (∑ ξK ∈ Ξ, ∑ᶠ γ₀ ∈ RK ∩ AutomorphicForm.centralCell K,
          ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
              Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
            ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK) =
        (CK : ℂ) * (((Ξ.card : ℂ) / (κ : ℂ)) * ∑ᶠ t ∈ T, I t) := by
    rw [Finset.sum_congr rfl hKξ, ← Finset.mul_sum, hchar]

  set cP : ℝ := (c₀ : ℝ) / (Module.finrank K L : ℝ) * CK with hcP
  have hLterm : ∀ δ₀ ∈ RL ∩ SL,
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL = (cP : ℂ) * I (bL δ₀) := by
    rintro δ₀ ⟨h₀R, h₀S⟩
    rw [CentralLedgerL.card_weights_eq_one hgen (hbL h₀S), Nat.cast_one, inv_one, one_mul]
    have hP := fun z =>
      AutomorphicForm.setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_central_transfer
        K L hprime α β hα hαβ D σ hσ hgen c₀ φ hφ hφc f hf hfc hcent C_H hC0 hCt hC_H δ₀ (bL δ₀)
        (hbLnc h₀S) (ΨL δ₀) (hΨLs δ₀ h₀R) (hΨL δ₀ h₀R) z
    simp_rw [hP]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show χL z * (((cP : ℝ) : ℂ) * F (ιK (bL δ₀) * N z)) = (cP : ℂ) * (χL z * F (ιK (bL δ₀) * N z))
    ring
  have hL : (∑ᶠ δ₀ ∈ RL ∩ SL,
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL) = (cP : ℂ) * ∑ᶠ t ∈ bL '' (RL ∩ SL), I t := by
    rw [finsum_mem_congr rfl hLterm, ← mul_finsum_mem, finsum_mem_image hinjOn]

  have hsplit : ∑ᶠ t ∈ T, I t = (∑ᶠ t ∈ bL '' (RL ∩ SL), I t) + ∑ᶠ t ∈ T \ bL '' (RL ∩ SL), I t := by
    have hfin1 : (bL '' (RL ∩ SL) ∩ Function.support I).Finite :=
      hfinT.subset (Set.inter_subset_inter_left _ himgT)
    have hfin2 : (T \ bL '' (RL ∩ SL) ∩ Function.support I).Finite :=
      hfinT.subset (Set.inter_subset_inter_left _ Set.diff_subset)
    rw [← finsum_mem_union' Set.disjoint_sdiff_right hfin1 hfin2, Set.union_diff_cancel himgT]
  have hvan : c₀ ≠ 0 → ∀ t ∈ T \ bL '' (RL ∩ SL), I t = 0 := by
    rintro hc0 t ⟨⟨q, rfl⟩, hnot⟩
    have hq : ¬ ∃ δ : GL (Fin 2) L, δ ∈ RL ∩ SL ∧ (QuotientGroup.mk (bL δ) : Kˣ ⧸ Nm) = q := by
      rintro ⟨δ, hδ, hδq⟩
      exact hnot ⟨δ, hδ, by rw [← hδq, hrep_b hδ]⟩
    rcases hprime.eq_two_or_odd' with h2 | hodd
    ·
      exfalso
      obtain ⟨δA, hδA⟩ := CentralLedgerL.exists_sigmaNormPow_eq_scalar_of_two (L := L) (σ := σ.symm) h2 (rep q)
      obtain ⟨δ₀, hδ₀, hq₀⟩ := hcover δA (rep q) hδA
      exact hq ⟨δ₀, hδ₀, by rw [hq₀, hrep_mk]⟩
    ·
      have hnotin : rep q ∉ Nm := by
        intro hin
        have hone : Nσ 1 = Matrix.GeneralLinearGroup.scalar (Fin 2) (ιF 1) := by
          simp only [Nσ]
          rw [map_one, map_one, LT.TwistedNorm.sigmaNormPow_one_left]
        obtain ⟨δ₀, hδ₀, hq₀⟩ := hcover 1 1 hone
        refine hq ⟨δ₀, hδ₀, ?_⟩
        rw [hq₀, ← hrep_mk q, QuotientGroup.mk_one, eq_comm, QuotientGroup.eq_one_iff]
        exact hin
      have hFz : ∀ z : (AdeleRing (𝓞 L) L)ˣ, F (ιK (rep q) * N z) = 0 := by
        intro z
        by_contra hne
        obtain ⟨τ, hτ, hOI⟩ :=
          AutomorphicForm.exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar K c₀
            (ιK (rep q) * N z) f
        have hnn : ¬ ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
            IsNormOf K L (AdeleRing (𝓞 K) K) σ.symm (centralScalar (𝓞 K) K (ιK (rep q) * N z)) δ := by
          intro hex
          have hmem := AutomorphicForm.mem_range_idelicNorm_of_isNormOf_centralScalar_of_odd K L hodd σ.symm hgen
            _ hex
          have hmem' : ιK (rep q) ∈ N.range := by
            obtain ⟨w, hw⟩ := hmem
            exact ⟨w * z⁻¹, by rw [map_mul, map_inv, hw, mul_inv_cancel_right]⟩
          obtain ⟨bfld, hb⟩ :=
            NumberField.exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic K L (rep q) hmem'
          have hb0 : bfld ≠ 0 := by
            intro h0
            apply (rep q).ne_zero
            rw [← hb, h0, Algebra.norm_zero]
          exact hnotin ⟨Units.mk0 bfld hb0, Units.ext (by simp only [Units.coe_map, Units.val_mk0]; exact hb)⟩
        have h0 := hcvan _ hnn τ hτ _ hOI
        rcases mul_eq_zero.mp h0 with h | h
        · exact hc0 (by exact_mod_cast h)
        · exact hne h
      show ∫ z in Θ, χL z * F (ιK (rep q) * N z) ∂νZL = 0
      simp only [hFz, mul_zero, integral_zero]

  refine ⟨?_, ?_⟩
  ·
    have hfinS : (RL ∩ SL ∩ bL ⁻¹' Function.support I).Finite := by
      refine Set.Finite.of_finite_image ?_ (hinjOn.mono Set.inter_subset_left)
      refine hfinT.subset ?_
      rintro _ ⟨δ, ⟨hδ, hI⟩, rfl⟩
      exact ⟨himgT ⟨δ, hδ, rfl⟩, hI⟩
    refine hfinS.subset ?_
    rintro δ₀ ⟨hδ₀, hsupp⟩
    refine ⟨hδ₀, ?_⟩
    rw [Function.mem_support, hLterm δ₀ hδ₀] at hsupp
    exact right_ne_zero_of_mul hsupp
  · rw [hL, hK, hsplit, hcP]
    exact CentralLedgerL.finalAlgebra c₀ κ (Module.finrank K L : ℝ) CK Ξ.card _ _ hκ.ne' hℓ0
      (fun hc => finsum_mem_of_eqOn_zero fun t ht => hvan hc t ht)
      (fun h0 => finsum_mem_of_eqOn_zero fun t _ => hempty (Finset.card_eq_zero.mp h0) t)

end S_AutomorphicForm_finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer
end P2MW
export P2MW.S_AutomorphicForm_finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer (solution)
