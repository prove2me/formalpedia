-- Prove2me | solution 1 for AutomorphicForm.exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/54759fc1-3c25-52b5-a21f-89181166f9ee

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_ne_top_and_setLIntegral_twistedCentralizer_conj_integral_norm_algebraNorm_det_rpow_eq_mul_of_map_conj_eq_smul_map_toTensorGL_localHaar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_ne_top_and_setLIntegral_iUnion_detShell_twistedCentralizer_norm_algebraNorm_det_rpow_eq_mul_and_tendsto_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem
import Theorems.Thm_AutomorphicForm_exists_continuousLinearEquiv_twistedCommutant_tensor_adicCompletion_mulVec_of_forall_ne_scalar
import Theorems.Thm_AutomorphicForm_exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar
import Theorems.Thm_AutomorphicForm_isCompact_and_exists_isOpen_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar
import Theorems.Thm_AutomorphicForm_finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_mul_map_eq_scalar_and_forall_isUnit_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace"
p2m_attr_erase "instance" "NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

noncomputable section

namespace Ws46CU

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)

def Dloc (v : HeightOneSpectrum (𝓞 K)) (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  {x | x * ((δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
    ((δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
      x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)}

def Wstd (v : HeightOneSpectrum (𝓞 K)) : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  {x | ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
    AutomorphicForm.semiLocalIntegers K L v}

def Wfirst (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  {x | ∃ g : GL (Fin 2) (v.adicCompletion K),
    (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
    y⁻¹ * x * y = AutomorphicForm.toTensorGL K L (v.adicCompletion K) g}

def Wsecond (v : HeightOneSpectrum (𝓞 K)) : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  ⋃ n : ℕ, {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ s : (v.adicCompletion K)ˣ,
    Valued.v (s : v.adicCompletion K) = WithZero.exp (-(n : ℤ)) ∧
    Matrix.GeneralLinearGroup.det x =
      Units.map (Algebra.TensorProduct.includeRight :
        v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}

def Lfirst (v : HeightOneSpectrum (𝓞 K)) (δv y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  Dloc K L σ v δv ∩ {x | ∃ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
    (∀ i j, m i j ∈ v.adicCompletionIntegers K) ∧
    ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * x *
      ((y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      m.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)}

def Lsecond (v : HeightOneSpectrum (𝓞 K)) (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  {x | x ∈ Dloc K L σ v δv ∧
    (x = 0 ∨ ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) ≤ 1 ∧
      Matrix.det x = (Algebra.TensorProduct.includeRight :
        v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) (s : v.adicCompletion K))}

def FK (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ)))
    (t : HeightOneSpectrum (𝓞 K) → ℝ≥0∞) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  letI := AutomorphicForm.glBorelOf (L ⊗[K] w.adicCompletion K)
  letI := AutomorphicForm.localGLBorel K w
  ∃ y : GL (Fin 2) (L ⊗[K] w.adicCompletion K),
    AutomorphicForm.IsNormConjugator K L (w.adicCompletion K) σ
      (AdelicLevel.finComponent (𝓞 K) K w (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
      (AutomorphicForm.tensorPlace K L w δ) y ∧
    Measure.map (fun x : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L w δ)) => y⁻¹ * (x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * y) (τf' w) =
      t w • Measure.map (AutomorphicForm.toTensorGL K L (w.adicCompletion K)) (AutomorphicForm.localHaar K w)

def yv (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ)))
    (t : HeightOneSpectrum (𝓞 K) → ℝ≥0∞) (w : HeightOneSpectrum (𝓞 K)) : GL (Fin 2) (L ⊗[K] w.adicCompletion K) :=
  if h : FK K L σ δ u τf' t w then h.choose else 1

def colv (v : HeightOneSpectrum (𝓞 K)) (b : Fin 2 → L) (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Fin 2 → L ⊗[K] v.adicCompletion K :=
  x.mulVec fun i => b i ⊗ₜ[K] (1 : v.adicCompletion K)

omit K L σ in
theorem scalar_mul_comm {R : Type*} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  exact ((Matrix.scalar_commute (z : R) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) R)).eq).symm

omit K L σ in
theorem scalar_mem_center {R : Type*} [CommRing R] (z : Rˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z ∈ Subgroup.center (GL (Fin 2) R) := by
  rw [Subgroup.mem_center_iff]; intro g; exact scalar_mul_comm z g

theorem Dloc_mul_scalar (v : HeightOneSpectrum (𝓞 K)) (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (s : (L ⊗[K] v.adicCompletion K)ˣ) :
    Dloc K L σ v (δv * Matrix.GeneralLinearGroup.scalar (Fin 2) s) = Dloc K L σ v δv := by
  ext x
  simp only [Dloc, Set.mem_setOf_eq, Units.val_mul]
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = Matrix.scalar (Fin 2) (s : L ⊗[K] v.adicCompletion K) := rfl
  rw [hs]
  have hss : Matrix.scalar (Fin 2) (s : L ⊗[K] v.adicCompletion K) *
      Matrix.scalar (Fin 2) ((s⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = 1 := by
    rw [← map_mul (Matrix.scalar (Fin 2)), Units.mul_inv, map_one]
  have hcomm : ∀ M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      Matrix.scalar (Fin 2) (s : L ⊗[K] v.adicCompletion K) * M = M * Matrix.scalar (Fin 2) (s : L ⊗[K] v.adicCompletion K) :=
    fun M => (Matrix.scalar_commute (s : L ⊗[K] v.adicCompletion K) (fun r' => Commute.all _ _) M).eq
  set z := Matrix.scalar (Fin 2) (s : L ⊗[K] v.adicCompletion K) with hz
  set z' := Matrix.scalar (Fin 2) ((s⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) with hz'
  have key : ∀ A B : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K), A * z = B * z → A = B := fun A B hAB => by
    calc A = A * (z * z') := by rw [hss, Matrix.mul_one]
      _ = (A * z) * z' := by rw [Matrix.mul_assoc]
      _ = (B * z) * z' := by rw [hAB]
      _ = B := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
  set x' := x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) with hx'
  set d := ((δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) with hd
  constructor
  · intro h
    apply key
    calc x * d * z = x * (d * z) := Matrix.mul_assoc _ _ _
      _ = d * z * x' := h
      _ = d * (z * x') := Matrix.mul_assoc _ _ _
      _ = d * (x' * z) := by rw [hcomm]
      _ = d * x' * z := (Matrix.mul_assoc _ _ _).symm
  · intro h
    calc x * (d * z) = x * d * z := (Matrix.mul_assoc _ _ _).symm
      _ = d * x' * z := by rw [h]
      _ = d * (x' * z) := Matrix.mul_assoc _ _ _
      _ = d * (z * x') := by rw [hcomm]
      _ = d * z * x' := (Matrix.mul_assoc _ _ _).symm

theorem tensorPlace_delta (v : HeightOneSpectrum (𝓞 K)) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
    Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (AutomorphicForm.tensorPlaceHom K L v).toRingHom.toMonoidHom c) := by
  rw [map_mul]
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AutomorphicForm.tensorPlace_apply]
  show AutomorphicForm.tensorPlaceHom K L v (Matrix.scalar (Fin 2) (c : L ⊗[K] AdeleRing (𝓞 K) K) i j) =
    Matrix.scalar (Fin 2) (AutomorphicForm.tensorPlaceHom K L v (c : L ⊗[K] AdeleRing (𝓞 K) K)) i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij]

theorem tensorPlace_normString (v : HeightOneSpectrum (𝓞 K)) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    AutomorphicForm.normString K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ) =
      AutomorphicForm.tensorPlace K L v (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ) := by
  have hit : ∀ i : ℕ, (⇑(AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ))^[i] (AutomorphicForm.tensorPlace K L v δ) =
      AutomorphicForm.tensorPlace K L v ((⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] δ) := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, AutomorphicForm.tensorPlace_sigmaGL]
  unfold AutomorphicForm.normString
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => hit i

def uv (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom u

omit σ in
theorem finComponent_glFin_centralScalar (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (uv K u v) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.finComponent_apply, AdelicLevel.glFin_apply]
  show ((Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K) i j).2 v : v.adicCompletion K) =
    Matrix.scalar (Fin 2) ((u : AdeleRing (𝓞 K) K).2 v) i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij]; rfl

theorem isNormOf_scalar_tensorPlace (v : HeightOneSpectrum (𝓞 K)) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u)) :
    AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (uv K u v)) (AutomorphicForm.tensorPlace K L v δ) := by
  refine ⟨1, ?_⟩
  show AutomorphicForm.toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) (uv K u v)) =
    1⁻¹ * AutomorphicForm.normString K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ) * 1
  rw [inv_one, one_mul, mul_one, tensorPlace_normString, hN, AutomorphicForm.tensorPlace_toTensorGL,
    finComponent_glFin_centralScalar]

theorem isSigmaConjugate_mul_scalar_iff (v : HeightOneSpectrum (𝓞 K)) (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (s z : (L ⊗[K] v.adicCompletion K)ˣ) :
    AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ (δv * Matrix.GeneralLinearGroup.scalar (Fin 2) s)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z) ↔
      AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δv
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (z * s⁻¹)) := by
  unfold AutomorphicForm.IsSigmaConjugate
  have key : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      x⁻¹ * (δv * Matrix.GeneralLinearGroup.scalar (Fin 2) s) * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x =
        x⁻¹ * δv * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
    intro x
    simp only [mul_assoc]
    rw [(scalar_mul_comm s (AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x)).symm]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have h3 : x⁻¹ * δv * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x * Matrix.GeneralLinearGroup.scalar (Fin 2) s =
        Matrix.GeneralLinearGroup.scalar (Fin 2) z := (hx.trans (key x)).symm
    rw [map_mul, map_inv]
    exact (eq_mul_inv_of_mul_eq h3).symm
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [key x, ← hx, map_mul, map_inv, inv_mul_cancel_right]

theorem forall_not_isSigmaConjugate_mul_scalar_iff (v : HeightOneSpectrum (𝓞 K)) (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (s : (L ⊗[K] v.adicCompletion K)ˣ) :
    (∀ z : (L ⊗[K] v.adicCompletion K)ˣ, ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
        (δv * Matrix.GeneralLinearGroup.scalar (Fin 2) s) (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
    (∀ z : (L ⊗[K] v.adicCompletion K)ˣ, ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δv
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) := by
  constructor
  · intro h z hz
    refine h (z * s) ?_
    rw [isSigmaConjugate_mul_scalar_iff, mul_inv_cancel_right]
    exact hz
  · intro h z hz
    exact h _ ((isSigmaConjugate_mul_scalar_iff K L σ v δv s z).1 hz)

theorem mem_Dloc_of_mem_twistedCentralizer (v : HeightOneSpectrum (𝓞 K)) (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hx : x ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δv) :
    (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Dloc K L σ v δv := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff] at hx
  have h : x * δv = δv * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x := by
    calc x * δv = x * δv * (AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x)⁻¹ *
          AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x := by rw [inv_mul_cancel_right]
      _ = δv * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x := by rw [hx]
  have h' := congrArg (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) h
  first | simpa only [Units.val_mul] using h' | (have h_1 := h'; simp only [Units.val_mul] at h_1; exact h_1) | (have h_1 := h'; simp only [Units.val_mul] at h_1 ⊢; exact h_1) | exact (h')

def Lch (fk : HeightOneSpectrum (𝓞 K) → Prop) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (y : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] w.adicCompletion K)) (w : HeightOneSpectrum (𝓞 K)) :
    Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) :=
  if fk w then Lfirst K L σ w (AutomorphicForm.tensorPlace K L w δ) (y w)
  else Lsecond K L σ w (AutomorphicForm.tensorPlace K L w δ)

def Wch (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (fk : HeightOneSpectrum (𝓞 K) → Prop)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (y : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] w.adicCompletion K)) (w : HeightOneSpectrum (𝓞 K)) :
    Set (GL (Fin 2) (L ⊗[K] w.adicCompletion K)) :=
  if w ∈ S₁ then {x | ((x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈
    Lch K L σ fk δ y w} else Wstd K L w

def Ulocch (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (fk : HeightOneSpectrum (𝓞 K) → Prop)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (y : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] w.adicCompletion K)) (b : Fin 2 → L)
    (w : HeightOneSpectrum (𝓞 K)) : Set (Fin 2 → L ⊗[K] w.adicCompletion K) :=
  if w ∈ S₁ then colv K L w b '' Lch K L σ fk δ y w
  else {z | ∀ i, z i ∈ AutomorphicForm.semiLocalIntegers K L w}

omit σ in
def Corrch (fk : HeightOneSpectrum (𝓞 K) → Prop) (t : HeightOneSpectrum (𝓞 K) → ℝ≥0∞)
    (w : HeightOneSpectrum (𝓞 K)) (s' : ℝ) : ℝ≥0∞ :=
  if fk w then t w
  else t w * (((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ *
    (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))

section chlemmas
variable (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (fk : HeightOneSpectrum (𝓞 K) → Prop)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (y : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] w.adicCompletion K)) (b : Fin 2 → L)
    (t : HeightOneSpectrum (𝓞 K) → ℝ≥0∞) (w : HeightOneSpectrum (𝓞 K))

theorem Wch_of_not_mem (h : w ∉ S₁) : Wch K L σ S₁ fk δ y w = Wstd K L w := by simp [Wch, h]
theorem Wch_of_mem (h : w ∈ S₁) : Wch K L σ S₁ fk δ y w =
    {x | ((x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈
      Lch K L σ fk δ y w} := by simp [Wch, h]
theorem Lch_of_fk (h1 : fk w) : Lch K L σ fk δ y w = Lfirst K L σ w (AutomorphicForm.tensorPlace K L w δ) (y w) := by simp [Lch, h1]
theorem Lch_of_not_fk (h1 : ¬ fk w) : Lch K L σ fk δ y w = Lsecond K L σ w (AutomorphicForm.tensorPlace K L w δ) := by
  simp [Lch, h1]
theorem Ulocch_of_not_mem (h : w ∉ S₁) :
    Ulocch K L σ S₁ fk δ y b w = {z | ∀ i, z i ∈ AutomorphicForm.semiLocalIntegers K L w} := by simp [Ulocch, h]
theorem Ulocch_of_mem (h : w ∈ S₁) : Ulocch K L σ S₁ fk δ y b w = colv K L w b '' Lch K L σ fk δ y w := by simp [Ulocch, h]
omit σ in
theorem Corrch_of_fk (h1 : fk w) (s' : ℝ) : Corrch K fk t w s' = t w := by simp [Corrch, h1]
omit σ in
theorem Corrch_of_not_fk (h1 : ¬ fk w) (s' : ℝ) : Corrch K fk t w s' =
    t w * (((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')) := by
  simp [Corrch, h1]
end chlemmas

theorem zero_mem_Dloc (v : HeightOneSpectrum (𝓞 K)) (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (0 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Dloc K L σ v δv := by
  simp [Dloc]

theorem zero_mem_Lfirst (v : HeightOneSpectrum (𝓞 K)) (δv y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (0 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Lfirst K L σ v δv y := by
  refine ⟨zero_mem_Dloc K L σ v δv, 0, fun i j => ?_, ?_⟩
  · simp
  · simp

theorem zero_mem_Lsecond (v : HeightOneSpectrum (𝓞 K)) (δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (0 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Lsecond K L σ v δv :=
  ⟨zero_mem_Dloc K L σ v δv, Or.inl rfl⟩

omit σ in
theorem colv_zero (v : HeightOneSpectrum (𝓞 K)) (b : Fin 2 → L) :
    colv K L v b 0 = 0 := by
  simp [colv]

omit σ in
theorem continuous_colv (v : HeightOneSpectrum (𝓞 K)) (b : Fin 2 → L) : Continuous (colv K L v b) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  unfold colv
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => (continuous_apply_apply i j).mul continuous_const

omit σ in

theorem measurableSet_coe_mem_of_isCompact (v : HeightOneSpectrum (𝓞 K))
    (O : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) (hO : IsCompact O) :
    MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)]
      {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
        ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ O} := by
  letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  exact (hO.isClosed.preimage Units.continuous_val).measurableSet

omit σ in
theorem measurableSet_Wstd (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (Wstd K L v) := by
  letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  have hcl : IsClosed {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
      ∀ i j, x i j ∈ AutomorphicForm.semiLocalIntegers K L v} := by
    have : {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | ∀ i j, x i j ∈ AutomorphicForm.semiLocalIntegers K L v} =
        ⋂ i, ⋂ j, (fun x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) => x i j) ⁻¹'
          AutomorphicForm.semiLocalIntegers K L v := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (AutomorphicForm.isCompact_semiLocalIntegers K L v).isClosed.preimage (continuous_apply_apply i j)
  exact (hcl.preimage Units.continuous_val).measurableSet

omit σ in

theorem isOpen_image_colv (v : HeightOneSpectrum (𝓞 K)) (b : Fin 2 → L)
    (D V : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (Dv : Submodule (v.adicCompletion K) (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (e : Dv ≃L[v.adicCompletion K] (Fin 2 → L ⊗[K] v.adicCompletion K))
    (hDv : (Dv : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = D)
    (he : ∀ x : Dv, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).mulVec (fun i => b i ⊗ₜ[K] 1))
    (hV : IsOpen V) : IsOpen (colv K L v b '' (V ∩ D)) := by
  have hset : colv K L v b '' (V ∩ D) = (fun x : Dv => e x) '' ((Subtype.val : Dv → _) ⁻¹' V) := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxV, hxD⟩, rfl⟩
      rw [← hDv] at hxD
      exact ⟨⟨x, hxD⟩, hxV, he ⟨x, hxD⟩⟩
    · rintro ⟨x, hxV, rfl⟩
      refine ⟨x, ⟨hxV, ?_⟩, (he x).symm⟩
      rw [← hDv]; exact x.2
  rw [hset]
  exact e.isOpenMap _ (hV.preimage continuous_subtype_val)

omit σ in

theorem isOpen_image_colv' (v : HeightOneSpectrum (𝓞 K)) (b : Fin 2 → L)
    (D V : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (Dv : Submodule (v.adicCompletion K) (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (e : Dv ≃L[v.adicCompletion K] (Fin 2 → L ⊗[K] v.adicCompletion K))
    (hDv : (Dv : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = D)
    (he : ∀ x : Dv, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).mulVec (fun i => b i ⊗ₜ[K] 1))
    (hV : IsOpen V) : IsOpen (colv K L v b '' (D ∩ V)) := by
  rw [Set.inter_comm]; exact isOpen_image_colv K L v b D V Dv e hDv he hV

omit σ in

theorem colv_injOn (v : HeightOneSpectrum (𝓞 K)) (b : Fin 2 → L)
    (D : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (Dv : Submodule (v.adicCompletion K) (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (e : Dv ≃L[v.adicCompletion K] (Fin 2 → L ⊗[K] v.adicCompletion K))
    (hDv : (Dv : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = D)
    (he : ∀ x : Dv, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).mulVec (fun i => b i ⊗ₜ[K] 1)) :
    Set.InjOn (colv K L v b) D := by
  intro x hx x' hx' hxx'
  rw [← hDv] at hx hx'
  have h1 : e ⟨x, hx⟩ = e ⟨x', hx'⟩ := by rw [he, he]; exact hxx'
  have h2 := e.injective h1
  exact congrArg Subtype.val h2

theorem Dloc_tensorPlace_delta (v : HeightOneSpectrum (𝓞 K)) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Dloc K L σ v (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) c)) =
    {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
        x * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ :
                GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ :
                GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
            x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)} := by
  rw [tensorPlace_delta, Dloc_mul_scalar]; rfl

omit σ in

theorem semiLocalEval_col_eq_colv (w : HeightOneSpectrum (𝓞 K)) (b : Fin 2 → L)
    (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    (fun i => AutomorphicForm.semiLocalEval K L w
      ((((Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) t) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
        (fun i => algebraMap L (AdeleRing (𝓞 L) L) (b i)) i).2)) =
    colv K L w b ((AutomorphicForm.tensorPlace K L w t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) := by
  funext i
  have hE : ∀ i j, ((Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) t) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
        AutomorphicForm.baseChangeEquiv K L ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) i j) := fun i j => rfl
  have hsum : ((Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) t) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
        (fun i => algebraMap L (AdeleRing (𝓞 L) L) (b i)) i =
      AutomorphicForm.baseChangeEquiv K L
        (∑ j, (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) i j * (b j ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K))) := by
    simp only [Matrix.mulVec, dotProduct, hE, map_sum, map_mul, AutomorphicForm.baseChangeEquiv_tmul_one]
  rw [hsum, AutomorphicForm.semiLocalEval_snd_baseChangeEquiv, map_sum]
  simp only [colv, Matrix.mulVec, dotProduct, map_mul, AutomorphicForm.tensorPlace_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1

theorem tensorPlace_mem_twistedCentralizer (w : HeightOneSpectrum (𝓞 K)) (δ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hx : x ∈ AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :
    AutomorphicForm.tensorPlace K L w x ∈
      AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δ) := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff] at hx ⊢
  have h := congrArg (AutomorphicForm.tensorPlace K L w) hx
  rwa [map_mul, map_mul, map_inv, AutomorphicForm.tensorPlace_sigmaGL] at h

end Ws46CU

set_option hygiene false in
set_option quotPrecheck false in
local notation "δA" => (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
    Matrix.GeneralLinearGroup.scalar (Fin 2) c)

open Ws46CU in
set_option maxHeartbeats 4000000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
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

    (τa' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτa' : τa'.IsHaarMeasure)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

    (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))

    (t : HeightOneSpectrum (𝓞 K) → ENNReal) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (ht : ∀ v ∉ S₀, t v = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          t v • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        t v +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}))

    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1) :
    ∃ (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
      (W : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
      (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
      (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞),
      IsOpen U ∧ IsCompact U ∧ U.Nonempty ∧ S₀ ⊆ S₁ ∧
      (∀ v, MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (W v)) ∧
      (∀ v ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
        ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ↔
          ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
            AutomorphicForm.semiLocalIntegers K L v)) ∧
      (∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
        (∀ v ∉ S, AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
            AutomorphicForm.semiLocalIntegralSet K L v) →
          U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) =
            ∏ v ∈ S, (W v).indicator (fun _ => (1 : ℂ))
              (AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∧
      (∀ v ∉ S₁,
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         letI := AutomorphicForm.localGLBorel K v
         ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
            (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
          Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
              y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
            Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v))) ∧
      (∀ v ∈ S₁, ∀ s' : ℝ, 1 ≤ s' →
        ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v},
            ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂(τf' v) =
          Corr v s' * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹)) ∧
      (∀ v ∈ S₁, (∀ s' : ℝ, 1 ≤ s' → Corr v s' ≠ ⊤) ∧ Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1))) ∧
      (∃ n : ℕ, 0 < n ∧ ∀ x : Fin 2 → FiniteAdeleRing (𝓞 L) L,
        (∀ i, x i ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) →
          (fun i => ((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * x i) ∈ U) := by
  classical

  let P1 : HeightOneSpectrum (𝓞 K) → Prop := FK K L σ δA u τf' t
  let yw : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] w.adicCompletion K) := yv K L σ δA u τf' t

  obtain ⟨⟨z₀, hz₀⟩, -⟩ :=
    AutomorphicForm.exists_mul_map_eq_scalar_and_forall_isUnit_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
      K L h2 σ hgen δ₀ c u hN hns
  have hδ₀cen : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L) := by
    rw [hz₀]; exact Ws46CU.scalar_mem_center z₀

  have hRamFin := (AutomorphicForm.finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two
    K L h2 σ hgen δ₀ hδ₀cen).1
  have hLat := AutomorphicForm.exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar
      K L h2 σ hgen δ₀ hδ₀cen hns v hv
  have hSlat := hLat.choose_spec
  let S₁ : Finset (HeightOneSpectrum (𝓞 K)) := S₀ ∪ hRamFin.toFinset ∪ hLat.choose
  have hS₁ : S₁ = S₀ ∪ hRamFin.toFinset ∪ hLat.choose := rfl

  have hP1 : ∀ w, w ∉ S₁ → P1 w := by
    intro w hw
    have hwR : w ∉ hRamFin.toFinset := fun h => hw (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hwR
    have hns2 : ¬ ∀ z : (L ⊗[K] w.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δA)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
      rw [Ws46CU.tensorPlace_delta, Ws46CU.forall_not_isSigmaConjugate_mul_scalar_iff]
      exact hwR
    exact (hfin w).resolve_right fun h => hns2 h.1

  let U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L) :=
    {a | ∀ w : HeightOneSpectrum (𝓞 K), (fun i => AutomorphicForm.semiLocalEval K L w (a i)) ∈ Ulocch K L σ S₁ P1 δA yw v w}

  have g4 : S₀ ⊆ S₁ := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)

  have g6 : ∀ w ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L w δA)),
      ((x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Wch K L σ S₁ P1 δA yw w ↔
        ∀ i j, ((x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) i j ∈
          AutomorphicForm.semiLocalIntegers K L w) := by
    intro w hw x
    rw [Ws46CU.Wch_of_not_mem K L σ S₁ P1 δA yw w hw]
    rfl

  have g8 : ∀ w ∉ S₁,
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] w.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K w
       ∃ y : GL (Fin 2) (L ⊗[K] w.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (w.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K w (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L w δA) y ∧
        Measure.map (fun x : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L w δA)) => y⁻¹ * (x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * y) (τf' w) =
          Measure.map (AutomorphicForm.toTensorGL K L (w.adicCompletion K)) (AutomorphicForm.localHaar K w)) := by
    intro w hw
    have hw0 : w ∉ S₀ := fun h => hw (g4 h)
    obtain ⟨y, hy1, hy2⟩ := hP1 w hw
    exact ⟨y, hy1, by rw [hy2, ht w hw0, one_smul]⟩

  have hL1 : ∀ w, ∀ h1 : P1 w,
      IsCompact (Lfirst K L σ w (AutomorphicForm.tensorPlace K L w δA) (yw w)) ∧
      (∃ V : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)), IsOpen V ∧ Lfirst K L σ w (AutomorphicForm.tensorPlace K L w δA) (yw w) =
        V ∩ Dloc K L σ w (AutomorphicForm.tensorPlace K L w δA)) ∧
      (∀ x : GL (Fin 2) (L ⊗[K] w.adicCompletion K), (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Lfirst K L σ w (AutomorphicForm.tensorPlace K L w δA) (yw w) ↔
        ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Dloc K L σ w (AutomorphicForm.tensorPlace K L w δA) ∧
          ∃ g : GL (Fin 2) (w.adicCompletion K),
            (∀ i j, (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j ∈ w.adicCompletionIntegers K) ∧
            (yw w)⁻¹ * x * (yw w) = AutomorphicForm.toTensorGL K L (w.adicCompletion K) g)) := by
    intro w h1
    have hy : yw w = h1.choose := dif_pos h1
    exact AutomorphicForm.isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar K L h2 σ hgen w
      (AutomorphicForm.tensorPlace K L w δA) (τf' w) (hτf' w) (yw w) (t w) (by rw [hy]; exact h1.choose_spec.2)
      (Lfirst K L σ w (AutomorphicForm.tensorPlace K L w δA) (yw w)) rfl
  have hL2 : ∀ w, ∀ h1 : ¬ P1 w,
      IsCompact (Lsecond K L σ w (AutomorphicForm.tensorPlace K L w δA)) ∧
      (∃ V : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)), IsOpen V ∧ Lsecond K L σ w (AutomorphicForm.tensorPlace K L w δA) =
        V ∩ Dloc K L σ w (AutomorphicForm.tensorPlace K L w δA)) ∧
      (∀ x : GL (Fin 2) (L ⊗[K] w.adicCompletion K), (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Lsecond K L σ w (AutomorphicForm.tensorPlace K L w δA) ↔
        ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Dloc K L σ w (AutomorphicForm.tensorPlace K L w δA) ∧
          x ∈ ⋃ n : ℕ, {x : GL (Fin 2) (L ⊗[K] w.adicCompletion K) | ∃ s : (w.adicCompletion K)ˣ,
              Valued.v (s : w.adicCompletion K) = WithZero.exp (-(n : ℤ)) ∧
              Matrix.GeneralLinearGroup.det x =
                Units.map (Algebra.TensorProduct.includeRight :
                  w.adicCompletion K →ₐ[K] L ⊗[K] w.adicCompletion K).toRingHom.toMonoidHom s})) := by
    intro w h1
    have h2k := (hfin w).resolve_left h1
    exact AutomorphicForm.isCompact_and_exists_isOpen_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar_of_finrank_eq_two K L h2 σ hgen w
      (Ws46CU.uv K u w) (AutomorphicForm.tensorPlace K L w δA) (Ws46CU.isNormOf_scalar_tensorPlace K L σ w δA u hN)
      h2k.1 (Lsecond K L σ w (AutomorphicForm.tensorPlace K L w δA)) rfl
  have hLc : ∀ w, IsCompact (Lch K L σ P1 δA yw w) ∧
      ∃ V : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)), IsOpen V ∧ Lch K L σ P1 δA yw w = V ∩ Dloc K L σ w (AutomorphicForm.tensorPlace K L w δA) := by
    intro w
    by_cases h1 : P1 w
    · rw [Ws46CU.Lch_of_fk K L σ P1 δA yw w h1]; exact ⟨(hL1 w h1).1, (hL1 w h1).2.1⟩
    · rw [Ws46CU.Lch_of_not_fk K L σ P1 δA yw w h1]; exact ⟨(hL2 w h1).1, (hL2 w h1).2.1⟩

  have hCE : ∀ w : HeightOneSpectrum (𝓞 K),
      ∃ (Dv : Submodule (w.adicCompletion K) (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K))) (e : Dv ≃L[w.adicCompletion K] (Fin 2 → L ⊗[K] w.adicCompletion K)),
        (Dv : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K))) = Dloc K L σ w (AutomorphicForm.tensorPlace K L w δA) ∧
        ∀ x : Dv, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)).mulVec (fun i => v i ⊗ₜ[K] 1) := by
    intro w
    rw [Ws46CU.Dloc_tensorPlace_delta]
    exact AutomorphicForm.exists_continuousLinearEquiv_twistedCommutant_tensor_adicCompletion_mulVec_of_forall_ne_scalar K L h2 σ hgen δ₀ hδ₀cen hns v hv w

  have hUo : ∀ w ∈ S₁, IsOpen (Ulocch K L σ S₁ P1 δA yw v w) := by
    intro w hw
    rw [Ws46CU.Ulocch_of_mem K L σ S₁ P1 δA yw v w hw]
    obtain ⟨-, V, hV, hLV⟩ := hLc w
    obtain ⟨Dv, e, hDv, he⟩ := hCE w
    rw [hLV]
    exact Ws46CU.isOpen_image_colv K L w v _ V Dv e hDv he hV
  have hUc : ∀ w ∈ S₁, IsCompact (Ulocch K L σ S₁ P1 δA yw v w) := by
    intro w hw
    rw [Ws46CU.Ulocch_of_mem K L σ S₁ P1 δA yw v w hw]
    exact (hLc w).1.image (Ws46CU.continuous_colv K L w v)
  have hU0 : ∀ w ∈ S₁, (0 : Fin 2 → L ⊗[K] w.adicCompletion K) ∈ Ulocch K L σ S₁ P1 δA yw v w := by
    intro w hw
    rw [Ws46CU.Ulocch_of_mem K L σ S₁ P1 δA yw v w hw]
    refine ⟨0, ?_, Ws46CU.colv_zero K L w v⟩
    by_cases h1 : P1 w
    · rw [Ws46CU.Lch_of_fk K L σ P1 δA yw w h1]; exact Ws46CU.zero_mem_Lfirst K L σ w _ _
    · rw [Ws46CU.Lch_of_not_fk K L σ P1 δA yw w h1]; exact Ws46CU.zero_mem_Lsecond K L σ w _
  have hUstd : ∀ w ∉ S₁, Ulocch K L σ S₁ P1 δA yw v w = {x | ∀ i, x i ∈ AutomorphicForm.semiLocalIntegers K L w} :=
    fun w hw => Ws46CU.Ulocch_of_not_mem K L σ S₁ P1 δA yw v w hw
  have hLB := AutomorphicForm.isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem K L S₁ (Ulocch K L σ S₁ P1 δA yw v) hUo hUc hU0 hUstd U rfl

  have g5 : ∀ w : HeightOneSpectrum (𝓞 K),
      MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] w.adicCompletion K)] (Wch K L σ S₁ P1 δA yw w) := by
    intro w
    by_cases hw : w ∈ S₁
    · rw [Ws46CU.Wch_of_mem K L σ S₁ P1 δA yw w hw]
      exact Ws46CU.measurableSet_coe_mem_of_isCompact K L w _ (hLc w).1
    · rw [Ws46CU.Wch_of_not_mem K L σ S₁ P1 δA yw w hw]
      exact Ws46CU.measurableSet_Wstd K L w
  refine ⟨S₁, Wch K L σ S₁ P1 δA yw, U, Corrch K P1 t, hLB.1, hLB.2.1, hLB.2.2.1, g4, g5, g6, ?g7, g8, ?g9, ?g10, hLB.2.2.2⟩
  case g9 =>
    intro w hw s' hs'
    rw [Ws46CU.Wch_of_mem K L σ S₁ P1 δA yw w hw]
    by_cases h1 : P1 w
    · rw [Ws46CU.Corrch_of_fk K P1 t w h1, Ws46CU.Lch_of_fk K L σ P1 δA yw w h1]
      have hy : yw w = h1.choose := dif_pos h1
      have key := (AutomorphicForm.ne_top_and_setLIntegral_twistedCentralizer_conj_integral_norm_algebraNorm_det_rpow_eq_mul_of_map_conj_eq_smul_map_toTensorGL_localHaar_of_finrank_eq_two K L h2 σ w
        (AutomorphicForm.tensorPlace K L w δA) (τf' w) (hτf' w) (yw w) (t w) (by rw [hy]; exact h1.choose_spec.2)).2 s' hs'
      have hset : {x : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δA)) | (x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ {x : GL (Fin 2) (L ⊗[K] w.adicCompletion K) | (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Lfirst K L σ w (AutomorphicForm.tensorPlace K L w δA) (yw w)}} =
          {x : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δA)) | ∃ g : GL (Fin 2) (w.adicCompletion K),
            (∀ i j, (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j ∈ w.adicCompletionIntegers K) ∧
            (yw w)⁻¹ * (x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) * (yw w) = AutomorphicForm.toTensorGL K L (w.adicCompletion K) g} := by
        ext x
        simp only [Set.mem_setOf_eq]
        rw [(hL1 w h1).2.2 (x : GL (Fin 2) (L ⊗[K] w.adicCompletion K))]
        exact ⟨fun h => h.2, fun h => ⟨Ws46CU.mem_Dloc_of_mem_twistedCentralizer K L σ w _ _ x.2, h⟩⟩
      rw [hset]
      exact key
    · rw [Ws46CU.Corrch_of_not_fk K P1 t w h1, Ws46CU.Lch_of_not_fk K L σ P1 δA yw w h1]
      have h2k := (hfin w).resolve_left h1
      have key := (AutomorphicForm.ne_top_and_setLIntegral_iUnion_detShell_twistedCentralizer_norm_algebraNorm_det_rpow_eq_mul_and_tendsto_of_not_isSigmaConjugate_scalar_of_finrank_eq_two K L h2 σ hgen w
        (Ws46CU.uv K u w) (AutomorphicForm.tensorPlace K L w δA) (Ws46CU.isNormOf_scalar_tensorPlace K L σ w δA u hN)
        h2k.1 (τf' w) (hτf' w) (t w) h2k.2).2.1 s' hs'
      have hset : {x : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δA)) | (x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ {x : GL (Fin 2) (L ⊗[K] w.adicCompletion K) | (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Lsecond K L σ w (AutomorphicForm.tensorPlace K L w δA)}} =
          {x : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δA)) | (x : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ ⋃ n : ℕ, {x : GL (Fin 2) (L ⊗[K] w.adicCompletion K) | ∃ s : (w.adicCompletion K)ˣ,
              Valued.v (s : w.adicCompletion K) = WithZero.exp (-(n : ℤ)) ∧
              Matrix.GeneralLinearGroup.det x =
                Units.map (Algebra.TensorProduct.includeRight :
                  w.adicCompletion K →ₐ[K] L ⊗[K] w.adicCompletion K).toRingHom.toMonoidHom s}} := by
        ext x
        simp only [Set.mem_setOf_eq]
        rw [(hL2 w h1).2.2 (x : GL (Fin 2) (L ⊗[K] w.adicCompletion K))]
        exact ⟨fun h => h.2, fun h => ⟨Ws46CU.mem_Dloc_of_mem_twistedCentralizer K L σ w _ _ x.2, h⟩⟩
      rw [hset]
      exact key
  case g10 =>
    intro w hw
    by_cases h1 : P1 w
    · have hC : Corrch K P1 t w = fun _ => t w := funext fun s' => Ws46CU.Corrch_of_fk K P1 t w h1 s'
      rw [hC]
      have hy : yw w = h1.choose := dif_pos h1
      have key := (AutomorphicForm.ne_top_and_setLIntegral_twistedCentralizer_conj_integral_norm_algebraNorm_det_rpow_eq_mul_of_map_conj_eq_smul_map_toTensorGL_localHaar_of_finrank_eq_two K L h2 σ w
        (AutomorphicForm.tensorPlace K L w δA) (τf' w) (hτf' w) (yw w) (t w) (by rw [hy]; exact h1.choose_spec.2)).1
      exact ⟨fun _ _ => key, tendsto_const_nhds⟩
    · have hC : Corrch K P1 t w = fun s' => t w * (((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) - 1)⁻¹ *
          (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s')) :=
        funext fun s' => Ws46CU.Corrch_of_not_fk K P1 t w h1 s'
      rw [hC]
      have h2k := (hfin w).resolve_left h1
      have key := AutomorphicForm.ne_top_and_setLIntegral_iUnion_detShell_twistedCentralizer_norm_algebraNorm_det_rpow_eq_mul_and_tendsto_of_not_isSigmaConjugate_scalar_of_finrank_eq_two K L h2 σ hgen w
        (Ws46CU.uv K u w) (AutomorphicForm.tensorPlace K L w δA) (Ws46CU.isNormOf_scalar_tensorPlace K L σ w δA u hN)
        h2k.1 (τf' w) (hτf' w) (t w) h2k.2
      exact ⟨key.2.2.1, key.2.2.2⟩
  case g7 =>
    intro S hS t hint
    have hxT : ∀ w, (AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∈ AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ (AutomorphicForm.tensorPlace K L w δA) :=
      fun w => Ws46CU.tensorPlace_mem_twistedCentralizer K L σ w δA _ t.2
    have hxD : ∀ w, (((AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Dloc K L σ w (AutomorphicForm.tensorPlace K L w δA) :=
      fun w => Ws46CU.mem_Dloc_of_mem_twistedCentralizer K L σ w _ _ (hxT w)
    have hdict : ∀ w, (fun i => AutomorphicForm.semiLocalEval K L w ((fun i => ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) i)) =
        colv K L w v (((AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) :=
      fun w => Ws46CU.semiLocalEval_col_eq_colv K L w v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))

    have hmemS₁ : ∀ w ∈ S₁, (colv K L w v (((AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Ulocch K L σ S₁ P1 δA yw v w ↔
        (AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∈ Wch K L σ S₁ P1 δA yw w) := by
      intro w hw
      rw [Ws46CU.Ulocch_of_mem K L σ S₁ P1 δA yw v w hw, Ws46CU.Wch_of_mem K L σ S₁ P1 δA yw w hw,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨m, hm, hmeq⟩
        obtain ⟨Dv, e, hDv, he⟩ := hCE w
        have hmD : m ∈ Dloc K L σ w (AutomorphicForm.tensorPlace K L w δA) := by
          obtain ⟨-, V, -, hLV⟩ := hLc w
          rw [hLV] at hm
          exact hm.2
        have hm' := Ws46CU.colv_injOn K L w v _ Dv e hDv he hmD (hxD w) hmeq
        rw [← hm']
        exact hm
      · intro h
        exact ⟨_, h, rfl⟩

    have hmem_std : ∀ w ∉ S₁, (colv K L w v (((AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈ Ulocch K L σ S₁ P1 δA yw v w ↔
        ∀ i j, (((AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) i j ∈ AutomorphicForm.semiLocalIntegers K L w) := by
      intro w hw
      rw [Ws46CU.Ulocch_of_not_mem K L σ S₁ P1 δA yw v w hw, Set.mem_setOf_eq]
      have hwL : w ∉ hLat.choose := fun h => hw (Finset.mem_union_right _ h)
      have hD := hxD w
      rw [Ws46CU.Dloc_tensorPlace_delta] at hD
      exact hSlat w hwL _ hD

    have hU_iff : (fun i => ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) ∈ U ↔ ∀ w ∈ S, (AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∈ Wch K L σ S₁ P1 δA yw w := by
      constructor
      · intro h w hwS
        have hw' : (fun i => AutomorphicForm.semiLocalEval K L w ((fun i => ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) i)) ∈ Ulocch K L σ S₁ P1 δA yw v w := h w
        rw [hdict w] at hw'
        by_cases hw1 : w ∈ S₁
        · exact (hmemS₁ w hw1).1 hw'
        · rw [Ws46CU.Wch_of_not_mem K L σ S₁ P1 δA yw w hw1]
          exact (hmem_std w hw1).1 hw'
      · intro h w
        show (fun i => AutomorphicForm.semiLocalEval K L w ((fun i => ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) i)) ∈ Ulocch K L σ S₁ P1 δA yw v w
        rw [hdict w]
        by_cases hwS : w ∈ S
        · by_cases hw1 : w ∈ S₁
          · exact (hmemS₁ w hw1).2 (h w hwS)
          · have h' := h w hwS
            rw [Ws46CU.Wch_of_not_mem K L σ S₁ P1 δA yw w hw1] at h'
            exact (hmem_std w hw1).2 h'
        · have hw1 : w ∉ S₁ := fun h' => hwS (hS h')
          exact (hmem_std w hw1).2 (AutomorphicForm.mem_integralUnitsSet.1 (hint w hwS)).1
    have hR : ∏ w ∈ S, (Wch K L σ S₁ P1 δA yw w).indicator (fun _ => (1 : ℂ)) (AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) =
        if (∀ w ∈ S, (AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∈ Wch K L σ S₁ P1 δA yw w) then 1 else 0 := by
      simp only [Set.indicator_apply]
      exact Finset.prod_boole
    rw [Set.indicator_apply, hR]
    by_cases hall : (fun i => ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) ∈ U
    · rw [if_pos hall, if_pos (hU_iff.1 hall)]
    · rw [if_neg hall, if_neg (fun h => hall (hU_iff.2 h))]

end

end S_AutomorphicForm_exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two (solution)
