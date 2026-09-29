-- Prove2me | solution 1 for AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/69a4d764-00a4-536f-a338-1fe0d1b9f302

import Definitions.Def_AutomorphicForm_TwistedOrbital
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
import Theorems.Thm_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace
import Theorems.Thm_NumberField_unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq
import Theorems.Thm_NumberField_finite_and_ncard_places_not_mem_range_norm_add_ne_one_of_forall_mem_zpowers_of_prime
import Theorems.Thm_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex"
p2m_attr_erase "instance" "ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen"
p2m_attr_erase "simp" "complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace K56BPS

open scoped TensorProduct

section NBC

open scoped TensorProduct.RightActions

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem repr_tmul {B : Type*} [CommRing B] [Algebra K B] (b : Module.Basis n K L) (l : L) (x : B) (i : n) :
    (b.rightBaseChange L (B := B)).repr (l ⊗ₜ[K] x) i = b.repr l i • x := by
  classical
  conv_lhs => rw [← b.sum_repr l]
  simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Module.Basis.rightBaseChange_repr, Finsupp.single_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => if_neg hk)]
  · rw [if_pos rfl]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem repr_map {E F : Type*} [CommRing E] [Algebra K E] [CommRing F] [Algebra K F]
    (b : Module.Basis n K L) (φ : E →ₐ[K] F) (y : L ⊗[K] E) (i : n) :
    (b.rightBaseChange L (B := F)).repr (Algebra.TensorProduct.map (AlgHom.id K L) φ y) i =
      φ ((b.rightBaseChange L (B := E)).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul l e =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul, repr_tmul, Algebra.smul_def,
        Algebra.smul_def, map_mul, φ.commutes]
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]

theorem map_norm_eq_norm_map [FiniteDimensional K L] {E F : Type*} [CommRing E] [Algebra K E]
    [CommRing F] [Algebra K F] (ι : E →ₐ[K] F) (x : L ⊗[K] E) :
    ι (Algebra.norm E x) = Algebra.norm F (Algebra.TensorProduct.map (AlgHom.id K L) ι x) := by
  classical
  let b := Module.finBasis K L
  rw [Algebra.norm_eq_matrix_det (b.rightBaseChange L (B := E)) x,
    Algebra.norm_eq_matrix_det (b.rightBaseChange L (B := F)), AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.rightBaseChange_apply, Module.Basis.rightBaseChange_apply]
  have hm : Algebra.TensorProduct.map (AlgHom.id K L) ι x * b j ⊗ₜ[K] (1 : F)
      = Algebra.TensorProduct.map (AlgHom.id K L) ι (x * b j ⊗ₜ[K] (1 : E)) := by
    rw [map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  rw [hm, repr_map]

theorem norm_tmul_one [FiniteDimensional K L] {A : Type*} [CommRing A] [Algebra K A] (l : L) :
    Algebra.norm A (l ⊗ₜ[K] (1 : A)) = algebraMap K A (Algebra.norm K l) := by
  classical
  let b := Module.finBasis K L
  rw [Algebra.norm_eq_matrix_det (b.rightBaseChange L (B := A)), Algebra.norm_eq_matrix_det b,
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.rightBaseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, repr_tmul, Algebra.smul_def, mul_one]

theorem mem_normSet_mul {A : Type*} [CommRing A] [Algebra K A] {a b : A}
    (ha : a ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)))
    (hb : b ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A))) :
    a * b ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  exact ⟨s * t, by simp [map_mul]⟩

theorem mem_normSet_inv {A : Type*} [CommRing A] [Algebra K A] (u : Aˣ)
    (hu : (u : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A))) :
    ((u⁻¹ : Aˣ) : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) := by
  obtain ⟨t, ht⟩ := hu
  refine ⟨t⁻¹, ?_⟩
  show Algebra.norm A ((t⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = ((u⁻¹ : Aˣ) : A)
  symm
  apply Units.inv_eq_of_mul_eq_one_left
  rw [← ht]
  show Algebra.norm A ((t⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * Algebra.norm A (t : L ⊗[K] A) = 1
  rw [← map_mul, Units.inv_mul, map_one]

theorem mem_normSet_one {A : Type*} [CommRing A] [Algebra K A] :
    (1 : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) :=
  ⟨1, by simp⟩

theorem algebraMap_norm_mem_normSet [FiniteDimensional K L] {A : Type*} [CommRing A] [Algebra K A]
    (l : L) (hl : l ≠ 0) :
    algebraMap K A (Algebra.norm K l) ∈
      Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) := by
  have hu : IsUnit (l ⊗ₜ[K] (1 : A) : L ⊗[K] A) :=
    (isUnit_iff_ne_zero.mpr hl).map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
  obtain ⟨t, ht⟩ := hu
  exact ⟨t, by rw [← norm_tmul_one, ← ht]⟩

theorem map_mem_normSet [FiniteDimensional K L] {E F : Type*} [CommRing E] [Algebra K E]
    [CommRing F] [Algebra K F] (ι : E →ₐ[K] F) {a : E}
    (ha : a ∈ Set.range (fun t : (L ⊗[K] E)ˣ => Algebra.norm E (t : L ⊗[K] E))) :
    ι a ∈ Set.range (fun t : (L ⊗[K] F)ˣ => Algebra.norm F (t : L ⊗[K] F)) := by
  obtain ⟨t, rfl⟩ := ha
  refine ⟨Units.map (Algebra.TensorProduct.map (AlgHom.id K L) ι : L ⊗[K] E →* L ⊗[K] F) t, ?_⟩
  show Algebra.norm F (Algebra.TensorProduct.map (AlgHom.id K L) ι (t : L ⊗[K] E)) = ι (Algebra.norm E (t : L ⊗[K] E))
  rw [map_norm_eq_norm_map]

theorem exists_norm_eq_of_mem_normSet [FiniteDimensional K L] {A : Type*} [CommRing A] [Algebra K A] {a : A}
    (ha : a ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A))) :
    ∃ z : A ⊗[K] L, Algebra.norm A z = a := by
  obtain ⟨t, rfl⟩ := ha
  refine ⟨(TensorProduct.RightActions.Algebra.TensorProduct.comm K A L).symm (t : L ⊗[K] A), ?_⟩
  show Algebra.norm A ((TensorProduct.RightActions.Algebra.TensorProduct.comm K A L).symm (t : L ⊗[K] A)) =
    Algebra.norm A (t : L ⊗[K] A)
  rw [← Algebra.norm_eq_of_algEquiv (TensorProduct.RightActions.Algebra.TensorProduct.comm K A L)
    ((TensorProduct.RightActions.Algebra.TensorProduct.comm K A L).symm (t : L ⊗[K] A)), AlgEquiv.apply_symm_apply]

end NBC

section Adelic

open scoped TensorProduct.RightActions
open AutomorphicForm M4aHerbrand.GenuineDescent

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem adelicNorm_baseChangeEquiv (t : L ⊗[K] AdeleRing (𝓞 K) K) :
    (genuineBaseChange K L).adelicNorm (baseChangeEquiv K L t) = Algebra.norm (AdeleRing (𝓞 K) K) t := by
  letI inst : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  have he : RingHom.comp (algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L))
      ↑(RingEquiv.refl (AdeleRing (𝓞 K) K)) =
      RingHom.comp ↑(baseChangeEquiv K L) (algebraMap (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K)) := by
    ext a
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.refl_apply,
      TensorProduct.RightActions.algebraMap_eval, baseChangeEquiv_one_tmul]
    rfl
  have h := Algebra.norm_eq_of_equiv_equiv (RingEquiv.refl _) (baseChangeEquiv K L) he t
  rw [h]
  rfl

variable [FiniteDimensional K L]

theorem idelicNorm_place_mem (w : (AdeleRing (𝓞 L) L)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((((genuineBaseChange K L).idelicNorm w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) ∈
      Set.range (fun t : (L ⊗[K] v.adicCompletion K)ˣ =>
        Algebra.norm (v.adicCompletion K) (t : L ⊗[K] v.adicCompletion K)) := by
  set t : L ⊗[K] AdeleRing (𝓞 K) K := (baseChangeEquiv K L).symm (w : AdeleRing (𝓞 L) L) with ht
  have htu : IsUnit t := (Units.isUnit w).map (baseChangeEquiv K L).symm
  have hN : (((genuineBaseChange K L).idelicNorm w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      Algebra.norm (AdeleRing (𝓞 K) K) t := by
    rw [← adelicNorm_baseChangeEquiv, ht, RingEquiv.apply_symm_apply]
    rfl
  rw [hN]
  obtain ⟨u, hu⟩ := htu.map (tensorPlaceHom K L v)
  refine ⟨u, ?_⟩
  show Algebra.norm (v.adicCompletion K) (u : L ⊗[K] v.adicCompletion K) = _
  rw [hu, show tensorPlaceHom K L v t = Algebra.TensorProduct.map (AlgHom.id K L) (adelePlaceAlgHom K v) t from rfl,
    ← map_norm_eq_norm_map]
  rfl

theorem idelicNorm_arch_mem (w : (AdeleRing (𝓞 L) L)ˣ) :
    ((((genuineBaseChange K L).idelicNorm w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) ∈
      Set.range (fun t : (L ⊗[K] InfiniteAdeleRing K)ˣ =>
        Algebra.norm (InfiniteAdeleRing K) (t : L ⊗[K] InfiniteAdeleRing K)) := by
  set t : L ⊗[K] AdeleRing (𝓞 K) K := (baseChangeEquiv K L).symm (w : AdeleRing (𝓞 L) L) with ht
  have htu : IsUnit t := (Units.isUnit w).map (baseChangeEquiv K L).symm
  have hN : (((genuineBaseChange K L).idelicNorm w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      Algebra.norm (AdeleRing (𝓞 K) K) t := by
    rw [← adelicNorm_baseChangeEquiv, ht, RingEquiv.apply_symm_apply]
    rfl
  rw [hN]
  obtain ⟨u, hu⟩ := htu.map (tensorArchHom K L)
  refine ⟨u, ?_⟩
  show Algebra.norm (InfiniteAdeleRing K) (u : L ⊗[K] InfiniteAdeleRing K) = _
  rw [hu, show tensorArchHom K L t = Algebra.TensorProduct.map (AlgHom.id K L) (adeleArchAlgHom K) t from rfl,
    ← map_norm_eq_norm_map]
  rfl

end Adelic

section Components

open AutomorphicForm NumberField.AdelicLevel
open LanglandsTunnell.CubicInduction (diagUnits2)

variable (K : Type) [Field K] [NumberField K]

noncomputable abbrev placeUnits (v : HeightOneSpectrum (𝓞 K)) : (AdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map ((adelePlaceAlgHom K v).toRingHom : AdeleRing (𝓞 K) K →* v.adicCompletion K)

noncomputable abbrev archUnits : (AdeleRing (𝓞 K) K)ˣ →* (InfiniteAdeleRing K)ˣ :=
  Units.map ((adeleArchAlgHom K).toRingHom : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K)

theorem finComponent_glFin_centralScalar_mul_diagUnits2 (Z U : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K (centralScalar (𝓞 K) K Z * diagUnits2 U 1)) =
      diagUnits2 (placeUnits K v (Z * U)) (placeUnits K v Z) := by
  ext i j
  rw [finComponent_apply]
  fin_cases i <;> fin_cases j <;>
    simp [glFin, centralScalar, Matrix.mul_apply, Fin.sum_univ_two,
      LanglandsTunnell.CubicInduction.coe_diagUnits2, placeUnits] <;> rfl

theorem glArch_centralScalar_mul_diagUnits2 (Z U : (AdeleRing (𝓞 K) K)ˣ) :
    glArch (𝓞 K) K (centralScalar (𝓞 K) K Z * diagUnits2 U 1) =
      diagUnits2 (archUnits K (Z * U)) (archUnits K Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glArch, centralScalar, Matrix.mul_apply, Fin.sum_univ_two,
      LanglandsTunnell.CubicInduction.coe_diagUnits2, archUnits] <;> rfl

end Components

section Units

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

theorem isUnit_sub_of_ne_one {A : Type} [CommRing A] [Algebra K A]
    (φ : AdeleRing (𝓞 K) K →ₐ[K] A) (Z : (AdeleRing (𝓞 K) K)ˣ) (u : Kˣ) (hu : (u : K) ≠ 1) :
    IsUnit (((Units.map (φ.toRingHom : AdeleRing (𝓞 K) K →* A)
        (Z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : Aˣ) : A) -
      ((Units.map (φ.toRingHom : AdeleRing (𝓞 K) K →* A) Z : Aˣ) : A)) := by
  have h : (((Units.map (φ.toRingHom : AdeleRing (𝓞 K) K →* A)
        (Z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : Aˣ) : A) -
      ((Units.map (φ.toRingHom : AdeleRing (𝓞 K) K →* A) Z : Aˣ) : A))
      = φ (Z : AdeleRing (𝓞 K) K) * algebraMap K A ((u : K) - 1) := by
    simp only [Units.coe_map, Units.val_mul, MonoidHom.coe_coe]
    rw [map_mul, map_sub, map_one, ← φ.commutes (u : K)]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring
  rw [h]
  exact ((Units.isUnit Z).map φ).mul
    ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu)).map (algebraMap K A))

end Units

end K56BPS

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (γ : GL (Fin 2) K)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (hγN : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 ∈ Set.range (Algebra.norm K : L → K) ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ Set.range (Algebra.norm K : L → K))
    (uγ dγ : Kˣ)
    (huγ : (uγ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
    (hdγ : (dγ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (hzK : z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range)
    (hzN : z ∉ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v ∈ P, ¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
            (AutomorphicForm.centralScalar (𝓞 K) K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) uγ) 1))) δ) ∧
      (P.Nonempty ∨
        ¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
          (AdelicLevel.glArch (𝓞 K) K
            (AutomorphicForm.centralScalar (𝓞 K) K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) uγ) 1)) δ) ∧
      ¬ (P.card = 1 ∧ ¬ (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
          (AdelicLevel.glArch (𝓞 K) K
            (AutomorphicForm.centralScalar (𝓞 K) K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) uγ) 1)) δ)) := by
  classical

  set ιK : K →* AdeleRing (𝓞 K) K := (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) with hιK
  set Zd : (AdeleRing (𝓞 K) K)ˣ := z * Units.map ιK dγ with hZd
  set U : (AdeleRing (𝓞 K) K)ˣ := Units.map ιK uγ with hU
  by_cases hb : ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K Zd * diagUnits2 U 1)) δ
  swap
  · exact ⟨∅, by simp, Or.inr hb, by simp⟩

  have huγ1 : (uγ : K) ≠ 1 := by rw [huγ]; exact hγ.2.2
  obtain ⟨ℓ, hℓ⟩ := hγN.2
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    apply dγ.ne_zero
    rw [hdγ, ← hℓ, h, Algebra.norm_zero]
  have hdγN : ∀ (A : Type) [CommRing A] [Algebra K A],
      algebraMap K A (dγ : K) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) := by
    intro A _ _
    rw [hdγ, ← hℓ]
    exact K56BPS.algebraMap_norm_mem_normSet ℓ hℓ0

  obtain ⟨y, hy, nw, hnw, hz⟩ := Subgroup.mem_sup.1 hzK
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hy
  obtain ⟨w', rfl⟩ := MonoidHom.mem_range.1 hnw
  have hZd' : Zd = Units.map ιK k *
      ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w' * Units.map ιK dγ) := by
    rw [hZd, ← hz, mul_assoc]

  have key : ∀ (A : Type) [CommRing A] [Algebra K A] (φ : AdeleRing (𝓞 K) K →ₐ[K] A),
      (φ (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w' :
          (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ∈
        Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) →
      ((Units.map (φ.toRingHom : AdeleRing (𝓞 K) K →* A) Zd : Aˣ) : A) ∈
        Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) →
      algebraMap K A (k : K) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) := by
    intro A _ _ φ hN hZ
    set φu : (AdeleRing (𝓞 K) K)ˣ →* Aˣ := Units.map (φ.toRingHom : AdeleRing (𝓞 K) K →* A) with hφu
    set m : Aˣ := φu ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w' * Units.map ιK dγ)
      with hm
    have hmN : (m : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) := by
      rw [hm, map_mul, Units.val_mul]
      refine K56BPS.mem_normSet_mul hN ?_
      have : ((φu (Units.map ιK dγ) : Aˣ) : A) = algebraMap K A (dγ : K) := by
        rw [hφu, hιK]
        simp only [Units.coe_map, MonoidHom.coe_coe]
        exact φ.commutes (dγ : K)
      rw [this]
      exact hdγN A
    have hk : ((φu (Units.map ιK k) : Aˣ) : A) = algebraMap K A (k : K) := by
      rw [hφu, hιK]
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.coe_coe]
      exact φ.commutes (k : K)
    rw [← hk, ← mul_inv_cancel_right (φu (Units.map ιK k)) m, ← map_mul, ← hZd', Units.val_mul]
    exact K56BPS.mem_normSet_mul hZ (K56BPS.mem_normSet_inv m hmN)

  have hkinf : algebraMap K (InfiniteAdeleRing K) (k : K) ∈
      Set.range (fun t : (L ⊗[K] InfiniteAdeleRing K)ˣ =>
        Algebra.norm (InfiniteAdeleRing K) (t : L ⊗[K] InfiniteAdeleRing K)) := by
    refine key (InfiniteAdeleRing K) (AutomorphicForm.adeleArchAlgHom K)
      (K56BPS.idelicNorm_arch_mem K L w') ?_
    rw [K56BPS.glArch_centralScalar_mul_diagUnits2] at hb
    exact ((AutomorphicForm.exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub K L σ hgen
      (InfiniteAdeleRing K) _ _ (K56BPS.isUnit_sub_of_ne_one K (AutomorphicForm.adeleArchAlgHom K) Zd uγ huγ1)).1 hb).2
  have hkw : ∀ w : InfinitePlace K, algebraMap K w.Completion (k : K) ∈
      Set.range (fun t : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (t : L ⊗[K] w.Completion)) := by
    intro w
    have h := (NumberField.InfiniteAdeleRing.mem_range_norm_tensorProduct_iff_forall_infinitePlace K L
      (Units.map (algebraMap K (InfiniteAdeleRing K) : K →* InfiniteAdeleRing K) k)).1
      (by simpa only [Units.coe_map, MonoidHom.coe_coe] using hkinf) w
    simp only [Units.coe_map, MonoidHom.coe_coe] at h
    exact h

  obtain ⟨hfin, hcount⟩ :=
    NumberField.finite_and_ncard_places_not_mem_range_norm_add_ne_one_of_forall_mem_zpowers_of_prime K L σ hgen hprime k
  have hSinf : {w : InfinitePlace K | algebraMap K w.Completion (k : K) ∉
      Set.range (fun x : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (x : L ⊗[K] w.Completion))} = ∅ :=
    Set.eq_empty_of_forall_notMem fun w hw => hw (hkw w)
  rw [hSinf, Set.ncard_empty, add_zero, Set.ncard_eq_toFinset_card _ hfin] at hcount

  have hPne : hfin.toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hP0
    apply hzN
    have hall : ∀ v : HeightOneSpectrum (𝓞 K), algebraMap K (v.adicCompletion K) (k : K) ∈
        Set.range (fun x : (L ⊗[K] v.adicCompletion K)ˣ =>
          Algebra.norm (v.adicCompletion K) (x : L ⊗[K] v.adicCompletion K)) := by
      intro v
      by_contra hv
      have hmem : v ∈ hfin.toFinset := hfin.mem_toFinset.2 hv
      rw [hP0] at hmem
      exact absurd hmem (Finset.notMem_empty v)
    obtain ⟨w₁, hw₁⟩ := NumberField.unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq K L k
      (fun v => K56BPS.exists_norm_eq_of_mem_normSet (hall v)) (K56BPS.exists_norm_eq_of_mem_normSet hkinf)
    refine ⟨w₁ * w', ?_⟩
    rw [map_mul, hw₁, hz]
  refine ⟨hfin.toFinset, ?_, Or.inl hPne, fun h => hcount h.1⟩
  intro v hv hXv
  have hkv := (hfin.mem_toFinset.1 hv)
  apply hkv
  refine key (v.adicCompletion K) (AutomorphicForm.adelePlaceAlgHom K v) (K56BPS.idelicNorm_place_mem K L w' v) ?_
  rw [K56BPS.finComponent_glFin_centralScalar_mul_diagUnits2] at hXv
  exact ((AutomorphicForm.exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub K L σ hgen
    (v.adicCompletion K) _ _ (K56BPS.isUnit_sub_of_ne_one K (AutomorphicForm.adelePlaceAlgHom K v) Zd uγ huγ1)).1 hXv).2

end S_AutomorphicForm_exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime (solution)
