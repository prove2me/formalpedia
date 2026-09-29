-- Prove2me | solution 1 for AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0dee5ce4-d386-58a1-9f24-bd9065200e6e

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
import Theorems.Thm_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
import Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached
import Theorems.Thm_LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_structureSheafSections_eq_finrank_span_germ
import Theorems.Thm_AlgebraicCurve_existsUnique_centre_place_of_isProper
import Theorems.Thm_AlgebraicCurve_exists_centre_and_finite_setOf_centre_of_isClosed_singleton
import Theorems.Thm_AlgebraicCurve_germ_mem_lSpaceOn_setOf_exists_centre_zero
import Theorems.Thm_AlgebraicCurve_isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range
import Theorems.Thm_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
import Theorems.Thm_AlgebraicCurve_not_isAffine_of_isProper_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise
noncomputable section

namespace PAGEGSAux

universe w

section Pi
variable {k : Type u} [Field k] {ι : Type v} (M : ι → Type w)
  [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

theorem finiteDimensional_pi_and_natCard_le
    (hfin : {i | Nontrivial (M i)}.Finite) (hfd : ∀ i, FiniteDimensional k (M i)) :
    FiniteDimensional k ((i : ι) → M i) ∧
      Nat.card {i | Nontrivial (M i)} ≤ Module.finrank k ((i : ι) → M i) := by
  classical
  set s : Set ι := {i | Nontrivial (M i)} with hs
  haveI : Fintype s := hfin.fintype
  have hzero : ∀ i, i ∉ s → ∀ x : M i, x = 0 := by
    intro i hi x
    have : Subsingleton (M i) := not_nontrivial_iff_subsingleton.mp hi
    exact Subsingleton.elim _ _
  let e : ((i : ι) → M i) ≃ₗ[k] ((i : s) → M i.1) :=
    { toFun := fun f i => f i.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun g i => if h : i ∈ s then g ⟨i, h⟩ else 0
      left_inv := fun f => by
        funext i
        by_cases h : i ∈ s
        · show (if h : i ∈ s then f i else 0) = f i
          rw [dif_pos h]
        · show (if h : i ∈ s then f i else 0) = f i
          rw [dif_neg h, hzero i h (f i)]
      right_inv := fun g => by
        funext i
        show (if h : (i.1 : ι) ∈ s then g ⟨i.1, h⟩ else 0) = g i
        rw [dif_pos i.2] }
  haveI : ∀ i : s, FiniteDimensional k (M i.1) := fun i => hfd i.1
  have hfdP : FiniteDimensional k ((i : ι) → M i) := LinearEquiv.finiteDimensional e.symm
  refine ⟨hfdP, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Nat.card_eq_fintype_card]
  calc Fintype.card s = ∑ _i : s, 1 := by simp
    _ ≤ ∑ i : s, Module.finrank k (M i.1) := Finset.sum_le_sum fun i _ => ?_
  haveI : Nontrivial (M i.1) := i.2
  exact Module.finrank_pos

end Pi

section SubDiff
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

def subDiff (P₀ P₁ P₀₁ : Submodule k V) (h₀ : P₀ ≤ P₀₁) (h₁ : P₁ ≤ P₀₁) :
    (↥P₀ × ↥P₁) →ₗ[k] ↥P₀₁ :=
  (Submodule.inclusion h₁).comp (LinearMap.snd k ↥P₀ ↥P₁) -
    (Submodule.inclusion h₀).comp (LinearMap.fst k ↥P₀ ↥P₁)

variable (P₀ P₁ P₀₁ : Submodule k V) (h₀ : P₀ ≤ P₀₁) (h₁ : P₁ ≤ P₀₁)

@[scoped simp] theorem coe_subDiff_apply (p : ↥P₀ × ↥P₁) :
    (subDiff P₀ P₁ P₀₁ h₀ h₁ p : V) = (p.2 : V) - p.1 := rfl

def kerSubDiffEquiv : ↥(LinearMap.ker (subDiff P₀ P₁ P₀₁ h₀ h₁)) ≃ₗ[k] ↥(P₀ ⊓ P₁) where
  toFun p := ⟨(p.1.1 : V), p.1.1.2, by
    have h : (subDiff P₀ P₁ P₀₁ h₀ h₁ p.1 : V) = 0 := by
      rw [LinearMap.mem_ker.mp p.2]; rfl
    rw [coe_subDiff_apply, sub_eq_zero] at h
    rw [← h]; exact p.1.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨(⟨f, f.2.1⟩, ⟨f, f.2.2⟩), by
    rw [LinearMap.mem_ker]; apply Subtype.ext; simp⟩
  left_inv p := by
    apply Subtype.ext; apply Prod.ext
    · rfl
    · apply Subtype.ext
      have h : (subDiff P₀ P₁ P₀₁ h₀ h₁ p.1 : V) = 0 := by
        rw [LinearMap.mem_ker.mp p.2]; rfl
      rw [coe_subDiff_apply, sub_eq_zero] at h
      exact h.symm
  right_inv f := rfl

theorem range_subDiff :
    LinearMap.range (subDiff P₀ P₁ P₀₁ h₀ h₁) = (P₀ ⊔ P₁).comap P₀₁.subtype := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    simp only [Submodule.mem_comap, Submodule.coe_subtype, coe_subDiff_apply]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right p.2.2) (Submodule.mem_sup_left p.1.2)
  · intro x hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    refine ⟨(-⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    simp only [coe_subDiff_apply]
    rw [← hab]; simp; abel

theorem finrank_ker_subDiff :
    Module.finrank k ↥(LinearMap.ker (subDiff P₀ P₁ P₀₁ h₀ h₁)) = Module.finrank k ↥(P₀ ⊓ P₁) :=
  (kerSubDiffEquiv P₀ P₁ P₀₁ h₀ h₁).finrank_eq

theorem finrank_quotient_range_subDiff :
    Module.finrank k (↥P₀₁ ⧸ LinearMap.range (subDiff P₀ P₁ P₀₁ h₀ h₁)) =
      Module.finrank k (↥P₀₁ ⧸ (P₀ ⊔ P₁).comap P₀₁.subtype) := by
  rw [range_subDiff]

end SubDiff

end PAGEGSAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing.PAGEGSAux"

namespace PAGEGSAux

theorem cech_euler {k : Type u} {K : Type v} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    [IsCurveOver k K] [Algebra.EssFiniteType k K]
    {S₀ S₁ : Set (Place k K)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    FiniteDimensional k ↥(cechH0 S₀ S₁ (0 : Divisor k K)) ∧ Module.Finite k (cechH1 S₀ S₁ (0 : Divisor k K)) ∧
      (Module.finrank k ↥(cechH0 S₀ S₁ (0 : Divisor k K)) : ℤ) - Module.finrank k (cechH1 S₀ S₁ (0 : Divisor k K))
        = 1 - (genusFF k K : ℤ) := by
  obtain ⟨v₀, hv₀⟩ := h₀
  have hC : ConstantsAreBase k K :=
    constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
  obtain ⟨_, hL0, γ, D₀, hr⟩ := stichtenothGenusExists_of_isCurveOver (K := k) (F := K) hC
  haveI := hL0
  obtain ⟨f0, f1, e0, e1, -, -⟩ := cechRiemannRoch_of_genusReached hr hcover ⟨v₀, hv₀⟩ h₁ (0 : Divisor k K)
  refine ⟨f0, f1, ?_⟩
  rw [e0, e1, ell_zero_eq_one_of_constantsAreBase hC, indexOfSpecialty_eq_finrank_H1]
  simp only [genusFF, Nat.cast_one]

section Curve
variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]

abbrev Dom (z : C) : letI := (baseToFunctionField c).toAlgebra; Place k C.functionField → Prop :=
  letI := (baseToFunctionField c).toAlgebra
  fun v => ∀ s : C.presheaf.stalk z,
    v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
    (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
      v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1)

abbrev Sof (U : C.Opens) : letI := (baseToFunctionField c).toAlgebra; Set (Place k C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | ∃ z : C, z ∈ U ∧ Dom k c z v}

abbrev Sat (z : C) : letI := (baseToFunctionField c).toAlgebra; Set (Place k C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | Dom k c z v}

abbrev At (z : C) : letI := (baseToFunctionField c).toAlgebra; Submodule k C.functionField :=
  letI := (baseToFunctionField c).toAlgebra
  lSpaceOn (Sat k c z) (0 : Divisor k C.functionField)

abbrev Oz (z : C) : letI := (baseToFunctionField c).toAlgebra; Submodule k C.functionField :=
  letI := (baseToFunctionField c).toAlgebra
  Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z) C.functionField))

abbrev Q (z : C) : Type u :=
  letI := (baseToFunctionField c).toAlgebra
  ↥(At k c z) ⧸ (Oz k c z).comap (At k c z).subtype

abbrev IU (U : C.Opens) : Type u := {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}

abbrev A (U : C.Opens) (hU : genericPoint C ∈ U) : letI := (baseToFunctionField c).toAlgebra; Submodule k C.functionField :=
  letI := (baseToFunctionField c).toAlgebra
  Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom)

abbrev phi (U : C.Opens) (T : letI := (baseToFunctionField c).toAlgebra; Set (Place k C.functionField))
    (hT : letI := (baseToFunctionField c).toAlgebra; ∀ z : C, z ∈ U → Sat k c z ⊆ T) :
    letI := (baseToFunctionField c).toAlgebra
    ↥(lSpaceOn T (0 : Divisor k C.functionField)) →ₗ[k] ((z : IU (C := C) U) → Q k c z.1) :=
  letI := (baseToFunctionField c).toAlgebra
  LinearMap.pi fun z => (Submodule.mkQ _).comp (Submodule.inclusion (lSpaceOn_anti (hT z.1 z.2.1) 0))

theorem coe_span_range_stalk_eq (z : C) :
    letI := (baseToFunctionField c).toAlgebra
    ((Oz k c z : Submodule k C.functionField) : Set C.functionField)
      = Set.range (algebraMap (C.presheaf.stalk z) C.functionField) := by
  letI := (baseToFunctionField c).toAlgebra
  let R : Submodule k C.functionField :=
  { carrier := Set.range (algebraMap (C.presheaf.stalk z) C.functionField)
    add_mem' := by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, map_add _ _ _⟩
    zero_mem' := ⟨0, map_zero _⟩
    smul_mem' := by
      rintro a _ ⟨s, rfl⟩
      let t : Γ(C, ⊤) := c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
      refine ⟨C.presheaf.germ ⊤ z trivial t * s, ?_⟩
      rw [map_mul, Algebra.smul_def]
      congr 1
      show (C.presheaf.stalkSpecializes _).hom (C.presheaf.germ ⊤ z trivial t) =
        (C.presheaf.germ ⊤ (genericPoint C) trivial).hom t
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _ }
  exact congrArg SetLike.coe (Submodule.span_eq R)

end Curve
p2m_reactivate "P2MW.S_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing.PAGEGSAux"

end PAGEGSAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing.PAGEGSAux"

open PAGEGSAux

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [IsIntegral C]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C)))
    (𝒱 : C.TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H1 ≤
      1 - (AlgebraicCurve.genusFF k F : ℤ) - (Nat.card {z : C // ¬ IsRegularLocalRing (C.presheaf.stalk z)} : ℤ) := by
  classical
  letI := (baseToFunctionField c).toAlgebra

  obtain ⟨hgen, ⟨e⟩⟩ :=
    AlgebraicCurve.CurveModel.apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
      k c M ν hν hbir
  haveI hK : IsCurveOver k C.functionField := by
    letI := M.functionFieldAlgebra
    refine isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      (c := M.toBase) (φ := (e.symm.trans M.ffAlgEquiv).toRingEquiv) ?_
    intro a
    show M.ffAlgEquiv (e.symm (algebraMap k C.functionField a)) = baseToFunctionField M.toBase a
    rw [e.symm.commutes, M.ffAlgEquiv.commutes]
    rfl
  have hgF : (genusFF k F : ℤ) = genusFF k C.functionField := by exact_mod_cast genusFF_eq_of_algEquiv e
  haveI : Algebra.EssFiniteType k C.functionField := essFiniteType_functionField c

  have hnotaff : ¬ IsAffine C := AlgebraicCurve.not_isAffine_of_isProper_of_isCurveOver k c hK
  have hne_top : ∀ U : C.Opens, IsAffineOpen U → U ≠ ⊤ := by
    rintro U hU rfl
    haveI : IsAffine (⊤ : C.Opens) := hU
    exact hnotaff (IsAffine.of_isIso C.topIso.inv)
  have hU0 : 𝒱.U0 ≠ ⊤ := hne_top _ 𝒱.isAffineOpen_U0
  have hU1 : 𝒱.U1 ≠ ⊤ := hne_top _ 𝒱.isAffineOpen_U1
  have hgenmem : ∀ U : C.Opens, U ≠ ⊥ → genericPoint C ∈ U := fun U hU =>
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
      (by simpa using (TopologicalSpace.Opens.ne_bot_iff_nonempty U).mp hU)
  have h0ne : 𝒱.U0 ≠ ⊥ := by
    intro h; apply hU1; have := 𝒱.sup_eq_top; rwa [h, bot_sup_eq] at this
  have h1ne : 𝒱.U1 ≠ ⊥ := by
    intro h; apply hU0; have := 𝒱.sup_eq_top; rwa [h, sup_bot_eq] at this
  have h0 : genericPoint C ∈ 𝒱.U0 := hgenmem _ h0ne
  have h1 : genericPoint C ∈ 𝒱.U1 := hgenmem _ h1ne
  have h01 : genericPoint C ∈ 𝒱.U0 ⊓ 𝒱.U1 := ⟨h0, h1⟩
  have hmem_cover : ∀ z : C, z ∈ 𝒱.U0 ∨ z ∈ 𝒱.U1 := fun z => by
    have hz : z ∈ (⊤ : C.Opens) := trivial
    rw [← 𝒱.sup_eq_top] at hz
    exact TopologicalSpace.Opens.mem_sup.mp hz

  have huniq := AlgebraicCurve.existsUnique_centre_place_of_isProper k c hK
  have hpts := (AlgebraicCurve.CurveModel.surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
    k c M ν hν hbir).2
  have hcover : Sof k c 𝒱.U0 ∪ Sof k c 𝒱.U1 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨z, hz, -⟩ := huniq v
    rcases hmem_cover z with hz0 | hz1
    · exact Or.inl ⟨z, hz0, hz⟩
    · exact Or.inr ⟨z, hz1, hz⟩
  have hS : Sof k c 𝒱.U0 ∩ Sof k c 𝒱.U1 = Sof k c (𝒱.U0 ⊓ 𝒱.U1) := by
    ext v; constructor
    · rintro ⟨⟨z0, hz0, hd0⟩, ⟨z1, hz1, hd1⟩⟩
      obtain rfl : z0 = z1 := (huniq v).unique hd0 hd1
      exact ⟨z0, ⟨hz0, hz1⟩, hd0⟩
    · rintro ⟨z, hz, hd⟩
      exact ⟨⟨z, hz.1, hd⟩, ⟨z, hz.2, hd⟩⟩
  have hout : ∀ U : C.Opens, U ≠ ⊤ → genericPoint C ∈ U → ∃ v, v ∉ Sof k c U := by
    intro U hUtop hgU
    obtain ⟨z, hz⟩ : ∃ z : C, z ∉ U := by
      by_contra h
      exact hUtop (eq_top_iff.mpr fun z _ => (not_exists_not.mp h) z)
    have hzc : IsClosed ({z} : Set C) := (hpts z).resolve_left (by rintro rfl; exact hz hgU)
    obtain ⟨⟨v, hv⟩, -⟩ :=
      AlgebraicCurve.exists_centre_and_finite_setOf_centre_of_isClosed_singleton k c hK z hzc
    refine ⟨v, ?_⟩
    rintro ⟨z', hz'U, hv'⟩
    obtain rfl : z = z' := (huniq v).unique hv hv'
    exact hz hz'U

  obtain ⟨fdH0, fdH1, hχ2⟩ :=
    PAGEGSAux.cech_euler (k := k) (K := C.functionField) hcover (hout _ hU0 h0) (hout _ hU1 h1)

  have L5gen : ∀ (U : C.Opens) (hUaff : IsAffineOpen U) (hU : genericPoint C ∈ U)
      (T : Set (Place k C.functionField)) (hT : T = Sof k c U)
      (hT' : ∀ z : C, z ∈ U → Sat k c z ⊆ T),
      Function.Surjective (phi k c U T hT') ∧
      LinearMap.ker (phi k c U T hT') =
        (A k c U hU).comap (lSpaceOn T (0 : Divisor k C.functionField)).subtype ∧
      {z : IU (C := C) U | Nontrivial (Q k c z.1)}.Finite ∧
      ∀ z : IU (C := C) U, FiniteDimensional k (Q k c z.1) := by
    intro U hUaff hU T hT hT'
    subst hT
    exact AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
      k c hK M ν hν hbir U hUaff hU
  have p0 : ∀ z : C, z ∈ 𝒱.U0 → Sat k c z ⊆ Sof k c 𝒱.U0 := fun z hz v hv => ⟨z, hz, hv⟩
  have p1 : ∀ z : C, z ∈ 𝒱.U1 → Sat k c z ⊆ Sof k c 𝒱.U1 := fun z hz v hv => ⟨z, hz, hv⟩
  have p01 : ∀ z : C, z ∈ 𝒱.U0 ⊓ 𝒱.U1 → Sat k c z ⊆ Sof k c 𝒱.U0 ∩ Sof k c 𝒱.U1 :=
    fun z hz v hv => ⟨⟨z, hz.1, hv⟩, ⟨z, hz.2, hv⟩⟩
  obtain ⟨sj0, ker0, fin0, fd0⟩ := L5gen 𝒱.U0 𝒱.isAffineOpen_U0 h0 _ rfl p0
  obtain ⟨sj1, ker1, fin1, fd1⟩ := L5gen 𝒱.U1 𝒱.isAffineOpen_U1 h1 _ rfl p1
  obtain ⟨sj01, ker01, fin01, fd01⟩ := L5gen (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf h01 _ hS p01

  have hA_le : ∀ (U : C.Opens) (hU : genericPoint C ∈ U),
      A k c U hU ≤ lSpaceOn (Sof k c U) (0 : Divisor k C.functionField) := fun U hU =>
    Submodule.span_le.mpr (by
      rintro _ ⟨t, rfl⟩
      exact AlgebraicCurve.germ_mem_lSpaceOn_setOf_exists_centre_zero k c U hU t)
  have hA0 := hA_le 𝒱.U0 h0
  have hA1 := hA_le 𝒱.U1 h1
  have hA01 : A k c (𝒱.U0 ⊓ 𝒱.U1) h01 ≤
      lSpaceOn (Sof k c 𝒱.U0 ∩ Sof k c 𝒱.U1) (0 : Divisor k C.functionField) := by
    rw [hS]; exact hA_le _ h01
  have hres : ∀ (U V : C.Opens) (hUV : V ≤ U) (hgU : genericPoint C ∈ U) (hgV : genericPoint C ∈ V),
      A k c U hgU ≤ A k c V hgV := by
    intro U V hUV hgU hgV
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨C.presheaf.map (homOfLE hUV).op t,
      TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE hUV) (genericPoint C) hgV t⟩
  have hA0le : A k c 𝒱.U0 h0 ≤ A k c (𝒱.U0 ⊓ 𝒱.U1) h01 := hres _ _ inf_le_left h0 h01
  have hA1le : A k c 𝒱.U1 h1 ≤ A k c (𝒱.U0 ⊓ 𝒱.U1) h01 := hres _ _ inf_le_right h1 h01

  let d₁ := PAGEGSAux.subDiff (A k c 𝒱.U0 h0) (A k c 𝒱.U1 h1) (A k c (𝒱.U0 ⊓ 𝒱.U1) h01) hA0le hA1le
  let d₂ := cechDiff (Sof k c 𝒱.U0) (Sof k c 𝒱.U1) (0 : Divisor k C.functionField)
  let r0 : ((z : IU (C := C) 𝒱.U0) → Q k c z.1) →ₗ[k] ((z : IU (C := C) (𝒱.U0 ⊓ 𝒱.U1)) → Q k c z.1) :=
    LinearMap.pi fun z => LinearMap.proj (⟨z.1, z.2.1.1, z.2.2⟩ : IU (C := C) 𝒱.U0)
  let r1 : ((z : IU (C := C) 𝒱.U1) → Q k c z.1) →ₗ[k] ((z : IU (C := C) (𝒱.U0 ⊓ 𝒱.U1)) → Q k c z.1) :=
    LinearMap.pi fun z => LinearMap.proj (⟨z.1, z.2.1.2, z.2.2⟩ : IU (C := C) 𝒱.U1)
  letI instQacg : ∀ z : C, AddCommGroup (Q k c z) := fun z => inferInstance
  letI instQmod : ∀ z : C, Module k (Q k c z) := fun z => inferInstance
  let d₃ : (((z : IU (C := C) 𝒱.U0) → Q k c z.1) × ((z : IU (C := C) 𝒱.U1) → Q k c z.1)) →ₗ[k]
      ((z : IU (C := C) (𝒱.U0 ⊓ 𝒱.U1)) → Q k c z.1) :=
    r1.comp (LinearMap.snd k ((z : IU (C := C) 𝒱.U0) → Q k c z.1) ((z : IU (C := C) 𝒱.U1) → Q k c z.1)) -
      r0.comp (LinearMap.fst k ((z : IU (C := C) 𝒱.U0) → Q k c z.1) ((z : IU (C := C) 𝒱.U1) → Q k c z.1))
  let f₁ := LinearMap.prodMap (R := k) (Submodule.inclusion hA0) (Submodule.inclusion hA1)
  let f₂ := (phi k c 𝒱.U0 _ p0).prodMap (phi k c 𝒱.U1 _ p1)
  let g₁ := Submodule.inclusion hA01
  let g₂ := phi k c (𝒱.U0 ⊓ 𝒱.U1) _ p01
  have hf₁ : Function.Injective f₁ :=
    Function.Injective.prodMap (Submodule.inclusion_injective hA0) (Submodule.inclusion_injective hA1)
  have hf₂ : Function.Surjective f₂ := Function.Surjective.prodMap sj0 sj1
  have hf : Function.Exact f₁ f₂ := by
    apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_prodMap, LinearMap.range_prodMap, ker0, ker1, Submodule.range_inclusion,
      Submodule.range_inclusion]
  have hg₁ : Function.Injective g₁ := Submodule.inclusion_injective hA01
  have hg₂ : Function.Surjective g₂ := sj01
  have hg : Function.Exact g₁ g₂ := by
    apply LinearMap.exact_iff.mpr
    rw [ker01, Submodule.range_inclusion]
  have h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁ := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    apply Subtype.ext
    rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_cechDiff_apply]
    rfl
  have h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂ := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    funext z
    simp only [d₃, r0, r1, f₂, g₂, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply, LinearMap.prodMap_apply,
      Submodule.mkQ_apply, Pi.sub_apply]
    rw [← Submodule.Quotient.mk_sub]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_inclusion, Submodule.coe_sub]
    exact coe_cechDiff_apply (x, y)

  haveI : FiniteDimensional k ↥(LinearMap.ker d₂) := fdH0
  haveI : Module.Finite k (↥(lSpaceOn (Sof k c 𝒱.U0 ∩ Sof k c 𝒱.U1) (0 : Divisor k C.functionField)) ⧸
      LinearMap.range d₂) := fdH1
  obtain ⟨fdP0, -⟩ := PAGEGSAux.finiteDimensional_pi_and_natCard_le
    (k := k) (fun z : IU (C := C) 𝒱.U0 => Q k c z.1) fin0 fd0
  obtain ⟨fdP1, -⟩ := PAGEGSAux.finiteDimensional_pi_and_natCard_le
    (k := k) (fun z : IU (C := C) 𝒱.U1 => Q k c z.1) fin1 fd1
  obtain ⟨fdP01, -⟩ := PAGEGSAux.finiteDimensional_pi_and_natCard_le
    (k := k) (fun z : IU (C := C) (𝒱.U0 ⊓ 𝒱.U1) => Q k c z.1) fin01 fd01
  haveI := fdP0; haveI := fdP1; haveI := fdP01
  have hsurj3 : Function.Surjective d₃ := by
    intro t
    refine ⟨(0, fun z => if h : z.1 ∈ 𝒱.U0 then t ⟨z.1, ⟨h, z.2.1⟩, z.2.2⟩ else 0), ?_⟩
    funext z
    simp only [d₃, r0, r1, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.fst_apply, LinearMap.pi_apply, LinearMap.proj_apply, map_zero, sub_zero]
    split_ifs with h
    · rfl
    · exact absurd z.2.1.1 h
  have hcoker3 : Module.finrank k (((z : IU (C := C) (𝒱.U0 ⊓ 𝒱.U1)) → Q k c z.1) ⧸ LinearMap.range d₃) = 0 := by
    rw [LinearMap.range_eq_top.mpr hsurj3]
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨fk1, fc1⟩ :=
    LinearMap.finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional
      d₁ d₂ d₃ f₁ f₂ g₁ g₂ hf₁ hf hf₂ hg₁ hg hg₂ h₁ h₂
  haveI := fk1; haveI := fc1
  obtain ⟨-, -, hχ⟩ := LinearMap.finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
    d₁ d₂ d₃ f₁ f₂ g₁ g₂ hf₁ hf hf₂ hg₁ hg hg₂ h₁ h₂

  obtain ⟨e0, e1, -, -⟩ := 𝒱.exists_sectionsOf_unit_equiv_structureSheafSections c
  obtain ⟨hH0, hH1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_structureSheafSections_eq_finrank_span_germ k c 𝒱 h0 h1
  rw [e0.finrank_eq, e1.finrank_eq, hH0, hH1,
    ← PAGEGSAux.finrank_ker_subDiff _ _ _ hA0le hA1le,
    ← PAGEGSAux.finrank_quotient_range_subDiff _ _ _ hA0le hA1le]

  have hcount : (Nat.card {z : C // ¬ IsRegularLocalRing (C.presheaf.stalk z)} : ℤ) ≤
      Module.finrank k ↥(LinearMap.ker d₃) := by

    have key : ∀ z : C, ¬ IsRegularLocalRing (C.presheaf.stalk z) →
        IsClosed ({z} : Set C) ∧ Nontrivial (Q k c z) := by
      intro z hreg
      have hzc : IsClosed ({z} : Set C) := by
        refine (hpts z).resolve_left ?_
        rintro rfl
        apply hreg
        change IsRegularLocalRing C.functionField
        infer_instance
      refine ⟨hzc, ?_⟩
      by_contra hnt
      apply hreg
      have hsub : Subsingleton (Q k c z) := not_nontrivial_iff_subsingleton.mp hnt
      refine AlgebraicCurve.isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range k c z
        (AlgebraicCurve.exists_centre_and_finite_setOf_centre_of_isClosed_singleton k c hK z hzc).2 ?_
      intro f hf
      have hmem : (⟨f, hf⟩ : ↥(At k c z)) ∈ (Oz k c z).comap (At k c z).subtype := by
        rw [← Submodule.Quotient.mk_eq_zero]
        exact Subsingleton.elim _ _
      rw [← PAGEGSAux.coe_span_range_stalk_eq k c z]
      exact hmem

    have finC : {z : {z : C // IsClosed ({z} : Set C)} | Nontrivial (Q k c z.1)}.Finite := by
      refine Set.Finite.subset ((fin0.image fun z => (⟨z.1, z.2.2⟩ : {z : C // IsClosed ({z} : Set C)})).union
        (fin1.image fun z => (⟨z.1, z.2.2⟩ : {z : C // IsClosed ({z} : Set C)}))) ?_
      intro z hz
      rcases hmem_cover z.1 with h | h
      · exact Or.inl ⟨⟨z.1, h, z.2⟩, hz, rfl⟩
      · exact Or.inr ⟨⟨z.1, h, z.2⟩, hz, rfl⟩
    have fdC : ∀ z : {z : C // IsClosed ({z} : Set C)}, FiniteDimensional k (Q k c z.1) := by
      intro z
      rcases hmem_cover z.1 with h | h
      · exact fd0 ⟨z.1, h, z.2⟩
      · exact fd1 ⟨z.1, h, z.2⟩
    obtain ⟨fdPC, hcardC⟩ := PAGEGSAux.finiteDimensional_pi_and_natCard_le
      (k := k) (fun z : {z : C // IsClosed ({z} : Set C)} => Q k c z.1) finC fdC
    haveI := fdPC

    let G : ((z : {z : C // IsClosed ({z} : Set C)}) → Q k c z.1) →ₗ[k]
        (((z : IU (C := C) 𝒱.U0) → Q k c z.1) × ((z : IU (C := C) 𝒱.U1) → Q k c z.1)) :=
      LinearMap.prod
        (LinearMap.pi fun z => LinearMap.proj (⟨z.1, z.2.2⟩ : {z : C // IsClosed ({z} : Set C)}))
        (LinearMap.pi fun z => LinearMap.proj (⟨z.1, z.2.2⟩ : {z : C // IsClosed ({z} : Set C)}))
    have hGker : ∀ w, G w ∈ LinearMap.ker d₃ := by
      intro w
      rw [LinearMap.mem_ker]
      funext z
      exact sub_self (w ⟨z.1, z.2.2⟩)
    have hGinj : Function.Injective (LinearMap.codRestrict (LinearMap.ker d₃) G hGker) := by
      intro w w' h
      have h' : G w = G w' := congrArg Subtype.val h
      funext z
      rcases hmem_cover z.1 with hz | hz
      · have := congrFun (congrArg Prod.fst h') ⟨z.1, hz, z.2⟩
        simpa [G] using this
      · have := congrFun (congrArg Prod.snd h') ⟨z.1, hz, z.2⟩
        simpa [G] using this
    have hle1 : Module.finrank k ((z : {z : C // IsClosed ({z} : Set C)}) → Q k c z.1) ≤
        Module.finrank k ↥(LinearMap.ker d₃) := by
      rw [← LinearMap.finrank_range_of_inj hGinj]
      exact Submodule.finrank_le _

    haveI : Finite {z : {z : C // IsClosed ({z} : Set C)} | Nontrivial (Q k c z.1)} := finC.to_subtype
    have hle2 : Nat.card {z : C // ¬ IsRegularLocalRing (C.presheaf.stalk z)} ≤
        Nat.card {z : {z : C // IsClosed ({z} : Set C)} | Nontrivial (Q k c z.1)} := by
      refine Nat.card_le_card_of_injective
        (fun z => ⟨⟨z.1, (key z.1 z.2).1⟩, (key z.1 z.2).2⟩) ?_
      intro a b h
      exact Subtype.ext (congrArg (fun x => x.1.1) h)
    exact_mod_cast hle2.trans (hcardC.trans hle1)

  have hχ2' : (Module.finrank k ↥(LinearMap.ker d₂) : ℤ) -
      Module.finrank k (↥(lSpaceOn (Sof k c 𝒱.U0 ∩ Sof k c 𝒱.U1) (0 : Divisor k C.functionField)) ⧸
        LinearMap.range d₂) = 1 - (genusFF k C.functionField : ℤ) := hχ2
  rw [hcoker3] at hχ
  push_cast at hχ
  linarith [hχ, hχ2', hcount, hgF]

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing.PAGEGSAux"

#print axioms solution

end S_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing (solution)
