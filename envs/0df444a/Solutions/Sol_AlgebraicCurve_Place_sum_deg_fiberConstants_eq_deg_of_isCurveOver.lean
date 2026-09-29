-- Prove2me | solution 1 for AlgebraicCurve.Place.sum_deg_fiberConstants_eq_deg_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c61cfa7a-4f3e-540c-ac5e-df36f59c4fac

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_residueField_eq_compositum_of_isConstantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open AlgebraicCurve IntermediateField Polynomial

namespace P2MWs12
namespace ConstFieldDeg

section Generic

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

theorem minpoly_eq_map_of_constants {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) {α : L} (hα : IsIntegral K α) :
    minpoly F α = (minpoly K α).map (algebraMap K F) := by
  have hαF : IsIntegral F α := hα.tower_top
  have hgmon : (minpoly F α).Monic := minpoly.monic hαF
  have hfmon : (minpoly K α).Monic := minpoly.monic hα
  have hdvd : minpoly F α ∣ (minpoly K α).map (algebraMap K F) := minpoly.dvd_map_of_isScalarTower K F α
  have hlift : minpoly F α ∈ Polynomial.lifts (algebraMap K F) := by
    have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F hfmon hgmon hdvd
    rw [Polynomial.lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨c, hc⟩ := h1 n
    have halg : IsAlgebraic K ((minpoly F α).coeff n) := by
      rw [← hc]
      exact (show IsIntegral K (c : F) from c.2).isAlgebraic
    exact hconst _ halg
  obtain ⟨g₀, hg₀map, -, hg₀mon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hgmon
  have hg₀α : Polynomial.aeval α g₀ = 0 := by
    have : Polynomial.aeval α (minpoly F α) = 0 := minpoly.aeval F α
    rwa [← hg₀map, Polynomial.aeval_map_algebraMap] at this
  have hfdvd : minpoly K α ∣ g₀ := minpoly.dvd K α hg₀α
  have hdeg : ((minpoly K α).map (algebraMap K F)).natDegree ≤ (minpoly F α).natDegree := by
    rw [Polynomial.natDegree_map, ← hg₀map, Polynomial.natDegree_map]
    exact Polynomial.natDegree_le_of_dvd hfdvd hg₀mon.ne_zero
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hgmon (hfmon.map _) hdvd hdeg).symm

theorem finiteType_of_adjoin_range_eq_top [FiniteDimensional K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) :
    Algebra.FiniteType F F' := by
  classical
  let b := Module.finBasis K K'
  refine ⟨⟨Finset.univ.image (fun i => algebraMap K' F' (b i)), ?_⟩⟩
  rw [eq_top_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro _ ⟨k, rfl⟩
  rw [← b.sum_repr k, map_sum]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K K' F',
    IsScalarTower.algebraMap_apply K F F']
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin ?_)
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
  exact ⟨i, rfl⟩

theorem isSeparable_algebraMap [Algebra.IsSeparable K K'] (k : K') :
    IsSeparable K (algebraMap K' F' k) := by
  rw [IsSeparable, minpoly.algebraMap_eq (algebraMap K' F').injective k]
  exact Algebra.IsSeparable.isSeparable K k

theorem isSeparable_of_adjoin_range_eq_top [Algebra.IsSeparable K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) :
    Algebra.IsSeparable F F' := by
  rw [← separableClosure.eq_top_iff, eq_top_iff]
  intro x _
  have hx : x ∈ Algebra.adjoin F (Set.range (algebraMap K' F')) := by rw [hgen]; trivial
  have hle : Algebra.adjoin F (Set.range (algebraMap K' F')) ≤ (separableClosure F F').toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact mem_separableClosure_iff.mpr ((isSeparable_algebraMap (K := K) k).tower_top F)
  exact hle hx

theorem finrank_eq_finrank [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) :
    Module.finrank F F' = Module.finrank K K' := by
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element K K'
  set b : F' := algebraMap K' F' β with hb
  have hβint : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hbint : IsIntegral K b := hβint.map (IsScalarTower.toAlgHom K K' F')
  have hbintF : IsIntegral F b := hbint.tower_top
  have hminb : minpoly K b = minpoly K β := minpoly.algebraMap_eq (algebraMap K' F').injective β

  have hrange : Set.range (algebraMap K' F') ⊆ (F⟮b⟯ : Set F') := by
    rintro _ ⟨k, rfl⟩
    have hk : k ∈ (K⟮β⟯).toSubalgebra := by rw [hβ]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hk
    obtain ⟨p, rfl⟩ := hk
    show (IsScalarTower.toAlgHom K K' F') (Polynomial.aeval β p) ∈ F⟮b⟯
    rw [← Polynomial.aeval_algHom_apply]
    show Polynomial.aeval b p ∈ F⟮b⟯
    have h1 : Polynomial.aeval b p ∈ Algebra.adjoin K {b} := Polynomial.aeval_mem_adjoin_singleton K b
    have h2 : Algebra.adjoin K {b} ≤ (F⟮b⟯.toSubalgebra).restrictScalars K :=
      Algebra.adjoin_le (by simpa using IntermediateField.mem_adjoin_simple_self F b)
    exact h2 h1
  have htop : F⟮b⟯ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin F (Set.range (algebraMap K' F')) := by rw [hgen]; trivial
    exact (Algebra.adjoin_le_iff.mpr hrange : Algebra.adjoin F _ ≤ F⟮b⟯.toSubalgebra) hx
  calc Module.finrank F F'
      = Module.finrank F (⊤ : IntermediateField F F') := IntermediateField.finrank_top'.symm
    _ = Module.finrank F F⟮b⟯ := by rw [htop]
    _ = (minpoly F b).natDegree := IntermediateField.adjoin.finrank hbintF
    _ = (minpoly K b).natDegree := by
        rw [minpoly_eq_map_of_constants hconst hbint, Polynomial.natDegree_map]
    _ = (minpoly K β).natDegree := by rw [hminb]
    _ = Module.finrank K K⟮β⟯ := (IntermediateField.adjoin.finrank hβint).symm
    _ = Module.finrank K K' := by rw [hβ, IntermediateField.finrank_top']

end Generic

section Key

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

theorem deg_forget_eq [FiniteDimensional K K'] (W : Place K' F') :
    (W.forgetConstants (K := K)).deg = Module.finrank K K' * W.deg := by
  letI : Algebra K W.toValuationSubring :=
    (inferInstance : Algebra K (W.forgetConstants (K := K)).toValuationSubring)
  haveI : IsScalarTower K K' W.toValuationSubring :=
    IsScalarTower.of_algebraMap_eq fun k => Subtype.ext (IsScalarTower.algebraMap_apply K K' F' k)
  haveI : IsScalarTower K K' W.ResidueField := IsScalarTower.of_algebraMap_eq fun k => by
    rw [IsScalarTower.algebraMap_apply K W.toValuationSubring W.ResidueField,
      IsScalarTower.algebraMap_apply K' W.toValuationSubring W.ResidueField,
      IsScalarTower.algebraMap_apply K K' W.toValuationSubring]
  exact (Module.finrank_mul_finrank K K' W.ResidueField).symm

theorem hasPrincipalDivisors_forget [FiniteDimensional K K'] [HasPrincipalDivisors K' F'] :
    HasPrincipalDivisors K F' := by
  classical
  refine ⟨fun f hf => ?_⟩
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K') f hf
  refine ⟨D.equivMapDomain (Place.constantFieldEquiv K K' (F' := F')).symm, fun w => ?_, ?_⟩
  · rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
    exact hD _
  · have hdegK : Divisor.degree (D.equivMapDomain (Place.constantFieldEquiv K K' (F' := F')).symm)
        = (Module.finrank K K' : ℤ) * Divisor.degree D := by
      rw [Finsupp.equivMapDomain_eq_mapDomain, Divisor.degree, Divisor.degree,
        Finsupp.liftAddHom_apply, Finsupp.liftAddHom_apply,
        Finsupp.sum_mapDomain_index_inj (Equiv.injective _), Finsupp.mul_sum]
      refine Finsupp.sum_congr fun W _ => ?_
      simp only [AddMonoidHom.mulRight_apply, Place.constantFieldEquiv_symm_apply, deg_forget_eq]
      push_cast
      ring
    rw [hdegK, hdeg, mul_zero]

theorem sum_deg_fiberConstants_eq [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Algebra.IsIntegral F F'] [HasPrincipalDivisors K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) (v : Place K F) :
    ∑ W ∈ Place.fiberConstants K' F' v, (W.deg : ℤ) = v.deg := by
  classical
  haveI : Algebra.FiniteType F F' := finiteType_of_adjoin_range_eq_top (K := K) hgen
  haveI : Module.Finite F F' := Algebra.IsIntegral.finite
  haveI : Algebra.IsSeparable F F' := isSeparable_of_adjoin_range_eq_top (K := K) hgen
  haveI : HasPrincipalDivisors K F' := hasPrincipalDivisors_forget (K := K) (K' := K')

  have hFI := Place.sum_ramificationIndex_mul_inertiaDeg (K := K) (F := F) (F' := F') v
  have he : ∀ w : Place K F', w.ramificationIndex F = 1 := fun w =>
    Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgen hconst
      (Place.extendConstants K' w)
  simp only [he, Nat.cast_one, one_mul] at hFI
  rw [finrank_eq_finrank (K := K) hgen hconst] at hFI

  have hre : ∑ W ∈ Place.fiberConstants K' F' v, (W.deg : ℤ)
      = ∑ w ∈ v.fiber F', ((Place.extendConstants K' w).deg : ℤ) := by
    refine (Finset.sum_equiv (Place.constantFieldEquiv K K' (F' := F')) (fun w => ?_) (fun w _ => rfl)).symm
    rw [Place.mem_fiber, Place.mem_fiberConstants]
    rfl
  rw [hre]

  have hpos : (0 : ℤ) < Module.finrank K K' := by exact_mod_cast Module.finrank_pos
  have key : (Module.finrank K K' : ℤ) * ∑ w ∈ v.fiber F', ((Place.extendConstants K' w).deg : ℤ)
      = (Module.finrank K K' : ℤ) * v.deg := by
    rw [Finset.mul_sum]
    calc ∑ w ∈ v.fiber F', (Module.finrank K K' : ℤ) * ((Place.extendConstants K' w).deg : ℤ)
        = ∑ w ∈ v.fiber F', ((v.deg : ℤ) * (w.inertiaDeg F : ℤ)) := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [Place.mem_fiber] at hw
          have h1 := deg_forget_eq (K := K) (Place.extendConstants K' w)
          have h2 := w.deg_restrict_mul_inertiaDeg (F := F)
          rw [hw] at h2
          have h3 : (Place.extendConstants K' w).forgetConstants (K := K) = w := Place.ext rfl
          rw [h3] at h1
          have h4 : Module.finrank K K' * (Place.extendConstants K' w).deg = v.deg * w.inertiaDeg F :=
            h1.symm.trans h2.symm
          exact_mod_cast h4
      _ = (v.deg : ℤ) * Module.finrank K K' := by rw [← Finset.mul_sum, hFI]
      _ = (Module.finrank K K' : ℤ) * v.deg := by ring
  exact mul_left_cancel₀ hpos.ne' key

end Key

end P2MWs12.ConstFieldDeg

set_option autoImplicit false
namespace P2MWs12
namespace Descent
open AlgebraicCurve

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

variable (F F') in

def FK (K₁ : IntermediateField K K') : IntermediateField F F' :=
  IntermediateField.adjoin F (algebraMap K' F' '' (K₁ : Set K'))

variable (K₁ : IntermediateField K K')

theorem algebraMap_mem_FK (k : K₁) : algebraMap K' F' (k : K') ∈ FK F F' K₁ :=
  IntermediateField.subset_adjoin _ _ ⟨k, k.2, rfl⟩

variable (F F') in

def toFK : K₁ →+* FK F F' K₁ where
  toFun k := ⟨algebraMap K' F' (k : K'), algebraMap_mem_FK K₁ k⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

noncomputable scoped instance algKFK : Algebra K₁ (FK F F' K₁) := (toFK F F' K₁).toAlgebra

example : Algebra K (FK F F' K₁) := inferInstance
example : Algebra F (FK F F' K₁) := inferInstance
example : Algebra (FK F F' K₁) F' := inferInstance
example : IsScalarTower F (FK F F' K₁) F' := inferInstance
example : IsScalarTower K F (FK F F' K₁) := inferInstance
scoped instance towerKFKF' : IsScalarTower K (FK F F' K₁) F' :=
  IsScalarTower.of_algebraMap_eq fun k => by
    show algebraMap K F' k = ((algebraMap K (FK F F' K₁) k : FK F F' K₁) : F')
    rw [IsScalarTower.algebraMap_apply K F (FK F F' K₁) k]
    show algebraMap K F' k = algebraMap F F' (algebraMap K F k)
    exact IsScalarTower.algebraMap_apply K F F' k

theorem algebraMap_FK_apply (k : K₁) : ((algebraMap K₁ (FK F F' K₁) k : FK F F' K₁) : F') = algebraMap K' F' (k : K') := rfl

scoped instance towerKK1FK : IsScalarTower K K₁ (FK F F' K₁) :=
  IsScalarTower.of_algebraMap_eq fun k => Subtype.ext (by
    show algebraMap K F' k = algebraMap K' F' (algebraMap K K' k)
    exact IsScalarTower.algebraMap_apply K K' F' k)

example : Algebra K₁ F' := inferInstance
example : IsScalarTower K₁ K' F' := inferInstance
example : IsScalarTower K K₁ F' := inferInstance
theorem algebraMap_K1_F' (k : K₁) : algebraMap K₁ F' k = algebraMap K' F' (k : K') := rfl

scoped instance towerK1FKF' : IsScalarTower K₁ (FK F F' K₁) F' :=
  IsScalarTower.of_algebraMap_eq fun k => (rfl : algebraMap K₁ F' k = ((algebraMap K₁ (FK F F' K₁) k : FK F F' K₁) : F'))

theorem FK_mono {K₁ K₂ : IntermediateField K K'} (h : K₁ ≤ K₂) : FK F F' K₁ ≤ FK F F' K₂ :=
  IntermediateField.adjoin.mono F _ _ (Set.image_mono h)

theorem isAlgebraic_of_mem_image [Algebra.IsAlgebraic K K'] {x : F'}
    (hx : x ∈ algebraMap K' F' '' (K₁ : Set K')) : IsAlgebraic F x := by
  obtain ⟨k, -, rfl⟩ := hx
  have h : IsAlgebraic K (algebraMap K' F' k) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := K) k).algHom (IsScalarTower.toAlgHom K K' F')
  exact h.tower_top (L := F)

theorem FK_toSubalgebra [Algebra.IsAlgebraic K K'] :
    (FK F F' K₁).toSubalgebra = Algebra.adjoin F (algebraMap K' F' '' (K₁ : Set K')) :=
  IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun _ hx => isAlgebraic_of_mem_image K₁ hx)

theorem adjoin_range_FK_eq_top [Algebra.IsAlgebraic K K'] :
    Algebra.adjoin F (Set.range (algebraMap K₁ (FK F F' K₁))) = ⊤ := by
  apply Subalgebra.map_injective (f := (FK F F' K₁).val) Subtype.val_injective
  rw [← Algebra.adjoin_image, Algebra.map_top, IntermediateField.range_val, FK_toSubalgebra]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨algebraMap K₁ (FK F F' K₁) ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩, rfl⟩

scoped instance isIntegral_FK_top [Algebra.IsIntegral F F'] : Algebra.IsIntegral (FK F F' K₁) F' :=
  Algebra.IsIntegral.tower_top (R := F)

scoped instance isIntegral_FK_bot [Algebra.IsIntegral F F'] : Algebra.IsIntegral F (FK F F' K₁) :=
  Algebra.IsIntegral.of_injective (FK F F' K₁).val Subtype.val_injective

variable (F F') in

noncomputable def res [Algebra.IsIntegral F F'] (W : Place K' F') : Place K₁ (FK F F' K₁) :=
  (W.forgetConstants (K := K₁)).restrict (FK F F' K₁)

section Fibres

variable [Algebra.IsIntegral F F']

theorem res_toValuationSubring (W : Place K' F') :
    (res F F' K₁ W).toValuationSubring
      = W.toValuationSubring.comap (algebraMap (FK F F' K₁) F') := rfl

theorem mem_res_iff (W : Place K' F') (x : FK F F' K₁) :
    x ∈ (res F F' K₁ W).toValuationSubring ↔ (x : F') ∈ W.toValuationSubring := Iff.rfl

theorem restrictConstants_res (W : Place K' F') :
    (res F F' K₁ W).restrictConstants F (K := K) = W.restrictConstants F (K := K) := by
  apply Place.ext
  ext f
  simp only [Place.restrictConstants_toValuationSubring, ValuationSubring.mem_comap,
    Place.forgetConstants_toValuationSubring, res_toValuationSubring, Place.restrict_toValuationSubring]
  rw [← IsScalarTower.algebraMap_apply F (FK F F' K₁) F']

variable (F F') in

def fiberSet (v : Place K F) : Set (Place K₁ (FK F F' K₁)) :=
  {U | U.restrictConstants F (K := K) = v}

theorem mem_fiberSet {v : Place K F} {U : Place K₁ (FK F F' K₁)} :
    U ∈ fiberSet F F' K₁ v ↔ U.restrictConstants F (K := K) = v := Iff.rfl

theorem mapsTo_res [HasPrincipalDivisors K' F'] (v : Place K F) :
    Set.MapsTo (res F F' K₁) ↑(Place.fiberConstants K' F' v) (fiberSet F F' K₁ v) := by
  intro W hW
  rw [mem_fiberSet, restrictConstants_res]
  exact Place.mem_fiberConstants.mp hW

theorem surjOn_res [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [HasPrincipalDivisors K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) (v : Place K F) :
    Set.SurjOn (res F F' K₁) ↑(Place.fiberConstants K' F' v) (fiberSet F F' K₁ v) := by
  intro U hU
  obtain ⟨W, hW⟩ := Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
    hgen hconst (M := FK F F' K₁) (U.forgetConstants (K := K))
  have hVS : (res F F' K₁ W).toValuationSubring = U.toValuationSubring := by
    have h := congrArg Place.toValuationSubring hW
    exact h
  have hres : res F F' K₁ W = U := Place.ext hVS
  refine ⟨W, ?_, hres⟩
  rw [Finset.mem_coe, Place.mem_fiberConstants, ← restrictConstants_res K₁ W, hres]
  exact hU

theorem exists_finset_mem_adjoin {t : F'}
    (ht : t ∈ Algebra.adjoin F (Set.range (algebraMap K' F'))) :
    ∃ S : Finset K', t ∈ Algebra.adjoin F ((algebraMap K' F') '' (S : Set K')) := by
  classical
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨{k}, Algebra.subset_adjoin ⟨k, by simp, rfl⟩⟩
  | algebraMap r => exact ⟨∅, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁⟩ := hx
    obtain ⟨S₂, h₂⟩ := hy
    refine ⟨S₁ ∪ S₂, add_mem (Algebra.adjoin_mono ?_ h₁) (Algebra.adjoin_mono ?_ h₂)⟩
    · exact Set.image_mono (by simp)
    · exact Set.image_mono (by simp)
  | mul x y _ _ hx hy =>
    obtain ⟨S₁, h₁⟩ := hx
    obtain ⟨S₂, h₂⟩ := hy
    refine ⟨S₁ ∪ S₂, mul_mem (Algebra.adjoin_mono ?_ h₁) (Algebra.adjoin_mono ?_ h₂)⟩
    · exact Set.image_mono (by simp)
    · exact Set.image_mono (by simp)

theorem exists_fd_mem_FK [Algebra.IsAlgebraic K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) (f : F') :
    ∃ K₀ : IntermediateField K K', FiniteDimensional K K₀ ∧ f ∈ FK F F' K₀ := by
  have hf : f ∈ Algebra.adjoin F (Set.range (algebraMap K' F')) := by rw [hgen]; trivial
  obtain ⟨S, hS⟩ := exists_finset_mem_adjoin hf
  refine ⟨IntermediateField.adjoin K (S : Set K'),
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral), ?_⟩
  have hle : Algebra.adjoin F ((algebraMap K' F') '' (S : Set K'))
      ≤ (FK F F' (IntermediateField.adjoin K (S : Set K'))).toSubalgebra := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, hs, rfl⟩
    exact algebraMap_mem_FK _ ⟨s, IntermediateField.subset_adjoin K _ hs⟩
  exact hle hS

theorem exists_fd_separating [Algebra.IsAlgebraic K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    {W W' : Place K' F'} (h : W ≠ W') :
    ∃ K₀ : IntermediateField K K', FiniteDimensional K K₀ ∧
      ∀ K₂ : IntermediateField K K', K₀ ≤ K₂ → res F F' K₂ W ≠ res F F' K₂ W' := by
  have hVS : W.toValuationSubring ≠ W'.toValuationSubring := fun h' => h (Place.ext h')
  obtain ⟨f, hf⟩ : ∃ f : F', ¬ (f ∈ W.toValuationSubring ↔ f ∈ W'.toValuationSubring) := by
    by_contra hall
    push_neg at hall
    exact hVS (SetLike.ext hall)
  obtain ⟨K₀, hfd, hfK₀⟩ := exists_fd_mem_FK (K := K) hgen f
  refine ⟨K₀, hfd, fun K₂ hle heq => hf ?_⟩
  have hf₂ : f ∈ FK F F' K₂ := FK_mono hle hfK₀
  have hVS₂ := congrArg Place.toValuationSubring heq
  exact (mem_res_iff K₂ W ⟨f, hf₂⟩).symm.trans
    ((SetLike.ext_iff.mp hVS₂ ⟨f, hf₂⟩).trans (mem_res_iff K₂ W' ⟨f, hf₂⟩))

theorem exists_fd_injOn [Algebra.IsAlgebraic K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (S : Finset (Place K' F')) :
    ∃ K₁ : IntermediateField K K', FiniteDimensional K K₁ ∧
      ∀ K₂ : IntermediateField K K', K₁ ≤ K₂ → Set.InjOn (res F F' K₂) ↑S := by
  classical
  have key : ∀ P : Place K' F' × Place K' F', ∃ K₀ : IntermediateField K K',
      FiniteDimensional K K₀ ∧
        (P.1 ≠ P.2 → ∀ K₂ : IntermediateField K K', K₀ ≤ K₂ → res F F' K₂ P.1 ≠ res F F' K₂ P.2) := by
    intro P
    by_cases hP : P.1 = P.2
    · exact ⟨⊥, inferInstance, fun h' => absurd hP h'⟩
    · obtain ⟨K₀, h1, h2⟩ := exists_fd_separating (K := K) hgen hP
      exact ⟨K₀, h1, fun _ => h2⟩
  choose g hg using key
  refine ⟨(S ×ˢ S).sup g, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun K₁ : IntermediateField K K' => FiniteDimensional K K₁)
      (inferInstance : FiniteDimensional K (⊥ : IntermediateField K K')) ?_ ?_
    · intro a ha b hb
      haveI : FiniteDimensional K a := ha
      haveI : FiniteDimensional K b := hb
      exact IntermediateField.finiteDimensional_sup a b
    · intro P _
      exact (hg P).1
  · intro K₂ hK₂ W hW W' hW' heq
    by_contra hne
    exact (hg (W, W')).2 hne K₂ ((Finset.le_sup (Finset.mk_mem_product hW hW')).trans hK₂) heq

theorem exists_fd_bijOn_res [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K']
    [HasPrincipalDivisors K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) (v : Place K F) :
    ∃ K₁ : IntermediateField K K', FiniteDimensional K K₁ ∧
      ∀ K₂ : IntermediateField K K', K₁ ≤ K₂ →
        Set.BijOn (res F F' K₂) ↑(Place.fiberConstants K' F' v) (fiberSet F F' K₂ v) := by
  obtain ⟨K₁, hfd, hinj⟩ := exists_fd_injOn (K := K) hgen (Place.fiberConstants K' F' v)
  exact ⟨K₁, hfd, fun K₂ hle =>
    ⟨mapsTo_res K₂ v, hinj K₂ hle, surjOn_res K₂ hgen hconst v⟩⟩

end Fibres

section Degrees

variable [Algebra.IsIntegral F F']

def ResGenerated {L E : Type*} [Field L] [Field E] [Algebra L E] (F₀ : Type*) [Field F₀]
    [Algebra F₀ E] (W : Place L E) : Prop :=
  Algebra.adjoin L {x : W.ResidueField |
      ∃ (a : F₀) (h : algebraMap F₀ E a ∈ W.toValuationSubring),
        IsLocalRing.residue W.toValuationSubring ⟨algebraMap F₀ E a, h⟩ = x} = ⊤

omit [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
  [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] in

theorem exists_residue_generator (v₀ : Place K F) [FiniteDimensional K v₀.ResidueField]
    [Algebra.IsSeparable K v₀.ResidueField] :
    ∃ (b : F) (_ : b ∈ v₀.toValuationSubring),
      ∀ (v : Place K F), v = v₀ → ∀ (hb : b ∈ v.toValuationSubring),
        IsIntegral K (IsLocalRing.residue v.toValuationSubring ⟨b, hb⟩) ∧
        Algebra.adjoin K {IsLocalRing.residue v.toValuationSubring ⟨b, hb⟩} = ⊤ := by
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element K v₀.ResidueField
  obtain ⟨b', hb'⟩ := IsLocalRing.residue_surjective β
  refine ⟨(b' : F), b'.2, ?_⟩
  intro v hv hb
  subst hv
  have hbb : (⟨(b' : F), hb⟩ : v.toValuationSubring) = b' := Subtype.ext rfl
  rw [hbb, hb']
  refine ⟨IsIntegral.of_finite K β, ?_⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.of_finite K β).isAlgebraic, hβ,
    IntermediateField.top_toSubalgebra]

omit [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] [Algebra F F']
  [IsScalarTower K F F'] [Algebra.IsIntegral F F'] in

theorem deg_eq_natDegree_minpoly {L E : Type*} [Field L] [Field E] [Algebra L E] (W : Place L E)
    (β : W.ResidueField) (hβ : IsIntegral L β) (htop : Algebra.adjoin L {β} = ⊤) :
    W.deg = (minpoly L β).natDegree := by
  have h1 : IntermediateField.adjoin L {β} = ⊤ := IntermediateField.toSubalgebra_injective (by
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβ.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra])
  rw [Place.deg, ← IntermediateField.finrank_top', ← h1, IntermediateField.adjoin.finrank hβ]

omit [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] [Algebra F F']
  [IsScalarTower K F F'] [Algebra.IsIntegral F F'] in

theorem restrictResidueMap_residue' {L E : Type*} [Field L] [Field E] [Algebra K L] [Algebra L E]
    [Algebra K E] [IsScalarTower K L E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E] (W : Place L E)
    (a : ((W.forgetConstants (K := K)).restrict F).toValuationSubring) :
    (Place.restrictResidueMap F (W.forgetConstants (K := K)) (IsLocalRing.residue _ a) :
        W.ResidueField)
      = IsLocalRing.residue W.toValuationSubring
          ⟨algebraMap F E (a : F), ValuationSubring.mem_comap.mp a.2⟩ :=
  Place.restrictResidueMap_residue (W.forgetConstants (K := K)) a

omit [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] [Algebra F F']
  [IsScalarTower K F F'] [Algebra.IsIntegral F F'] in

theorem restrictResidueMap_algebraMap {L E : Type*} [Field L] [Field E] [Algebra K L] [Algebra L E]
    [Algebra K E] [IsScalarTower K L E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E] (W : Place L E) (k : K) :
    (Place.restrictResidueMap F (W.forgetConstants (K := K))
        (algebraMap K ((W.forgetConstants (K := K)).restrict F).ResidueField k) : W.ResidueField)
      = algebraMap L W.ResidueField (algebraMap K L k) := by
  rw [IsScalarTower.algebraMap_apply K ((W.forgetConstants (K := K)).restrict F).toValuationSubring
      ((W.forgetConstants (K := K)).restrict F).ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq, restrictResidueMap_residue',
    IsScalarTower.algebraMap_apply L W.toValuationSubring W.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]
  congr 1
  apply Subtype.ext
  show algebraMap F E (algebraMap K F k) = algebraMap L E (algebraMap K L k)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

omit [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] [Algebra F F']
  [IsScalarTower K F F'] [Algebra.IsIntegral F F'] in

theorem isIntegral_restrictResidueMap {L E : Type*} [Field L] [Field E] [Algebra K L] [Algebra L E]
    [Algebra K E] [IsScalarTower K L E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E] (W : Place L E)
    {y : ((W.forgetConstants (K := K)).restrict F).ResidueField} (hy : IsIntegral K y) :
    IsIntegral L (A := W.ResidueField) (Place.restrictResidueMap F (W.forgetConstants (K := K)) y) := by
  let φ : ((W.forgetConstants (K := K)).restrict F).ResidueField →+* W.ResidueField :=
    Place.restrictResidueMap F (W.forgetConstants (K := K))
  show IsIntegral L (φ y)
  obtain ⟨p, hpm, hp0⟩ := hy
  refine ⟨p.map (algebraMap K L), hpm.map _, ?_⟩
  have hcomp : φ.comp (algebraMap K ((W.forgetConstants (K := K)).restrict F).ResidueField)
        = (algebraMap L W.ResidueField).comp (algebraMap K L) :=
    RingHom.ext (restrictResidueMap_algebraMap (K := K) W)
  rw [Polynomial.eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hp0, map_zero]

omit [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] [Algebra F F']
  [IsScalarTower K F F'] [Algebra.IsIntegral F F'] in

theorem deg_eq_of_resGenerated {L E : Type*} [Field L] [Field E] [Algebra K L] [Algebra L E]
    [Algebra K E] [IsScalarTower K L E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E]
    (W : Place L E) (hRC : ResGenerated F W)
    {b : F} (hb : algebraMap F E b ∈ W.toValuationSubring)
    (hint : IsIntegral K (IsLocalRing.residue
      ((W.forgetConstants (K := K)).restrict F).toValuationSubring ⟨b, hb⟩))
    (hgen : Algebra.adjoin K {IsLocalRing.residue
      ((W.forgetConstants (K := K)).restrict F).toValuationSubring ⟨b, hb⟩} = ⊤) :
    IsIntegral L (IsLocalRing.residue W.toValuationSubring ⟨algebraMap F E b, hb⟩) ∧
    W.deg = (minpoly L (IsLocalRing.residue W.toValuationSubring ⟨algebraMap F E b, hb⟩)).natDegree := by
  set v : Place K F := (W.forgetConstants (K := K)).restrict F with hv
  set β : v.ResidueField := IsLocalRing.residue v.toValuationSubring ⟨b, hb⟩ with hβdef
  set βW : W.ResidueField := IsLocalRing.residue W.toValuationSubring ⟨algebraMap F E b, hb⟩
    with hβWdef
  let φ : v.ResidueField →+* W.ResidueField := Place.restrictResidueMap F (W.forgetConstants (K := K))
  have hφβ : φ β = βW := restrictResidueMap_residue' (K := K) W ⟨b, hb⟩

  have hS : ∀ y : v.ResidueField, φ y ∈ Algebra.adjoin L {βW} := by
    intro y
    have hy : y ∈ Algebra.adjoin K {β} := by rw [hgen]; exact Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx, hφβ]
      exact Algebra.self_mem_adjoin_singleton L βW
    | algebraMap k =>
      rw [show φ (algebraMap K v.ResidueField k) = algebraMap L W.ResidueField (algebraMap K L k)
        from restrictResidueMap_algebraMap (K := K) W k]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : Algebra.adjoin L {βW} = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [ResGenerated] at hRC
    rw [← hRC]
    refine Algebra.adjoin_le ?_
    rintro x ⟨a, ha, rfl⟩
    exact hS (IsLocalRing.residue _ ⟨a, ha⟩)
  have hintW : IsIntegral L βW := hφβ ▸ isIntegral_restrictResidueMap (K := K) W hint
  exact ⟨hintW, deg_eq_natDegree_minpoly W βW hintW htop⟩

theorem natDegree_minpoly_res_eq (K₂ : IntermediateField K K') (W : Place K' F') {b : F}
    (hbW : algebraMap F F' b ∈ W.toValuationSubring)
    (hbU : algebraMap F (FK F F' K₂) b ∈ (res F F' K₂ W).toValuationSubring)
    (hintU : IsIntegral K₂
      (IsLocalRing.residue (res F F' K₂ W).toValuationSubring ⟨algebraMap F (FK F F' K₂) b, hbU⟩))
    (hintW : IsIntegral K' (IsLocalRing.residue W.toValuationSubring ⟨algebraMap F F' b, hbW⟩))
    (hcoeff : ∀ n : ℕ,
      (minpoly K' (IsLocalRing.residue W.toValuationSubring ⟨algebraMap F F' b, hbW⟩)).coeff n ∈ K₂) :
    (minpoly K₂ (IsLocalRing.residue (res F F' K₂ W).toValuationSubring
        ⟨algebraMap F (FK F F' K₂) b, hbU⟩)).natDegree
      = (minpoly K' (IsLocalRing.residue W.toValuationSubring ⟨algebraMap F F' b, hbW⟩)).natDegree := by
  set U := res F F' K₂ W with hU
  set βU : U.ResidueField := IsLocalRing.residue U.toValuationSubring ⟨algebraMap F (FK F F' K₂) b, hbU⟩
    with hβUdef
  set βW : W.ResidueField := IsLocalRing.residue W.toValuationSubring ⟨algebraMap F F' b, hbW⟩
    with hβWdef
  let ψ : U.ResidueField →+* W.ResidueField :=
    Place.restrictResidueMap (FK F F' K₂) (W.forgetConstants (K := K₂))
  have hψres : ∀ a : U.toValuationSubring,
      ψ (IsLocalRing.residue _ a) = IsLocalRing.residue W.toValuationSubring
        ⟨algebraMap (FK F F' K₂) F' (a : FK F F' K₂), ValuationSubring.mem_comap.mp a.2⟩ := fun a =>
    Place.restrictResidueMap_residue (W.forgetConstants (K := K₂)) a
  have hψβ : ψ βU = βW := by
    rw [hβUdef, hψres]
    congr 1
  have hψK : ∀ k : K₂, ψ (algebraMap K₂ U.ResidueField k) = algebraMap K' W.ResidueField (k : K') := by
    intro k
    rw [IsScalarTower.algebraMap_apply K₂ U.toValuationSubring U.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq, hψres,
      IsScalarTower.algebraMap_apply K' W.toValuationSubring W.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
    congr 1
  have hcomp : ψ.comp (algebraMap K₂ U.ResidueField)
      = (algebraMap K' W.ResidueField).comp (algebraMap K₂ K') := RingHom.ext hψK
  apply le_antisymm
  ·
    set P := minpoly K' βW with hP
    have hlifts : P ∈ Polynomial.lifts (algebraMap K₂ K') := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨P.coeff n, hcoeff n⟩, rfl⟩
    obtain ⟨P₂, hP₂, hdeg, -⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic hlifts (minpoly.monic hintW)
    have hP0 : P ≠ 0 := minpoly.ne_zero hintW
    have hP₂0 : P₂ ≠ 0 := by
      rintro rfl
      rw [Polynomial.map_zero] at hP₂
      exact hP0 hP₂.symm
    have hroot : Polynomial.aeval βU P₂ = 0 := by
      apply ψ.injective
      rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, hψβ, ← Polynomial.eval₂_map,
        hP₂, ← Polynomial.aeval_def, hP, minpoly.aeval]
    calc (minpoly K₂ βU).natDegree ≤ P₂.natDegree :=
          Polynomial.natDegree_le_of_dvd (minpoly.dvd K₂ βU hroot) hP₂0
      _ = P.natDegree := by
          rw [← hP₂, Polynomial.natDegree_map]
  ·
    set Q := minpoly K₂ βU with hQ
    have hQm : (Q.map (algebraMap K₂ K')).Monic := (minpoly.monic hintU).map _
    have hroot : Polynomial.aeval βW (Q.map (algebraMap K₂ K')) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hcomp, ← hψβ, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, hQ, minpoly.aeval, map_zero]
    calc (minpoly K' βW).natDegree ≤ (Q.map (algebraMap K₂ K')).natDegree :=
          Polynomial.natDegree_le_of_dvd (minpoly.dvd K' βW hroot) hQm.ne_zero
      _ = Q.natDegree := Polynomial.natDegree_map _

theorem exists_fd_deg_res_eq_one [Algebra.IsAlgebraic K K']
    [∀ v : Place K F, FiniteDimensional K v.ResidueField]
    [∀ v : Place K F, Algebra.IsSeparable K v.ResidueField]
    (hRCW : ∀ W : Place K' F', ResGenerated F W)
    (hRCU : ∀ (K₂ : IntermediateField K K') (U : Place K₂ (FK F F' K₂)), ResGenerated F U)
    (W : Place K' F') :
    ∃ K₁ : IntermediateField K K', FiniteDimensional K K₁ ∧
      ∀ K₂ : IntermediateField K K', K₁ ≤ K₂ → (res F F' K₂ W).deg = W.deg := by

  set v₀ : Place K F := (W.forgetConstants (K := K)).restrict F with hv₀
  obtain ⟨b, hb₀, hgenv⟩ := exists_residue_generator (K := K) v₀
  have hbW : algebraMap F F' b ∈ W.toValuationSubring := ValuationSubring.mem_comap.mp hb₀

  obtain ⟨hintv, hgen₀⟩ := hgenv v₀ rfl hb₀
  obtain ⟨hintW, hdegW⟩ := deg_eq_of_resGenerated (K := K) W (hRCW W) hbW hintv hgen₀
  set βW : W.ResidueField := IsLocalRing.residue W.toValuationSubring ⟨algebraMap F F' b, hbW⟩
    with hβWdef

  refine ⟨IntermediateField.adjoin K (↑(minpoly K' βW).coeffs : Set K'),
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral), ?_⟩
  intro K₂ hK₂

  have hbU : algebraMap F (FK F F' K₂) b ∈ (res F F' K₂ W).toValuationSubring := by
    rw [mem_res_iff]
    exact hbW
  have hv₁ : ((res F F' K₂ W).forgetConstants (K := K)).restrict F = v₀ :=
    restrictConstants_res K₂ W
  obtain ⟨hintv₁, hgen₁⟩ := hgenv _ hv₁ hbU
  obtain ⟨hintU, hdegU⟩ :=
    deg_eq_of_resGenerated (K := K) (res F F' K₂ W) (hRCU K₂ _) hbU hintv₁ hgen₁
  rw [hdegU, hdegW]
  apply natDegree_minpoly_res_eq K₂ W hbW hbU hintU hintW
  intro n
  by_cases hn : (minpoly K' βW).coeff n = 0
  · rw [hn]; exact zero_mem _
  · exact hK₂ (IntermediateField.subset_adjoin K _ (Finset.mem_coe.mpr (Polynomial.coeff_mem_coeffs hn)))

theorem exists_fd_deg_res_eq [Algebra.IsAlgebraic K K'] [HasPrincipalDivisors K' F']
    [∀ v : Place K F, FiniteDimensional K v.ResidueField]
    [∀ v : Place K F, Algebra.IsSeparable K v.ResidueField]
    (hRCW : ∀ W : Place K' F', ResGenerated F W)
    (hRCU : ∀ (K₂ : IntermediateField K K') (U : Place K₂ (FK F F' K₂)), ResGenerated F U)
    (v : Place K F) :
    ∃ K₁ : IntermediateField K K', FiniteDimensional K K₁ ∧
      ∀ K₂ : IntermediateField K K', K₁ ≤ K₂ →
        ∀ W ∈ Place.fiberConstants K' F' v, (res F F' K₂ W).deg = W.deg := by
  classical
  choose g hg using fun W : Place K' F' => exists_fd_deg_res_eq_one (K := K) hRCW hRCU W
  refine ⟨(Place.fiberConstants K' F' v).sup g, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun K₁ : IntermediateField K K' => FiniteDimensional K K₁)
      (inferInstance : FiniteDimensional K (⊥ : IntermediateField K K')) ?_ ?_
    · intro a ha b hb
      haveI : FiniteDimensional K a := ha
      haveI : FiniteDimensional K b := hb
      exact IntermediateField.finiteDimensional_sup a b
    · intro W _
      exact (hg W).1
  · intro K₂ hK₂ W hW
    exact (hg W).2 K₂ ((Finset.le_sup hW).trans hK₂)

end Degrees

section Bridge

omit [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] [Algebra F F']
  [IsScalarTower K F F'] in

theorem setOf_residue_eq_range {L E : Type*} [Field L] [Field E] [Algebra K L] [Algebra L E]
    [Algebra K E] [IsScalarTower K L E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E] (W : Place L E) :
    {x : W.ResidueField | ∃ (a : F) (h : algebraMap F E a ∈ W.toValuationSubring),
        IsLocalRing.residue W.toValuationSubring ⟨algebraMap F E a, h⟩ = x}
      = Set.range (Place.restrictResidueMap F (W.forgetConstants (K := K))) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨IsLocalRing.residue _ ⟨a, ha⟩, ?_⟩
    exact Place.restrictResidueMap_residue (W.forgetConstants (K := K)) ⟨a, ha⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, a.2, (Place.restrictResidueMap_residue (W.forgetConstants (K := K)) a).symm⟩

omit [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] [Algebra F F']
  [IsScalarTower K F F'] in

theorem resGenerated_of_adjoin_range_eq_top {L E : Type*} [Field L] [Field E] [Algebra K L]
    [Algebra L E] [Algebra K E] [IsScalarTower K L E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E] (W : Place L E)
    (h : Algebra.adjoin L (A := W.ResidueField)
        (Set.range (Place.restrictResidueMap F (W.forgetConstants (K := K)))) = ⊤) :
    ResGenerated F W := by
  rw [ResGenerated, setOf_residue_eq_range (K := K)]
  exact h

omit [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra K K'] [Algebra F F']
  [IsScalarTower K F F'] in

theorem resGenerated_of_intermediateField_adjoin_range_eq_top {L E : Type*} [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E] [Algebra F E]
    [IsScalarTower K F E] [Algebra.IsIntegral F E] (W : Place L E)
    [FiniteDimensional K ((W.forgetConstants (K := K)).restrict F).ResidueField]
    (h : IntermediateField.adjoin L (E := W.ResidueField)
        (Set.range (Place.restrictResidueMap F (W.forgetConstants (K := K)))) = ⊤) :
    ResGenerated F W := by
  apply resGenerated_of_adjoin_range_eq_top (K := K) W
  have halg : ∀ x ∈ (Set.range (Place.restrictResidueMap F (W.forgetConstants (K := K))) :
      Set W.ResidueField), IsAlgebraic L x := by
    rintro _ ⟨y, rfl⟩
    exact (isIntegral_restrictResidueMap (K := K) W (IsIntegral.of_finite K y)).isAlgebraic
  have h' := congrArg IntermediateField.toSubalgebra h
  rwa [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, IntermediateField.top_toSubalgebra] at h'

end Bridge

end P2MWs12.Descent
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12 P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12.Descent"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12"

namespace P2MWs12
namespace Descent
open AlgebraicCurve IntermediateField

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
variable (K₁ : IntermediateField K K')

theorem finiteDimensional_FK [Algebra.IsIntegral F F'] [FiniteDimensional K K₁] :
    FiniteDimensional F (FK F F' K₁) := by
  classical
  let b := Module.finBasis K K₁
  have hFK : FK F F' K₁ = IntermediateField.adjoin F
      ((Finset.univ.image fun i => algebraMap K' F' (b i : K')) : Set F') := by
    apply le_antisymm
    · rw [FK, IntermediateField.adjoin_le_iff]
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (⟨k, hk⟩ : K₁) = ∑ i, (b.repr ⟨k, hk⟩ i) • b i := (b.sum_repr ⟨k, hk⟩).symm
      have hval : algebraMap K' F' k = algebraMap K' F' (K₁.val (∑ i, (b.repr ⟨k, hk⟩ i) • b i)) := by
        rw [← hk']; rfl
      rw [hval, map_sum, map_sum]
      refine sum_mem fun i _ => ?_
      rw [map_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K K' F',
        IsScalarTower.algebraMap_apply K F F']
      exact mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.subset_adjoin _ _ (by simp))
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
      obtain ⟨i, rfl⟩ := hy
      exact algebraMap_mem_FK K₁ (b i)
  rw [hFK]
  exact IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsIntegral.isIntegral (R := F) y)

theorem isSeparable_FK [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K₁] :
    Algebra.IsSeparable F (FK F F' K₁) :=
  P2MWs12.ConstFieldDeg.isSeparable_of_adjoin_range_eq_top (K := K) (adjoin_range_FK_eq_top K₁)

theorem isCurveOver_FK [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [Algebra.IsIntegral F F'] [Algebra.IsAlgebraic K K'] [FiniteDimensional K K₁] :
    IsCurveOver K (FK F F' K₁) := by
  obtain ⟨t, ht, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := hfd
  haveI := hsep
  haveI : FiniteDimensional F (FK F F' K₁) := finiteDimensional_FK K₁
  haveI : Algebra.IsAlgebraic K K₁ := Algebra.IsAlgebraic.of_finite K K₁
  haveI : Algebra.IsSeparable K K₁ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable F (FK F F' K₁) := isSeparable_FK K₁

  haveI : IsScalarTower (IntermediateField.adjoin K ({t} : Set F)) F (FK F F' K₁) := inferInstance
  haveI : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) (FK F F' K₁) :=
    Module.Finite.trans F (FK F F' K₁)
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) (FK F F' K₁) :=
    Algebra.IsSeparable.trans (IntermediateField.adjoin K ({t} : Set F)) F (FK F F' K₁)

  set x : FK F F' K₁ := algebraMap F (FK F F' K₁) t with hx
  have hxt : Transcendental K x :=
    (transcendental_algebraMap_iff (algebraMap F (FK F F' K₁)).injective).mpr ht
  have hmap : (IntermediateField.adjoin K ({t} : Set F)).map (IsScalarTower.toAlgHom K F (FK F F' K₁))
      = IntermediateField.adjoin K ({x} : Set (FK F F' K₁)) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
  let e : IntermediateField.adjoin K ({t} : Set F) ≃ₐ[K] IntermediateField.adjoin K ({x} : Set (FK F F' K₁)) :=
    ((IntermediateField.adjoin K ({t} : Set F)).equivMap (IsScalarTower.toAlgHom K F (FK F F' K₁))).trans
      (IntermediateField.equivOfEq hmap)
  have he : (algebraMap (IntermediateField.adjoin K ({x} : Set (FK F F' K₁))) (FK F F' K₁)).comp
      (e : IntermediateField.adjoin K ({t} : Set F) →+* IntermediateField.adjoin K ({x} : Set (FK F F' K₁)))
      = (RingEquiv.refl (FK F F' K₁) : FK F F' K₁ →+* FK F F' K₁).comp
        (algebraMap (IntermediateField.adjoin K ({t} : Set F)) (FK F F' K₁)) := by
    ext a
    rfl
  haveI : FiniteDimensional (IntermediateField.adjoin K ({x} : Set (FK F F' K₁))) (FK F F' K₁) :=
    Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl _) he
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set (FK F F' K₁))) (FK F F' K₁) :=
    Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl _) he
  exact isCurveOver_of_transcendental hxt inferInstance inferInstance

end P2MWs12.Descent
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12 P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12.Descent"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12 P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12.Descent"

namespace P2MWs12
namespace Descent
open AlgebraicCurve IntermediateField

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

theorem degree_equivMapDomain_constantFieldEquiv_symm {M : Type*} [Field M] [Algebra K M]
    (K₁ : IntermediateField K K') [Algebra K₁ M] [IsScalarTower K K₁ M] [FiniteDimensional K K₁]
    (D : Divisor K₁ M) :
    Divisor.degree (D.equivMapDomain (Place.constantFieldEquiv K K₁ (F' := M)).symm)
      = (Module.finrank K K₁ : ℤ) * Divisor.degree D := by
  classical
  rw [Finsupp.equivMapDomain_eq_mapDomain, Divisor.degree, Divisor.degree,
    Finsupp.liftAddHom_apply, Finsupp.liftAddHom_apply,
    Finsupp.sum_mapDomain_index_inj (Equiv.injective _), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun W _ => ?_
  simp only [AddMonoidHom.mulRight_apply, Place.constantFieldEquiv_symm_apply,
    P2MWs12.ConstFieldDeg.deg_forget_eq]
  push_cast
  ring

variable (K₁ : IntermediateField K K')

theorem hasPrincipalDivisors_FK [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [Algebra.IsIntegral F F'] [Algebra.IsAlgebraic K K'] [FiniteDimensional K K₁] :
    HasPrincipalDivisors K₁ (FK F F' K₁) := by
  classical
  haveI : IsCurveOver K (FK F F' K₁) := isCurveOver_FK K₁
  refine ⟨fun f hf => ?_⟩
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  set e := Place.constantFieldEquiv K K₁ (F' := FK F F' K₁) with he
  refine ⟨D.equivMapDomain e, fun W => ?_, ?_⟩
  · rw [Finsupp.equivMapDomain_apply]
    exact hD _
  · have h1 : (D.equivMapDomain e).equivMapDomain e.symm = D := by
      ext w; simp
    have h2 := degree_equivMapDomain_constantFieldEquiv_symm (K := K) K₁ (D.equivMapDomain e)
    rw [h1, hdeg] at h2
    have hpos : (Module.finrank K K₁ : ℤ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
    exact (mul_eq_zero.mp h2.symm).resolve_left hpos

theorem sum_deg_fiberConstants_FK [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [Algebra.IsIntegral F F'] [Algebra.IsAlgebraic K K'] [FiniteDimensional K K₁]
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) (v : Place K F) :
    haveI := hasPrincipalDivisors_FK (F := F) (F' := F') K₁
    ∑ U ∈ Place.fiberConstants K₁ (FK F F' K₁) v, (U.deg : ℤ) = v.deg := by
  haveI := hasPrincipalDivisors_FK (F := F) (F' := F') K₁
  haveI : Algebra.IsAlgebraic K K₁ := Algebra.IsAlgebraic.of_finite K K₁
  haveI : Algebra.IsSeparable K K₁ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact P2MWs12.ConstFieldDeg.sum_deg_fiberConstants_eq (K := K) (K' := K₁) (F := F)
    (F' := FK F F' K₁) (adjoin_range_FK_eq_top K₁) hconst v

theorem coe_fiberConstants_FK [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [Algebra.IsIntegral F F'] [Algebra.IsAlgebraic K K'] [FiniteDimensional K K₁] (v : Place K F) :
    haveI := hasPrincipalDivisors_FK (F := F) (F' := F') K₁
    (↑(Place.fiberConstants K₁ (FK F F' K₁) v) : Set (Place K₁ (FK F F' K₁))) = fiberSet F F' K₁ v := by
  ext U
  simp only [Finset.mem_coe, Place.mem_fiberConstants, mem_fiberSet]

end P2MWs12.Descent
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12 P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12.Descent"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12 P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12.Descent"

namespace P2MWs12
namespace Descent
open AlgebraicCurve IntermediateField

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

theorem sum_deg_fiberConstants_eq_deg [PerfectField K] [Algebra.IsAlgebraic K K'] [Algebra.IsIntegral F F']
    [Algebra.EssFiniteType K F] [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (hRCW : ∀ W : Place K' F', ResGenerated F W)
    (hRCU : ∀ (K₂ : IntermediateField K K') (U : Place K₂ (FK F F' K₂)), ResGenerated F U)
    (v : Place K F) :
    ∑ W ∈ Place.fiberConstants K' F' v, (W.deg : ℤ) = v.deg := by
  classical
  haveI : Algebra.IsSeparable K K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : ∀ u : Place K F, FiniteDimensional K u.ResidueField := fun u => IsCurveOver.finiteResidue u
  haveI : ∀ u : Place K F, Algebra.IsSeparable K u.ResidueField := fun u =>
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨K₁, hK₁, hbij⟩ := exists_fd_bijOn_res (K := K) hgen hconst v
  obtain ⟨K₂, hK₂, hdeg⟩ := exists_fd_deg_res_eq (K := K) hRCW hRCU v
  haveI : FiniteDimensional K K₁ := hK₁
  haveI : FiniteDimensional K K₂ := hK₂
  haveI : FiniteDimensional K (K₁ ⊔ K₂ : IntermediateField K K') :=
    IntermediateField.finiteDimensional_sup K₁ K₂
  have hb := hbij (K₁ ⊔ K₂) le_sup_left
  have hd := hdeg (K₁ ⊔ K₂) le_sup_right
  haveI := hasPrincipalDivisors_FK (F := F) (F' := F') (K₁ ⊔ K₂)
  rw [← coe_fiberConstants_FK (K₁ ⊔ K₂) v] at hb
  calc ∑ W ∈ Place.fiberConstants K' F' v, (W.deg : ℤ)
      = ∑ W ∈ Place.fiberConstants K' F' v, ((res F F' (K₁ ⊔ K₂) W).deg : ℤ) :=
        Finset.sum_congr rfl fun W hW => by rw [hd W hW]
    _ = ∑ U ∈ Place.fiberConstants (K₁ ⊔ K₂ : IntermediateField K K') (FK F F' (K₁ ⊔ K₂)) v, (U.deg : ℤ) :=
        Finset.sum_nbij (res F F' (K₁ ⊔ K₂)) (fun W hW => Finset.mem_coe.mp (hb.mapsTo (Finset.mem_coe.mpr hW)))
          (fun W hW W' hW' h => hb.injOn hW hW' h)
          (fun U hU => by
            obtain ⟨W, hW, rfl⟩ := hb.surjOn hU
            exact ⟨W, hW, rfl⟩)
          (fun W _ => rfl)
    _ = v.deg := sum_deg_fiberConstants_FK (K₁ ⊔ K₂) hconst v

theorem resGenerated_top [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [IsCurveOver K F]
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) (W : Place K' F') : ResGenerated F W := by
  haveI : ∀ u : Place K F, FiniteDimensional K u.ResidueField := fun u => IsCurveOver.finiteResidue u
  exact resGenerated_of_intermediateField_adjoin_range_eq_top (K := K) W
    (AlgebraicCurve.Place.residueField_eq_compositum_of_isConstantFieldExtension (K := K) hgen W)

theorem resGenerated_FK [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [IsCurveOver K F]
    (K₂ : IntermediateField K K') (U : Place K₂ (FK F F' K₂)) : ResGenerated F U := by
  haveI : Algebra.IsAlgebraic K K₂ :=
    ⟨fun x => (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K K₂ K') Subtype.val_injective).mp
      (Algebra.IsAlgebraic.isAlgebraic (x : K'))⟩
  haveI : Algebra.IsSeparable K K₂ := Algebra.isSeparable_tower_bot_of_isSeparable K K₂ K'
  haveI : ∀ u : Place K F, FiniteDimensional K u.ResidueField := fun u => IsCurveOver.finiteResidue u
  exact resGenerated_of_intermediateField_adjoin_range_eq_top (K := K) U
    (AlgebraicCurve.Place.residueField_eq_compositum_of_isConstantFieldExtension
      (K := K) (K' := K₂) (F := F) (F' := FK F F' K₂) (adjoin_range_FK_eq_top K₂) U)

end P2MWs12.Descent
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12 P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12.Descent"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12 P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver.P2MWs12.Descent"

open AlgebraicCurve in
theorem solution
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [PerfectField K] [Algebra.IsAlgebraic K K'] [Algebra.IsIntegral F F']
    [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (v : AlgebraicCurve.Place K F) :
    ∑ W ∈ AlgebraicCurve.Place.fiberConstants K' F' v, (W.deg : ℤ) = v.deg := by
  haveI : Algebra.IsSeparable K K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact P2MWs12.Descent.sum_deg_fiberConstants_eq_deg hgen hconst
    (fun W => P2MWs12.Descent.resGenerated_top (K := K) hgen W)
    (fun K₂ U => P2MWs12.Descent.resGenerated_FK (K := K) K₂ U) v

end S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver
end P2MW
export P2MW.S_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver (solution)
