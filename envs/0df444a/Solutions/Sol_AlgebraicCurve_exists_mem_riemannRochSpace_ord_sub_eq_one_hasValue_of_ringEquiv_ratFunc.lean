-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a5024ef4-7cd1-54c6-a715-190ae95f2be5

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

open IsLocalRing Polynomial
open scoped Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum Place.congrRingEquiv Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply RationalFunctionField.placeInfty Place.residue_algebraMap"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "adicValuation_eq_exp_neg_ord ext coe_algebraMap ResidueField deg adicValuation ord ord_zero ord_mul ord_inv ofHeightOneSpectrum algebraMap_mem' toValuationSubring mem_iff_adicValuation_le_one mem_maximalIdeal_iff_adicValuation_lt_one comapSymmRingEquiv congrRingEquiv ord_congrRingEquiv congrResidueAlgEquiv congrEquiv congrEquiv_apply residue_algebraMap HasValue"
p2m_open "AlgebraicCurve.Place~restrict"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_of_ord_sub_algebraMap_pos (v : Place K F) {g : F} {γ : K}
    (h : 0 < v.ord (g - algebraMap K F γ)) : v.HasValue g γ := by
  have hne : g - algebraMap K F γ ≠ 0 := by
    intro h0
    rw [h0, ord_zero] at h
    exact lt_irrefl _ h
  have hval : v.adicValuation (g - algebraMap K F γ) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord hne, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hmem : g - algebraMap K F γ ∈ v.toValuationSubring :=
    v.mem_iff_adicValuation_le_one.mpr hval.le
  have hg : g ∈ v.toValuationSubring := by
    have := add_mem hmem (v.algebraMap_mem' γ)
    rwa [sub_add_cancel] at this
  refine ⟨hg, ?_⟩
  have hmax : (⟨g - algebraMap K F γ, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal _ :=
    (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hval
  rw [← residue_eq_zero_iff] at hmax
  have hx : (⟨g - algebraMap K F γ, hmem⟩ : v.toValuationSubring)
      = ⟨g, hg⟩ - algebraMap K v.toValuationSubring γ := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, coe_algebraMap]
  rw [hx, map_sub, sub_eq_zero, residue_algebraMap] at hmax
  exact hmax

section CongrTransport

variable {F' : Type*} [Field F'] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he

theorem congrResidueAlgEquiv_residue (v : Place K F) (x : v.toValuationSubring) :
    congrResidueAlgEquiv e he v (IsLocalRing.residue _ x)
      = IsLocalRing.residue _ (comapSymmRingEquiv e v.toValuationSubring x) := by
  show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem hasValue_congrRingEquiv_iff (v : Place K F) (g : F) (c : K) :
    (congrRingEquiv e he v).HasValue (e g) c ↔ v.HasValue g c := by
  have hmem : e g ∈ (congrRingEquiv e he v).toValuationSubring ↔ g ∈ v.toValuationSubring := by
    show e.symm (e g) ∈ v.toValuationSubring ↔ _
    rw [e.symm_apply_apply]
  have key : ∀ hg : g ∈ v.toValuationSubring,
      IsLocalRing.residue _ (⟨e g, hmem.mpr hg⟩ : (congrRingEquiv e he v).toValuationSubring)
        = congrResidueAlgEquiv e he v (IsLocalRing.residue _ ⟨g, hg⟩) := by
    intro hg
    rw [congrResidueAlgEquiv_residue]
    rfl
  constructor
  · rintro ⟨h, hr⟩
    refine ⟨hmem.mp h, (congrResidueAlgEquiv e he v).injective ?_⟩
    rw [AlgEquiv.commutes, ← key (hmem.mp h)]
    exact hr
  · rintro ⟨hg, hr⟩
    refine ⟨hmem.mpr hg, ?_⟩
    rw [key hg, hr, AlgEquiv.commutes]

theorem mem_riemannRochSpace_mapDomain_congrEquiv_iff (D : Divisor K F) (f : F) :
    e f ∈ riemannRochSpace (Finsupp.mapDomain (congrEquiv e he) D) ↔ f ∈ riemannRochSpace D := by
  rw [mem_riemannRochSpace_iff, mem_riemannRochSpace_iff]
  constructor
  · intro h v
    have := h (congrEquiv e he v)
    rwa [Finsupp.mapDomain_apply (congrEquiv e he).injective, congrEquiv_apply, ord_congrRingEquiv,
      EmbeddingLike.map_eq_zero_iff] at this
  · intro h v'
    obtain ⟨v, rfl⟩ := (congrEquiv e he).surjective v'
    rw [Finsupp.mapDomain_apply (congrEquiv e he).injective, congrEquiv_apply, ord_congrRingEquiv,
      EmbeddingLike.map_eq_zero_iff]
    exact h v

theorem algebraMap_comm_trans {F'' : Type*} [Field F''] [Algebra K F''] (e' : F' ≃+* F'')
    (he' : ∀ a : K, e' (algebraMap K F' a) = algebraMap K F'' a) (a : K) :
    (e.trans e') (algebraMap K F a) = algebraMap K F'' a := by
  rw [RingEquiv.trans_apply, he, he']

theorem congrEquiv_trans_apply {F'' : Type*} [Field F''] [Algebra K F''] (e' : F' ≃+* F'')
    (he' : ∀ a : K, e' (algebraMap K F' a) = algebraMap K F'' a) (v : Place K F) :
    congrEquiv (e.trans e') (algebraMap_comm_trans e he e' he') v
      = congrEquiv e' he' (congrEquiv e he v) := by
  ext x
  show (e.trans e').symm x ∈ v.toValuationSubring ↔ e.symm (e'.symm x) ∈ v.toValuationSubring
  rfl

end CongrTransport

end Place

end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum Place.congrRingEquiv Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply RationalFunctionField.placeInfty Place.residue_algebraMap"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum surjective_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

variable (k : Type*) [Field k]

section Points

def divisorPoints (E : Divisor k (RatFunc k)) : Finset k :=
  E.support.preimage (placeOfPoint k) ((placeOfPoint_injective k).injOn)

variable {k}

@[scoped simp]
theorem mem_divisorPoints {E : Divisor k (RatFunc k)} {a : k} :
    a ∈ divisorPoints k E ↔ E (placeOfPoint k a) ≠ 0 := by
  simp [divisorPoints]

variable (k) in

def divisorPolynomial (E : Divisor k (RatFunc k)) : k[X] :=
  ∏ a ∈ divisorPoints k E, (X - C a) ^ (E (placeOfPoint k a)).toNat

theorem divisorPolynomial_ne_zero (E : Divisor k (RatFunc k)) : divisorPolynomial k E ≠ 0 := by
  rw [divisorPolynomial]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (X_sub_C_ne_zero a)

theorem algebraMap_divisorPolynomial_ne_zero (E : Divisor k (RatFunc k)) :
    algebraMap k[X] (RatFunc k) (divisorPolynomial k E) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (divisorPolynomial_ne_zero E)

theorem rootMultiplicity_divisorPolynomial (E : Divisor k (RatFunc k)) (b : k) :
    rootMultiplicity b (divisorPolynomial k E) = (E (placeOfPoint k b)).toNat := by
  classical
  rw [divisorPolynomial]
  have key : ∀ s : Finset k, rootMultiplicity b (∏ a ∈ s, (X - C a) ^ (E (placeOfPoint k a)).toNat)
      = if b ∈ s then (E (placeOfPoint k b)).toNat else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, rootMultiplicity_mul, ih]
      · by_cases hb : b = a
        · subst hb
          rw [rootMultiplicity_X_sub_C_pow]
          simp [ha]
        · have h0 : rootMultiplicity b ((X - C a) ^ (E (placeOfPoint k a)).toNat) = 0 := by
            refine rootMultiplicity_eq_zero ?_
            rw [IsRoot, eval_pow, eval_sub, eval_X, eval_C]
            exact pow_ne_zero _ (sub_ne_zero.mpr hb)
          rw [h0]
          simp [hb, Finset.mem_insert]
      · exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a))
          (Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (X_sub_C_ne_zero a))
  rw [key]
  by_cases hb : b ∈ divisorPoints k E
  · simp [hb]
  · rw [if_neg hb]
    rw [mem_divisorPoints, not_not] at hb
    simp [hb]

theorem natDegree_divisorPolynomial (E : Divisor k (RatFunc k)) :
    (divisorPolynomial k E).natDegree = ∑ a ∈ divisorPoints k E, (E (placeOfPoint k a)).toNat := by
  rw [divisorPolynomial, natDegree_prod _ _ fun a _ => pow_ne_zero _ (X_sub_C_ne_zero a)]
  simp [natDegree_pow]

theorem eval_divisorPolynomial_ne_zero {E : Divisor k (RatFunc k)} {b : k} (hb : E (placeOfPoint k b) = 0) :
    (divisorPolynomial k E).eval b ≠ 0 := by
  rw [divisorPolynomial, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
  rw [eval_pow]
  refine pow_ne_zero _ ?_
  rw [eval_sub, eval_X, eval_C, sub_ne_zero]
  rintro rfl
  exact (mem_divisorPoints.mp ha) hb

theorem ord_placeOfPoint_divisorPolynomial (E : Divisor k (RatFunc k)) (b : k) :
    (placeOfPoint k b).ord (algebraMap k[X] (RatFunc k) (divisorPolynomial k E))
      = (E (placeOfPoint k b)).toNat := by
  rw [ord_placeOfPoint_algebraMap b (divisorPolynomial_ne_zero E), rootMultiplicity_divisorPolynomial]

theorem ord_placeInfty_divisorPolynomial [DecidableEq (RatFunc k)] (E : Divisor k (RatFunc k)) :
    (placeInfty k).ord (algebraMap k[X] (RatFunc k) (divisorPolynomial k E))
      = -((divisorPolynomial k E).natDegree : ℤ) := by
  rw [ord_placeInfty (algebraMap_divisorPolynomial_ne_zero E), RatFunc.intDegree_polynomial]

theorem ord_placeOfPoint_div_divisorPolynomial (E : Divisor k (RatFunc k)) {P : k[X]} (hP : P ≠ 0) (b : k) :
    (placeOfPoint k b).ord (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E))
      = (rootMultiplicity b P : ℤ) - (E (placeOfPoint k b)).toNat := by
  have hP' : algebraMap k[X] (RatFunc k) P ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hP
  rw [div_eq_mul_inv, (placeOfPoint k b).ord_mul hP' (inv_ne_zero (algebraMap_divisorPolynomial_ne_zero E)),
    Place.ord_inv, ord_placeOfPoint_algebraMap b hP, ord_placeOfPoint_divisorPolynomial]
  ring

theorem ord_placeInfty_div_divisorPolynomial [DecidableEq (RatFunc k)] (E : Divisor k (RatFunc k)) {P : k[X]} (hP : P ≠ 0) :
    (placeInfty k).ord (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E))
      = ((divisorPolynomial k E).natDegree : ℤ) - P.natDegree := by
  have hP' : algebraMap k[X] (RatFunc k) P ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hP
  rw [div_eq_mul_inv, (placeInfty k).ord_mul hP' (inv_ne_zero (algebraMap_divisorPolynomial_ne_zero E)),
    Place.ord_inv, ord_placeInfty hP', RatFunc.intDegree_polynomial, ord_placeInfty_divisorPolynomial]
  ring

open scoped Classical in

theorem support_subset_insert [IsAlgClosed k] [DecidableEq (RatFunc k)] (E : Divisor k (RatFunc k)) :
    E.support ⊆ insert (placeInfty k) ((divisorPoints k E).image (placeOfPoint k)) := by
  intro v hv
  rcases eq_placeOfPoint_or_eq_placeInfty k v with ⟨a, rfl⟩ | rfl
  · refine Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_)
    exact mem_divisorPoints.mpr (Finsupp.mem_support_iff.mp hv)
  · exact Finset.mem_insert_self _ _

theorem degree_eq_sum_divisorPoints [IsAlgClosed k] [DecidableEq (RatFunc k)] (E : Divisor k (RatFunc k)) :
    E.degree = (∑ a ∈ divisorPoints k E, E (placeOfPoint k a)) + E (placeInfty k) := by
  classical
  have h1 : E.degree = ∑ v ∈ insert (placeInfty k) ((divisorPoints k E).image (placeOfPoint k)),
      E v * (v.deg : ℤ) := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum_of_support_subset E (support_subset_insert E)]
    · rfl
    · intro v _
      exact zero_mul _
  rw [h1, Finset.sum_insert, Finset.sum_image fun a _ b _ h => placeOfPoint_injective k h,
    deg_placeInfty, add_comm]
  · simp [deg_placeOfPoint]
  · simp only [Finset.mem_image, not_exists, not_and]
    exact fun a _ h => placeOfPoint_ne_placeInfty k a h

theorem degree_eq_natDegree_add [IsAlgClosed k] [DecidableEq (RatFunc k)] {E : Divisor k (RatFunc k)}
    (hE : 0 ≤ E) :
    E.degree = (divisorPolynomial k E).natDegree + E (placeInfty k) := by
  rw [degree_eq_sum_divisorPoints, natDegree_divisorPolynomial, Nat.cast_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => (Int.toNat_of_nonneg (hE _)).symm

theorem degree_nonneg [IsAlgClosed k] [DecidableEq (RatFunc k)] {E : Divisor k (RatFunc k)}
    (hE : 0 ≤ E) : 0 ≤ E.degree := by
  rw [degree_eq_natDegree_add hE]
  have := hE (placeInfty k)
  simp only [Finsupp.coe_zero, Pi.zero_apply] at this
  omega

end Points

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum Place.congrRingEquiv Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply RationalFunctionField.placeInfty Place.residue_algebraMap"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum surjective_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

section RiemannRoch

variable {k : Type*} [Field k]

theorem ord_placeOfPoint_div (b : k) {P Q : k[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (placeOfPoint k b).ord (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q)
      = (rootMultiplicity b P : ℤ) - rootMultiplicity b Q := by
  have hP' : algebraMap k[X] (RatFunc k) P ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hP
  have hQ' : algebraMap k[X] (RatFunc k) Q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hQ
  rw [div_eq_mul_inv, (placeOfPoint k b).ord_mul hP' (inv_ne_zero hQ'), Place.ord_inv, ord_placeOfPoint_algebraMap b hP,
    ord_placeOfPoint_algebraMap b hQ]
  ring

theorem exists_eq_algebraMap_of_forall_ord_nonneg [IsAlgClosed k] {f : RatFunc k}
    (hf : ∀ a : k, 0 ≤ (placeOfPoint k a).ord f) :
    ∃ P : k[X], f = algebraMap k[X] (RatFunc k) P := by
  have key : f = algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom :=
    (RatFunc.num_div_denom f).symm
  suffices hden : f.denom = 1 by
    refine ⟨f.num, ?_⟩
    rw [key, hden, map_one, div_one, RatFunc.num_algebraMap]
  by_contra hden
  have hdeg : f.denom.degree ≠ 0 := by
    intro h0
    apply hden
    have h1 : f.denom.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr h0.le
    exact (RatFunc.monic_denom f).natDegree_eq_zero.mp h1
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom hdeg
  have hnum0 : f.num ≠ 0 := by
    intro h
    rw [RatFunc.num_eq_zero_iff] at h
    subst h
    exact hden RatFunc.denom_zero
  have hnum : ¬ f.num.IsRoot a := fun hn =>
    not_isUnit_X_sub_C a ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd'
      (dvd_iff_isRoot.mpr hn) (dvd_iff_isRoot.mpr ha))
  have h1 : rootMultiplicity a f.num = 0 := rootMultiplicity_eq_zero hnum
  have h2 : 0 < rootMultiplicity a f.denom :=
    (rootMultiplicity_pos (RatFunc.denom_ne_zero f)).mpr ha
  have h3 := hf a
  rw [key, ord_placeOfPoint_div a hnum0 (RatFunc.denom_ne_zero f), h1] at h3
  simp only [CharP.cast_eq_zero, zero_sub, Left.nonneg_neg_iff] at h3
  exact absurd h3 (by exact_mod_cast h2.ne' ∘ fun h => le_antisymm h (Nat.cast_nonneg _) )

variable [IsAlgClosed k] [DecidableEq (RatFunc k)]

theorem div_divisorPolynomial_mem_riemannRochSpace {E : Divisor k (RatFunc k)} (hE : 0 ≤ E) {P : k[X]}
    (hP : (P.natDegree : ℤ) ≤ E.degree) :
    algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E)
      ∈ riemannRochSpace E := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  rw [mem_riemannRochSpace_iff]
  intro v
  right
  rcases eq_placeOfPoint_or_eq_placeInfty k v with ⟨b, rfl⟩ | rfl
  · rw [ord_placeOfPoint_div_divisorPolynomial E hP0, Int.toNat_of_nonneg (hE _)]
    have : (0 : ℤ) ≤ rootMultiplicity b P := Nat.cast_nonneg _
    linarith
  · rw [ord_placeInfty_div_divisorPolynomial E hP0]
    rw [degree_eq_natDegree_add hE] at hP
    linarith

theorem exists_eq_div_divisorPolynomial_of_mem {E : Divisor k (RatFunc k)} (hE : 0 ≤ E) {f : RatFunc k}
    (hf : f ∈ riemannRochSpace E) :
    ∃ P : k[X], (P.natDegree : ℤ) ≤ E.degree ∧
      f = algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, by simpa using degree_nonneg hE, by simp⟩
  have hh := algebraMap_divisorPolynomial_ne_zero E
  have hg : ∀ a : k, 0 ≤ (placeOfPoint k a).ord (f * algebraMap k[X] (RatFunc k) (divisorPolynomial k E)) := by
    intro a
    rw [(placeOfPoint k a).ord_mul hf0 hh, ord_placeOfPoint_divisorPolynomial, Int.toNat_of_nonneg (hE _)]
    have := ((mem_riemannRochSpace_iff.mp hf) (placeOfPoint k a)).resolve_left hf0
    linarith
  obtain ⟨P, hP⟩ := exists_eq_algebraMap_of_forall_ord_nonneg hg
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero] at hP
    exact (mul_ne_zero hf0 hh) hP
  have hfP : f = algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E) := by
    rw [eq_div_iff hh, hP]
  refine ⟨P, ?_, hfP⟩
  have hinf := ((mem_riemannRochSpace_iff.mp hf) (placeInfty k)).resolve_left hf0
  rw [hfP, ord_placeInfty_div_divisorPolynomial E hP0] at hinf
  rw [degree_eq_natDegree_add hE]
  linarith

theorem mem_riemannRochSpace_iff_exists_polynomial {E : Divisor k (RatFunc k)} (hE : 0 ≤ E) {f : RatFunc k} :
    f ∈ riemannRochSpace E ↔ ∃ P : k[X], (P.natDegree : ℤ) ≤ E.degree ∧
      f = algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E) :=
  ⟨exists_eq_div_divisorPolynomial_of_mem hE,
    fun ⟨_, hP, hf⟩ => hf ▸ div_divisorPolynomial_mem_riemannRochSpace hE hP⟩

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in

def divDivisorPolynomial (E : Divisor k (RatFunc k)) : k[X] →ₗ[k] RatFunc k :=
  (LinearMap.mulRight k (algebraMap k[X] (RatFunc k) (divisorPolynomial k E))⁻¹).comp
    (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
@[scoped simp]
theorem divDivisorPolynomial_apply (E : Divisor k (RatFunc k)) (P : k[X]) :
    divDivisorPolynomial E P
      = algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E) := by
  simp [divDivisorPolynomial, div_eq_mul_inv]

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
theorem divDivisorPolynomial_injective (E : Divisor k (RatFunc k)) :
    Function.Injective (divDivisorPolynomial E) := by
  intro P Q hPQ
  simp only [divDivisorPolynomial_apply] at hPQ
  exact IsFractionRing.injective k[X] (RatFunc k)
    ((div_left_inj' (algebraMap_divisorPolynomial_ne_zero E)).mp hPQ)

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
theorem mem_degreeLT_succ_iff {P : k[X]} {d : ℕ} : P ∈ degreeLT k (d + 1) ↔ P.natDegree ≤ d := by
  rw [mem_degreeLT]
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · rw [degree_eq_natDegree hP, Nat.cast_lt, Nat.lt_succ_iff]

def riemannRochSpaceEquiv {E : Divisor k (RatFunc k)} (hE : 0 ≤ E) :
    degreeLT k (E.degree.toNat + 1) ≃ₗ[k] riemannRochSpace E :=
  LinearEquiv.ofBijective
    ((divDivisorPolynomial E).restrict (p := degreeLT k (E.degree.toNat + 1)) (q := riemannRochSpace E)
      (fun P hP => by
        rw [divDivisorPolynomial_apply]
        refine div_divisorPolynomial_mem_riemannRochSpace hE ?_
        rw [mem_degreeLT_succ_iff] at hP
        have := degree_nonneg hE
        omega))
    ⟨fun P Q h => Subtype.ext (divDivisorPolynomial_injective E (congrArg Subtype.val h)),
      fun ⟨f, hf⟩ => by
        obtain ⟨P, hP, rfl⟩ := exists_eq_div_divisorPolynomial_of_mem hE hf
        refine ⟨⟨P, ?_⟩, Subtype.ext (by simp [LinearMap.restrict_apply])⟩
        rw [mem_degreeLT_succ_iff]
        have := degree_nonneg hE
        omega⟩

@[scoped simp]
theorem riemannRochSpaceEquiv_apply {E : Divisor k (RatFunc k)} (hE : 0 ≤ E)
    (P : degreeLT k (E.degree.toNat + 1)) :
    (riemannRochSpaceEquiv hE P : RatFunc k)
      = algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E) := by
  simp [riemannRochSpaceEquiv, LinearMap.restrict_apply]

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
theorem finrank_degreeLT (n : ℕ) : Module.finrank k (degreeLT k n) = n := by
  rw [LinearEquiv.finrank_eq (degreeLTEquiv k n), Module.finrank_fin_fun]

theorem finrank_riemannRochSpace {E : Divisor k (RatFunc k)} (hE : 0 ≤ E) :
    Module.finrank k (riemannRochSpace E) = E.degree.toNat + 1 := by
  rw [← (riemannRochSpaceEquiv hE).finrank_eq, finrank_degreeLT]

theorem finiteDimensional_riemannRochSpace {E : Divisor k (RatFunc k)} (hE : 0 ≤ E) :
    FiniteDimensional k (riemannRochSpace E) :=
  LinearEquiv.finiteDimensional (riemannRochSpaceEquiv hE)

end RiemannRoch
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum Place.congrRingEquiv Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply RationalFunctionField.placeInfty Place.residue_algebraMap"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum surjective_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

section Values

variable {k : Type*} [Field k]

theorem hasValue_placeOfPoint_algebraMap (b : k) (P : k[X]) :
    (placeOfPoint k b).HasValue (algebraMap k[X] (RatFunc k) P) (P.eval b) := by
  let w := heightOneSpectrumOfIrreducible k (irreducible_X_sub_C b)
  refine ⟨algebraMap_mem_ofHeightOneSpectrum k w P, ?_⟩
  have h1 : IsLocalRing.residue _
      ⟨algebraMap k[X] (RatFunc k) P, algebraMap_mem_ofHeightOneSpectrum k w P⟩
      = residueOfHeightOneSpectrum k w P := (residueOfHeightOneSpectrum_apply k w P).symm
  have h2 : residueOfHeightOneSpectrum k w (P - C (P.eval b)) = 0 := by
    rw [← RingHom.mem_ker, ker_residueOfHeightOneSpectrum, heightOneSpectrumOfIrreducible_asIdeal,
      Ideal.mem_span_singleton, dvd_iff_isRoot]
    simp
  have h3 : residueOfHeightOneSpectrum k w P = residueOfHeightOneSpectrum k w (C (P.eval b)) := by
    rw [← sub_eq_zero, ← map_sub, h2]
  have h4 : residueOfHeightOneSpectrum k w (C (P.eval b))
      = algebraMap k (Place.ofHeightOneSpectrum (K := k) (F := RatFunc k) w).ResidueField (P.eval b) := by
    rw [residueOfHeightOneSpectrum_apply]
    have : (⟨algebraMap k[X] (RatFunc k) (C (P.eval b)), algebraMap_mem_ofHeightOneSpectrum k w _⟩ :
        (Place.ofHeightOneSpectrum (K := k) (F := RatFunc k) w).toValuationSubring)
        = algebraMap k _ (P.eval b) := by
      apply Subtype.ext
      rw [Place.coe_algebraMap, IsScalarTower.algebraMap_apply k k[X] (RatFunc k), Polynomial.algebraMap_eq]
    rw [this, Place.residue_algebraMap]
  exact h1.trans (h3.trans h4)

theorem hasValue_placeOfPoint_div (b : k) (P : k[X]) {Q : k[X]} (hQ : Q.eval b ≠ 0) :
    (placeOfPoint k b).HasValue (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q)
      (P.eval b / Q.eval b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact (hasValue_placeOfPoint_algebraMap b P).mul ((hasValue_placeOfPoint_algebraMap b Q).inv hQ)

theorem hasValue_placeOfPoint_div_divisorPolynomial {E : Divisor k (RatFunc k)} {b : k}
    (hb : E (placeOfPoint k b) = 0) (P : k[X]) :
    (placeOfPoint k b).HasValue
      (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k E))
      (P.eval b / (divisorPolynomial k E).eval b) :=
  hasValue_placeOfPoint_div b P (eval_divisorPolynomial_ne_zero hb)

theorem algebraMap_residueField_placeOfPoint_surjective (b : k) :
    Function.Surjective (algebraMap k (placeOfPoint k b).ResidueField) := by
  intro x
  obtain ⟨P, hP⟩ := surjective_residueOfHeightOneSpectrum k
    (heightOneSpectrumOfIrreducible k (irreducible_X_sub_C b)) x
  refine ⟨P.eval b, ?_⟩
  rw [← hP, ← (hasValue_placeOfPoint_algebraMap b P).residue_eq, residueOfHeightOneSpectrum_apply]
  rfl

end Values
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum Place.congrRingEquiv Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply RationalFunctionField.placeInfty Place.residue_algebraMap"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum surjective_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

section Pencil

variable {k : Type*} [Field k]

def nodePoly (Z : Finset k) : k[X] := ∏ z ∈ Z, (X - C z)

theorem nodePoly_monic (Z : Finset k) : (nodePoly Z).Monic :=
  monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z

theorem natDegree_nodePoly (Z : Finset k) : (nodePoly Z).natDegree = Z.card := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun z _ => monic_X_sub_C z]
  simp

theorem eval_nodePoly (Z : Finset k) (a : k) : (nodePoly Z).eval a = ∏ z ∈ Z, (a - z) := by
  simp [nodePoly, eval_prod]

theorem eval_nodePoly_ne_zero {Z : Finset k} {a : k} (ha : a ∉ Z) : (nodePoly Z).eval a ≠ 0 := by
  rw [eval_nodePoly]
  refine Finset.prod_ne_zero_iff.mpr fun z hz => sub_ne_zero.mpr ?_
  rintro rfl
  exact ha hz

theorem eval_nodePoly_eq_zero {Z : Finset k} {a : k} (ha : a ∈ Z) : (nodePoly Z).eval a = 0 := by
  rw [eval_nodePoly]
  exact Finset.prod_eq_zero ha (sub_self a)

theorem exists_pencil [Infinite k] [DecidableEq k] (h : k[X]) (b₀ β : k) (Zv Za : Finset k)
    (w : k → k) (bad : Finset k) (hb₀v : b₀ ∉ Zv) (hb₀a : b₀ ∉ Za) (hva : Disjoint Zv Za)
    (hha : ∀ a ∈ Za, h.eval a ≠ 0) :
    ∃ S : k[X], S.natDegree ≤ Zv.card ∧ S.eval b₀ ≠ 0 ∧
      (∀ z ∈ Zv, (z - b₀) * S.eval z = (w z - β) * h.eval z) ∧
      (∀ a ∈ Za, (C β * h + (X - C b₀) * S).eval a / h.eval a ∉ bad) := by

  set r : k → k := fun z => (w z - β) * h.eval z / (z - b₀) with hr
  set R : k[X] := Lagrange.interpolate Zv id r with hR
  set N : k[X] := nodePoly Zv with hN
  have hRdeg : R.natDegree ≤ Zv.card := by
    have h1 : R.degree < Zv.card := Lagrange.degree_interpolate_lt r Function.injective_id.injOn
    exact natDegree_le_iff_degree_le.mpr h1.le
  have hReval : ∀ z ∈ Zv, R.eval z = r z := fun z hz => by
    have := Lagrange.eval_interpolate_at_node (s := Zv) (v := id) r Function.injective_id.injOn hz
    simpa [R] using this
  have hNb₀ : N.eval b₀ ≠ 0 := eval_nodePoly_ne_zero hb₀v
  have hNa : ∀ a ∈ Za, N.eval a ≠ 0 := fun a ha =>
    eval_nodePoly_ne_zero (Finset.disjoint_right.mp hva ha)

  set μ₁ : k := -R.eval b₀ / N.eval b₀ with hμ₁
  set μab : k × k → k := fun p =>
    (p.2 * h.eval p.1 - β * h.eval p.1 - (p.1 - b₀) * R.eval p.1) / ((p.1 - b₀) * N.eval p.1) with hμab
  obtain ⟨μ, hμ⟩ := Infinite.exists_notMem_finset (insert μ₁ ((Za ×ˢ bad).image μab))
  rw [Finset.mem_insert, not_or, Finset.mem_image, not_exists] at hμ
  refine ⟨R + C μ * N, ?_, ?_, ?_, ?_⟩
  ·
    refine (natDegree_add_le _ _).trans (max_le hRdeg ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [hN, natDegree_nodePoly]
  ·
    intro h0
    apply hμ.1
    rw [eval_add, eval_mul, eval_C] at h0
    rw [hμ₁, eq_div_iff hNb₀]
    linear_combination h0
  ·
    intro z hz
    have hzb : z - b₀ ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hb₀v hz)
    rw [eval_add, eval_mul, eval_C, hReval z hz, hN, eval_nodePoly_eq_zero hz, mul_zero, add_zero, hr]
    field_simp
  ·
    intro a ha hbad
    apply hμ.2 ⟨a, (C β * h + (X - C b₀) * (R + C μ * N)).eval a / h.eval a⟩
    refine ⟨Finset.mem_product.mpr ⟨ha, hbad⟩, ?_⟩
    have hab : a - b₀ ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hb₀a ha)
    have hha' := hha a ha
    have hNa' := hNa a ha
    rw [hμab]
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X]
    rw [div_eq_iff (mul_ne_zero hab (hNa a ha))]
    field_simp
    ring

end Pencil
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum Place.congrRingEquiv Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply RationalFunctionField.placeInfty Place.residue_algebraMap"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum surjective_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

section AllFinite

variable {k : Type*} [Field k]

open scoped Classical in

theorem sum_single_one_apply {F : Type*} [Field F] [Algebra k F] (U : Finset (Place k F))
    (v : Place k F) :
    (∑ u ∈ U, Finsupp.single u (1 : ℤ)) v = if v ∈ U then 1 else 0 := by
  classical
  simp only [Finset.sum_apply', Finsupp.single_apply]
  split_ifs with hv
  · rw [Finset.sum_eq_single_of_mem v hv (fun u _ huv => if_neg huv), if_pos rfl]
  · exact Finset.sum_eq_zero fun u hu => if_neg (fun h : u = v => hv (h ▸ hu))

def finsetPoints (S : Finset (Place k (RatFunc k))) : Finset k :=
  S.preimage (placeOfPoint k) ((placeOfPoint_injective k).injOn)

@[scoped simp]
theorem mem_finsetPoints {S : Finset (Place k (RatFunc k))} {a : k} :
    a ∈ finsetPoints S ↔ placeOfPoint k a ∈ S := by
  simp [finsetPoints]

open scoped Classical in
theorem image_finsetPoints [IsAlgClosed k] [DecidableEq (RatFunc k)]
    {S : Finset (Place k (RatFunc k))} (hS : ∀ v ∈ S, v ≠ placeInfty k) :
    (finsetPoints S).image (placeOfPoint k) = S := by
  classical
  ext v
  simp only [Finset.mem_image, mem_finsetPoints]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hv
    rcases eq_placeOfPoint_or_eq_placeInfty k v with ⟨a, rfl⟩ | rfl
    · exact ⟨a, hv, rfl⟩
    · exact absurd rfl (hS _ hv)

theorem card_finsetPoints [IsAlgClosed k] [DecidableEq (RatFunc k)]
    {S : Finset (Place k (RatFunc k))} (hS : ∀ v ∈ S, v ≠ placeInfty k) :
    (finsetPoints S).card = S.card := by
  classical
  conv_rhs => rw [← image_finsetPoints hS]
  rw [Finset.card_image_of_injective _ (placeOfPoint_injective k)]

theorem div_sub_algebraMap (P h : k[X]) (hh : algebraMap k[X] (RatFunc k) h ≠ 0) (γ : k) :
    algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) h - algebraMap k (RatFunc k) γ
      = algebraMap k[X] (RatFunc k) (P - C γ * h) / algebraMap k[X] (RatFunc k) h := by
  rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k), Polynomial.algebraMap_eq, map_sub, map_mul,
    sub_div, mul_div_assoc, div_self hh, mul_one]

theorem exists_interp_of_forall_ne_placeInfty [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (U Zv Za : Finset (Place k (RatFunc k))) (t₀ : Place k (RatFunc k)) (β : k)
    (val : Place k (RatFunc k) → k) (bad : Finset k)
    (hUZv : Disjoint U Zv) (hUZa : Disjoint U Za) (hZ : Disjoint Zv Za)
    (ht₀U : t₀ ∉ U) (ht₀v : t₀ ∉ Zv) (ht₀a : t₀ ∉ Za)
    (hcard : Zv.card + 1 ≤ U.card)
    (hU : ∀ v ∈ U, v ≠ placeInfty k) (hZv : ∀ v ∈ Zv, v ≠ placeInfty k)
    (hZa : ∀ v ∈ Za, v ≠ placeInfty k) (ht₀ : t₀ ≠ placeInfty k) :
    ∃ g : RatFunc k,
      g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
      t₀.ord (g - algebraMap k (RatFunc k) β) = 1 ∧
      (∀ z ∈ Zv, z.HasValue g (val z)) ∧
      (∀ z ∈ Za, ∃ γ : k, γ ∉ bad ∧ z.HasValue g γ) := by
  classical

  set D : Divisor k (RatFunc k) := ∑ u ∈ U, Finsupp.single u (1 : ℤ) with hDdef
  have hDapp : ∀ v, D v = if v ∈ U then 1 else 0 := sum_single_one_apply U
  have hD0 : 0 ≤ D := Finsupp.le_def.mpr fun v => by
    rw [hDapp]
    split_ifs <;> simp
  have hDinf : D (placeInfty k) = 0 := by
    rw [hDapp, if_neg]
    exact fun h => hU _ h rfl
  have hDdeg : D.degree = U.card := by
    rw [hDdef, map_sum]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rcases eq_placeOfPoint_or_eq_placeInfty k u with ⟨a, rfl⟩ | rfl
    · rw [Divisor.degree_single, deg_placeOfPoint]
      simp
    · exact absurd rfl (hU _ hu)
  have hh0 : algebraMap k[X] (RatFunc k) (divisorPolynomial k D) ≠ 0 :=
    algebraMap_divisorPolynomial_ne_zero D
  have hhdeg : ((divisorPolynomial k D).natDegree : ℤ) = U.card := by
    have := degree_eq_natDegree_add (k := k) hD0
    rw [hDinf, add_zero, hDdeg] at this
    exact this.symm

  obtain ⟨b₀, rfl⟩ : ∃ b₀, t₀ = placeOfPoint k b₀ :=
    (eq_placeOfPoint_or_eq_placeInfty k t₀).resolve_right ht₀
  set Zv₀ := finsetPoints Zv with hZv₀
  set Za₀ := finsetPoints Za with hZa₀
  have hb₀v : b₀ ∉ Zv₀ := fun h => ht₀v (mem_finsetPoints.mp h)
  have hb₀a : b₀ ∉ Za₀ := fun h => ht₀a (mem_finsetPoints.mp h)
  have hva : Disjoint Zv₀ Za₀ := by
    rw [Finset.disjoint_left]
    intro a hav haa
    exact Finset.disjoint_left.mp hZ (mem_finsetPoints.mp hav) (mem_finsetPoints.mp haa)
  have hDoff : ∀ v, v ∉ U → D v = 0 := fun v hv => by rw [hDapp, if_neg hv]
  have hDb₀ : D (placeOfPoint k b₀) = 0 := hDoff _ ht₀U
  have hDZv : ∀ z ∈ Zv₀, D (placeOfPoint k z) = 0 := fun z hz =>
    hDoff _ (Finset.disjoint_right.mp hUZv (mem_finsetPoints.mp hz))
  have hDZa : ∀ a ∈ Za₀, D (placeOfPoint k a) = 0 := fun a ha =>
    hDoff _ (Finset.disjoint_right.mp hUZa (mem_finsetPoints.mp ha))
  have hha : ∀ a ∈ Za₀, (divisorPolynomial k D).eval a ≠ 0 := fun a ha =>
    eval_divisorPolynomial_ne_zero (hDZa a ha)

  obtain ⟨S, hSdeg, hSb₀, hSv, hSa⟩ := exists_pencil (divisorPolynomial k D) b₀ β Zv₀ Za₀
    (fun a => val (placeOfPoint k a)) bad hb₀v hb₀a hva hha
  set P : k[X] := C β * divisorPolynomial k D + (X - C b₀) * S with hPdef
  have hcardv : Zv₀.card = Zv.card := card_finsetPoints hZv
  have hPdeg : (P.natDegree : ℤ) ≤ D.degree := by
    rw [hDdeg]
    have h1 : (C β * divisorPolynomial k D).natDegree ≤ U.card := by
      refine (natDegree_C_mul_le _ _).trans ?_
      exact_mod_cast hhdeg.le
    have h2 : ((X - C b₀) * S).natDegree ≤ U.card := by
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X_sub_C]
      omega
    exact_mod_cast (natDegree_add_le _ _).trans (max_le h1 h2)
  refine ⟨algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) (divisorPolynomial k D),
    ?_, ?_, ?_, ?_⟩
  ·
    exact div_divisorPolynomial_mem_riemannRochSpace hD0 hPdeg
  ·
    rw [div_sub_algebraMap P _ hh0 β]
    have hPβ : P - C β * divisorPolynomial k D = (X - C b₀) * S := by rw [hPdef]; ring
    have hS0 : S ≠ 0 := fun h0 => hSb₀ (by rw [h0, eval_zero])
    have hXS : (X - C b₀) * S ≠ 0 := mul_ne_zero (X_sub_C_ne_zero b₀) hS0
    rw [hPβ, ord_placeOfPoint_div b₀ hXS (divisorPolynomial_ne_zero D),
      rootMultiplicity_mul hXS, rootMultiplicity_X_sub_C_self,
      rootMultiplicity_eq_zero (fun h => hSb₀ h),
      rootMultiplicity_eq_zero (fun h => eval_divisorPolynomial_ne_zero hDb₀ h)]
    simp
  ·
    intro z hz
    obtain ⟨a, rfl⟩ : ∃ a, z = placeOfPoint k a :=
      (eq_placeOfPoint_or_eq_placeInfty k z).resolve_right (hZv z hz)
    have ha : a ∈ Zv₀ := mem_finsetPoints.mpr hz
    have hval := hasValue_placeOfPoint_div_divisorPolynomial (hDZv a ha) P
    have hev : P.eval a / (divisorPolynomial k D).eval a = val (placeOfPoint k a) := by
      rw [div_eq_iff (eval_divisorPolynomial_ne_zero (hDZv a ha)), hPdef]
      simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X]
      linear_combination hSv a ha
    rwa [hev] at hval
  ·
    intro z hz
    obtain ⟨a, rfl⟩ : ∃ a, z = placeOfPoint k a :=
      (eq_placeOfPoint_or_eq_placeInfty k z).resolve_right (hZa z hz)
    have ha : a ∈ Za₀ := mem_finsetPoints.mpr hz
    exact ⟨P.eval a / (divisorPolynomial k D).eval a, hSa a ha,
      hasValue_placeOfPoint_div_divisorPolynomial (hDZa a ha) P⟩

end AllFinite
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum Place.congrRingEquiv Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply RationalFunctionField.placeInfty Place.residue_algebraMap"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum surjective_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial IntermediateField

section Moebius

variable (k : Type*) [Field k]

theorem X_sub_C_eq_algebraMap (c : k) :
    (RatFunc.X - RatFunc.C c : RatFunc k) = algebraMap k[X] (RatFunc k) (X - C c) := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem ratFunc_X_sub_C_ne_zero (c : k) : (RatFunc.X - RatFunc.C c : RatFunc k) ≠ 0 := by
  rw [X_sub_C_eq_algebraMap]
  exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (X_sub_C_ne_zero c)

def moebiusFun (c : k) : RatFunc k := (RatFunc.X - RatFunc.C c)⁻¹

theorem moebiusFun_ne_C (c : k) : ¬ ∃ c' : k, moebiusFun k c = RatFunc.C c' := by
  rintro ⟨c', hc'⟩
  have h1 : (RatFunc.X - RatFunc.C c : RatFunc k) * RatFunc.C c' = 1 := by
    rw [← hc', moebiusFun, mul_inv_cancel₀ (ratFunc_X_sub_C_ne_zero k c)]
  have hC0 : (RatFunc.C c' : RatFunc k) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have h2 := congrArg RatFunc.intDegree h1
  rw [RatFunc.intDegree_mul (ratFunc_X_sub_C_ne_zero k c) hC0, RatFunc.intDegree_C,
    RatFunc.intDegree_one, X_sub_C_eq_algebraMap, RatFunc.intDegree_polynomial,
    natDegree_X_sub_C] at h2
  norm_num at h2

theorem transcendental_moebiusFun (c : k) : Transcendental k (moebiusFun k c) :=
  RatFunc.transcendental_of_ne_C _ (moebiusFun_ne_C k c)

theorem adjoin_moebiusFun (c : k) : k⟮moebiusFun k c⟯ = ⊤ := by
  have hy : moebiusFun k c ∈ k⟮moebiusFun k c⟯ := IntermediateField.mem_adjoin_simple_self k _
  have hX : (RatFunc.X : RatFunc k) ∈ k⟮moebiusFun k c⟯ := by
    have h1 : (RatFunc.X : RatFunc k) = (moebiusFun k c)⁻¹ + algebraMap k (RatFunc k) c := by
      rw [moebiusFun, inv_inv, RatFunc.algebraMap_eq_C, sub_add_cancel]
    rw [h1]
    exact add_mem (inv_mem hy) (IntermediateField.algebraMap_mem _ c)
  rw [eq_top_iff, ← RatFunc.adjoin_X, IntermediateField.adjoin_simple_le_iff]
  exact hX

def moebiusAlgHom (c : k) : RatFunc k →ₐ[k] RatFunc k :=
  (IntermediateField.val _).comp
    (RatFunc.algEquivOfTranscendental _ (transcendental_moebiusFun k c)).toAlgHom

theorem moebiusAlgHom_X (c : k) : moebiusAlgHom k c RatFunc.X = moebiusFun k c := by
  rw [moebiusAlgHom, AlgHom.comp_apply]
  exact RatFunc.algEquivOfTranscendental_X _ _

theorem moebiusAlgHom_bijective (c : k) : Function.Bijective (moebiusAlgHom k c) := by
  refine ⟨(moebiusAlgHom k c).toRingHom.injective, fun u => ?_⟩
  have hu : u ∈ k⟮moebiusFun k c⟯ := by
    rw [adjoin_moebiusFun]
    exact IntermediateField.mem_top
  refine ⟨(RatFunc.algEquivOfTranscendental _ (transcendental_moebiusFun k c)).symm ⟨u, hu⟩, ?_⟩
  change ((RatFunc.algEquivOfTranscendental _ (transcendental_moebiusFun k c)
    ((RatFunc.algEquivOfTranscendental _ (transcendental_moebiusFun k c)).symm ⟨u, hu⟩) :
      k⟮moebiusFun k c⟯) : RatFunc k) = u
  rw [AlgEquiv.apply_symm_apply]

def moebius (c : k) : RatFunc k ≃ₐ[k] RatFunc k :=
  AlgEquiv.ofBijective (moebiusAlgHom k c) (moebiusAlgHom_bijective k c)

theorem moebius_X (c : k) : moebius k c RatFunc.X = moebiusFun k c :=
  moebiusAlgHom_X k c

theorem congrEquiv_moebius_placeInfty [IsAlgClosed k] [DecidableEq (RatFunc k)] (c : k) :
    Place.congrEquiv (moebius k c).toRingEquiv (fun a => (moebius k c).commutes a) (placeInfty k)
      = placeOfPoint k c := by
  classical
  set w := Place.congrEquiv (moebius k c).toRingEquiv (fun a => (moebius k c).commutes a)
    (placeInfty k) with hw
  have h1 : w.ord ((moebius k c) RatFunc.X) = (placeInfty k).ord RatFunc.X := by
    rw [hw, Place.congrEquiv_apply]
    exact Place.ord_congrRingEquiv _ _ _ _
  rw [moebius_X, moebiusFun, Place.ord_inv, ord_placeInfty RatFunc.X_ne_zero,
    RatFunc.intDegree_X] at h1
  have hord : w.ord (RatFunc.X - RatFunc.C c) = 1 := by omega
  clear h1
  rcases eq_placeOfPoint_or_eq_placeInfty k w with ⟨a, ha⟩ | ha
  · rw [ha] at hord ⊢
    rw [X_sub_C_eq_algebraMap, ord_placeOfPoint_algebraMap a (X_sub_C_ne_zero c),
      rootMultiplicity_X_sub_C] at hord
    split_ifs at hord with hac
    · rw [hac]
    · exact absurd hord (by norm_num)
  · rw [ha, X_sub_C_eq_algebraMap, ord_placeInfty ((map_ne_zero_iff _
      (IsFractionRing.injective k[X] (RatFunc k))).mpr (X_sub_C_ne_zero c)),
      RatFunc.intDegree_polynomial, natDegree_X_sub_C] at hord
    norm_num at hord

end Moebius
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

theorem exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc'
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (U Zv Za : Finset (Place k F)) (t₀ : Place k F) (β : k)
    (val : Place k F → k) (bad : Finset k)
    (hUZv : Disjoint U Zv) (hUZa : Disjoint U Za) (hZ : Disjoint Zv Za)
    (ht₀U : t₀ ∉ U) (ht₀v : t₀ ∉ Zv) (ht₀a : t₀ ∉ Za)
    (hcard : Zv.card + 1 ≤ U.card) :
    ∃ g : F,
      g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
      t₀.ord (g - algebraMap k F β) = 1 ∧
      (∀ z ∈ Zv, z.HasValue g (val z)) ∧
      (∀ z ∈ Za, ∃ γ : k, γ ∉ bad ∧ z.HasValue g γ) := by
  classical

  set S : Finset (Place k F) := insert t₀ (U ∪ Zv ∪ Za) with hS
  set ε₀ := (Place.congrEquiv e he).symm with hε₀
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (RationalFunctionField.finsetPoints (S.image ε₀))
  have hσa : ∀ a : k, (RationalFunctionField.moebius k c).toRingEquiv (algebraMap k (RatFunc k) a)
      = algebraMap k (RatFunc k) a := fun a => (RationalFunctionField.moebius k c).commutes a
  have he' : ∀ a : k, ((RationalFunctionField.moebius k c).toRingEquiv.trans e)
      (algebraMap k (RatFunc k) a) = algebraMap k F a :=
    Place.algebraMap_comm_trans _ hσa e he
  set ε := (Place.congrEquiv _ he').symm with hε
  have hεinj : Function.Injective ε := ε.injective
  have hfin : ∀ P ∈ S, ε P ≠ RationalFunctionField.placeInfty k := by
    intro P hP hPinf
    apply hc
    rw [RationalFunctionField.mem_finsetPoints, Finset.mem_image]
    refine ⟨P, hP, ?_⟩
    have h1 : Place.congrEquiv _ he' (RationalFunctionField.placeInfty k) = P := by
      rw [← hPinf, hε, Equiv.apply_symm_apply]
    rw [Place.congrEquiv_trans_apply _ hσa e he, RationalFunctionField.congrEquiv_moebius_placeInfty] at h1
    rw [← h1, hε₀, Equiv.symm_apply_apply]
  have hSU : ∀ P ∈ U, P ∈ S := fun P hP =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hP))
  have hSZv : ∀ P ∈ Zv, P ∈ S := fun P hP =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hP))
  have hSZa : ∀ P ∈ Za, P ∈ S := fun P hP => Finset.mem_insert_of_mem (Finset.mem_union_right _ hP)
  have himg : ∀ (T : Finset (Place k F)) (hT : ∀ P ∈ T, P ∈ S),
      ∀ v ∈ T.image ε, v ≠ RationalFunctionField.placeInfty k := by
    intro T hT v hv
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hv
    exact hfin P (hT P hP)

  obtain ⟨g, hgL, hgord, hgv, hga⟩ :=
    RationalFunctionField.exists_interp_of_forall_ne_placeInfty
      (U.image ε) (Zv.image ε) (Za.image ε) (ε t₀) β (fun v => val (ε.symm v)) bad
      ((Finset.disjoint_image hεinj).mpr hUZv) ((Finset.disjoint_image hεinj).mpr hUZa)
      ((Finset.disjoint_image hεinj).mpr hZ)
      (fun h => ht₀U (hεinj.mem_finset_image.mp h)) (fun h => ht₀v (hεinj.mem_finset_image.mp h))
      (fun h => ht₀a (hεinj.mem_finset_image.mp h))
      (by rw [Finset.card_image_of_injective _ hεinj, Finset.card_image_of_injective _ hεinj]
          exact hcard)
      (himg U hSU) (himg Zv hSZv) (himg Za hSZa) (hfin t₀ (Finset.mem_insert_self _ _))

  have hback : ∀ P : Place k F, Place.congrRingEquiv _ he' (ε P) = P := fun P => by
    rw [← Place.congrEquiv_apply, hε, Equiv.apply_symm_apply]
  refine ⟨((RationalFunctionField.moebius k c).toRingEquiv.trans e) g, ?_, ?_, ?_, ?_⟩
  · have hD : Finsupp.mapDomain (Place.congrEquiv _ he')
        (∑ u ∈ U.image ε, Finsupp.single u (1 : ℤ)) = ∑ u ∈ U, Finsupp.single u (1 : ℤ) := by
      rw [Finsupp.mapDomain_finsetSum, Finset.sum_image fun x _ y _ h => hεinj h]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finsupp.mapDomain_single, hε, Equiv.apply_symm_apply]
    rw [← hD, Place.mem_riemannRochSpace_mapDomain_congrEquiv_iff]
    exact hgL
  · have key := Place.ord_congrRingEquiv _ he' (ε t₀) (g - algebraMap k (RatFunc k) β)
    rw [map_sub, he', hback t₀] at key
    rw [key]
    exact hgord
  · intro z hz
    have h1 := hgv (ε z) (Finset.mem_image_of_mem _ hz)
    rw [Equiv.symm_apply_apply] at h1
    have key := (Place.hasValue_congrRingEquiv_iff _ he' (ε z) g (val z)).mpr h1
    rwa [hback z] at key
  · intro z hz
    obtain ⟨γ, hγ, h1⟩ := hga (ε z) (Finset.mem_image_of_mem _ hz)
    refine ⟨γ, hγ, ?_⟩
    have key := (Place.hasValue_congrRingEquiv_iff _ he' (ε z) g γ).mpr h1
    rwa [hback z] at key

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.AlgebraicCurve in
theorem solution
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (U Zv Za : Finset (Place k F)) (t₀ : Place k F) (β : k)
    (val : Place k F → k) (bad : Finset k)
    (hUZv : Disjoint U Zv) (hUZa : Disjoint U Za) (hZ : Disjoint Zv Za)
    (ht₀U : t₀ ∉ U) (ht₀v : t₀ ∉ Zv) (ht₀a : t₀ ∉ Za)
    (hcard : Zv.card + 1 ≤ U.card) :
    ∃ g : F,
      g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
      t₀.ord (g - algebraMap k F β) = 1 ∧
      (∀ z ∈ Zv, z.HasValue g (val z)) ∧
      (∀ z ∈ Za, ∃ γ : k, γ ∉ bad ∧ z.HasValue g γ) :=
  exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc' e he U Zv Za t₀ β val
    bad hUZv hUZa hZ ht₀U ht₀v ht₀a hcard

end S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc (solution)
