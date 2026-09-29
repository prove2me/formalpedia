-- Prove2me | solution 1 for AlgebraicCurve.finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/27a31c64-df8f-5d15-ba0a-85dcbfeada78

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

namespace P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Place.ofHeightOneSpectrum RationalFunctionField.placeOfPoint Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "adicValuation_eq_exp_neg_ord ext coe_algebraMap ResidueField deg adicValuation ord ord_mul ord_inv ofHeightOneSpectrum mk.injEq toValuationSubring mk mem_iff_adicValuation_le_one mem_maximalIdeal_iff_adicValuation_lt_one comapSymmRingEquiv congrRingEquiv ord_congrRingEquiv congrResidueAlgEquiv deg_congrRingEquiv congrEquiv congrEquiv_apply residue_algebraMap HasValue hasValue_algebraMap"
p2m_open "AlgebraicCurve.Place~restrict"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 := by
  simpa using hasValue_algebraMap v (0 : K)

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "residue_eq mul inv unique" end HasValue
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.add {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.add"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.neg {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.neg"
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.sub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.smul {g : F} {a : K} (c : K) (h : v.HasValue g a) : v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]
  exact (hasValue_algebraMap v c).mul h

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.smul"

theorem mem_toValuationSubring_of_mem_riemannRochSpace {D : Divisor K F} {f : F}
    (hf : f ∈ riemannRochSpace D) (hv : D v ≤ 0) : f ∈ v.toValuationSubring := by
  rw [v.mem_iff_adicValuation_le_one]
  refine (hf v).trans ?_
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  exact hv

p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

theorem HasValue.ord_pos_of_eq_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  obtain ⟨hm, hr⟩ := h
  rw [map_zero, IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff_adicValuation_lt_one] at hr
  have h1 : v.adicValuation g = WithZero.exp (-v.ord g) := v.adicValuation_eq_exp_neg_ord hg
  rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hr
  omega

end Place

section NodePairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def nodeCompatiblePairs (E₁ E₂ : Divisor K F) {ι : Type*} (v₁ v₂ : ι → Place K F) :
    Submodule K (F × F) where
  carrier := {p | p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
    ∀ i, ∃ c : K, (v₁ i).HasValue p.1 c ∧ (v₂ i).HasValue p.2 c}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _,
    fun i => ⟨0, Place.hasValue_zero _, Place.hasValue_zero _⟩⟩
  add_mem' := by
    rintro p q ⟨hp1, hp2, hp⟩ ⟨hq1, hq2, hq⟩
    refine ⟨Submodule.add_mem _ hp1 hq1, Submodule.add_mem _ hp2 hq2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    obtain ⟨d, hd1, hd2⟩ := hq i
    exact ⟨c + d, hc1.add hd1, hc2.add hd2⟩
  smul_mem' := by
    rintro a p ⟨hp1, hp2, hp⟩
    refine ⟨Submodule.smul_mem _ a hp1, Submodule.smul_mem _ a hp2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    exact ⟨a * c, hc1.smul a, hc2.smul a⟩

theorem mem_nodeCompatiblePairs_iff {E₁ E₂ : Divisor K F} {ι : Type*} {v₁ v₂ : ι → Place K F}
    {p : F × F} :
    p ∈ nodeCompatiblePairs E₁ E₂ v₁ v₂ ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : K, (v₁ i).HasValue p.1 c ∧ (v₂ i).HasValue p.2 c :=
  Iff.rfl

theorem nodeCompatiblePairs_le_comp {E₁ E₂ : Divisor K F} {ι ι' : Type*} (v₁ v₂ : ι → Place K F)
    (u : ι' → ι) :
    nodeCompatiblePairs E₁ E₂ v₁ v₂ ≤ nodeCompatiblePairs E₁ E₂ (v₁ ∘ u) (v₂ ∘ u) :=
  fun _ ⟨h1, h2, h⟩ => ⟨h1, h2, fun i => h (u i)⟩

end NodePairs

end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Place.ofHeightOneSpectrum RationalFunctionField.placeOfPoint Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap"
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
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Place.ofHeightOneSpectrum RationalFunctionField.placeOfPoint Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap"
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
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Place.ofHeightOneSpectrum RationalFunctionField.placeOfPoint Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap"
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
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Place.ofHeightOneSpectrum RationalFunctionField.placeOfPoint Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum surjective_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

section Interp

variable {k : Type*} [Field k] {ι : Type*}

def wEvalAt (a w : ι → k) (n : ℕ) : degreeLT k n →ₗ[k] (ι → k) where
  toFun P := fun i => w i * (P : k[X]).eval (a i)
  map_add' P Q := by ext i; simp [mul_add]
  map_smul' c P := by ext i; simp; ring

@[scoped simp]
theorem wEvalAt_apply (a w : ι → k) (n : ℕ) (P : degreeLT k n) (i : ι) :
    wEvalAt a w n P i = w i * (P : k[X]).eval (a i) := rfl

variable [Fintype ι] [DecidableEq ι]

theorem wEvalAt_surjective {a w : ι → k} (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0) {n : ℕ}
    (hn : Fintype.card ι ≤ n) : Function.Surjective (wEvalAt a w n) := by
  intro t
  let r : ι → k := fun i => (w i)⁻¹ * t i
  refine ⟨⟨Lagrange.interpolate Finset.univ a r, ?_⟩, ?_⟩
  · refine degreeLT_mono hn (mem_degreeLT.mpr ?_)
    have := Lagrange.degree_interpolate_lt r ha.injOn (s := Finset.univ)
    rwa [Finset.card_univ] at this
  · ext i
    rw [wEvalAt_apply]
    show w i * (Lagrange.interpolate Finset.univ a r).eval (a i) = t i
    rw [Lagrange.eval_interpolate_at_node r ha.injOn (Finset.mem_univ i)]
    simp [r, hw i]

variable {V₁ V₂ W : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup W] [Module k W]

omit [Fintype ι] [DecidableEq ι] in
theorem finrank_ker_coprod_neg_add [FiniteDimensional k V₁] [FiniteDimensional k V₂] [FiniteDimensional k W]
    (e₁ : V₁ →ₗ[k] W) (e₂ : V₂ →ₗ[k] W) (h : Function.Surjective e₁ ∨ Function.Surjective e₂) :
    Module.finrank k (LinearMap.ker (e₁.coprod (-e₂))) + Module.finrank k W
      = Module.finrank k V₁ + Module.finrank k V₂ := by
  have hsurj : LinearMap.range (e₁.coprod (-e₂)) = ⊤ := by
    rw [LinearMap.range_coprod]
    rcases h with h | h
    · rw [LinearMap.range_eq_top.mpr h, top_sup_eq]
    · have : LinearMap.range (-e₂) = ⊤ := by
        rw [LinearMap.range_neg, LinearMap.range_eq_top.mpr h]
      rw [this, sup_top_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker (e₁.coprod (-e₂))
  rw [hsurj, finrank_top, Module.finrank_prod] at hrn
  omega

end Interp
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

section Nodes

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
variable {ι : Type*}

theorem nodeCompatiblePairs_eq_map {E₁ E₂ : Divisor k (RatFunc k)} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (haE : ∀ i, E₁ (placeOfPoint k (a i)) = 0) (hbE : ∀ i, E₂ (placeOfPoint k (b i)) = 0) :
    nodeCompatiblePairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))
      = Submodule.map
          ((divDivisorPolynomial E₁ ∘ₗ (degreeLT k (E₁.degree.toNat + 1)).subtype).prodMap
            (divDivisorPolynomial E₂ ∘ₗ (degreeLT k (E₂.degree.toNat + 1)).subtype))
          (LinearMap.ker
            ((wEvalAt a (fun i => ((divisorPolynomial k E₁).eval (a i))⁻¹) (E₁.degree.toNat + 1)).coprod
              (-(wEvalAt b (fun i => ((divisorPolynomial k E₂).eval (b i))⁻¹) (E₂.degree.toNat + 1))))) := by
  have hd₁ := degree_nonneg hE₁
  have hd₂ := degree_nonneg hE₂
  ext ⟨g₁, g₂⟩
  simp only [mem_nodeCompatiblePairs_iff, Submodule.mem_map, LinearMap.mem_ker, LinearMap.coprod_apply,
    LinearMap.neg_apply, LinearMap.prodMap_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, divDivisorPolynomial_apply, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨hg₁, hg₂, hnode⟩
    obtain ⟨P₁, hP₁, rfl⟩ := exists_eq_div_divisorPolynomial_of_mem hE₁ hg₁
    obtain ⟨P₂, hP₂, rfl⟩ := exists_eq_div_divisorPolynomial_of_mem hE₂ hg₂
    refine ⟨⟨P₁, mem_degreeLT_succ_iff.mpr (by omega)⟩, ⟨P₂, mem_degreeLT_succ_iff.mpr (by omega)⟩, ?_, rfl, rfl⟩
    ext i
    obtain ⟨c, hc₁, hc₂⟩ := hnode i
    have h₁ := hc₁.unique (hasValue_placeOfPoint_div_divisorPolynomial (haE i) P₁)
    have h₂ := hc₂.unique (hasValue_placeOfPoint_div_divisorPolynomial (hbE i) P₂)
    simp only [Pi.add_apply, Pi.neg_apply, wEvalAt_apply, Pi.zero_apply]
    rw [inv_mul_eq_div, inv_mul_eq_div, ← h₁, ← h₂, add_neg_cancel]
  · rintro ⟨P₁, P₂, hker, rfl, rfl⟩
    refine ⟨div_divisorPolynomial_mem_riemannRochSpace hE₁ ?_,
      div_divisorPolynomial_mem_riemannRochSpace hE₂ ?_, fun i => ?_⟩
    · have := mem_degreeLT_succ_iff.mp P₁.2; omega
    · have := mem_degreeLT_succ_iff.mp P₂.2; omega
    refine ⟨(P₁ : k[X]).eval (a i) / (divisorPolynomial k E₁).eval (a i),
      hasValue_placeOfPoint_div_divisorPolynomial (haE i) _, ?_⟩
    have hi := congrFun hker i
    simp only [Pi.add_apply, Pi.neg_apply, wEvalAt_apply, Pi.zero_apply, add_neg_eq_zero,
      inv_mul_eq_div] at hi
    rw [hi]
    exact hasValue_placeOfPoint_div_divisorPolynomial (hbE i) _

theorem finiteDimensional_nodeCompatiblePairs {E₁ E₂ : Divisor k (RatFunc k)} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (haE : ∀ i, E₁ (placeOfPoint k (a i)) = 0) (hbE : ∀ i, E₂ (placeOfPoint k (b i)) = 0) :
    FiniteDimensional k
      (nodeCompatiblePairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))) := by
  rw [nodeCompatiblePairs_eq_map hE₁ hE₂ a b haE hbE]
  infer_instance

variable [Fintype ι] [DecidableEq ι]

theorem finrank_nodeCompatiblePairs_add_card {E₁ E₂ : Divisor k (RatFunc k)} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (haE : ∀ i, E₁ (placeOfPoint k (a i)) = 0) (hbE : ∀ i, E₂ (placeOfPoint k (b i)) = 0)
    (hcard : Fintype.card ι ≤ max E₁.degree.toNat E₂.degree.toNat + 1) :
    Module.finrank k (nodeCompatiblePairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i)))
      + Fintype.card ι = (E₁.degree.toNat + 1) + (E₂.degree.toNat + 1) := by
  rw [nodeCompatiblePairs_eq_map hE₁ hE₂ a b haE hbE]
  have hinj : Function.Injective
      ((divDivisorPolynomial E₁ ∘ₗ (degreeLT k (E₁.degree.toNat + 1)).subtype).prodMap
        (divDivisorPolynomial E₂ ∘ₗ (degreeLT k (E₂.degree.toNat + 1)).subtype)) :=
    Function.Injective.prodMap ((divDivisorPolynomial_injective E₁).comp Subtype.val_injective)
      ((divDivisorPolynomial_injective E₂).comp Subtype.val_injective)
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
  have key := finrank_ker_coprod_neg_add
    (wEvalAt a (fun i => ((divisorPolynomial k E₁).eval (a i))⁻¹) (E₁.degree.toNat + 1))
    (wEvalAt b (fun i => ((divisorPolynomial k E₂).eval (b i))⁻¹) (E₂.degree.toNat + 1)) ?_
  · rw [finrank_degreeLT, finrank_degreeLT, Module.finrank_fintype_fun_eq_card] at key
    exact key
  · rcases le_max_iff.mp (Nat.sub_le_iff_le_add.mpr hcard) with h | h
    · left
      exact wEvalAt_surjective ha (fun i => inv_ne_zero (eval_divisorPolynomial_ne_zero (haE i))) (by omega)
    · right
      exact wEvalAt_surjective hb (fun i => inv_ne_zero (eval_divisorPolynomial_ne_zero (hbE i))) (by omega)

omit [DecidableEq ι] in

theorem finrank_nodeCompatiblePairs_add_min_le {E₁ E₂ : Divisor k (RatFunc k)} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (haE : ∀ i, E₁ (placeOfPoint k (a i)) = 0) (hbE : ∀ i, E₂ (placeOfPoint k (b i)) = 0) :
    Module.finrank k (nodeCompatiblePairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i)))
      + min (Fintype.card ι) (max E₁.degree.toNat E₂.degree.toNat + 1)
      ≤ (E₁.degree.toNat + 1) + (E₂.degree.toNat + 1) := by
  set m := min (Fintype.card ι) (max E₁.degree.toNat E₂.degree.toNat + 1) with hm
  let u : Fin m ↪ ι := (Fin.castLEEmb (min_le_left _ _)).trans (Fintype.equivFin ι).symm.toEmbedding
  have hle := nodeCompatiblePairs_le_comp (E₁ := E₁) (E₂ := E₂)
    (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i)) u
  have heq := finrank_nodeCompatiblePairs_add_card hE₁ hE₂ (a ∘ u) (b ∘ u)
    (ha.comp u.injective) (hb.comp u.injective) (fun i => haE (u i)) (fun i => hbE (u i))
    (by rw [Fintype.card_fin]; exact min_le_right _ _)
  rw [Fintype.card_fin] at heq
  haveI : FiniteDimensional k (nodeCompatiblePairs E₁ E₂ ((fun i => placeOfPoint k (a i)) ∘ u)
      ((fun i => placeOfPoint k (b i)) ∘ u)) :=
    finiteDimensional_nodeCompatiblePairs hE₁ hE₂ (a ∘ u) (b ∘ u) (fun i => haE (u i)) (fun i => hbE (u i))
  have hmono := Submodule.finrank_mono hle
  change Module.finrank k _ ≤ Module.finrank k
    (nodeCompatiblePairs E₁ E₂ (fun i => placeOfPoint k ((a ∘ u) i)) (fun i => placeOfPoint k ((b ∘ u) i))) at hmono
  omega

end Nodes
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Divisor Divisor.degree Place.ofHeightOneSpectrum RationalFunctionField.placeOfPoint Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "adicValuation_eq_exp_neg_ord ext coe_algebraMap ResidueField deg adicValuation ord ord_mul ord_inv ofHeightOneSpectrum mk.injEq toValuationSubring mk mem_iff_adicValuation_le_one mem_maximalIdeal_iff_adicValuation_lt_one comapSymmRingEquiv congrRingEquiv ord_congrRingEquiv congrResidueAlgEquiv deg_congrRingEquiv congrEquiv congrEquiv_apply residue_algebraMap HasValue hasValue_algebraMap"
p2m_open "AlgebraicCurve.Place~restrict"

section CongrTransport

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

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

theorem degree_mapDomain_congrEquiv (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain (congrEquiv e he) D) = Divisor.degree D := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_mapDomain_index_inj (congrEquiv e he).injective]
  refine Finsupp.sum_congr fun v _ => ?_
  show D v * ((congrEquiv e he v).deg : ℤ) = D v * (v.deg : ℤ)
  rw [congrEquiv_apply, deg_congrRingEquiv]

theorem mapDomain_congrEquiv_mapDomain_symm (D' : Divisor K F') :
    Finsupp.mapDomain (congrEquiv e he) (Finsupp.mapDomain (congrEquiv e he).symm D') = D' := by
  rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]

theorem mapDomain_symm_apply (D' : Divisor K F') (v : Place K F) :
    (Finsupp.mapDomain (congrEquiv e he).symm D') v = D' (congrEquiv e he v) := by
  conv_rhs => rw [← mapDomain_congrEquiv_mapDomain_symm e he D']
  rw [Finsupp.mapDomain_apply (congrEquiv e he).injective]

end CongrTransport
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

section CongrNodes

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

theorem nodeCompatiblePairs_mapDomain_congrEquiv (E₁ E₂ : Divisor K F) {ι : Type*} (v₁ v₂ : ι → Place K F) :
    nodeCompatiblePairs (Finsupp.mapDomain (Place.congrEquiv e he) E₁) (Finsupp.mapDomain (Place.congrEquiv e he) E₂)
        (fun i => Place.congrEquiv e he (v₁ i)) (fun i => Place.congrEquiv e he (v₂ i))
      = Submodule.map (((AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv.prodCongr
          (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv) : F × F →ₗ[K] F' × F')
          (nodeCompatiblePairs E₁ E₂ v₁ v₂) := by
  ext ⟨g₁', g₂'⟩
  obtain ⟨g₁, rfl⟩ := e.surjective g₁'
  obtain ⟨g₂, rfl⟩ := e.surjective g₂'
  have hmem : (e g₁, e g₂) ∈ Submodule.map (((AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv.prodCongr
          (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv) : F × F →ₗ[K] F' × F')
          (nodeCompatiblePairs E₁ E₂ v₁ v₂) ↔ (g₁, g₂) ∈ nodeCompatiblePairs E₁ E₂ v₁ v₂ := by
    constructor
    · rintro ⟨⟨f₁, f₂⟩, hf, hfe⟩
      have h1 : e f₁ = e g₁ := congrArg Prod.fst hfe
      have h2 : e f₂ = e g₂ := congrArg Prod.snd hfe
      obtain rfl := e.injective h1
      obtain rfl := e.injective h2
      exact hf
    · intro h
      exact ⟨(g₁, g₂), h, rfl⟩
  rw [hmem, mem_nodeCompatiblePairs_iff, mem_nodeCompatiblePairs_iff,
    Place.mem_riemannRochSpace_mapDomain_congrEquiv_iff, Place.mem_riemannRochSpace_mapDomain_congrEquiv_iff]
  simp only [Place.congrEquiv_apply, Place.hasValue_congrRingEquiv_iff]

theorem finrank_nodeCompatiblePairs_mapDomain_congrEquiv (E₁ E₂ : Divisor K F) {ι : Type*}
    (v₁ v₂ : ι → Place K F) :
    Module.finrank K (nodeCompatiblePairs (Finsupp.mapDomain (Place.congrEquiv e he) E₁)
        (Finsupp.mapDomain (Place.congrEquiv e he) E₂)
        (fun i => Place.congrEquiv e he (v₁ i)) (fun i => Place.congrEquiv e he (v₂ i)))
      = Module.finrank K (nodeCompatiblePairs E₁ E₂ v₁ v₂) := by
  rw [nodeCompatiblePairs_mapDomain_congrEquiv]
  exact LinearEquiv.finrank_map_eq _ _

end CongrNodes
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum surjective_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

section Model

variable {k F : Type*} [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)] [Field F] [Algebra k F]

theorem finrank_riemannRochSpace_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {E : Divisor k F} (hE : 0 ≤ E) :
    Module.finrank k (riemannRochSpace E) = E.degree.toNat + 1 := by
  set E₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E with hE₀
  have hE₀' : 0 ≤ E₀ := fun v => by
    rw [hE₀, Place.mapDomain_symm_apply]
    exact hE _
  have hEE : E = Finsupp.mapDomain (Place.congrEquiv e he) E₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E).symm
  have hmap : riemannRochSpace E
      = Submodule.map ((AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv : RatFunc k →ₗ[k] F)
          (riemannRochSpace E₀) := by
    ext f'
    obtain ⟨f, rfl⟩ := e.surjective f'
    rw [hEE, Place.mem_riemannRochSpace_mapDomain_congrEquiv_iff]
    constructor
    · intro h
      exact ⟨f, h, rfl⟩
    · rintro ⟨g, hg, hge⟩
      simp only [LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, AlgEquiv.ofRingEquiv_apply,
        EmbeddingLike.apply_eq_iff_eq] at hge
      subst hge
      exact hg
  rw [hmap, LinearEquiv.finrank_map_eq, finrank_riemannRochSpace hE₀', hEE, Place.degree_mapDomain_congrEquiv]

theorem degree_nonneg_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {E : Divisor k F} (hE : 0 ≤ E) : 0 ≤ E.degree := by
  rw [← Place.mapDomain_congrEquiv_mapDomain_symm e he E, Place.degree_mapDomain_congrEquiv]
  exact degree_nonneg (fun v => by rw [Place.mapDomain_symm_apply]; exact hE _)

theorem finiteDimensional_riemannRochSpace_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {E : Divisor k F} (hE : 0 ≤ E) :
    FiniteDimensional k (riemannRochSpace E) := by
  have h := finrank_riemannRochSpace_of_ringEquiv e he hE
  exact Module.finite_of_finrank_eq_succ h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem finrank_nodeCompatiblePairs_add_min_le_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {E₁ E₂ : Divisor k F} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (haE : ∀ i, E₁ (Place.congrEquiv e he (placeOfPoint k (a i))) = 0)
    (hbE : ∀ i, E₂ (Place.congrEquiv e he (placeOfPoint k (b i))) = 0) :
    Module.finrank k (nodeCompatiblePairs E₁ E₂
        (fun i => Place.congrEquiv e he (placeOfPoint k (a i)))
        (fun i => Place.congrEquiv e he (placeOfPoint k (b i))))
      + min (Fintype.card ι) (max E₁.degree.toNat E₂.degree.toNat + 1)
      ≤ (E₁.degree.toNat + 1) + (E₂.degree.toNat + 1) := by
  set E₁₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E₁ with hE₁₀
  set E₂₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E₂ with hE₂₀
  have h1 : E₁ = Finsupp.mapDomain (Place.congrEquiv e he) E₁₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E₁).symm
  have h2 : E₂ = Finsupp.mapDomain (Place.congrEquiv e he) E₂₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E₂).symm
  have key := finrank_nodeCompatiblePairs_add_min_le (k := k) (E₁ := E₁₀) (E₂ := E₂₀)
    (fun v => by rw [hE₁₀, Place.mapDomain_symm_apply]; exact hE₁ _)
    (fun v => by rw [hE₂₀, Place.mapDomain_symm_apply]; exact hE₂ _)
    a b ha hb
    (fun i => by rw [hE₁₀, Place.mapDomain_symm_apply]; exact haE i)
    (fun i => by rw [hE₂₀, Place.mapDomain_symm_apply]; exact hbE i)
  rw [h1, h2, finrank_nodeCompatiblePairs_mapDomain_congrEquiv, Place.degree_mapDomain_congrEquiv,
    Place.degree_mapDomain_congrEquiv]
  exact key

theorem finrank_nodeCompatiblePairs_add_card_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {E₁ E₂ : Divisor k F} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (haE : ∀ i, E₁ (Place.congrEquiv e he (placeOfPoint k (a i))) = 0)
    (hbE : ∀ i, E₂ (Place.congrEquiv e he (placeOfPoint k (b i))) = 0)
    (hcard : Fintype.card ι ≤ max E₁.degree.toNat E₂.degree.toNat + 1) :
    Module.finrank k (nodeCompatiblePairs E₁ E₂
        (fun i => Place.congrEquiv e he (placeOfPoint k (a i)))
        (fun i => Place.congrEquiv e he (placeOfPoint k (b i))))
      + Fintype.card ι = (E₁.degree.toNat + 1) + (E₂.degree.toNat + 1) := by
  set E₁₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E₁ with hE₁₀
  set E₂₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E₂ with hE₂₀
  have h1 : E₁ = Finsupp.mapDomain (Place.congrEquiv e he) E₁₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E₁).symm
  have h2 : E₂ = Finsupp.mapDomain (Place.congrEquiv e he) E₂₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E₂).symm
  have hd1 : E₁₀.degree = E₁.degree := by rw [h1, Place.degree_mapDomain_congrEquiv]
  have hd2 : E₂₀.degree = E₂.degree := by rw [h2, Place.degree_mapDomain_congrEquiv]
  have key := finrank_nodeCompatiblePairs_add_card (k := k) (E₁ := E₁₀) (E₂ := E₂₀)
    (fun v => by rw [hE₁₀, Place.mapDomain_symm_apply]; exact hE₁ _)
    (fun v => by rw [hE₂₀, Place.mapDomain_symm_apply]; exact hE₂ _)
    a b ha hb
    (fun i => by rw [hE₁₀, Place.mapDomain_symm_apply]; exact haE i)
    (fun i => by rw [hE₂₀, Place.mapDomain_symm_apply]; exact hbE i)
    (by rw [hd1, hd2]; exact hcard)
  rw [h1, h2, finrank_nodeCompatiblePairs_mapDomain_congrEquiv, Place.degree_mapDomain_congrEquiv,
    Place.degree_mapDomain_congrEquiv]
  exact key

end Model
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

section Cards
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField"

theorem FltWs24.P1.cardA
    {k : Type*} [Field k] [IsAlgClosed k] (E : Divisor k (RatFunc k)) (hE : 0 ≤ E) :
    (Module.finrank k (riemannRochSpace E) : ℤ) = E.degree + 1 := by
  classical
  rw [finrank_riemannRochSpace hE]
  have := degree_nonneg hE
  omega

theorem FltWs24.P1.cardB
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {ι : Type*} [Fintype ι]
    (E₁ E₂ : Divisor k F) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (haE : ∀ i, E₁ (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i))) = 0)
    (hbE : ∀ i, E₂ (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (b i))) = 0)
    (T : Submodule k (F × F))
    (hT : ∀ p, p ∈ T ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : k, (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i))).HasValue p.1 c ∧
        (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (b i))).HasValue p.2 c) :
    (Module.finrank k T : ℤ) + min (Fintype.card ι : ℤ) (max E₁.degree E₂.degree + 1)
      ≤ (E₁.degree + 1) + (E₂.degree + 1) := by
  classical
  have hTe : T = nodeCompatiblePairs E₁ E₂ (fun i => Place.congrEquiv e he (placeOfPoint k (a i)))
      (fun i => Place.congrEquiv e he (placeOfPoint k (b i))) := by
    ext p
    rw [hT, mem_nodeCompatiblePairs_iff]
  have key := finrank_nodeCompatiblePairs_add_min_le_of_ringEquiv e he hE₁ hE₂ a b ha hb haE hbE
  rw [← hTe] at key
  have h1 := Int.toNat_of_nonneg (degree_nonneg_of_ringEquiv e he hE₁)
  have h2 := Int.toNat_of_nonneg (degree_nonneg_of_ringEquiv e he hE₂)
  omega

theorem FltWs24.P1.cardC
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {ι : Type*} [Fintype ι]
    (E₁ E₂ : Divisor k F) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (haE : ∀ i, E₁ (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i))) = 0)
    (hbE : ∀ i, E₂ (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (b i))) = 0)
    (hcard : (Fintype.card ι : ℤ) ≤ max E₁.degree E₂.degree + 1)
    (T : Submodule k (F × F))
    (hT : ∀ p, p ∈ T ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : k, (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i))).HasValue p.1 c ∧
        (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (b i))).HasValue p.2 c) :
    (Module.finrank k T : ℤ) + Fintype.card ι = (E₁.degree + 1) + (E₂.degree + 1) := by
  classical
  have hTe : T = nodeCompatiblePairs E₁ E₂ (fun i => Place.congrEquiv e he (placeOfPoint k (a i)))
      (fun i => Place.congrEquiv e he (placeOfPoint k (b i))) := by
    ext p
    rw [hT, mem_nodeCompatiblePairs_iff]
  have h1 := Int.toNat_of_nonneg (degree_nonneg_of_ringEquiv e he hE₁)
  have h2 := Int.toNat_of_nonneg (degree_nonneg_of_ringEquiv e he hE₂)
  have key := finrank_nodeCompatiblePairs_add_card_of_ringEquiv e he hE₁ hE₂ a b ha hb haE hbE (by omega)
  rw [← hTe] at key
  omega

theorem FltWs24.P1.cardD
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) (hE : 0 ≤ E) :
    (Module.finrank k (riemannRochSpace E) : ℤ) = E.degree + 1 := by
  classical
  rw [AlgebraicCurve.RationalFunctionField.finrank_riemannRochSpace_of_ringEquiv e he hE]
  have := AlgebraicCurve.RationalFunctionField.degree_nonneg_of_ringEquiv e he hE
  omega

end Cards
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc.AlgebraicCurve in
theorem solution
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) (hE : 0 ≤ E) :
    (Module.finrank k (riemannRochSpace E) : ℤ) = E.degree + 1 :=
  FltWs24.P1.cardD e he E hE

end S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc
end P2MW
export P2MW.S_AlgebraicCurve_finrank_riemannRochSpace_eq_degree_add_one_of_ringEquiv_ratFunc (solution)
