-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c1aa4e3a-9c52-58b8-9ce8-cefb704f3d91

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

namespace P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Place.ord_zpow Divisor Divisor.degree Place.ofHeightOneSpectrum Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap Place.HasValue"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg ord ord_mul ord_inv ord_zpow ofHeightOneSpectrum mk.injEq toValuationSubring mk comapSymmRingEquiv congrRingEquiv ord_congrRingEquiv congrResidueAlgEquiv deg_congrRingEquiv congrEquiv congrEquiv_apply residue_algebraMap HasValue hasValue_one hasValue_algebraMap"
p2m_open "AlgebraicCurve.Place~restrict"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 := by
  simpa using hasValue_algebraMap v (0 : K)

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mul inv unique" end HasValue
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
private theorem _root_.AlgebraicCurve.Place.HasValue.const_mul {g : F} {a : K} (c : K) (h : v.HasValue g a) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]
  exact (hasValue_algebraMap v c).mul h

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.const_mul"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.pow {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using hasValue_one v
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.pow"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.zpow {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) (n : ℤ) :
    v.HasValue (g ^ n) (a ^ n) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact h.pow n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    exact (h.pow _).inv (pow_ne_zero _ ha)

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.zpow"
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.prod {ι : Type*} (s : Finset ι) {g : ι → F} {a : ι → K}
    (h : ∀ i ∈ s, v.HasValue (g i) (a i)) : v.HasValue (∏ i ∈ s, g i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValue_one v
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ord_prod {ι : Type*} (s : Finset ι) {g : ι → F} (h : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      v.ord_mul (h i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

end Place

section TwistedPairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def twistedPairs (E₁ E₂ : Divisor K F) {ι : Type*} (v₁ v₂ : ι → Place K F) (t₁ t₂ : ι → F)
    (lam : ι → K) : Submodule K (F × F) where
  carrier := {p | p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
    ∀ i, ∃ c : K, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _, fun i =>
    ⟨0, by simpa using Place.hasValue_zero (v₁ i), by simpa using Place.hasValue_zero (v₂ i)⟩⟩
  add_mem' := by
    rintro p q ⟨hp1, hp2, hp⟩ ⟨hq1, hq2, hq⟩
    refine ⟨Submodule.add_mem _ hp1 hq1, Submodule.add_mem _ hp2 hq2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    obtain ⟨d, hd1, hd2⟩ := hq i
    refine ⟨c + d, ?_, ?_⟩
    · simpa [mul_add] using hc1.add hd1
    · simpa [mul_add] using hc2.add hd2
  smul_mem' := by
    rintro a p ⟨hp1, hp2, hp⟩
    refine ⟨Submodule.smul_mem _ a hp1, Submodule.smul_mem _ a hp2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    refine ⟨a * c, ?_, ?_⟩
    · have := hc1.const_mul a
      rw [Prod.smul_fst, mul_smul_comm]
      convert this using 1
      ring
    · have := hc2.const_mul a
      rw [Prod.smul_snd, mul_smul_comm]
      exact this

theorem mem_twistedPairs_iff {E₁ E₂ : Divisor K F} {ι : Type*} {v₁ v₂ : ι → Place K F}
    {t₁ t₂ : ι → F} {lam : ι → K} {p : F × F} :
    p ∈ twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : K, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c :=
  Iff.rfl

theorem twistedPairs_le_comp {E₁ E₂ : Divisor K F} {ι ι' : Type*} (v₁ v₂ : ι → Place K F)
    (t₁ t₂ : ι → F) (lam : ι → K) (u : ι' → ι) :
    twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam
      ≤ twistedPairs E₁ E₂ (v₁ ∘ u) (v₂ ∘ u) (t₁ ∘ u) (t₂ ∘ u) (lam ∘ u) :=
  fun _ ⟨h1, h2, h⟩ => ⟨h1, h2, fun i => h (u i)⟩

end TwistedPairs

end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Place.ord_zpow Divisor Divisor.degree Place.ofHeightOneSpectrum Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap Place.HasValue"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
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

theorem algebraMap_X_sub_C (a : k) :
    algebraMap k[X] (RatFunc k) (X - C a) = RatFunc.X - RatFunc.C a := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem ratFunc_X_sub_C_ne_zero (a : k) : (RatFunc.X - RatFunc.C a : RatFunc k) ≠ 0 := by
  rw [← algebraMap_X_sub_C]
  exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (X_sub_C_ne_zero a)

open scoped Classical in

theorem ord_placeOfPoint_X_sub_C (a b : k) :
    (placeOfPoint k b).ord (RatFunc.X - RatFunc.C a : RatFunc k) = if b = a then 1 else 0 := by
  rw [← algebraMap_X_sub_C, ord_placeOfPoint_algebraMap b (X_sub_C_ne_zero a)]
  split_ifs with h
  · subst h
    exact_mod_cast rootMultiplicity_X_sub_C_self
  · rw [Nat.cast_eq_zero]
    refine rootMultiplicity_eq_zero ?_
    rw [IsRoot, eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr h

theorem ord_placeInfty_X_sub_C [DecidableEq (RatFunc k)] (a : k) :
    (placeInfty k).ord (RatFunc.X - RatFunc.C a : RatFunc k) = -1 := by
  rw [ord_placeInfty (ratFunc_X_sub_C_ne_zero a), ← algebraMap_X_sub_C, RatFunc.intDegree_polynomial,
    natDegree_X_sub_C]
  simp

variable (k) in

def divisorFn (E : Divisor k (RatFunc k)) (S : Finset k) : RatFunc k :=
  ∏ a ∈ S, (RatFunc.X - RatFunc.C a) ^ (E (placeOfPoint k a))

theorem divisorFn_ne_zero (E : Divisor k (RatFunc k)) (S : Finset k) : divisorFn k E S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun a _ => zpow_ne_zero _ (ratFunc_X_sub_C_ne_zero a)

theorem divisorFn_eq_of_subset {E : Divisor k (RatFunc k)} {S : Finset k} (hS : divisorPoints k E ⊆ S) :
    divisorFn k E S = divisorFn k E (divisorPoints k E) := by
  rw [divisorFn, divisorFn]
  refine (Finset.prod_subset hS fun a _ ha => ?_).symm
  rw [mem_divisorPoints, not_not] at ha
  rw [ha, zpow_zero]

theorem divisorFn_insert_erase [DecidableEq k] (E : Divisor k (RatFunc k)) (b : k) :
    divisorFn k E (divisorPoints k E)
      = (RatFunc.X - RatFunc.C b) ^ (E (placeOfPoint k b)) * divisorFn k E ((divisorPoints k E).erase b) := by
  rw [← divisorFn_eq_of_subset (Finset.subset_insert b (divisorPoints k E)), divisorFn,
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self b _), Finset.erase_insert_eq_erase]
  rfl

theorem ord_placeOfPoint_divisorFn {E : Divisor k (RatFunc k)} {S : Finset k} (hS : divisorPoints k E ⊆ S)
    (b : k) : (placeOfPoint k b).ord (divisorFn k E S) = E (placeOfPoint k b) := by
  classical
  rw [divisorFn, Place.ord_prod _ fun a _ => zpow_ne_zero _ (ratFunc_X_sub_C_ne_zero a)]
  simp only [Place.ord_zpow, ord_placeOfPoint_X_sub_C, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with hb
  · rfl
  · have : b ∉ divisorPoints k E := fun h => hb (hS h)
    rw [mem_divisorPoints, not_not] at this
    exact this.symm

theorem ord_placeInfty_divisorFn [DecidableEq (RatFunc k)] (E : Divisor k (RatFunc k)) (S : Finset k) :
    (placeInfty k).ord (divisorFn k E S) = -∑ a ∈ S, E (placeOfPoint k a) := by
  rw [divisorFn, Place.ord_prod _ fun a _ => zpow_ne_zero _ (ratFunc_X_sub_C_ne_zero a)]
  simp only [Place.ord_zpow, ord_placeInfty_X_sub_C, mul_neg, mul_one, Finset.sum_neg_distrib]

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

theorem degree_eq_sum_of_subset [IsAlgClosed k] [DecidableEq (RatFunc k)] {E : Divisor k (RatFunc k)}
    {S : Finset k} (hS : divisorPoints k E ⊆ S) :
    E.degree = (∑ a ∈ S, E (placeOfPoint k a)) + E (placeInfty k) := by
  rw [degree_eq_sum_divisorPoints, Finset.sum_subset hS]
  intro a _ ha
  rw [mem_divisorPoints, not_not] at ha
  exact ha

end Points

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Place.ord_zpow Divisor Divisor.degree Place.ofHeightOneSpectrum Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap Place.HasValue"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

section RiemannRoch

variable {k : Type*} [Field k]

theorem algebraMap_ne_zero' {P : k[X]} (hP : P ≠ 0) : algebraMap k[X] (RatFunc k) P ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hP

theorem mem_degreeLT_iff_natDegree {P : k[X]} {n : ℕ} : P ∈ degreeLT k n ↔ P = 0 ∨ P.natDegree < n := by
  rw [mem_degreeLT]
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · rw [degree_eq_natDegree hP, Nat.cast_lt]
    simp [hP]

theorem ord_placeOfPoint_div_divisorFn {E : Divisor k (RatFunc k)} {S : Finset k}
    (hS : divisorPoints k E ⊆ S) {P : k[X]} (hP : P ≠ 0) (b : k) :
    (placeOfPoint k b).ord (algebraMap k[X] (RatFunc k) P / divisorFn k E S)
      = (rootMultiplicity b P : ℤ) - E (placeOfPoint k b) := by
  rw [div_eq_mul_inv, (placeOfPoint k b).ord_mul (algebraMap_ne_zero' hP) (inv_ne_zero (divisorFn_ne_zero E S)),
    Place.ord_inv, ord_placeOfPoint_algebraMap b hP, ord_placeOfPoint_divisorFn hS]
  ring

theorem ord_placeInfty_div_divisorFn [DecidableEq (RatFunc k)] (E : Divisor k (RatFunc k)) (S : Finset k)
    {P : k[X]} (hP : P ≠ 0) :
    (placeInfty k).ord (algebraMap k[X] (RatFunc k) P / divisorFn k E S)
      = (∑ a ∈ S, E (placeOfPoint k a)) - P.natDegree := by
  rw [div_eq_mul_inv, (placeInfty k).ord_mul (algebraMap_ne_zero' hP) (inv_ne_zero (divisorFn_ne_zero E S)),
    Place.ord_inv, ord_placeInfty (algebraMap_ne_zero' hP), RatFunc.intDegree_polynomial,
    ord_placeInfty_divisorFn]
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
  rw [key, div_eq_mul_inv, (placeOfPoint k a).ord_mul (algebraMap_ne_zero' hnum0)
      (inv_ne_zero (algebraMap_ne_zero' (RatFunc.denom_ne_zero f))), Place.ord_inv,
    ord_placeOfPoint_algebraMap a hnum0, ord_placeOfPoint_algebraMap a (RatFunc.denom_ne_zero f), h1] at h3
  simp only [CharP.cast_eq_zero, zero_add, Left.nonneg_neg_iff] at h3
  omega

variable [IsAlgClosed k] [DecidableEq (RatFunc k)]

theorem div_divisorFn_mem_riemannRochSpace (E : Divisor k (RatFunc k)) {P : k[X]}
    (hP : P ∈ degreeLT k (E.degree + 1).toNat) :
    algebraMap k[X] (RatFunc k) P / divisorFn k E (divisorPoints k E) ∈ riemannRochSpace E := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  have hPd : (P.natDegree : ℤ) ≤ E.degree := by
    rcases mem_degreeLT_iff_natDegree.mp hP with h | h
    · exact absurd h hP0
    · omega
  rw [mem_riemannRochSpace_iff]
  intro v
  right
  rcases eq_placeOfPoint_or_eq_placeInfty k v with ⟨b, rfl⟩ | rfl
  · rw [ord_placeOfPoint_div_divisorFn subset_rfl hP0]
    have : (0 : ℤ) ≤ rootMultiplicity b P := Nat.cast_nonneg _
    linarith
  · rw [ord_placeInfty_div_divisorFn _ _ hP0]
    rw [degree_eq_sum_divisorPoints] at hPd
    linarith

set_option maxHeartbeats 1600000 in

theorem exists_eq_div_divisorFn_of_mem (E : Divisor k (RatFunc k)) {f : RatFunc k}
    (hf : f ∈ riemannRochSpace E) :
    ∃ P : k[X], P ∈ degreeLT k (E.degree + 1).toNat ∧
      f = algebraMap k[X] (RatFunc k) P / divisorFn k E (divisorPoints k E) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, Submodule.zero_mem _, by simp⟩
  have hh := divisorFn_ne_zero E (divisorPoints k E)
  have hg : ∀ a : k, 0 ≤ (placeOfPoint k a).ord (f * divisorFn k E (divisorPoints k E)) := by
    intro a
    rw [(placeOfPoint k a).ord_mul hf0 hh, ord_placeOfPoint_divisorFn subset_rfl]
    have := ((mem_riemannRochSpace_iff.mp hf) (placeOfPoint k a)).resolve_left hf0
    linarith
  obtain ⟨P, hP⟩ := exists_eq_algebraMap_of_forall_ord_nonneg hg
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero] at hP
    exact (mul_ne_zero hf0 hh) hP
  have hfP : f = algebraMap k[X] (RatFunc k) P / divisorFn k E (divisorPoints k E) := by
    rw [eq_div_iff hh, hP]
  refine ⟨P, ?_, hfP⟩
  have hinf := ((mem_riemannRochSpace_iff.mp hf) (placeInfty k)).resolve_left hf0
  rw [hfP, ord_placeInfty_div_divisorFn _ _ hP0] at hinf
  have hd := degree_eq_sum_divisorPoints (k := k) E
  rw [mem_degreeLT_iff_natDegree]
  right
  omega

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in

def divDivisorFn (E : Divisor k (RatFunc k)) : k[X] →ₗ[k] RatFunc k :=
  (LinearMap.mulRight k (divisorFn k E (divisorPoints k E))⁻¹).comp
    (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
@[scoped simp]
theorem divDivisorFn_apply (E : Divisor k (RatFunc k)) (P : k[X]) :
    divDivisorFn E P = algebraMap k[X] (RatFunc k) P / divisorFn k E (divisorPoints k E) := by
  simp [divDivisorFn, div_eq_mul_inv]

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
theorem divDivisorFn_injective (E : Divisor k (RatFunc k)) : Function.Injective (divDivisorFn E) := by
  intro P Q hPQ
  simp only [divDivisorFn_apply] at hPQ
  exact IsFractionRing.injective k[X] (RatFunc k) ((div_left_inj' (divisorFn_ne_zero E _)).mp hPQ)

def riemannRochSpaceEquiv (E : Divisor k (RatFunc k)) :
    degreeLT k (E.degree + 1).toNat ≃ₗ[k] riemannRochSpace E :=
  LinearEquiv.ofBijective
    ((divDivisorFn E).restrict (p := degreeLT k (E.degree + 1).toNat) (q := riemannRochSpace E)
      (fun P hP => by
        rw [divDivisorFn_apply]
        exact div_divisorFn_mem_riemannRochSpace E hP))
    ⟨fun P Q h => Subtype.ext (divDivisorFn_injective E (congrArg Subtype.val h)),
      fun ⟨f, hf⟩ => by
        obtain ⟨P, hP, rfl⟩ := exists_eq_div_divisorFn_of_mem E hf
        exact ⟨⟨P, hP⟩, Subtype.ext (by simp [LinearMap.restrict_apply])⟩⟩

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
theorem finrank_degreeLT (n : ℕ) : Module.finrank k (degreeLT k n) = n := by
  rw [LinearEquiv.finrank_eq (degreeLTEquiv k n), Module.finrank_fin_fun]

theorem finrank_riemannRochSpace (E : Divisor k (RatFunc k)) :
    Module.finrank k (riemannRochSpace E) = (E.degree + 1).toNat := by
  rw [← (riemannRochSpaceEquiv E).finrank_eq, finrank_degreeLT]

end RiemannRoch
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Place.ord_zpow Divisor Divisor.degree Place.ofHeightOneSpectrum Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap Place.HasValue"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

section Values

variable {k : Type*} [Field k]

set_option maxHeartbeats 1600000 in

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

theorem hasValue_placeOfPoint_X_sub_C (b a : k) :
    (placeOfPoint k b).HasValue (RatFunc.X - RatFunc.C a : RatFunc k) (b - a) := by
  have := hasValue_placeOfPoint_algebraMap b (X - C a)
  rwa [algebraMap_X_sub_C, eval_sub, eval_X, eval_C] at this

variable (k) in

def divisorFnEval (E : Divisor k (RatFunc k)) (S : Finset k) (b : k) : k :=
  ∏ a ∈ S, (b - a) ^ (E (placeOfPoint k a))

theorem divisorFnEval_ne_zero (E : Divisor k (RatFunc k)) {S : Finset k} {b : k} (hb : b ∉ S) :
    divisorFnEval k E S b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun a ha => zpow_ne_zero _ (sub_ne_zero.mpr fun h => hb (h ▸ ha))

theorem hasValue_placeOfPoint_divisorFn (E : Divisor k (RatFunc k)) {S : Finset k} {b : k} (hb : b ∉ S) :
    (placeOfPoint k b).HasValue (divisorFn k E S) (divisorFnEval k E S b) :=
  Place.HasValue.prod S fun a ha =>
    (hasValue_placeOfPoint_X_sub_C b a).zpow (sub_ne_zero.mpr fun h => hb (h ▸ ha)) _

theorem hasValue_placeOfPoint_twist [DecidableEq k] (E : Divisor k (RatFunc k)) (b : k) (P : k[X]) :
    (placeOfPoint k b).HasValue
      ((RatFunc.X - RatFunc.C b) ^ (E (placeOfPoint k b)) *
        (algebraMap k[X] (RatFunc k) P / divisorFn k E (divisorPoints k E)))
      (P.eval b / divisorFnEval k E ((divisorPoints k E).erase b) b) := by
  have hb : b ∉ (divisorPoints k E).erase b := Finset.notMem_erase b _
  have hne : (RatFunc.X - RatFunc.C b : RatFunc k) ^ (E (placeOfPoint k b)) ≠ 0 :=
    zpow_ne_zero _ (ratFunc_X_sub_C_ne_zero b)
  have key : (RatFunc.X - RatFunc.C b) ^ (E (placeOfPoint k b)) *
        (algebraMap k[X] (RatFunc k) P / divisorFn k E (divisorPoints k E))
      = algebraMap k[X] (RatFunc k) P / divisorFn k E ((divisorPoints k E).erase b) := by
    rw [divisorFn_insert_erase E b, ← mul_div_assoc, mul_div_mul_left _ _ hne]
  rw [key, div_eq_mul_inv, div_eq_mul_inv]
  exact (hasValue_placeOfPoint_algebraMap b P).mul
    ((hasValue_placeOfPoint_divisorFn E hb).inv (divisorFnEval_ne_zero E hb))

end Values
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Place.ord_zpow Divisor Divisor.degree Place.ofHeightOneSpectrum Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap Place.HasValue"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
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
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

section Nodes

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
variable {ι : Type*}

def twistWeight (E : Divisor k (RatFunc k)) (b : k) : k :=
  (divisorFnEval k E ((divisorPoints k E).erase b) b)⁻¹

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
theorem twistWeight_ne_zero (E : Divisor k (RatFunc k)) (b : k) : twistWeight E b ≠ 0 :=
  inv_ne_zero (divisorFnEval_ne_zero E (Finset.notMem_erase b _))

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
theorem hasValue_twist' (E : Divisor k (RatFunc k)) (b : k) (P : k[X]) :
    (placeOfPoint k b).HasValue
      ((RatFunc.X - RatFunc.C b) ^ (E (placeOfPoint k b)) *
        (algebraMap k[X] (RatFunc k) P / divisorFn k E (divisorPoints k E)))
      (twistWeight E b * P.eval b) := by
  rw [twistWeight, inv_mul_eq_div]
  exact hasValue_placeOfPoint_twist E b P

def twistFn (E : Divisor k (RatFunc k)) (b : k) : RatFunc k :=
  (RatFunc.X - RatFunc.C b) ^ (E (placeOfPoint k b))

set_option maxHeartbeats 1600000 in

theorem twistedPairs_eq_map (E₁ E₂ : Divisor k (RatFunc k)) (a b : ι → k) (lam : ι → k) :
    twistedPairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))
        (fun i => twistFn E₁ (a i)) (fun i => twistFn E₂ (b i)) lam
      = Submodule.map
          ((divDivisorFn E₁ ∘ₗ (degreeLT k (E₁.degree + 1).toNat).subtype).prodMap
            (divDivisorFn E₂ ∘ₗ (degreeLT k (E₂.degree + 1).toNat).subtype))
          (LinearMap.ker
            ((wEvalAt a (fun i => twistWeight E₁ (a i)) (E₁.degree + 1).toNat).coprod
              (-(wEvalAt b (fun i => lam i * twistWeight E₂ (b i)) (E₂.degree + 1).toNat)))) := by
  ext ⟨g₁, g₂⟩
  simp only [twistFn, mem_twistedPairs_iff, Submodule.mem_map, LinearMap.mem_ker, LinearMap.coprod_apply,
    LinearMap.neg_apply, LinearMap.prodMap_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, divDivisorFn_apply, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨hg₁, hg₂, hnode⟩
    obtain ⟨P₁, hP₁, rfl⟩ := exists_eq_div_divisorFn_of_mem E₁ hg₁
    obtain ⟨P₂, hP₂, rfl⟩ := exists_eq_div_divisorFn_of_mem E₂ hg₂
    refine ⟨⟨P₁, hP₁⟩, ⟨P₂, hP₂⟩, ?_, rfl, rfl⟩
    ext i
    obtain ⟨c, hc₁, hc₂⟩ := hnode i
    have h₁ := hc₁.unique (hasValue_twist' E₁ (a i) P₁)
    have h₂ := hc₂.unique (hasValue_twist' E₂ (b i) P₂)
    simp only [Pi.add_apply, Pi.neg_apply, wEvalAt_apply, Pi.zero_apply]
    rw [mul_assoc, ← h₂, ← h₁, add_neg_cancel]
  · rintro ⟨P₁, P₂, hker, rfl, rfl⟩
    refine ⟨div_divisorFn_mem_riemannRochSpace E₁ P₁.2, div_divisorFn_mem_riemannRochSpace E₂ P₂.2,
      fun i => ?_⟩
    refine ⟨twistWeight E₂ (b i) * (P₂ : k[X]).eval (b i), ?_, hasValue_twist' E₂ (b i) _⟩
    have hi := congrFun hker i
    simp only [Pi.add_apply, Pi.neg_apply, wEvalAt_apply, Pi.zero_apply, add_neg_eq_zero] at hi
    have := hasValue_twist' E₁ (a i) (P₁ : k[X])
    rwa [hi, mul_assoc] at this

theorem finiteDimensional_twistedPairs (E₁ E₂ : Divisor k (RatFunc k)) (a b : ι → k) (lam : ι → k) :
    FiniteDimensional k
      (twistedPairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))
        (fun i => twistFn E₁ (a i)) (fun i => twistFn E₂ (b i)) lam) := by
  rw [twistedPairs_eq_map E₁ E₂ a b lam]
  infer_instance

variable [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1600000 in

theorem finrank_twistedPairs_add_card (E₁ E₂ : Divisor k (RatFunc k))
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (lam : ι → k) (hlam : ∀ i, lam i ≠ 0)
    (hcard : Fintype.card ι ≤ max (E₁.degree + 1).toNat (E₂.degree + 1).toNat) :
    Module.finrank k (twistedPairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))
        (fun i => twistFn E₁ (a i)) (fun i => twistFn E₂ (b i)) lam)
      + Fintype.card ι = (E₁.degree + 1).toNat + (E₂.degree + 1).toNat := by
  rw [twistedPairs_eq_map E₁ E₂ a b lam]
  have hinj : Function.Injective
      ((divDivisorFn E₁ ∘ₗ (degreeLT k (E₁.degree + 1).toNat).subtype).prodMap
        (divDivisorFn E₂ ∘ₗ (degreeLT k (E₂.degree + 1).toNat).subtype)) :=
    Function.Injective.prodMap ((divDivisorFn_injective E₁).comp Subtype.val_injective)
      ((divDivisorFn_injective E₂).comp Subtype.val_injective)
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
  have key := finrank_ker_coprod_neg_add
    (wEvalAt a (fun i => twistWeight E₁ (a i)) (E₁.degree + 1).toNat)
    (wEvalAt b (fun i => lam i * twistWeight E₂ (b i)) (E₂.degree + 1).toNat) ?_
  · rw [finrank_degreeLT, finrank_degreeLT, Module.finrank_fintype_fun_eq_card] at key
    exact key
  · rcases le_max_iff.mp hcard with h | h
    · left
      exact wEvalAt_surjective ha (fun i => twistWeight_ne_zero E₁ (a i)) h
    · right
      exact wEvalAt_surjective hb (fun i => mul_ne_zero (hlam i) (twistWeight_ne_zero E₂ (b i))) h

set_option maxHeartbeats 1600000 in
omit [DecidableEq ι] in

theorem finrank_twistedPairs_add_min_le (E₁ E₂ : Divisor k (RatFunc k))
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (lam : ι → k) (hlam : ∀ i, lam i ≠ 0) :
    Module.finrank k (twistedPairs E₁ E₂ (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))
        (fun i => twistFn E₁ (a i)) (fun i => twistFn E₂ (b i)) lam)
      + min (Fintype.card ι) (max (E₁.degree + 1).toNat (E₂.degree + 1).toNat)
      ≤ (E₁.degree + 1).toNat + (E₂.degree + 1).toNat := by
  set m := min (Fintype.card ι) (max (E₁.degree + 1).toNat (E₂.degree + 1).toNat) with hm
  let u : Fin m ↪ ι := (Fin.castLEEmb (min_le_left _ _)).trans (Fintype.equivFin ι).symm.toEmbedding
  have hle := twistedPairs_le_comp (E₁ := E₁) (E₂ := E₂)
    (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))
    (fun i => twistFn E₁ (a i)) (fun i => twistFn E₂ (b i)) lam u
  have heq := finrank_twistedPairs_add_card E₁ E₂ (a ∘ u) (b ∘ u)
    (ha.comp u.injective) (hb.comp u.injective) (lam ∘ u) (fun i => hlam (u i))
    (by rw [Fintype.card_fin]; exact min_le_right _ _)
  rw [Fintype.card_fin] at heq
  haveI : FiniteDimensional k (twistedPairs E₁ E₂ ((fun i => placeOfPoint k (a i)) ∘ u)
      ((fun i => placeOfPoint k (b i)) ∘ u) ((fun i => twistFn E₁ (a i)) ∘ u) ((fun i => twistFn E₂ (b i)) ∘ u)
      (lam ∘ u)) :=
    finiteDimensional_twistedPairs E₁ E₂ (a ∘ u) (b ∘ u) (lam ∘ u)
  have hmono := Submodule.finrank_mono hle
  change Module.finrank k _ ≤ Module.finrank k
    (twistedPairs E₁ E₂ (fun i => placeOfPoint k ((a ∘ u) i)) (fun i => placeOfPoint k ((b ∘ u) i))
      (fun i => twistFn E₁ ((a ∘ u) i)) (fun i => twistFn E₂ ((b ∘ u) i)) (lam ∘ u)) at hmono
  omega

end Nodes
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Place.ord_zpow Divisor Divisor.degree Place.ofHeightOneSpectrum Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap Place.HasValue"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg ord ord_mul ord_inv ord_zpow ofHeightOneSpectrum mk.injEq toValuationSubring mk comapSymmRingEquiv congrRingEquiv ord_congrRingEquiv congrResidueAlgEquiv deg_congrRingEquiv congrEquiv congrEquiv_apply residue_algebraMap HasValue hasValue_one hasValue_algebraMap"
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
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

section CongrTwisted

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

set_option maxHeartbeats 1600000 in

theorem twistedPairs_mapDomain_congrEquiv (E₁ E₂ : Divisor K F) {ι : Type*} (v₁ v₂ : ι → Place K F)
    (t₁ t₂ : ι → F) (lam : ι → K) :
    twistedPairs (Finsupp.mapDomain (Place.congrEquiv e he) E₁) (Finsupp.mapDomain (Place.congrEquiv e he) E₂)
        (fun i => Place.congrEquiv e he (v₁ i)) (fun i => Place.congrEquiv e he (v₂ i))
        (fun i => e (t₁ i)) (fun i => e (t₂ i)) lam
      = Submodule.map (((AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv.prodCongr
          (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv) : F × F →ₗ[K] F' × F')
          (twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam) := by
  ext ⟨g₁', g₂'⟩
  obtain ⟨g₁, rfl⟩ := e.surjective g₁'
  obtain ⟨g₂, rfl⟩ := e.surjective g₂'
  have hmem : (e g₁, e g₂) ∈ Submodule.map (((AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv.prodCongr
          (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv) : F × F →ₗ[K] F' × F')
          (twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam) ↔ (g₁, g₂) ∈ twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam := by
    constructor
    · rintro ⟨⟨f₁, f₂⟩, hf, hfe⟩
      have h1 : e f₁ = e g₁ := congrArg Prod.fst hfe
      have h2 : e f₂ = e g₂ := congrArg Prod.snd hfe
      obtain rfl := e.injective h1
      obtain rfl := e.injective h2
      exact hf
    · intro h
      exact ⟨(g₁, g₂), h, rfl⟩
  rw [hmem, mem_twistedPairs_iff, mem_twistedPairs_iff,
    Place.mem_riemannRochSpace_mapDomain_congrEquiv_iff, Place.mem_riemannRochSpace_mapDomain_congrEquiv_iff]
  simp only [Place.congrEquiv_apply, ← map_mul, Place.hasValue_congrRingEquiv_iff]

theorem finrank_twistedPairs_mapDomain_congrEquiv (E₁ E₂ : Divisor K F) {ι : Type*}
    (v₁ v₂ : ι → Place K F) (t₁ t₂ : ι → F) (lam : ι → K) :
    Module.finrank K (twistedPairs (Finsupp.mapDomain (Place.congrEquiv e he) E₁)
        (Finsupp.mapDomain (Place.congrEquiv e he) E₂)
        (fun i => Place.congrEquiv e he (v₁ i)) (fun i => Place.congrEquiv e he (v₂ i))
        (fun i => e (t₁ i)) (fun i => e (t₂ i)) lam)
      = Module.finrank K (twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam) := by
  rw [twistedPairs_mapDomain_congrEquiv]
  exact LinearEquiv.finrank_map_eq _ _

end CongrTwisted
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

section Model

variable {k F : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] [DecidableEq (RatFunc k)] [Field F] [Algebra k F]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1600000 in

theorem finrank_twistedPairs_add_min_le_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E₁ E₂ : Divisor k F)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (lam : ι → k) (hlam : ∀ i, lam i ≠ 0) :
    Module.finrank k (twistedPairs E₁ E₂
        (fun i => Place.congrEquiv e he (placeOfPoint k (a i)))
        (fun i => Place.congrEquiv e he (placeOfPoint k (b i)))
        (fun i => e ((RatFunc.X - RatFunc.C (a i)) ^ (E₁ (Place.congrEquiv e he (placeOfPoint k (a i))))))
        (fun i => e ((RatFunc.X - RatFunc.C (b i)) ^ (E₂ (Place.congrEquiv e he (placeOfPoint k (b i))))))
        lam)
      + min (Fintype.card ι) (max (E₁.degree + 1).toNat (E₂.degree + 1).toNat)
      ≤ (E₁.degree + 1).toNat + (E₂.degree + 1).toNat := by
  set E₁₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E₁ with hE₁₀
  set E₂₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E₂ with hE₂₀
  have h1 : E₁ = Finsupp.mapDomain (Place.congrEquiv e he) E₁₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E₁).symm
  have h2 : E₂ = Finsupp.mapDomain (Place.congrEquiv e he) E₂₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E₂).symm
  have hd1 : E₁₀.degree = E₁.degree := by rw [h1, Place.degree_mapDomain_congrEquiv]
  have hd2 : E₂₀.degree = E₂.degree := by rw [h2, Place.degree_mapDomain_congrEquiv]
  have ht1 : ∀ i, E₁ (Place.congrEquiv e he (placeOfPoint k (a i))) = E₁₀ (placeOfPoint k (a i)) :=
    fun i => (Place.mapDomain_symm_apply e he E₁ _).symm
  have ht2 : ∀ i, E₂ (Place.congrEquiv e he (placeOfPoint k (b i))) = E₂₀ (placeOfPoint k (b i)) :=
    fun i => (Place.mapDomain_symm_apply e he E₂ _).symm
  have key := finrank_twistedPairs_add_min_le (k := k) E₁₀ E₂₀ a b ha hb lam hlam
  have hfin := finrank_twistedPairs_mapDomain_congrEquiv e he E₁₀ E₂₀
    (fun i => placeOfPoint k (a i)) (fun i => placeOfPoint k (b i))
    (fun i => twistFn E₁₀ (a i)) (fun i => twistFn E₂₀ (b i)) lam
  rw [← hfin, ← h1, ← h2, hd1, hd2] at key
  have hsub : twistedPairs E₁ E₂
        (fun i => Place.congrEquiv e he (placeOfPoint k (a i)))
        (fun i => Place.congrEquiv e he (placeOfPoint k (b i)))
        (fun i => e ((RatFunc.X - RatFunc.C (a i)) ^ (E₁ (Place.congrEquiv e he (placeOfPoint k (a i))))))
        (fun i => e ((RatFunc.X - RatFunc.C (b i)) ^ (E₂ (Place.congrEquiv e he (placeOfPoint k (b i))))))
        lam
      = twistedPairs E₁ E₂
        (fun i => Place.congrEquiv e he (placeOfPoint k (a i)))
        (fun i => Place.congrEquiv e he (placeOfPoint k (b i)))
        (fun i => e (twistFn E₁₀ (a i))) (fun i => e (twistFn E₂₀ (b i))) lam := by
    ext p
    simp only [mem_twistedPairs_iff, twistFn, ht1, ht2]
  rw [hsub]
  exact key

end Model
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Place.coe_algebraMap Place.ord_inv Place.ord_zpow Divisor Divisor.degree Place.ofHeightOneSpectrum Place.ord_congrRingEquiv Place.congrEquiv Place.congrEquiv_apply Place.residue_algebraMap Place.HasValue"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal algebraMap_mem_ofHeightOneSpectrum residueOfHeightOneSpectrum residueOfHeightOneSpectrum_apply ker_residueOfHeightOneSpectrum placeOfPoint placeOfPoint_injective deg_placeOfPoint placeInfty ord_placeOfPoint_algebraMap ord_placeInfty eq_placeOfPoint_or_eq_placeInfty placeOfPoint_ne_placeInfty deg_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

open Polynomial
open scoped Polynomial

section Avoidance

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_mem_riemannRochSpace_forall_hasValue_twist (E : Divisor k (RatFunc k))
    (hE : Fintype.card ι ≤ (E.degree + 1).toNat) (a : ι → k) (ha : Function.Injective a) (c : ι → k) :
    ∃ p ∈ riemannRochSpace E, ∀ i, (placeOfPoint k (a i)).HasValue (twistFn E (a i) * p) (c i) := by
  obtain ⟨P, hP⟩ := wEvalAt_surjective ha (fun i => twistWeight_ne_zero E (a i)) hE c
  refine ⟨_, div_divisorFn_mem_riemannRochSpace E P.2, fun i => ?_⟩
  have hv := hasValue_twist' E (a i) (P : k[X])
  have hi : twistWeight E (a i) * (P : k[X]).eval (a i) = c i := by
    rw [← wEvalAt_apply a (fun i => twistWeight E (a i)) _ P i, hP]
  rw [hi] at hv
  exact hv

omit [DecidableEq k] [Fintype ι] [DecidableEq ι] in

theorem exists_mem_riemannRochSpace_ord_eq (E : Divisor k (RatFunc k)) (hE : 0 ≤ E.degree)
    (w : Place k (RatFunc k)) :
    ∃ p ∈ riemannRochSpace E, p ≠ 0 ∧ w.ord p = -E w := by
  have hsum := degree_eq_sum_divisorPoints (k := k) E
  rcases eq_placeOfPoint_or_eq_placeInfty k w with ⟨b, rfl⟩ | rfl
  · refine ⟨algebraMap k[X] (RatFunc k) 1 / divisorFn k E (divisorPoints k E),
      div_divisorFn_mem_riemannRochSpace E ?_, ?_, ?_⟩
    · rw [mem_degreeLT_iff_natDegree]
      right
      rw [natDegree_one]
      omega
    · exact div_ne_zero (algebraMap_ne_zero' one_ne_zero) (divisorFn_ne_zero _ _)
    · rw [ord_placeOfPoint_div_divisorFn subset_rfl one_ne_zero]
      have : rootMultiplicity b (1 : k[X]) = 0 := rootMultiplicity_eq_zero (by simp)
      rw [this]
      simp
  · refine ⟨algebraMap k[X] (RatFunc k) (X ^ E.degree.toNat) / divisorFn k E (divisorPoints k E),
      div_divisorFn_mem_riemannRochSpace E ?_, ?_, ?_⟩
    · rw [mem_degreeLT_iff_natDegree]
      right
      rw [natDegree_X_pow]
      omega
    · exact div_ne_zero (algebraMap_ne_zero' (pow_ne_zero _ X_ne_zero)) (divisorFn_ne_zero _ _)
    · rw [ord_placeInfty_div_divisorFn _ _ (pow_ne_zero _ X_ne_zero), natDegree_X_pow]
      omega

end Avoidance
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

section AvoidanceModel

variable {k F : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] [DecidableEq (RatFunc k)] [Field F] [Algebra k F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_mem_riemannRochSpace_forall_hasValue_twist_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) (hE : Fintype.card ι ≤ (E.degree + 1).toNat)
    (a : ι → k) (ha : Function.Injective a) (c : ι → k) :
    ∃ p ∈ riemannRochSpace E, ∀ i,
      (Place.congrEquiv e he (placeOfPoint k (a i))).HasValue
        (e ((RatFunc.X - RatFunc.C (a i)) ^ (E (Place.congrEquiv e he (placeOfPoint k (a i))))) * p) (c i) := by
  set E₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E with hE₀
  have h1 : E = Finsupp.mapDomain (Place.congrEquiv e he) E₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E).symm
  have hd : E₀.degree = E.degree := by rw [h1, Place.degree_mapDomain_congrEquiv]
  have ht : ∀ i, E (Place.congrEquiv e he (placeOfPoint k (a i))) = E₀ (placeOfPoint k (a i)) :=
    fun i => (Place.mapDomain_symm_apply e he E _).symm
  obtain ⟨p, hp, hv⟩ := exists_mem_riemannRochSpace_forall_hasValue_twist E₀ (by rwa [hd]) a ha c
  refine ⟨e p, ?_, fun i => ?_⟩
  · have := (Place.mem_riemannRochSpace_mapDomain_congrEquiv_iff e he E₀ p).mpr hp
    rwa [← h1] at this
  · rw [ht i, ← map_mul, Place.congrEquiv_apply, Place.hasValue_congrRingEquiv_iff]
    exact hv i

omit [DecidableEq k] [Fintype ι] [DecidableEq ι] in

theorem exists_mem_riemannRochSpace_ord_eq_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) (hE : 0 ≤ E.degree) (w : Place k F) :
    ∃ p ∈ riemannRochSpace E, p ≠ 0 ∧ w.ord p = -E w := by
  set E₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E with hE₀
  have h1 : E = Finsupp.mapDomain (Place.congrEquiv e he) E₀ :=
    (Place.mapDomain_congrEquiv_mapDomain_symm e he E).symm
  have hd : E₀.degree = E.degree := by rw [h1, Place.degree_mapDomain_congrEquiv]
  set v : Place k (RatFunc k) := (Place.congrEquiv e he).symm w with hv
  have hw : w = Place.congrEquiv e he v := ((Place.congrEquiv e he).apply_symm_apply w).symm
  have hEv : E w = E₀ v := by rw [hw]; exact (Place.mapDomain_symm_apply e he E v).symm
  obtain ⟨p, hp, hp0, hord⟩ := exists_mem_riemannRochSpace_ord_eq E₀ (by rwa [hd]) v
  refine ⟨e p, ?_, (map_ne_zero e).mpr hp0, ?_⟩
  · have := (Place.mem_riemannRochSpace_mapDomain_congrEquiv_iff e he E₀ p).mpr hp
    rwa [← h1] at this
  · rw [hEv, hw, Place.congrEquiv_apply, Place.ord_congrRingEquiv]
    exact hord

end AvoidanceModel
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve _root_.AlgebraicCurve.RationalFunctionField _root_.P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.AlgebraicCurve.RationalFunctionField in
theorem solution
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) (hE : 0 ≤ E.degree) (w : Place k F) :
    ∃ p ∈ riemannRochSpace E, p ∉ riemannRochSpace (E - Finsupp.single w 1) := by
  classical
  obtain ⟨p, hp, hp0, hord⟩ := exists_mem_riemannRochSpace_ord_eq_of_ringEquiv e he E hE w
  refine ⟨p, hp, fun h => ?_⟩
  rcases (mem_riemannRochSpace_iff.mp h) w with h0 | hle
  · exact hp0 h0
  · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same] at hle
    omega

end S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc (solution)
