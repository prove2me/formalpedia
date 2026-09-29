-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/67b0c6d5-1a24-5dfa-b750-464179480688

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ValuationSubring_natDegree_map_eq_card_roots_of_splits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open scoped Polynomial

namespace DeuringRatFuncReduction

section RationalPlace

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
  (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)

include hKA in
theorem valuation_algebraMap_eq_one {k : K} (hk : k ≠ 0) :
    A.valuation (algebraMap K E k) = 1 := by
  apply le_antisymm ((A.valuation_le_one_iff _).mpr (hKA k))
  have h1 : A.valuation (algebraMap K E k) * A.valuation (algebraMap K E k⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hk, map_one, map_one]
  have h2 : A.valuation (algebraMap K E k⁻¹) ≤ 1 := (A.valuation_le_one_iff _).mpr (hKA _)
  calc (1 : A.ValueGroup) = _ := h1.symm
    _ ≤ A.valuation (algebraMap K E k) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

include hKA in
theorem valuation_algebraMap_le_one (k : K) : A.valuation (algebraMap K E k) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (hKA k)

include hKA in

theorem const_unique {a : E} {k k' : K}
    (hk : A.valuation (a - algebraMap K E k) < 1) (hk' : A.valuation (a - algebraMap K E k') < 1) :
    k = k' := by
  by_contra hne
  have hsub : algebraMap K E k' - algebraMap K E k =
      (a - algebraMap K E k) - (a - algebraMap K E k') := by ring
  have h1 : A.valuation (algebraMap K E k' - algebraMap K E k) < 1 := by
    rw [hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hk hk')
  have h2 : A.valuation (algebraMap K E k' - algebraMap K E k) = 1 := by
    rw [← map_sub]
    exact valuation_algebraMap_eq_one A hKA (sub_ne_zero.mpr (Ne.symm hne))
  exact (lt_irrefl (1 : A.ValueGroup)) (h2 ▸ h1)

noncomputable def sigmaFun (a : A) : K := (hArat a a.2).choose

theorem sigmaFun_spec (a : A) :
    A.valuation ((a : E) - algebraMap K E (sigmaFun A hArat a)) < 1 :=
  (hArat a a.2).choose_spec

include hKA in
theorem sigmaFun_eq_iff (a : A) (k : K) :
    sigmaFun A hArat a = k ↔ A.valuation ((a : E) - algebraMap K E k) < 1 :=
  ⟨fun h => h ▸ sigmaFun_spec A hArat a, fun h => const_unique A hKA (sigmaFun_spec A hArat a) h⟩

noncomputable def sigma : A →+* K where
  toFun := sigmaFun A hArat
  map_one' := by
    rw [sigmaFun_eq_iff A hKA hArat]
    simp
  map_mul' a b := by
    rw [sigmaFun_eq_iff A hKA hArat]
    have ha := sigmaFun_spec A hArat a
    have hb := sigmaFun_spec A hArat b
    set k := sigmaFun A hArat a
    set k' := sigmaFun A hArat b
    have hid : ((a * b : A) : E) - algebraMap K E (k * k') =
        (a : E) * ((b : E) - algebraMap K E k') + algebraMap K E k' * ((a : E) - algebraMap K E k) := by
      simp only [MulMemClass.coe_mul, map_mul]; ring
    rw [hid]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact (mul_le_mul_left (A.valuation_le_one a) _).trans_lt (by rwa [one_mul])
    · rw [map_mul]
      exact (mul_le_mul_left (valuation_algebraMap_le_one A hKA k') _).trans_lt
        (by rwa [one_mul])
  map_zero' := by
    rw [sigmaFun_eq_iff A hKA hArat]
    simp
  map_add' a b := by
    rw [sigmaFun_eq_iff A hKA hArat]
    have ha := sigmaFun_spec A hArat a
    have hb := sigmaFun_spec A hArat b
    set k := sigmaFun A hArat a
    set k' := sigmaFun A hArat b
    have hid : ((a + b : A) : E) - algebraMap K E (k + k') =
        ((a : E) - algebraMap K E k) + ((b : E) - algebraMap K E k') := by
      simp only [AddMemClass.coe_add, map_add]; ring
    rw [hid]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)

theorem sigma_spec (a : A) :
    A.valuation ((a : E) - algebraMap K E (sigma A hKA hArat a)) < 1 :=
  sigmaFun_spec A hArat a

theorem sigma_eq_iff (a : A) (k : K) :
    sigma A hKA hArat a = k ↔ A.valuation ((a : E) - algebraMap K E k) < 1 :=
  sigmaFun_eq_iff A hKA hArat a k

theorem ker_sigma : RingHom.ker (sigma A hKA hArat) = IsLocalRing.maximalIdeal A := by
  ext a
  rw [RingHom.mem_ker, sigma_eq_iff, map_zero, sub_zero]
  exact (A.valuation_lt_one_iff a).symm

end RationalPlace

theorem isUnit_iff_inv_mem {L : Type*} [Field L] (O : ValuationSubring L) (z : O) (hz : (z : L) ≠ 0) :
    IsUnit z ↔ (z : L)⁻¹ ∈ O := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 := congrArg (fun w : O => (w : L)) u.mul_inv
    simp only [Subring.coe_one, hu] at h1
    push_cast at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨z, ⟨(z : L)⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hz), Subtype.ext (inv_mul_cancel₀ hz)⟩, rfl⟩

theorem map_eq_zero_of_not_isUnit {L R : Type*} [Field L] [Semiring R] (O : ValuationSubring L)
    (ρ : O →+* R) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O) {z : O} (hz : ¬ IsUnit z) :
    ρ z = 0 := by
  rw [← RingHom.mem_ker, hker]
  exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hz)

theorem isUnit_of_map_ne_zero {L R : Type*} [Field L] [Semiring R] (O : ValuationSubring L)
    (ρ : O →+* R) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O) {z : O} (hz : ρ z ≠ 0) :
    IsUnit z := by
  by_contra h
  exact hz (map_eq_zero_of_not_isUnit O ρ hker h)

theorem coeff_C_inv_mul_mem {E : Type*} [Field E] (A : ValuationSubring E) (f : E[X]) (c₀ : E)
    (hmax : ∀ c ∈ f.coeffs, A.valuation c ≤ A.valuation c₀) (n : ℕ) :
    (Polynomial.C c₀⁻¹ * f).coeff n ∈ A := by
  rw [Polynomial.coeff_C_mul]
  by_cases hn : f.coeff n = 0
  · rw [hn, mul_zero]; exact A.zero_mem
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀, ← div_eq_inv_mul]
  exact div_le_one_of_le₀ (hmax _ (Polynomial.coeff_mem_coeffs hn)) zero_le'

theorem exists_normalization {E : Type*} [Field E] (A : ValuationSubring E) (f : E[X])
    (hf : f ≠ 0) :
    ∃ (c : E) (f₁ : A[X]), c ≠ 0 ∧ f = Polynomial.C c * f₁.map (algebraMap A E) ∧
      ∃ n, f₁.coeff n = 1 := by
  classical
  have hne : f.coeffs.Nonempty :=
    ⟨f.leadingCoeff, Polynomial.coeff_mem_coeffs (Polynomial.leadingCoeff_ne_zero.mpr hf)⟩
  obtain ⟨c₀, hc₀T, hmax⟩ := Finset.exists_max_image f.coeffs (fun c => A.valuation c) hne
  obtain ⟨n₀, hn₀, hc₀⟩ := Polynomial.mem_coeffs_iff.mp hc₀T
  have hc₀0 : c₀ ≠ 0 := hc₀ ▸ Polynomial.mem_support_iff.mp hn₀
  have hA : ∀ n, (Polynomial.C c₀⁻¹ * f).coeff n ∈ A := coeff_C_inv_mul_mem A f c₀ hmax
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : A[X], f₁.map (algebraMap A E) = Polynomial.C c₀⁻¹ * f := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hA n⟩, rfl⟩
  refine ⟨c₀, f₁, hc₀0, ?_, n₀, ?_⟩
  · rw [hf₁, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc₀0, Polynomial.C_1, one_mul]
  · apply Subtype.ext
    have := congrArg (fun g => Polynomial.coeff g n₀) hf₁
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
    rw [show ((f₁.coeff n₀ : A) : E) = algebraMap A E (f₁.coeff n₀) from rfl, this, ← hc₀,
      inv_mul_cancel₀ hc₀0]
    rfl

section OrdLemmas

variable (k : Type*) [Field k]

theorem ord_placeInfty_eq_neg_intDegree [DecidableEq (RatFunc k)] {f : RatFunc k} (hf : f ≠ 0) :
    (placeInfty k).ord f = -f.intDegree := by
  set d := f.intDegree with hd
  have hX0 : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  set u : RatFunc k := f * RatFunc.X ^ (-d) with hu_def
  have hu0 : u ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hX0)
  have hval : RatFunc.inftyValuation k u = 1 := by
    rw [hu_def, map_mul, RatFunc.inftyValuation.X_zpow, RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero (hx := hf), ← WithZero.exp_add, ← hd, add_neg_cancel,
      WithZero.exp_zero]
  have hmem : ∀ x : RatFunc k, RatFunc.inftyValuation k x = 1 →
      x ∈ (placeInfty k).toValuationSubring := by
    intro x hx
    rw [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff]
    exact le_of_eq hx
  have huinv : RatFunc.inftyValuation k u⁻¹ = 1 := by rw [map_inv₀, hval, inv_one]
  let U : (placeInfty k).toValuationSubringˣ :=
    ⟨⟨u, hmem u hval⟩, ⟨u⁻¹, hmem _ huinv⟩, Subtype.ext (mul_inv_cancel₀ hu0),
      Subtype.ext (inv_mul_cancel₀ hu0)⟩
  have hordu : (placeInfty k).ord u = 0 := (placeInfty k).ord_coe_unit U
  have hf' : f = u * RatFunc.X ^ d := by
    rw [hu_def, mul_assoc, ← zpow_add₀ hX0, neg_add_cancel, zpow_zero, mul_one]
  rw [hf', (placeInfty k).ord_mul hu0 (zpow_ne_zero _ hX0), hordu, (placeInfty k).ord_zpow,
    ord_placeInfty_X]
  ring

theorem ord_placeInfty_algebraMap [DecidableEq (RatFunc k)] {f : k[X]} (hf : f ≠ 0) :
    (placeInfty k).ord (algebraMap k[X] (RatFunc k) f) = -(f.natDegree : ℤ) := by
  rw [ord_placeInfty_eq_neg_intDegree k
    ((map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hf),
    RatFunc.intDegree_polynomial]

theorem ord_placeOfPoint_div (β : k) {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (placeOfPoint k β).ord (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) =
      (p.rootMultiplicity β : ℤ) - q.rootMultiplicity β := by
  have hp' : algebraMap k[X] (RatFunc k) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hp
  have hq' : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq
  rw [div_eq_mul_inv, (placeOfPoint k β).ord_mul hp' (inv_ne_zero hq'), (placeOfPoint k β).ord_inv,
    ord_placeOfPoint_algebraMap β hp, ord_placeOfPoint_algebraMap β hq]
  ring

end OrdLemmas

section Counting

variable {E : Type*} [Field E] (A : ValuationSubring E)

open Classical in

theorem card_roots_map_eq (f : A[X]) (hf : f ≠ 0) :
    Multiset.card (f.map (algebraMap A E)).roots =
      Multiset.card f.roots +
        Multiset.card ((f.map (algebraMap A E)).roots.filter (fun β => β ∉ A)) := by
  set R := (f.map (algebraMap A E)).roots with hR
  have hι : Function.Injective (algebraMap A E) := Subtype.val_injective
  have h1 : R.filter (fun β => β ∈ A) = f.roots.map (algebraMap A E) := by
    refine Multiset.ext.mpr fun x => ?_
    by_cases hx : x ∈ A
    · rw [Multiset.count_filter_of_pos hx]
      have : x = algebraMap A E ⟨x, hx⟩ := rfl
      rw [this, Multiset.count_map_eq_count' _ _ hι, Polynomial.count_roots,
        Polynomial.count_roots]
      exact (Polynomial.eq_rootMultiplicity_map hι _).symm
    · rw [Multiset.count_filter_of_neg hx, eq_comm, Multiset.count_eq_zero]
      intro hmem
      obtain ⟨a, -, ha⟩ := Multiset.mem_map.mp hmem
      exact hx (ha ▸ a.2)
  have _ := hf
  conv_lhs => rw [← Multiset.filter_add_not (fun β => β ∈ A) R]
  rw [Multiset.card_add, h1, Multiset.card_map]

open Classical in

theorem sum_count_eq_card_filter (R : Multiset E) (T : Finset E)
    (hT : ∀ β ∈ R, β ∉ A → β ∈ T) (hTA : ∀ β ∈ T, β ∉ A) :
    ∑ β ∈ T, R.count β = Multiset.card (R.filter (fun β => β ∉ A)) := by
  set R' := R.filter (fun β => β ∉ A) with hR'
  have h1 : ∀ β ∈ T, R.count β = R'.count β :=
    fun β hβ => (Multiset.count_filter_of_pos (p := fun β => β ∉ A) (hTA β hβ)).symm
  rw [Finset.sum_congr rfl h1, ← Multiset.toFinset_sum_count_eq R']
  symm
  apply Finset.sum_subset
  · intro β hβ
    rw [Multiset.mem_toFinset, hR', Multiset.mem_filter] at hβ
    exact hT β hβ.1 hβ.2
  · intro β _ hβ
    rw [Multiset.mem_toFinset] at hβ
    exact Multiset.count_eq_zero.mpr hβ

end Counting

section Reduction

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra (RatFunc K) L]
  (A : ValuationSubring E)
  (hKA : ∀ k : K, algebraMap K E k ∈ A)
  (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
  (O : ValuationSubring (RatFunc E)) (ρ : O →+* L)
  (hO : ∀ c : E, algebraMap E (RatFunc E) c ∈ O ↔ c ∈ A)
  (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
  (hρ : ∀ p : K[X], ∃ h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O,
    ρ ⟨_, h⟩ = algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p))

include hρ in
theorem polyK_mem (p : K[X]) : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O := by
  obtain ⟨h, -⟩ := hρ p
  exact h

include hρ in
theorem rho_polyK (p : K[X]) (h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O) :
    ρ ⟨_, h⟩ = algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) := by
  obtain ⟨h', hh⟩ := hρ p
  exact hh

include hρ in
theorem X_mem : (RatFunc.X : RatFunc E) ∈ O := by
  have := polyK_mem O ρ hρ Polynomial.X
  rwa [Polynomial.map_X, RatFunc.algebraMap_X] at this

include hρ in
theorem rho_X (h : (RatFunc.X : RatFunc E) ∈ O) :
    ρ ⟨RatFunc.X, h⟩ = algebraMap (RatFunc K) L RatFunc.X := by
  have e : (⟨RatFunc.X, h⟩ : O) =
      ⟨algebraMap E[X] (RatFunc E) ((Polynomial.X : K[X]).map (algebraMap K E)),
        polyK_mem O ρ hρ _⟩ :=
    Subtype.ext (show (RatFunc.X : RatFunc E) =
        algebraMap E[X] (RatFunc E) ((Polynomial.X : K[X]).map (algebraMap K E)) by
      rw [Polynomial.map_X, RatFunc.algebraMap_X])
  rw [e, rho_polyK O ρ hρ, RatFunc.algebraMap_X]

noncomputable def constEmb : A →+* O where
  toFun a := ⟨algebraMap E (RatFunc E) a, (hO a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constEmb (a : A) :
    ((constEmb A O hO a : O) : RatFunc E) = algebraMap E (RatFunc E) a := rfl

include hKA hker hρ in

theorem rho_constEmb (a : A) :
    ρ (constEmb A O hO a) =
      algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (sigma A hKA hArat a)) := by
  set k := sigma A hKA hArat a with hk_def
  have hk : A.valuation ((a : E) - algebraMap K E k) < 1 := sigma_spec A hKA hArat a
  have hmA : (a : E) - algebraMap K E k ∈ A := A.sub_mem a.2 (hKA k)

  have hconst : ρ (constEmb A O hO ⟨algebraMap K E k, hKA k⟩) =
      algebraMap (RatFunc K) L (algebraMap K (RatFunc K) k) := by
    have e1 : constEmb A O hO ⟨algebraMap K E k, hKA k⟩ =
        ⟨algebraMap E[X] (RatFunc E) ((Polynomial.C k).map (algebraMap K E)),
          polyK_mem O ρ hρ _⟩ :=
      Subtype.ext (show algebraMap E (RatFunc E) (algebraMap K E k) =
          algebraMap E[X] (RatFunc E) ((Polynomial.C k).map (algebraMap K E)) by
        rw [Polynomial.map_C, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C])
    rw [e1, rho_polyK O ρ hρ, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]

  have hinf : ρ (constEmb A O hO ⟨_, hmA⟩) = 0 := by
    by_cases hm0 : (a : E) - algebraMap K E k = 0
    · have : constEmb A O hO ⟨_, hmA⟩ = 0 := Subtype.ext (by simp [hm0])
      rw [this, map_zero]
    apply map_eq_zero_of_not_isUnit O ρ hker
    intro hu
    have hinv := (isUnit_iff_inv_mem O _ (by
      show algebraMap E (RatFunc E) ((a : E) - algebraMap K E k) ≠ 0
      exact (map_ne_zero _).mpr hm0)).mp hu
    simp only [coe_constEmb, ← map_inv₀] at hinv
    rw [hO] at hinv
    have hunitA : IsUnit (⟨_, hmA⟩ : A) :=
      (isUnit_iff_inv_mem A ⟨_, hmA⟩ hm0).mpr hinv
    have hmax : (⟨_, hmA⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
      (ValuationSubring.valuation_lt_one_iff A _).mpr hk
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmax) hunitA
  have hsplit : a = ⟨algebraMap K E k, hKA k⟩ + ⟨_, hmA⟩ := Subtype.ext (by simp)
  rw [hsplit, map_add, map_add, hconst, hinf, add_zero]

noncomputable def polyEmb : A[X] →+* O :=
  Polynomial.eval₂RingHom (constEmb A O hO) ⟨_, X_mem O ρ hρ⟩

theorem coe_polyEmb (p₀ : A[X]) :
    ((polyEmb A O ρ hO hρ p₀ : O) : RatFunc E) =
      algebraMap E[X] (RatFunc E) (p₀.map (algebraMap A E)) := by
  have hLR : O.subtype.comp (polyEmb A O ρ hO hρ) =
      (algebraMap E[X] (RatFunc E)).comp (Polynomial.mapRingHom (algebraMap A E)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, RatFunc.algebraMap_C]
      rw [← RatFunc.algebraMap_eq_C]
      rfl
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X]
      rfl
  have := DFunLike.congr_fun hLR p₀
  simpa using this

include hKA hArat hker in
theorem rho_polyEmb (p₀ : A[X]) :
    ρ (polyEmb A O ρ hO hρ p₀) =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) (p₀.map (sigma A hKA hArat))) := by
  have hLR : ρ.comp (polyEmb A O ρ hO hρ) =
      ((algebraMap (RatFunc K) L).comp (algebraMap K[X] (RatFunc K))).comp
        (Polynomial.mapRingHom (sigma A hKA hArat)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, RatFunc.algebraMap_C]
      rw [rho_constEmb A hKA hArat O ρ hO hker hρ, ← RatFunc.algebraMap_eq_C]
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X]
      exact rho_X O ρ hρ _
  have := DFunLike.congr_fun hLR p₀
  simpa using this

theorem map_sigma_ne_zero (f₁ : A[X]) (h1 : ∃ n, f₁.coeff n = 1) :
    f₁.map (sigma A hKA hArat) ≠ 0 := by
  obtain ⟨n, hn⟩ := h1
  intro h0
  have := congrArg (fun f => Polynomial.coeff f n) h0
  simp only [Polynomial.coeff_map, hn, map_one, Polynomial.coeff_zero] at this
  exact one_ne_zero this

include hKA hArat hker in

theorem isUnit_polyEmb (f₁ : A[X]) (h1 : ∃ n, f₁.coeff n = 1) :
    IsUnit (polyEmb A O ρ hO hρ f₁) := by
  apply isUnit_of_map_ne_zero O ρ hker
  rw [rho_polyEmb A hKA hArat O ρ hO hker hρ]
  exact fun h => map_sigma_ne_zero A hKA hArat f₁ h1 (IsFractionRing.injective K[X] (RatFunc K)
    ((algebraMap (RatFunc K) L).injective (by rw [h, map_zero, map_zero])))

include hKA hArat hO hker hρ in
theorem main [IsAlgClosed E] [DecidableEq (RatFunc K)] [DecidableEq (RatFunc E)]
    (G : O) (N : RatFunc K) (hN : N ≠ 0) (hGN : ρ G = algebraMap (RatFunc K) L N)
    (S : Finset E) (hSA : ∀ β ∈ S, β ∉ A)
    (hS : ∀ β : E, β ∉ A → (placeOfPoint E β).ord (G : RatFunc E) ≠ 0 → β ∈ S) :
    (placeInfty K).ord N =
      (placeInfty E).ord (G : RatFunc E) + ∑ β ∈ S, (placeOfPoint E β).ord (G : RatFunc E) := by
  classical

  have hσ : RingHom.ker (sigma A hKA hArat) = IsLocalRing.maximalIdeal A := ker_sigma A hKA hArat
  have hι : Function.Injective (algebraMap A E) := Subtype.val_injective
  have hιE : Function.Injective (algebraMap E[X] (RatFunc E)) := IsFractionRing.injective _ _
  have hιK : Function.Injective (algebraMap K[X] (RatFunc K)) := IsFractionRing.injective _ _
  set g : RatFunc E := (G : RatFunc E) with hg_def
  have hG0 : g ≠ 0 := by
    intro h
    apply hN
    have hG : G = 0 := Subtype.ext h
    rw [hG, map_zero, eq_comm, map_eq_zero_iff _ (algebraMap (RatFunc K) L).injective] at hGN
    exact hGN

  have hnum0 : g.num ≠ 0 := RatFunc.num_ne_zero hG0
  have hden0 : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  obtain ⟨c₁, p, hc₁, hp, hp1⟩ := exists_normalization A g.num hnum0
  obtain ⟨c₂, q, hc₂, hq, hq1⟩ := exists_normalization A g.denom hden0
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, mul_zero] at hp
    exact hnum0 hp
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, mul_zero] at hq
    exact hden0 hq
  have hpE0 : p.map (algebraMap A E) ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hp0
  have hqE0 : q.map (algebraMap A E) ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hq0
  set P : O := polyEmb A O ρ hO hρ p with hP_def
  set Q : O := polyEmb A O ρ hO hρ q with hQ_def
  have hPu : IsUnit P := isUnit_polyEmb A hKA hArat O ρ hO hker hρ p hp1
  have hQu : IsUnit Q := isUnit_polyEmb A hKA hArat O ρ hO hker hρ q hq1
  have hPc : (P : RatFunc E) = algebraMap E[X] (RatFunc E) (p.map (algebraMap A E)) :=
    coe_polyEmb A O ρ hO hρ p
  have hQc : (Q : RatFunc E) = algebraMap E[X] (RatFunc E) (q.map (algebraMap A E)) :=
    coe_polyEmb A O ρ hO hρ q
  have hPv0 : (P : RatFunc E) ≠ 0 := by rw [hPc]; exact (map_ne_zero_iff _ hιE).mpr hpE0
  have hQv0 : (Q : RatFunc E) ≠ 0 := by rw [hQc]; exact (map_ne_zero_iff _ hιE).mpr hqE0

  have hgd : g * algebraMap E[X] (RatFunc E) g.denom = algebraMap E[X] (RatFunc E) g.num :=
    ((div_eq_iff ((map_ne_zero_iff _ hιE).mpr hden0)).mp (RatFunc.num_div_denom g)).symm
  have hE1 : g * (algebraMap E (RatFunc E) c₂ * (Q : RatFunc E)) =
      algebraMap E (RatFunc E) c₁ * (P : RatFunc E) := by
    rw [hPc, hQc, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C,
      ← map_mul, ← map_mul, ← hp, ← hq, hgd]

  set c : E := c₁ / c₂ with hc_def
  have hc0 : c ≠ 0 := div_ne_zero hc₁ hc₂
  have hcE2 : algebraMap E (RatFunc E) c₂ ≠ 0 := (map_ne_zero _).mpr hc₂
  have hcv : algebraMap E (RatFunc E) c = g * (Q : RatFunc E) * (P : RatFunc E)⁻¹ := by
    rw [hc_def, map_div₀, eq_mul_inv_iff_mul_eq₀ hPv0, div_mul_eq_mul_div,
      div_eq_iff hcE2, ← hE1]
    ring
  have hcO : algebraMap E (RatFunc E) c ∈ O := by
    rw [hcv]
    exact O.mul_mem _ _ (O.mul_mem _ _ G.2 Q.2) ((isUnit_iff_inv_mem O P hPv0).mp hPu)
  have hcA : c ∈ A := (hO c).mp hcO

  have hOid : constEmb A O hO ⟨c, hcA⟩ * P = G * Q := by
    apply Subtype.ext
    show algebraMap E (RatFunc E) c * (P : RatFunc E) = g * (Q : RatFunc E)
    rw [hcv, mul_assoc, inv_mul_cancel₀ hPv0, mul_one]
  have hred := congrArg ρ hOid
  rw [map_mul, map_mul, rho_constEmb A hKA hArat O ρ hO hker hρ, hGN, hP_def, hQ_def,
    rho_polyEmb A hKA hArat O ρ hO hker hρ, rho_polyEmb A hKA hArat O ρ hO hker hρ,
    ← map_mul, ← map_mul] at hred
  have hE2 : algebraMap K (RatFunc K) (sigma A hKA hArat ⟨c, hcA⟩) *
      algebraMap K[X] (RatFunc K) (p.map (sigma A hKA hArat)) =
        N * algebraMap K[X] (RatFunc K) (q.map (sigma A hKA hArat)) :=
    (algebraMap (RatFunc K) L).injective hred
  set pbar := p.map (sigma A hKA hArat) with hpbar
  set qbar := q.map (sigma A hKA hArat) with hqbar
  have hpbar0 : pbar ≠ 0 := map_sigma_ne_zero A hKA hArat p hp1
  have hqbar0 : qbar ≠ 0 := map_sigma_ne_zero A hKA hArat q hq1
  have hpbarv0 : algebraMap K[X] (RatFunc K) pbar ≠ 0 := (map_ne_zero_iff _ hιK).mpr hpbar0
  have hqbarv0 : algebraMap K[X] (RatFunc K) qbar ≠ 0 := (map_ne_zero_iff _ hιK).mpr hqbar0
  have hσc0 : sigma A hKA hArat ⟨c, hcA⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hE2
    exact (mul_ne_zero hN hqbarv0) hE2.symm
  have hσcv0 : algebraMap K (RatFunc K) (sigma A hKA hArat ⟨c, hcA⟩) ≠ 0 :=
    (map_ne_zero _).mpr hσc0

  have hordN : (placeInfty K).ord N = (qbar.natDegree : ℤ) - pbar.natDegree := by
    have h1 := congrArg (placeInfty K).ord hE2
    rw [(placeInfty K).ord_mul hσcv0 hpbarv0, (placeInfty K).ord_mul hN hqbarv0,
      ord_placeInfty_algebraMap K hpbar0, ord_placeInfty_algebraMap K hqbar0,
      RatFunc.algebraMap_eq_C, ord_placeInfty_eq_neg_intDegree K
        (show (RatFunc.C (sigma A hKA hArat ⟨c, hcA⟩) : RatFunc K) ≠ 0 from
          RatFunc.algebraMap_eq_C (K := K) ▸ hσcv0),
      RatFunc.intDegree_C] at h1
    linarith

  have hsplitp : Multiset.card (p.map (algebraMap A E)).roots = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map_eq_of_injective hι]
  have hsplitq : Multiset.card (q.map (algebraMap A E)).roots = q.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map_eq_of_injective hι]
  have hdegp : pbar.natDegree = Multiset.card p.roots :=
    ValuationSubring.natDegree_map_eq_card_roots_of_splits A _ hσ p hpbar0 hsplitp
  have hdegq : qbar.natDegree = Multiset.card q.roots :=
    ValuationSubring.natDegree_map_eq_card_roots_of_splits A _ hσ q hqbar0 hsplitq
  set Rp := (p.map (algebraMap A E)).roots with hRp
  set Rq := (q.map (algebraMap A E)).roots with hRq
  have hcardp := card_roots_map_eq A p hp0
  have hcardq := card_roots_map_eq A q hq0

  have hordg : (placeInfty E).ord g = (q.natDegree : ℤ) - p.natDegree := by
    rw [ord_placeInfty_eq_neg_intDegree E hG0, RatFunc.intDegree, hp, hq,
      Polynomial.natDegree_C_mul hc₁, Polynomial.natDegree_C_mul hc₂,
      Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι]
    ring

  have hordβ : ∀ β : E, (placeOfPoint E β).ord g = (Rp.count β : ℤ) - Rq.count β := by
    intro β
    rw [← RatFunc.num_div_denom g, ord_placeOfPoint_div E β hnum0 hden0, hp, hq,
      ← Polynomial.count_roots, ← Polynomial.count_roots, Polynomial.roots_C_mul _ hc₁,
      Polynomial.roots_C_mul _ hc₂]

  set T : Finset E := S ∪ (Rp.filter (fun β => β ∉ A)).toFinset ∪
    (Rq.filter (fun β => β ∉ A)).toFinset with hT
  have hTA : ∀ β ∈ T, β ∉ A := by
    intro β hβ
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_filter] at hβ
    rcases hβ with (hβ | hβ) | hβ
    · exact hSA β hβ
    · exact hβ.2
    · exact hβ.2
  have hST : S ⊆ T := fun β hβ => by
    simp only [hT, Finset.mem_union]
    exact Or.inl (Or.inl hβ)
  have hsumST : ∑ β ∈ S, (placeOfPoint E β).ord g = ∑ β ∈ T, (placeOfPoint E β).ord g := by
    apply Finset.sum_subset hST
    intro β hβT hβS
    by_contra h
    exact hβS (hS β (hTA β hβT) h)
  have hTp : ∀ β ∈ Rp, β ∉ A → β ∈ T := by
    intro β hβ hβA
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_filter]
    exact Or.inl (Or.inr ⟨hβ, hβA⟩)
  have hTq : ∀ β ∈ Rq, β ∉ A → β ∈ T := by
    intro β hβ hβA
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_filter]
    exact Or.inr ⟨hβ, hβA⟩
  have hsump : ∑ β ∈ T, Rp.count β = Multiset.card (Rp.filter (fun β => β ∉ A)) :=
    sum_count_eq_card_filter A Rp T hTp hTA
  have hsumq : ∑ β ∈ T, Rq.count β = Multiset.card (Rq.filter (fun β => β ∉ A)) :=
    sum_count_eq_card_filter A Rq T hTq hTA
  have hsumT : ∑ β ∈ T, (placeOfPoint E β).ord g =
      (Multiset.card (Rp.filter (fun β => β ∉ A)) : ℤ) -
        Multiset.card (Rq.filter (fun β => β ∉ A)) := by
    rw [← hsump, ← hsumq, Finset.sum_congr rfl (fun β _ => hordβ β), Finset.sum_sub_distrib]
    push_cast
    ring

  rw [hordN, hordg, hsumST, hsumT, hdegp, hdegq]
  have e1 : (p.natDegree : ℤ) = Multiset.card p.roots + Multiset.card (Rp.filter (fun β => β ∉ A)) := by
    rw [← hsplitp, hRp]
    exact_mod_cast hcardp
  have e2 : (q.natDegree : ℤ) = Multiset.card q.roots + Multiset.card (Rq.filter (fun β => β ∉ A)) := by
    rw [← hsplitq, hRq]
    exact_mod_cast hcardq
  linarith

end Reduction

end DeuringRatFuncReduction
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction.DeuringRatFuncReduction"

open DeuringRatFuncReduction in
theorem solution
    (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [IsAlgClosed E]
    [DecidableEq (RatFunc K)] [DecidableEq (RatFunc E)] [Algebra (RatFunc K) L]
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring (RatFunc E)) (ρ : O →+* L)
    (hO : ∀ c : E, algebraMap E (RatFunc E) c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ p : K[X],
      ∃ h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O,
        ρ ⟨_, h⟩ = algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p))
    (G : O) (N : RatFunc K) (hN : N ≠ 0) (hGN : ρ G = algebraMap (RatFunc K) L N)
    (S : Finset E) (hSA : ∀ β ∈ S, β ∉ A)
    (hS : ∀ β : E, β ∉ A → (placeOfPoint E β).ord (G : RatFunc E) ≠ 0 → β ∈ S) :
    (placeInfty K).ord N =
      (placeInfty E).ord (G : RatFunc E) + ∑ β ∈ S, (placeOfPoint E β).ord (G : RatFunc E) :=
  main A hKA hArat O ρ hO hker hρ G N hN hGN S hSA hS

end S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction (solution)
