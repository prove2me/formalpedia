-- Prove2me | solution 1 for AlgebraicCurve.exists_place_notMem_ord_neg_and_forall_ord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5eab68bf-4e9b-5420-9e72-df1658bc2e82

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Theorems.Thm_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded
import Theorems.Thm_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_indexOfSpecialtyFinite_of_ratFunc_tower
import Theorems.Thm_AlgebraicCurve_riemannGenusBounded_of_indexFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_place_notMem_ord_neg_and_forall_ord_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option autoImplicit false

namespace PlaceOrd

open AlgebraicCurve

variable {K : Type*} [Field K]
variable {F : Type*} [Field F] [Algebra K F]

private theorem ord_nonneg_of_mem' (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem mem_of_ord_nonneg' (v : Place K F) {f : F} (hf : f ≠ 0)
    (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem ne_zero_of_ord_pos (v : Place K F) {f : F} (h : 1 ≤ v.ord f) : f ≠ 0 := by
  intro hf0
  rw [hf0, v.ord_zero] at h
  omega

private theorem ord_inv' (v : Place K F) {f : F} (hf : f ≠ 0) : v.ord f⁻¹ = -v.ord f := by
  have h1 : v.ord (f * f⁻¹) = v.ord f + v.ord f⁻¹ := v.ord_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, v.ord_one] at h1
  omega

private theorem ord_neg' (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | h0
  · simp
  · have h2 : v.ord ((-1 : F) * (-1 : F)) = v.ord (-1 : F) + v.ord (-1 : F) :=
      v.ord_mul (by norm_num) (by norm_num)
    have h2' : v.ord (1 : F) = v.ord (-1 : F) + v.ord (-1 : F) := by rw [← h2]; norm_num
    rw [v.ord_one] at h2'
    have h1 : v.ord ((-1 : F) * f) = v.ord (-1 : F) + v.ord f := v.ord_mul (by norm_num) h0
    rw [neg_eq_neg_one_mul]
    omega

end PlaceOrd

namespace OrdCalculus

open AlgebraicCurve Polynomial

section Minis
variable {K : Type*} [Field K]
variable {L : Type*} [Field L] [Algebra K L]

private theorem min_core (v : Place K L) {x y : L} {m : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hmx : m ≤ v.ord x) (hmy : m ≤ v.ord y) : m ≤ v.ord (x + y) := by
  have core : ∀ a b : L, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → m ≤ v.ord a → v.ord a ≤ v.ord b →
      m ≤ v.ord (a + b) := by
    intro a b ha hb hab hma hord
    have hq : b / a ∈ v.toValuationSubring := by
      apply PlaceOrd.mem_of_ord_nonneg' v (div_ne_zero hb ha)
      rw [div_eq_mul_inv, v.ord_mul hb (inv_ne_zero ha), PlaceOrd.ord_inv' v ha]
      omega
    have hsum : (1 : L) + b / a ∈ v.toValuationSubring := add_mem (one_mem _) hq
    have has : a + b = a * (1 + b / a) := by field_simp
    rcases eq_or_ne ((1 : L) + b / a) 0 with hz | hz
    · exact absurd (by rw [has, hz, mul_zero]) hab
    have h0s := PlaceOrd.ord_nonneg_of_mem' v hsum
    rw [has, v.ord_mul ha hz]
    omega
  rcases le_total (v.ord x) (v.ord y) with hle | hle
  · exact core x y hx hy hxy hmx hle
  · have := core y x hy hx (by rwa [add_comm]) hmy hle
    rwa [add_comm]

private theorem ord_add_eq_of_lt (v : Place K L) {a b : L} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (h : v.ord b < v.ord a) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord b := by
  have hne : a + b ≠ 0 := by
    intro h0
    have hab : a = -b := eq_neg_of_add_eq_zero_left h0
    rw [hab, PlaceOrd.ord_neg' v b] at h
    omega
  refine ⟨hne, ?_⟩
  have hge : v.ord b ≤ v.ord (a + b) := min_core v ha0 hb0 hne (by omega) (by omega)
  have hkey : min (v.ord (a + b)) (v.ord a) ≤ v.ord b := by
    have hrepr : (a + b) + (-a) = b := by ring
    have := min_core v hne (neg_ne_zero.mpr ha0)
      (by rw [hrepr]; exact hb0) (min_le_left _ _)
      (by rw [PlaceOrd.ord_neg' v a]; exact min_le_right _ _)
    rwa [hrepr] at this
  rcases min_cases (v.ord (a + b)) (v.ord a) with ⟨hmeq, _⟩ | ⟨hmeq, _⟩ <;>
    (rw [hmeq] at hkey; omega)

private theorem ord_algebraMap_ne (v : Place K L) {c : K} (hc : c ≠ 0) :
    v.ord (algebraMap K L c) = 0 := by
  have hA : algebraMap K L c ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hc
  have hB : algebraMap K L c⁻¹ ≠ 0 := (map_ne_zero (algebraMap K L)).mpr (inv_ne_zero hc)
  have h1 := PlaceOrd.ord_nonneg_of_mem' v (v.algebraMap_mem' c)
  have h2 := PlaceOrd.ord_nonneg_of_mem' v (v.algebraMap_mem' c⁻¹)
  have h3 : v.ord (algebraMap K L c) + v.ord (algebraMap K L c⁻¹) = 0 := by
    rw [← v.ord_mul hA hB, ← map_mul, mul_inv_cancel₀ hc, map_one, v.ord_one]
  omega

end Minis

end OrdCalculus

namespace PoleZeroPrescription

open AlgebraicCurve
open scoped nonZeroDivisors

variable {K : Type*} [Field K]
variable {F : Type*} [Field F] [Algebra K F]

private theorem aeval_comap_nzd (t : F) (ht : Transcendental K t) :
    (Polynomial K)⁰ ≤ F⁰.comap (Polynomial.aeval t : Polynomial K →ₐ[K] F).toRingHom := by
  intro q hq
  rw [Submonoid.mem_comap]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq ⊢
  exact fun h0 => ht ⟨q, hq, h0⟩

private noncomputable def ratFuncEval (t : F) (ht : Transcendental K t) : RatFunc K →ₐ[K] F :=
  RatFunc.liftAlgHom (Polynomial.aeval t) (aeval_comap_nzd t ht)

private theorem ratFuncEval_apply_div (t : F) (ht : Transcendental K t) (p q : Polynomial K) :
    ratFuncEval t ht (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q)
      = Polynomial.aeval t p / Polynomial.aeval t q :=
  RatFunc.liftAlgHom_apply_div _ _ p q

private theorem ratFuncEval_X (t : F) (ht : Transcendental K t) : ratFuncEval t ht RatFunc.X = t := by
  have h1 : (RatFunc.X : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) Polynomial.X
      / algebraMap (Polynomial K) (RatFunc K) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_X]
  rw [h1, ratFuncEval_apply_div]
  simp

private theorem fieldRange_ratFuncEval (t : F) (ht : Transcendental K t) :
    (ratFuncEval t ht).fieldRange = IntermediateField.adjoin K {t} := by
  apply le_antisymm
  · rintro - ⟨r, rfl⟩
    induction r using RatFunc.induction_on with
    | f p q hq =>
      show ratFuncEval t ht (algebraMap (Polynomial K) (RatFunc K) p
          / algebraMap (Polynomial K) (RatFunc K) q) ∈ IntermediateField.adjoin K {t}
      rw [ratFuncEval_apply_div]
      exact div_mem
        ((IntermediateField.algebra_adjoin_le_adjoin K _)
          (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩))
        ((IntermediateField.algebra_adjoin_le_adjoin K _)
          (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨q, rfl⟩))
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨RatFunc.X, ratFuncEval_X t ht⟩

private noncomputable def ratFuncEquivAdjoin (t : F) (ht : Transcendental K t) :
    RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({t} : Set F) :=
  (AlgEquiv.ofInjectiveField (ratFuncEval t ht)).trans (IntermediateField.equivOfEq (fieldRange_ratFuncEval t ht))

private theorem coe_ratFuncEquivAdjoin (t : F) (ht : Transcendental K t) (r : RatFunc K) :
    ((ratFuncEquivAdjoin t ht r : IntermediateField.adjoin K ({t} : Set F)) : F) = ratFuncEval t ht r := rfl

private theorem exists_genus_reached [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    [Nonempty (Place K F)] : ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  classical
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) := finiteDimensional_lSpace_zero K F
  obtain ⟨t, ht, hfin, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := hfin
  haveI := hsep
  letI : Algebra (RatFunc K) F := (ratFuncEval t ht).toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun k => ((ratFuncEval t ht).commutes k).symm
  have key : ∀ s : IntermediateField.adjoin K ({t} : Set F),
      ratFuncEval t ht ((ratFuncEquivAdjoin t ht).symm s) = (s : F) := by
    intro s
    rw [← coe_ratFuncEquivAdjoin, AlgEquiv.apply_symm_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv (ratFuncEquivAdjoin t ht).symm.toRingEquiv (RingEquiv.refl F)
      (by ext s; exact key s)
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv (ratFuncEquivAdjoin t ht).symm.toRingEquiv (RingEquiv.refl F)
      (by ext s; exact key s)
  exact exists_riemannGenusReachedAt_of_bounded
    (riemannGenusBounded_of_indexFinite (RationalFunctionField.indexOfSpecialtyFinite_of_ratFunc_tower K F))

private theorem exists_const_ord_sub_nonpos [CharZero K] (t : F) (T : Finset (Place K F)) :
    ∃ a : K, ∀ v ∈ T, v.ord (t - algebraMap K F a) ≤ 0 := by
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hfin : {a : K | ∃ v ∈ T, 0 < v.ord (t - algebraMap K F a)}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion T.finite_toSet
      (fun v _ => (?_ : {a : K | 0 < v.ord (t - algebraMap K F a)}.Finite))) ?_
    · refine Set.Subsingleton.finite fun a ha b hb => ?_
      by_contra hab
      have ha1 : 0 < v.ord (t - algebraMap K F a) := ha
      have hb1 : 0 < v.ord (t - algebraMap K F b) := hb
      have ha' : t - algebraMap K F a ≠ 0 := PlaceOrd.ne_zero_of_ord_pos v (by omega)
      have hb' : -(t - algebraMap K F b) ≠ 0 :=
        neg_ne_zero.mpr (PlaceOrd.ne_zero_of_ord_pos v (by omega))
      have hsum : (t - algebraMap K F a) + -(t - algebraMap K F b) = algebraMap K F (b - a) := by
        rw [map_sub]; ring
      have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
      have hne : (t - algebraMap K F a) + -(t - algebraMap K F b) ≠ 0 := by
        rw [hsum]; exact (map_ne_zero (algebraMap K F)).mpr hba
      have h1 : (1 : ℤ) ≤ v.ord ((t - algebraMap K F a) + -(t - algebraMap K F b)) :=
        OrdCalculus.min_core v ha' hb' hne (by omega) (by rw [PlaceOrd.ord_neg']; omega)
      rw [hsum, OrdCalculus.ord_algebraMap_ne v hba] at h1
      omega
    · intro a ha
      obtain ⟨v, hv, h⟩ := ha
      exact Set.mem_biUnion (Finset.mem_coe.mpr hv) h
  obtain ⟨a, ha⟩ := hfin.infinite_compl.nonempty
  refine ⟨a, fun v hv => ?_⟩
  by_contra h
  exact ha ⟨v, hv, by omega⟩

private theorem exists_place_notMem [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (T : Finset (Place K F)) : ∃ u : Place K F, u ∉ T := by
  obtain ⟨t, ht, hfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  obtain ⟨a, ha⟩ := exists_const_ord_sub_nonpos t T
  set s : F := t - algebraMap K F a with hs_def
  have hts : t = s + algebraMap K F a := by rw [hs_def]; ring
  have hs : Transcendental K s := by
    intro hsalg
    apply ht
    rw [hts]
    exact hsalg.add (isAlgebraic_algebraMap a)
  have hy : Transcendental K s⁻¹ := by
    intro h
    apply hs
    simpa using h.inv
  have hadj : IntermediateField.adjoin K ({s⁻¹} : Set F) = IntermediateField.adjoin K ({t} : Set F) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact inv_mem (sub_mem (IntermediateField.mem_adjoin_simple_self K t)
        (IntermediateField.algebraMap_mem _ a))
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz, hts]
      have h2 : s ∈ IntermediateField.adjoin K ({s⁻¹} : Set F) := by
        simpa using inv_mem (IntermediateField.mem_adjoin_simple_self K s⁻¹)
      exact add_mem h2 (IntermediateField.algebraMap_mem _ a)
  haveI : FiniteDimensional (IntermediateField.adjoin K ({s⁻¹} : Set F)) F := hadj ▸ hfin
  obtain ⟨u, hu⟩ := Place.exists_ord_neg_of_transcendental s⁻¹ hy
  refine ⟨u, fun huT => ?_⟩
  have h1 := ha u huT
  rw [u.ord_inv] at hu
  omega

private theorem ord_neg_of_zero [IsCurveOver K F] (u₀ : Place K F) (x : F)
    (hreg : ∀ v : Place K F, v ≠ u₀ → 0 ≤ v.ord x)
    (hzero : ∃ v : Place K F, v ≠ u₀ ∧ 1 ≤ v.ord x) : u₀.ord x < 0 := by
  classical
  obtain ⟨v₁, hv₁, hx1⟩ := hzero
  have hx0 : x ≠ 0 := PlaceOrd.ne_zero_of_ord_pos v₁ hx1
  by_contra hcon
  have hge : 0 ≤ u₀.ord x := not_lt.mp hcon
  have hmem : x ∈ LSpace (-(Finsupp.single v₁ (1 : ℤ)) : Divisor K F) := by
    rw [mem_lSpace_iff_ord]
    right
    intro v
    rw [Finsupp.neg_apply, neg_neg, Finsupp.single_apply]
    split_ifs with hv
    · rw [← hv]
      exact hx1
    · by_cases hvu : v = u₀
      · rw [hvu]
        exact hge
      · exact hreg v hvu
  have hdeg : Divisor.degree (-(Finsupp.single v₁ (1 : ℤ)) : Divisor K F) < 0 := by
    rw [map_neg, Divisor.degree_single, one_mul]
    haveI := IsCurveOver.finite_residueField v₁
    have hpos : 0 < Module.finrank K v₁.ResidueField := Module.finrank_pos
    have hd : v₁.deg = Module.finrank K v₁.ResidueField := rfl
    omega
  rw [lSpace_eq_bot_of_degree_neg hdeg, Submodule.mem_bot K] at hmem
  exact hx0 hmem

private theorem strong_approx [IsCurveOver K F] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (hreach : RiemannGenusReachedAt γ D₀)
    (u₀ : Place K F) (T : Finset (Place K F)) (hT : u₀ ∉ T) (N : ℕ) (t : Place K F → F)
    (ht : ∀ Q ∈ T, 0 ≤ Q.ord (t Q)) :
    ∃ f : F, (∀ v : Place K F, v ≠ u₀ → 0 ≤ v.ord f) ∧
      ∀ Q ∈ T, f - t Q = 0 ∨ (N : ℤ) ≤ Q.ord (f - t Q) := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : Divisor K F, ∀ v, D v = if v ∈ T then -(N : ℤ) else 0 :=
    ⟨Finsupp.onFinset T (fun v => if v ∈ T then -(N : ℤ) else 0)
      (fun a ha => by by_contra h; exact ha (if_neg h)), fun v => Finsupp.onFinset_apply⟩
  obtain ⟨α, hα⟩ : ∃ α : Place K F → F, ∀ v, α v = if v ∈ T then t v else 0 :=
    ⟨fun v => if v ∈ T then t v else 0, fun v => rfl⟩
  have hbad : {v | v ∈ {v : Place K F | v ≠ u₀} ∧
      ¬ v.adicValuation (α v) ≤ WithZero.exp (D v)}.Finite := by
    refine T.finite_toSet.subset ?_
    intro v hv
    by_contra h
    have h' : v ∉ T := fun hvT => h (Finset.mem_coe.mpr hvT)
    exact hv.2 (by simp [hα v, h'])
  obtain ⟨f, hf⟩ := exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt hreach
    {v : Place K F | v ≠ u₀} (v₀ := u₀) (by simp) D α hbad
  refine ⟨f, ?_, ?_⟩
  · intro v hv
    have h := (v.adicValuation_le_exp_iff).mp (hf v hv)
    by_cases hvT : v ∈ T
    · have hαv : α v = t v := by rw [hα v, if_pos hvT]
      have hDv : D v = -(N : ℤ) := by rw [hD v, if_pos hvT]
      rw [hαv, hDv, neg_neg] at h
      have htv := ht v hvT
      rcases h with h0 | hN
      · rw [sub_eq_zero] at h0
        rw [← h0]
        exact htv
      · rcases eq_or_ne f 0 with rfl | hf0
        · simp
        rcases eq_or_ne (t v) 0 with htv0 | htv0
        · rw [htv0, zero_sub, PlaceOrd.ord_neg' v] at hN
          omega
        rcases eq_or_ne (t v - f) 0 with hd0 | hd0
        · rw [sub_eq_zero] at hd0
          rw [← hd0]
          exact htv
        · have hrepr : f = t v + -(t v - f) := by ring
          have hneg : v.ord (-(t v - f)) = v.ord (t v - f) := PlaceOrd.ord_neg' v _
          have hmin : (0 : ℤ) ≤ v.ord (t v + -(t v - f)) :=
            OrdCalculus.min_core v htv0 (neg_ne_zero.mpr hd0) (by rw [← hrepr]; exact hf0) htv
              (by rw [hneg]; omega)
          rwa [← hrepr] at hmin
    · have hαv : α v = 0 := by rw [hα v, if_neg hvT]
      have hDv : D v = 0 := by rw [hD v, if_neg hvT]
      rw [hαv, hDv, zero_sub, PlaceOrd.ord_neg' v, neg_zero] at h
      rcases h with h0 | h0
      · rw [neg_eq_zero] at h0
        rw [h0]
        simp
      · exact h0
  · intro Q hQT
    have hQS : Q ≠ u₀ := fun h => hT (h ▸ hQT)
    have h := (Q.adicValuation_le_exp_iff).mp (hf Q hQS)
    have hαQ : α Q = t Q := by rw [hα Q, if_pos hQT]
    have hDQ : D Q = -(N : ℤ) := by rw [hD Q, if_pos hQT]
    rw [hαQ, hDQ, neg_neg] at h
    rcases h with h0 | hN
    · left
      rw [sub_eq_zero] at h0 ⊢
      exact h0.symm
    · right
      rw [show f - t Q = -(t Q - f) by ring, PlaceOrd.ord_neg' Q]
      exact hN

private theorem exists_simple_zeros [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (T : Finset (Place K F)) (u₀ : Place K F) (hu₀ : u₀ ∉ T) :
    ∃ x : F, (∀ v : Place K F, v ≠ u₀ → 0 ≤ v.ord x) ∧ (∀ v ∈ T, v.ord x = 1) ∧
      ∃ v : Place K F, v ≠ u₀ ∧ 1 ≤ v.ord x := by
  classical
  obtain ⟨u₁, hu₁⟩ := exists_place_notMem (insert u₀ T)
  have hu₁u₀ : u₁ ≠ u₀ := fun h => hu₁ (by rw [h]; exact Finset.mem_insert_self u₀ T)
  have hu₀' : u₀ ∉ insert u₁ T := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hu₁u₀ h.symm
    · exact hu₀ h
  haveI : Nonempty (Place K F) := ⟨u₀⟩
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) := finiteDimensional_lSpace_zero K F
  obtain ⟨γ, D₀, hreach⟩ := exists_genus_reached (K := K) (F := F)
  choose π hπ using fun v : Place K F => Place.exists_ord_eq_one v
  obtain ⟨f, hreg, hjet⟩ := strong_approx hreach u₀ (insert u₁ T) hu₀' 2 π
    (fun Q _ => by have := hπ Q; omega)
  have hord : ∀ Q ∈ insert u₁ T, Q.ord f = 1 := by
    intro Q hQ
    have hπQ := hπ Q
    rcases hjet Q hQ with h0 | h2
    · rw [sub_eq_zero.mp h0]
      exact hπQ
    · have hπ0 : π Q ≠ 0 := PlaceOrd.ne_zero_of_ord_pos Q (by omega)
      have hd0 : f - π Q ≠ 0 := by
        intro h
        rw [h, Q.ord_zero] at h2
        omega
      have hlt : Q.ord (π Q) < Q.ord (f - π Q) := by omega
      obtain ⟨-, heq⟩ := OrdCalculus.ord_add_eq_of_lt Q hd0 hπ0 hlt
      rw [sub_add_cancel] at heq
      rw [heq]
      exact hπQ
  refine ⟨f, hreg, fun v hv => hord v (Finset.mem_insert_of_mem hv), u₁, hu₁u₀, ?_⟩
  have := hord u₁ (Finset.mem_insert_self u₁ T)
  omega

end PoleZeroPrescription

theorem solution
    {K : Type*} [Field K] [CharZero K] {F : Type*} [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    (T : Finset (AlgebraicCurve.Place K F)) :
    ∃ (u₀ : AlgebraicCurve.Place K F) (x : F), u₀ ∉ T ∧ u₀.ord x < 0 ∧
      (∀ v : AlgebraicCurve.Place K F, v ≠ u₀ → 0 ≤ v.ord x) ∧
      ∀ v ∈ T, v.ord x = 1 := by

  have hplace : ∃ u₀ : AlgebraicCurve.Place K F, u₀ ∉ T := by
    exact PoleZeroPrescription.exists_place_notMem T
  obtain ⟨u₀, hu₀⟩ := hplace

  have hpole : ∀ x : F, (∀ v : AlgebraicCurve.Place K F, v ≠ u₀ → 0 ≤ v.ord x) →
      (∃ v : AlgebraicCurve.Place K F, v ≠ u₀ ∧ 1 ≤ v.ord x) → u₀.ord x < 0 := by
    exact fun x hreg hzero => PoleZeroPrescription.ord_neg_of_zero u₀ x hreg hzero

  have hSA : ∃ x : F, (∀ v : AlgebraicCurve.Place K F, v ≠ u₀ → 0 ≤ v.ord x) ∧ (∀ v ∈ T, v.ord x = 1) ∧
      ∃ v : AlgebraicCurve.Place K F, v ≠ u₀ ∧ 1 ≤ v.ord x := by
    exact PoleZeroPrescription.exists_simple_zeros T u₀ hu₀

  obtain ⟨x, hreg, hT, hzero⟩ := hSA
  exact ⟨u₀, x, hu₀, hpole x hreg hzero, hreg, hT⟩

end S_AlgebraicCurve_exists_place_notMem_ord_neg_and_forall_ord_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_exists_place_notMem_ord_neg_and_forall_ord_eq_one (solution)
