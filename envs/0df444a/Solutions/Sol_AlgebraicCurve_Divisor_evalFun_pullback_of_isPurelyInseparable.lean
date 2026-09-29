-- Prove2me | solution 1 for AlgebraicCurve.Divisor.evalFun_pullback_of_isPurelyInseparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0adf787b-3a75-5550-9523-25e5fe418df5

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Divisor_support_pullback_subset
import Theorems.Thm_AlgebraicCurve_Place_pairwiseDisjoint_fiber
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_pullback_of_isPurelyInseparable
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

p2m_open "AlgebraicCurve~IsFrobeniusEndo"

set_option autoImplicit false

namespace Ws47
namespace EVPI

section PI
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsPurelyInseparable F E]

theorem exists_algebraMap_eq_pow_finrank (x : E) : ∃ y : F, algebraMap F E y = x ^ Module.finrank F E := by
  obtain ⟨k, hk⟩ := IsPurelyInseparable.finrank_eq_pow F E (ringExpChar F)
  obtain ⟨m, y, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F (ringExpChar F) x
  have hxy : x ^ ringExpChar F ^ m = algebraMap F E y := by
    have h := minpoly.aeval F x
    rw [hmin, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, sub_eq_zero] at h
    exact h
  have hdeg : ringExpChar F ^ m ≤ ringExpChar F ^ k := by
    have h1 : (minpoly F x).natDegree ≤ Module.finrank F E := minpoly.natDegree_le x
    rw [hmin, Polynomial.natDegree_X_pow_sub_C, hk] at h1
    exact h1
  rw [hk]
  rcases Nat.lt_or_ge 1 (ringExpChar F) with hq | hq
  ·
    have hmk : m ≤ k := (Nat.pow_le_pow_iff_right hq).mp hdeg
    refine ⟨y ^ ringExpChar F ^ (k - m), ?_⟩
    rw [map_pow, ← hxy, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hmk]
  ·
    have h1 : ringExpChar F = 1 := le_antisymm hq (Nat.one_le_iff_ne_zero.mpr (expChar_pos F (ringExpChar F)).ne')
    refine ⟨y, ?_⟩
    rw [h1, one_pow, pow_one]
    rw [h1, one_pow, pow_one] at hxy
    exact hxy.symm

theorem algebraMap_norm_eq_pow_finrank (x : E) :
    algebraMap F E (Algebra.norm F x) = x ^ Module.finrank F E := by
  obtain ⟨k, hk⟩ := IsPurelyInseparable.finrank_eq_pow F E (ringExpChar F)
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_pow_finrank (F := F) x
  suffices h : Algebra.norm F x = y by rw [h, hy]

  have hpow : Algebra.norm F x ^ Module.finrank F E = y ^ Module.finrank F E := by
    rw [← map_pow, ← hy, Algebra.norm_algebraMap]
  have hsub : (Algebra.norm F x - y) ^ Module.finrank F E = 0 := by
    rw [hk, sub_pow_expChar_pow, ← hk, hpow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Module.finrank_pos).ne' |>.mp hsub)

end PI

section Places
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F'] [FiniteDimensional F F']

theorem deg_eq_one_of_isRational {L : Type*} [Field L] [Algebra K L] (v : Place K L) (hv : v.IsRational) : v.deg = 1 := by
  let e : K ≃ₐ[K] v.ResidueField := AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField)
    ⟨v.algebraMap_residueField_injective, hv⟩
  rw [Place.deg, ← e.toLinearEquiv.finrank_eq, Module.finrank_self]

omit [FiniteDimensional F F'] in

theorem evalAt_restrict_eq [Algebra.IsIntegral F F'] (w : Place K F') (hv : (w.restrict F).IsRational) (hw : w.IsRational)
    {y : F} (hy : algebraMap F F' y ∈ w.toValuationSubring) :
    (w.restrict F).evalAt y = w.evalAt (algebraMap F F' y) := by
  apply w.algebraMap_residueField_injective
  have hy' : y ∈ (w.restrict F).toValuationSubring := hy
  rw [IsScalarTower.algebraMap_apply K (w.restrict F).ResidueField w.ResidueField,
    (w.restrict F).algebraMap_evalAt hv hy', Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue,
    w.algebraMap_evalAt hw hy]
  rfl

omit [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] in

theorem evalAt_pow (w : Place K F') (hw : w.IsRational) {f : F'} (hf : f ∈ w.toValuationSubring) (n : ℕ) :
    w.evalAt (f ^ n) = w.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, w.evalAt_mul hw (pow_mem hf n) hf, ih, pow_succ]

variable [IsPurelyInseparable F F']

theorem restrict_injective : Function.Injective fun w : Place K F' => w.restrict F := by
  intro w₁ w₂ h
  simp only at h

  have key : ∀ (w : Place K F') (x : F'), x ∈ w.toValuationSubring ↔
      ∃ y : F, algebraMap F F' y = x ^ Module.finrank F F' ∧ y ∈ (w.restrict F).toValuationSubring := by
    intro w x
    obtain ⟨y, hy⟩ := exists_algebraMap_eq_pow_finrank (F := F) x
    have hn : 0 < Module.finrank F F' := Module.finrank_pos
    constructor
    · intro hx
      exact ⟨y, hy, show algebraMap F F' y ∈ w.toValuationSubring from hy ▸ pow_mem hx _⟩
    · rintro ⟨y', hy', hmem⟩
      have hxn : x ^ Module.finrank F F' ∈ w.toValuationSubring := hy' ▸ (show algebraMap F F' y' ∈ w.toValuationSubring from hmem)
      rcases eq_or_ne x 0 with rfl | hx0
      · exact zero_mem _
      · rw [w.mem_iff_ord_nonneg hx0]
        have h2 := (w.mem_iff_ord_nonneg (pow_ne_zero _ hx0)).mp hxn
        rw [← zpow_natCast, w.ord_zpow] at h2
        exact nonneg_of_mul_nonneg_right (by rwa [mul_comm] at h2) (by exact_mod_cast hn)
  ext x
  rw [key w₁ x, key w₂ x, h]

end Places

end Ws47.EVPI

open Ws47.EVPI in

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [IsPurelyInseparable F F'] [HasPrincipalDivisors K F'] [FundamentalIdentity K F F'] {f : F'} (hf : f ≠ 0) (E : Divisor K F) (hrat : ∀ v ∈ E.support, Place.IsRational v) (hratw : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', Place.IsRational w) (hord : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', w.ord f = 0) : Divisor.evalFun f (Divisor.pullback F' E) = Divisor.evalFun (Algebra.norm F f) E := by
  classical
  rw [show Divisor.evalFun f (Divisor.pullback F' E)
      = ∏ w ∈ E.support.biUnion (fun v => v.fiber F'), w.evalAt f ^ (Divisor.pullback F' E) w from
    Finsupp.prod_of_support_subset _ (AlgebraicCurve.Divisor.support_pullback_subset E)
      (fun w n => w.evalAt f ^ n) fun w _ => zpow_zero _,
    Finset.prod_biUnion (AlgebraicCurve.Place.pairwiseDisjoint_fiber E.support), Divisor.evalFun_def]
  refine Finset.prod_congr rfl fun v hv => ?_

  have hFI := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') v
  have hdegv : v.deg = 1 := deg_eq_one_of_isRational v (hrat v hv)
  have hn : 0 < Module.finrank F F' := Module.finrank_pos
  have hne : (v.fiber F').Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty, hdegv] at hFI
    push_cast at hFI
    omega
  obtain ⟨w, hw⟩ := hne
  have hwv : w.restrict F = v := Place.mem_fiber.mp hw
  have hfib : v.fiber F' = {w} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hw, fun w' hw' => restrict_injective (K := K) (F := F) (F' := F') ?_⟩
    show w'.restrict F = w.restrict F
    rw [Place.mem_fiber.mp hw', hwv]
  have hdegw : w.deg = 1 := deg_eq_one_of_isRational w (hratw v hv w hw)
  have he : w.ramificationIndex F = Module.finrank F F' := by
    rw [hfib, Finset.sum_singleton, hdegw, hdegv] at hFI
    push_cast at hFI
    simpa using hFI

  rw [hfib, Finset.prod_singleton, Divisor.pullback_apply, hwv, he, zpow_mul, zpow_natCast]
  congr 1
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_pow_finrank (F := F) f
  have hnorm : algebraMap F F' (Algebra.norm F f) = algebraMap F F' y := by
    rw [algebraMap_norm_eq_pow_finrank, hy]
  have hNy : Algebra.norm F f = y := (algebraMap F F').injective hnorm
  have hfmem : f ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg hf).mpr (hord v hv w hw).ge
  have hymem : algebraMap F F' y ∈ w.toValuationSubring := hy ▸ pow_mem hfmem _
  rw [← evalAt_pow w (hratw v hv w hw) hfmem, ← hy, hNy]
  subst hwv
  exact (evalAt_restrict_eq w (hrat _ hv) (hratw _ hv w hw) hymem).symm

end S_AlgebraicCurve_Divisor_evalFun_pullback_of_isPurelyInseparable
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_evalFun_pullback_of_isPurelyInseparable (solution)
