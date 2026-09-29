-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6bf05747-d2a9-5409-8275-e06499f01219

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.AlgebraicCurve IsLocalRing Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place Place.coe_algebraMap Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField Place.exists_forall_ord_eq"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero integers residue_algebraMap algebraMap_mem_iff residue"
namespace ORLS
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

section places

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (P : Place K F) {f : F} (hf : f ∈ P.toValuationSubring) :
    0 ≤ P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · exact (P.mem_iff_ord_nonneg hf0).mp hf

private theorem _root_.AlgebraicCurve.RegularProlongation.ORLS.mem_nonunits_iff (P : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ P.toValuationSubring.nonunits ↔ 0 < P.ord f := by
  constructor
  · intro h
    have hmem : f ∈ P.toValuationSubring := P.toValuationSubring.nonunits_subset h
    exact (P.mem_maximalIdeal_iff_ord_pos hf hmem).mp
      ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨f, hmem⟩)).mp h)
  · intro h
    have hmem : f ∈ P.toValuationSubring := (P.mem_iff_ord_nonneg hf).mpr h.le
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f, hmem⟩)).mpr
      ((P.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h)

p2m_export "AlgebraicCurve.RegularProlongation.ORLS" "mem_nonunits_iff"
theorem zero_mem_nonunits (P : Place K F) : (0 : F) ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one

theorem ord_eq_zero_of_isUnit (P : Place K F) {f : F} (hf : f ∈ P.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : P.toValuationSubring)) : P.ord f = 0 := by
  obtain ⟨u, hu⟩ := hu
  have := P.ord_coe_unit u
  rwa [hu] at this

theorem ord_add_eq_zero (P : Place K F) {u m : F} (hu : u ∈ P.toValuationSubring)
    (hu0 : P.ord u = 0) (hu1 : u ≠ 0) (hm : m ∈ P.toValuationSubring.nonunits) :
    P.ord (u + m) = 0 ∧ u + m ≠ 0 := by
  have hmO : m ∈ P.toValuationSubring := P.toValuationSubring.nonunits_subset hm
  have hsum : u + m ∈ P.toValuationSubring := add_mem hu hmO
  have hne : u + m ≠ 0 := by
    intro h
    have : u = -m := eq_neg_of_add_eq_zero_left h
    rcases eq_or_ne m 0 with rfl | hm0
    · exact hu1 (by simpa using this)
    · have h1 := (mem_nonunits_iff P hm0).mp hm
      rw [this, P.ord_neg] at hu0
      omega
  refine ⟨?_, hne⟩
  by_contra hpos
  have hpos' : 0 < P.ord (u + m) :=
    lt_of_le_of_ne (ord_nonneg_of_mem P hsum) (Ne.symm hpos)
  have hmem : u + m ∈ P.toValuationSubring.nonunits := (mem_nonunits_iff P hne).mpr hpos'

  have hu' : u ∈ P.toValuationSubring.nonunits := by
    have h1 : (⟨u + m, hsum⟩ : P.toValuationSubring) ∈ maximalIdeal _ :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨u + m, hsum⟩)).mp hmem
    have h2 : (⟨m, hmO⟩ : P.toValuationSubring) ∈ maximalIdeal _ :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨m, hmO⟩)).mp hm
    have h3 := sub_mem h1 h2
    have : (⟨u + m, hsum⟩ : P.toValuationSubring) - ⟨m, hmO⟩ = ⟨u, hu⟩ := by
      ext; push_cast; ring
    rw [this] at h3
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨u, hu⟩)).mpr h3
  have := (mem_nonunits_iff P hu1).mp hu'
  omega

theorem ord_prod {ι : Type*} (P : Place K F) (s : Finset ι) (g : ι → F) (hg : ∀ i ∈ s, g i ≠ 0) :
    P.ord (∏ i ∈ s, g i) = ∑ i ∈ s, P.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      P.ord_mul (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem ord_pow (P : Place K F) (g : F) (n : ℕ) : P.ord (g ^ n) = n * P.ord g := by
  rw [← zpow_natCast, P.ord_zpow]

theorem exists_sub_algebraMap_mem [IsAlgClosed K] [IsCurveOver K F] (P : Place K F)
    (y : P.toValuationSubring) :
    ∃ c : K, y - algebraMap K P.toValuationSubring c ∈ maximalIdeal P.toValuationSubring := by
  haveI := IsCurveOver.finite_residueField (K := K) P
  haveI : Algebra.IsIntegral K P.ResidueField := Algebra.IsIntegral.of_finite K _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := P.ResidueField)).2 (IsLocalRing.residue _ y)
  refine ⟨c, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hc, sub_eq_zero, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

theorem exists_sub_algebraMap_mem_nonunits [IsAlgClosed K] [IsCurveOver K F] (P : Place K F)
    {y : F} (hy : y ∈ P.toValuationSubring) :
    ∃ c : K, y - algebraMap K F c ∈ P.toValuationSubring.nonunits := by
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem P (⟨y, hy⟩ : P.toValuationSubring)
  refine ⟨c, ?_⟩
  have := (ValuationSubring.coe_mem_nonunits_iff
    (a := (⟨y, hy⟩ : P.toValuationSubring) - algebraMap K _ c)).mpr hc
  simpa using this

theorem isIntegral_of_forall_mem (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (z : F)
    (hz : ∀ P : Place K F, x ∈ P.toValuationSubring → z ∈ P.toValuationSubring) :
    IsIntegral (Algebra.adjoin K {x}) z := by
  rw [← mem_integralClosure_iff]
  by_contra hzR
  obtain ⟨V, hRV, hzV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure (Algebra.adjoin K ({x} : Set F)) F).toSubring) hzR
  have hsub : ∀ y : F, y ∈ Algebra.adjoin K ({x} : Set F) → y ∈ V := fun y hy =>
    hRV (Subalgebra.mem_toSubring.mpr ((mem_integralClosure_iff _ _).mpr
      (isIntegral_algebraMap (x := (⟨y, hy⟩ : Algebra.adjoin K {x})))))
  have hK : ∀ a : K, algebraMap K F a ∈ V := fun a => hsub _ (Subalgebra.algebraMap_mem _ a)
  have hV : V ≠ ⊤ := fun h => hzV (h ▸ trivial)
  haveI := ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x V hK hV
  exact hzV (hz ⟨V, hK, hV, inferInstance⟩ (hsub x (Algebra.self_mem_adjoin_singleton K x)))

end places

section gauss

theorem exists_rescale {L : Type*} [Field L] (A : ValuationSubring L) {p : L[X]} (hp : p ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ a : ℕ → A, (∀ i, (a i : L) = c * p.coeff i) ∧ ∃ i₀, a i₀ = 1 := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := p.support.exists_max_image (fun i => A.valuation (p.coeff i))
    (Polynomial.support_nonempty.mpr hp)
  have hc0 : p.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have hmem : ∀ i, (p.coeff i₀)⁻¹ * p.coeff i ∈ A := by
    intro i
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hi : i ∈ p.support
    · rw [inv_mul_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc0))]
      exact hmax i hi
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero, mul_zero]
      exact zero_le'
  refine ⟨(p.coeff i₀)⁻¹, inv_ne_zero hc0, fun i => ⟨_, hmem i⟩, fun i => rfl, i₀, ?_⟩
  ext
  simp [hc0]

variable {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)

def cst (a : A) : R.integers := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩

@[scoped simp] theorem coe_cst (a : A) : (cst R a : F) = algebraMap L F a := rfl

theorem residue_cst (a : A) :
    R.residue (cst R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem exists_gauss (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    {p : L[X]} (hp : p ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ q₀ : R.integers, (q₀ : F) = algebraMap L F c * aeval (x : F) p ∧
      R.residue q₀ ≠ 0 ∧ R.residue q₀ ∈ Algebra.adjoin (ResidueField A) {R.residue x} := by
  classical
  obtain ⟨c, hc0, a, ha, i₀, hi₀⟩ := exists_rescale A hp
  let q₀ : R.integers := ∑ i ∈ Finset.range (p.natDegree + 1), cst R (a i) * x ^ i
  have hq₀F : (q₀ : F) = algebraMap L F c * aeval (x : F) p := by
    simp only [q₀]
    rw [aeval_eq_sum_range, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_cst, ha i, map_mul, Algebra.smul_def, mul_assoc]
  let pbar : (ResidueField A)[X] := ∑ i ∈ Finset.range (p.natDegree + 1),
    Polynomial.monomial i (IsLocalRing.residue A (a i))
  have hres_q₀ : R.residue q₀ = aeval (R.residue x) pbar := by
    simp only [q₀, pbar, map_sum, map_mul, map_pow, aeval_monomial, residue_cst]
  have hi₀mem : i₀ ∈ Finset.range (p.natDegree + 1) := by
    refine Finset.mem_range_succ_iff.mpr (Polynomial.le_natDegree_of_ne_zero fun h => ?_)
    have := ha i₀
    rw [hi₀, h, mul_zero] at this
    exact one_ne_zero (by exact_mod_cast this)
  have hpbar : pbar.coeff i₀ = 1 := by
    simp only [pbar, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i₀, if_pos rfl, hi₀, map_one]
    · intro j _ hj; exact if_neg hj
    · intro h; exact absurd hi₀mem h
  have hpbar0 : pbar ≠ 0 := fun h => by simp [h] at hpbar
  refine ⟨c, hc0, q₀, hq₀F, fun h => hx ⟨pbar, hpbar0, ?_⟩, ?_⟩
  · rw [← hres_q₀, h]
  · rw [hres_q₀]
    exact Polynomial.aeval_mem_adjoin_singleton _ _

theorem transcendental (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x)) :
    Transcendental L (x : F) := by
  rintro ⟨p, hp0, hp⟩
  obtain ⟨c, -, q₀, hq₀F, hres, -⟩ := exists_gauss R x hx hp0
  rw [hp, mul_zero] at hq₀F
  exact hres (by rw [show q₀ = 0 from Subtype.ext hq₀F, map_zero])

theorem residue_mem_adjoin (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (y : R.integers) (hy : (y : F) ∈ Algebra.adjoin L {(x : F)}) :
    R.residue y ∈ Algebra.adjoin (ResidueField A) {R.residue x} := by
  obtain ⟨p, hp⟩ : ∃ p : L[X], aeval (x : F) p = (y : F) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    exact hy
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [map_zero] at hp
    rw [show y = 0 from Subtype.ext hp.symm, map_zero]
    exact zero_mem _
  obtain ⟨c, hc0, q₀, hq₀F, hres0, hresmem⟩ := exists_gauss R x hx hp0
  rw [hp] at hq₀F
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hres0
  have hc' : algebraMap L F c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
  have h1 : (((u⁻¹ : R.integersˣ) : R.integers) : F) * (q₀ : F) = 1 := by
    rw [← hu]
    exact_mod_cast congrArg (fun z : R.integers => (z : F)) u.inv_mul

  have hcinv : algebraMap L F c⁻¹ = (y : F) * ((u⁻¹ : R.integersˣ) : R.integers) := by
    rw [map_inv₀, eq_comm, ← mul_eq_one_iff_eq_inv₀ hc']
    calc (y : F) * ((u⁻¹ : R.integersˣ) : R.integers) * algebraMap L F c
        = ((u⁻¹ : R.integersˣ) : R.integers) * (algebraMap L F c * y) := by ring
      _ = 1 := by rw [← hq₀F, h1]
  have hcA : c⁻¹ ∈ A := (R.algebraMap_mem_iff _).mp (hcinv ▸ mul_mem y.2 (Subtype.coe_prop _))
  have hy' : y = cst R ⟨c⁻¹, hcA⟩ * q₀ := by
    apply Subtype.ext
    push_cast
    rw [coe_cst, hq₀F, map_inv₀, inv_mul_cancel_left₀ hc']
  rw [hy', map_mul, residue_cst]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) hresmem

theorem residue_mem_adjoin_simple (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (c : IntermediateField.adjoin L ({(x : F)} : Set F)) (hc : (c : F) ∈ R.integers) :
    R.residue ⟨c, hc⟩ ∈ IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar) := by
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff L (c : F)).mp c.2
  by_cases hs : aeval (x : F) s = 0
  · rw [hs, div_zero] at hrs
    have : (⟨c, hc⟩ : R.integers) = 0 := Subtype.ext hrs
    rw [this, map_zero]
    exact zero_mem _
  have hs0 : s ≠ 0 := fun h => hs (by rw [h, map_zero])
  obtain ⟨d, hd0, q₀, hq₀F, hres0, hresmem⟩ := exists_gauss R x hx hs0
  have hprod : (((⟨c, hc⟩ : R.integers) * q₀ : R.integers) : F) ∈ Algebra.adjoin L {(x : F)} := by
    have : (c : F) * q₀ = aeval (x : F) (C d * r) := by
      rw [hrs, hq₀F, map_mul, aeval_C]
      field_simp
    push_cast
    rw [this]
    exact Polynomial.aeval_mem_adjoin_singleton _ _
  have h1 := residue_mem_adjoin R x hx _ hprod
  rw [map_mul] at h1
  have h2 : R.residue ⟨c, hc⟩ = R.residue ⟨c, hc⟩ * R.residue q₀ * (R.residue q₀)⁻¹ := by
    rw [mul_inv_cancel_right₀ hres0]
  rw [h2]
  exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin _ _ h1)
    (inv_mem (IntermediateField.algebra_adjoin_le_adjoin _ _ hresmem))

end gauss

section key

open scoped IntermediateField.algebraAdjoinAdjoin

variable {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)

theorem isIntegral_of_monic_of_coeff_mem {k E : Type*} [CommRing k] [CommRing E] [Nontrivial E]
    [Algebra k E] (B : Subalgebra k E) {p : E[X]} (hp : p.Monic) (hcoeff : ∀ i, p.coeff i ∈ B) {z : E}
    (hz : p.eval z = 0) : IsIntegral B z := by
  have hl : p ∈ lifts (algebraMap B E) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hcoeff i⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hp
  refine ⟨q, hqm, ?_⟩
  rw [← eval_map, hq, hz]

theorem exists_lift_basis (x : R.integers)
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) :
    ∃ ω : Fin (Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar) → R.integers,
      (∀ i, IsIntegral (Algebra.adjoin L {(x : F)}) (ω i : F)) ∧
      LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
        (fun i => R.residue (ω i)) := by
  set Kb := IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)
  haveI : FiniteDimensional Kb Fbar := Module.finite_of_finrank_pos hfin
  let b := Module.finBasis Kb Fbar
  have halg : ∀ i, IsAlgebraic (Algebra.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
      (b i) := fun i =>
    IsAlgebraic.restrictScalars (R := Algebra.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
      (S := Kb) (A := Fbar) (Algebra.IsAlgebraic.isAlgebraic (b i))
  choose d hd0 hdint using fun i => (halg i).exists_integral_multiple
  choose ω hωint hωres using fun i => hchart _ (hdint i)
  refine ⟨ω, hωint, ?_⟩
  have hu : ∀ i, algebraMap _ Kb (d i) ≠ 0 := fun i h =>
    hd0 i ((FaithfulSMul.algebraMap_injective _ Kb) (h.trans (map_zero _).symm))
  have : (fun i => R.residue (ω i)) = fun i => Units.mk0 _ (hu i) • b i := by
    funext i
    rw [hωres i, Units.smul_def, Units.val_mk0, algebraMap_smul]
  rw [this]
  exact b.linearIndependent.units_smul _

variable (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (ω : Fin n → R.integers)
  (hli : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (ω i)))
include hx hli

theorem valuation_sum_eq (c : Fin n → IntermediateField.adjoin L ({(x : F)} : Set F)) (j : Fin n)
    (hj : ∀ i, R.integers.valuation (c i : F) ≤ R.integers.valuation (c j : F)) (hcj : c j ≠ 0) :
    R.integers.valuation (∑ i, (c i : F) * ω i) = R.integers.valuation (c j : F) := by
  have hcjF : ((c j : IntermediateField.adjoin L ({(x : F)} : Set F)) : F) ≠ 0 := by
    exact_mod_cast hcj

  have hdmem : ∀ i, ((c i / c j : IntermediateField.adjoin L ({(x : F)} : Set F)) : F) ∈
      R.integers := fun i => by
    rw [← R.integers.valuation_le_one_iff]
    push_cast
    rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hcjF))]
    exact hj i
  let dO : Fin n → R.integers := fun i => ⟨_, hdmem i⟩
  let u : R.integers := ∑ i, dO i * ω i

  let e : Fin n → IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar) :=
    fun i => ⟨R.residue (dO i), residue_mem_adjoin_simple R x hx (c i / c j) (hdmem i)⟩
  have hres : R.residue u = ∑ i, e i • R.residue (ω i) := by
    simp only [u, map_sum, map_mul, e, IntermediateField.smul_def, smul_eq_mul]
  have hej : e j = 1 := by
    apply Subtype.ext
    show R.residue (dO j) = 1
    have : dO j = 1 := Subtype.ext (by simp [dO, div_self hcj])
    rw [this, map_one]
  have hu0 : R.residue u ≠ 0 := fun h0 => by
    have := (Fintype.linearIndependent_iff.mp hli) e (hres ▸ h0) j
    rw [hej] at this
    exact one_ne_zero this
  obtain ⟨v, hv⟩ := R.isUnit_of_residue_ne_zero hu0
  have hval : R.integers.valuation (u : F) = 1 := by
    rw [← hv]
    exact R.integers.valuation_unit v
  have hsum : ∑ i, (c i : F) * ω i = (c j : F) * u := by
    simp only [u, dO]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, mul_div_cancel₀ _ hcjF]
  rw [hsum, map_mul, hval, mul_one]

omit hx hli in

theorem exists_max_coeff (c : Fin n → IntermediateField.adjoin L ({(x : F)} : Set F))
    (hc : ∃ i, c i ≠ 0) :
    ∃ j, c j ≠ 0 ∧ ∀ i, R.integers.valuation (c i : F) ≤ R.integers.valuation (c j : F) := by
  classical
  obtain ⟨i, hi⟩ := hc
  obtain ⟨j, -, hj⟩ := Finset.univ.exists_max_image
    (fun i => R.integers.valuation ((c i : IntermediateField.adjoin L ({(x : F)} : Set F)) : F))
    ⟨i, Finset.mem_univ _⟩
  refine ⟨j, fun h => hi ?_, fun i => hj i (Finset.mem_univ _)⟩
  have := hj i (Finset.mem_univ _)
  rw [h, ZeroMemClass.coe_zero, map_zero, le_zero_iff, Valuation.zero_iff] at this
  exact_mod_cast this

theorem coeff_eq_zero (c : Fin n → IntermediateField.adjoin L ({(x : F)} : Set F))
    (h0 : ∑ i, (c i : F) * ω i = 0) : ∀ i, c i = 0 := by
  by_contra h
  push Not at h
  obtain ⟨j, hj0, hj⟩ := exists_max_coeff R x c h
  have := valuation_sum_eq R x hx ω hli c j hj hj0
  rw [h0, map_zero, eq_comm, Valuation.zero_iff] at this
  exact hj0 (by exact_mod_cast this)

theorem coeff_mem (c : Fin n → IntermediateField.adjoin L ({(x : F)} : Set F))
    (hmem : ∑ i, (c i : F) * ω i ∈ R.integers) : ∀ i, (c i : F) ∈ R.integers := by
  by_cases h : ∃ i, c i ≠ 0
  · obtain ⟨j, hj0, hj⟩ := exists_max_coeff R x c h
    have hv := valuation_sum_eq R x hx ω hli c j hj hj0
    intro i
    rw [← R.integers.valuation_le_one_iff]
    refine (hj i).trans ?_
    rw [← hv, R.integers.valuation_le_one_iff]
    exact hmem
  · push Not at h
    intro i
    rw [h i, ZeroMemClass.coe_zero]
    exact zero_mem _

omit hli in

theorem isIntegral_residue
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (h : R.integers) (hh : IsIntegral (Algebra.adjoin L {(x : F)}) (h : F)) :
    IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) (R.residue h) := by
  classical
  set Kx := IntermediateField.adjoin L ({(x : F)} : Set F) with hKx
  haveI : FiniteDimensional Kx F := Module.finite_of_finrank_pos (hdeg ▸ hfin)
  obtain ⟨ω, hωint, hli⟩ := exists_lift_basis R x hfin hchart

  have hωli : LinearIndependent Kx (fun i => (ω i : F)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    refine coeff_eq_zero R x hx ω hli g ?_
    simpa only [IntermediateField.smul_def, smul_eq_mul] using hg
  have hspan : Submodule.span Kx (Set.range fun i => (ω i : F)) = ⊤ := by
    haveI : Nonempty (Fin (Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)) :=
      ⟨⟨0, hfin⟩⟩
    exact hωli.span_eq_top_of_card_eq_finrank ((Fintype.card_fin _).trans hdeg.symm)

  let OG : ValuationSubring Kx := R.integers.comap (algebraMap Kx F)
  let S : Subalgebra OG F :=
    { carrier := R.integers
      mul_mem' := fun ha hb => mul_mem ha hb
      one_mem' := one_mem _
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      algebraMap_mem' := fun r => r.2 }
  have hSfg : (Subalgebra.toSubmodule S).FG := by
    refine ⟨Finset.univ.image fun i => (ω i : F), le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact (ω i).2
    · intro y hy
      have hy' : y ∈ R.integers := hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Kx).mp
        (hspan ▸ Submodule.mem_top : y ∈ Submodule.span Kx (Set.range fun i => (ω i : F)))
      have hc' : ∑ i, (c i : F) * ω i = y := by
        simpa only [IntermediateField.smul_def, smul_eq_mul] using hc
      have hcO := coeff_mem R x hx ω hli c (hc' ▸ hy')
      rw [← hc']
      refine Submodule.sum_mem _ fun i _ => ?_
      have : (c i : F) * ω i = (⟨c i, hcO i⟩ : OG) • (ω i : F) := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hint : IsIntegral OG (h : F) := IsIntegral.of_mem_of_fg S hSfg _ h.2

  haveI : IsIntegrallyClosed (Algebra.adjoin L ({(x : F)} : Set F)) :=
    IsIntegrallyClosed.of_equiv
      (Polynomial.algEquivOfTranscendental L (x : F) (transcendental R x hx)).toRingEquiv
  have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' (R := OG) (S := F) Kx hint
  have h2 := minpoly.isIntegrallyClosed_eq_field_fractions'
    (R := Algebra.adjoin L ({(x : F)} : Set F)) (S := F) Kx hh
  have hcoefO : ∀ i, ((minpoly Kx (h : F)).coeff i : F) ∈ R.integers := fun i => by
    rw [h1, coeff_map]
    exact ((minpoly OG (h : F)).coeff i).2
  have hcoefP : ∀ i, ((minpoly Kx (h : F)).coeff i : F) ∈ Algebra.adjoin L ({(x : F)} : Set F) :=
    fun i => by
    rw [h2, coeff_map, IntermediateField.algebraAdjoinAdjoin.coe_algebraMap]
    exact Subtype.coe_prop _

  have hlifts : (minpoly Kx (h : F)).map (algebraMap Kx F) ∈ lifts (algebraMap R.integers F) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_map]
    exact ⟨⟨_, hcoefO i⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqmonic⟩ := lifts_and_degree_eq_and_monic hlifts
    ((minpoly.monic hh.tower_top).map _)
  have hqeval : q.eval h = 0 := by
    have h0 : ((minpoly Kx (h : F)).map (algebraMap Kx F)).eval (h : F) = 0 := by
      rw [eval_map, ← aeval_def, minpoly.aeval]
    rwa [← hqmap, eval_map, show (h : F) = algebraMap R.integers F h from rfl, eval₂_hom,
      show algebraMap R.integers F (q.eval h) = ((q.eval h : R.integers) : F) from rfl,
      ZeroMemClass.coe_eq_zero] at h0
  have hqcoeff : ∀ i, (q.coeff i : F) = ((minpoly Kx (h : F)).coeff i : F) := fun i => by
    have := congrArg (fun p => p.coeff i) hqmap
    simp only [coeff_map] at this
    exact this

  refine isIntegral_of_monic_of_coeff_mem _ (hqmonic.map R.residue) (fun i => ?_)
    (z := R.residue h) (by rw [eval_map, eval₂_hom, hqeval, map_zero])
  rw [coeff_map]
  exact residue_mem_adjoin R x hx _ ((hqcoeff i).symm ▸ hcoefP i)

end key

section stepB

variable {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)

theorem isIntegral_of_mem_adjoin {x y : F} (hy : y ∈ Algebra.adjoin L ({x} : Set F)) :
    IsIntegral (Algebra.adjoin L ({x} : Set F)) y :=
  isIntegral_algebraMap (x := (⟨y, hy⟩ : Algebra.adjoin L ({x} : Set F)))

theorem isIntegral_cst (x : R.integers) (a : A) :
    IsIntegral (Algebra.adjoin L {(x : F)}) (cst R a : F) :=
  isIntegral_of_mem_adjoin (Subalgebra.algebraMap_mem _ _)

theorem isIntegral_self (x : R.integers) : IsIntegral (Algebra.adjoin L {(x : F)}) (x : F) :=
  isIntegral_of_mem_adjoin (Algebra.self_mem_adjoin_singleton L (x : F))

theorem exists_vanishing [IsAlgClosed L] [IsCurveOver L F]
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (Q : Place (ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (P : Place L F) (hxP : (x : F) ∈ P.toValuationSubring)
    (hPT : ¬ ((∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits)) :
    ∃ y : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (y : F) ∧ (y : F) ≠ 0 ∧
      0 < P.ord (y : F) ∧ R.residue y ≠ 0 ∧ Q.ord (R.residue y) = 0 := by
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_nonunits P hxP
  by_cases hcA : c ∈ A
  ·
    have h2 : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits :=
      ⟨⟨c, hcA⟩, hc⟩
    have h3 : ∃ h₁ : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h₁ : F) ∧ ∃ a : A,
        (h₁ : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits ∧
          R.residue h₁ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∉
            Q.toValuationSubring.nonunits := by
      by_contra hne
      push Not at hne
      exact hPT ⟨h2, hne⟩
    obtain ⟨h₁, hh₁, a, ha, hres⟩ := h3
    have hcoe : ((h₁ - cst R a : R.integers) : F) = (h₁ : F) - algebraMap L F a := by
      push_cast; rw [coe_cst]
    have hres' : R.residue (h₁ - cst R a) = R.residue h₁ -
        algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
      rw [map_sub, residue_cst]
    have hyint : IsIntegral (Algebra.adjoin L {(x : F)}) ((h₁ - cst R a : R.integers) : F) := by
      rw [hcoe]; exact hh₁.sub (isIntegral_cst R x a)
    have hyO : R.residue (h₁ - cst R a) ∈ Q.toValuationSubring :=
      Q.mem_toValuationSubring_of_isIntegral_adjoin hQ
        (isIntegral_residue R x hx hfin hdeg hchart _ hyint)
    have hord0 : Q.ord (R.residue (h₁ - cst R a)) = 0 := by
      refine ord_eq_zero_of_isUnit Q hyO ?_
      by_contra hnu
      apply hres
      rw [← hres']
      exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hyO⟩)).mpr
        ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have hresne : R.residue (h₁ - cst R a) ≠ 0 := by
      intro h0
      apply hres
      rw [← hres', h0]
      exact zero_mem_nonunits Q
    have hy0 : ((h₁ - cst R a : R.integers) : F) ≠ 0 := by
      intro h0
      apply hresne
      rw [show h₁ - cst R a = 0 from Subtype.ext h0, map_zero]
    refine ⟨h₁ - cst R a, hyint, hy0, ?_, hresne, hord0⟩
    have := (mem_nonunits_iff P (hcoe ▸ hy0)).mp ha
    rwa [← hcoe] at this
  ·
    have hc0 : c ≠ 0 := fun h => hcA (h ▸ zero_mem A)
    have hc' : algebraMap L F c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hres0 : IsLocalRing.residue A ⟨c⁻¹, hcinv⟩ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      show A.valuation c⁻¹ < 1
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc0))]
      exact lt_of_not_ge fun h => hcA ((A.valuation_le_one_iff c).mp h)
    let y : R.integers := 1 - cst R ⟨c⁻¹, hcinv⟩ * x
    have hxc : (x : F) - algebraMap L F c ≠ 0 := by
      intro h
      exact transcendental R x hx (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c)
    have hyF : (y : F) = -(algebraMap L F c)⁻¹ * ((x : F) - algebraMap L F c) := by
      simp only [y]
      push_cast
      rw [coe_cst]
      show 1 - algebraMap L F c⁻¹ * (x : F) = _
      rw [map_inv₀]
      field_simp
      ring
    have hy0 : (y : F) ≠ 0 := by
      rw [hyF]; exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hc')) hxc
    have hordy : 0 < P.ord (y : F) := by
      rw [hyF, P.ord_mul (neg_ne_zero.mpr (inv_ne_zero hc')) hxc, P.ord_neg, ← map_inv₀,
        P.ord_algebraMap, zero_add]
      exact (mem_nonunits_iff P hxc).mp hc
    have hresy : R.residue y = 1 := by
      simp only [y, map_sub, map_one, map_mul, residue_cst, hres0, map_zero, zero_mul, sub_zero]
    refine ⟨y, ?_, hy0, hordy, ?_, ?_⟩
    · have : IsIntegral (Algebra.adjoin L {(x : F)}) ((1 : F) - (cst R ⟨c⁻¹, hcinv⟩ : F) * x) :=
        isIntegral_one.sub ((isIntegral_cst R x _).mul (isIntegral_self R x))
      exact this
    · rw [hresy]; exact one_ne_zero
    · rw [hresy]; exact Q.ord_one

theorem pole_killing [IsAlgClosed L] [IsCurveOver L F]
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0)
    (Q : Place (ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits))
    (h : R.integers) (hh : IsIntegral (Algebra.adjoin L {(x : F)}) (h : F))
    (hvan : ∀ P ∈ T, (h : F) = 0 ∨ D P ≤ P.ord (h : F)) :
    R.residue h = 0 ∨ Q.ord (R.residue f) ≤ Q.ord (R.residue h) := by
  classical
  by_cases hh0 : (h : F) = 0
  · left; rw [show h = 0 from Subtype.ext hh0, map_zero]
  by_cases hresh : R.residue h = 0
  · exact Or.inl hresh
  right
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  have hf0 : (f : F) ≠ 0 := fun h0 => hf (by rw [show f = 0 from Subtype.ext h0, map_zero])

  let B : Finset (Place L F) :=
    D.support.filter fun P => (x : F) ∈ P.toValuationSubring ∧ P ∉ T
  have hy : ∀ P : Place L F, ∃ y : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (y : F) ∧
      (y : F) ≠ 0 ∧ (P ∈ B → 0 < P.ord (y : F)) ∧ R.residue y ≠ 0 ∧
      Q.ord (R.residue y) = 0 := by
    intro P
    by_cases hPB : P ∈ B
    · obtain ⟨hPD, hxP, hPT⟩ := Finset.mem_filter.mp hPB
      obtain ⟨y, h1, h2, h3, h4, h5⟩ := exists_vanishing R x hx hfin hdeg hchart Q hQ P hxP
        (fun hc => hPT ((hT P).mpr ⟨Finsupp.mem_support_iff.mp hPD, hc⟩))
      exact ⟨y, h1, h2, fun _ => h3, h4, h5⟩
    · refine ⟨1, ?_, by simp, fun h => absurd h hPB, by simp, by rw [map_one, Q.ord_one]⟩
      have : IsIntegral (Algebra.adjoin L {(x : F)}) (1 : F) := isIntegral_one
      simpa using this
  choose y hyint hy0 hyord hyres hyQ using hy
  let U : R.integers := ∏ P ∈ B, y P ^ (D P).toNat
  have hUF : (U : F) = ∏ P ∈ B, (y P : F) ^ (D P).toNat := by
    simp only [U]; push_cast; rfl
  have hUint : IsIntegral (Algebra.adjoin L {(x : F)}) (U : F) := by
    rw [hUF]; exact IsIntegral.prod _ fun P _ => (hyint P).pow _
  have hU0 : (U : F) ≠ 0 := by
    rw [hUF]; exact Finset.prod_ne_zero_iff.mpr fun P _ => pow_ne_zero _ (hy0 P)
  have hresU : R.residue U = ∏ P ∈ B, R.residue (y P) ^ (D P).toNat := by
    simp only [U, map_prod, map_pow]
  have hresU0 : R.residue U ≠ 0 := by
    rw [hresU]; exact Finset.prod_ne_zero_iff.mpr fun P _ => pow_ne_zero _ (hyres P)
  have hordU : Q.ord (R.residue U) = 0 := by
    rw [hresU, ord_prod Q B _ fun P _ => pow_ne_zero _ (hyres P)]
    exact Finset.sum_eq_zero fun P _ => by rw [ord_pow, hyQ, mul_zero]
  obtain ⟨uf, huf⟩ := R.isUnit_of_residue_ne_zero hf
  have hufinv : (((uf⁻¹ : R.integersˣ) : R.integers) : F) = (f : F)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← huf]
    exact_mod_cast congrArg (fun z : R.integers => (z : F)) uf.inv_mul
  let g : R.integers := U * h * ↑(uf⁻¹)
  have hgF : (g : F) = (U : F) * h * (f : F)⁻¹ := by
    simp only [g]; push_cast; rw [hufinv]
  have hg0 : (g : F) ≠ 0 := by
    rw [hgF]; exact mul_ne_zero (mul_ne_zero hU0 hh0) (inv_ne_zero hf0)

  have hgmem : ∀ P : Place L F, (x : F) ∈ P.toValuationSubring →
      (g : F) ∈ P.toValuationSubring := by
    intro P hxP
    rw [P.mem_iff_ord_nonneg hg0, hgF, P.ord_mul (mul_ne_zero hU0 hh0) (inv_ne_zero hf0),
      P.ord_mul hU0 hh0, P.ord_inv, ← hD]
    have hUnn : 0 ≤ P.ord (U : F) :=
      ord_nonneg_of_mem P (P.mem_toValuationSubring_of_isIntegral_adjoin hxP hUint)
    have hhnn : 0 ≤ P.ord (h : F) :=
      ord_nonneg_of_mem P (P.mem_toValuationSubring_of_isIntegral_adjoin hxP hh)
    have hDnn : 0 ≤ D P :=
      (hD P).symm ▸ ord_nonneg_of_mem P (P.mem_toValuationSubring_of_isIntegral_adjoin hxP hfi)
    by_cases hPT : P ∈ T
    · rcases hvan P hPT with h0 | h0
      · exact absurd h0 hh0
      · omega
    by_cases hDP : D P = 0
    · omega
    have hPB : P ∈ B := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hDP, hxP, hPT⟩
    have hDU : D P ≤ P.ord (U : F) := by
      rw [hUF, ord_prod P B _ fun P' _ => pow_ne_zero _ (hy0 P')]
      have h1 : D P ≤ P.ord ((y P : F) ^ (D P).toNat) := by
        rw [ord_pow]
        have := hyord P hPB
        calc D P = ((D P).toNat : ℤ) * 1 := by rw [mul_one, Int.toNat_of_nonneg hDnn]
          _ ≤ ((D P).toNat : ℤ) * P.ord (y P : F) :=
            mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
      refine h1.trans ?_
      exact Finset.single_le_sum (f := fun P' => P.ord ((y P' : F) ^ (D P').toNat))
        (fun P' _ => by
          show 0 ≤ P.ord ((y P' : F) ^ (D P').toNat)
          rw [ord_pow]
          exact mul_nonneg (Int.natCast_nonneg _) (ord_nonneg_of_mem P
            (P.mem_toValuationSubring_of_isIntegral_adjoin hxP (hyint P'))))
        hPB
    omega
  have hgint : IsIntegral (Algebra.adjoin L {(x : F)}) (g : F) :=
    isIntegral_of_forall_mem (x : F) (g : F) hgmem
  have hresg : R.residue g ∈ Q.toValuationSubring :=
    Q.mem_toValuationSubring_of_isIntegral_adjoin hQ
      (isIntegral_residue R x hx hfin hdeg hchart g hgint)
  have hgf : g * f = U * h := by
    simp only [g]; rw [← huf, mul_assoc, Units.inv_mul, mul_one]
  have hres : R.residue g * R.residue f = R.residue U * R.residue h := by
    rw [← map_mul, hgf, map_mul]
  have hresg0 : R.residue g ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hres
    exact mul_ne_zero hresU0 hresh hres.symm
  have h1 := congrArg Q.ord hres
  rw [Q.ord_mul hresg0 hf, Q.ord_mul hresU0 hresh, hordU, zero_add] at h1
  have h2 := ord_nonneg_of_mem Q hresg
  omega

end stepB

section local_lemmas

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

theorem exists_integral_uniformizer [IsAlgClosed K] [IsCurveOver K F] (x : F)
    (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (Q : Place K F) (hQ : x ∈ Q.toValuationSubring) :
    ∃ t : F, IsIntegral (Algebra.adjoin K {x}) t ∧ Q.ord t = 1 := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_sub_algebraMap_mem_nonunits Q hQ
  set z := x - algebraMap K F c₀ with hz
  have hz0 : z ≠ 0 := fun h => hx (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c₀)
  obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0

  obtain ⟨t₀, ht₀0, ht₀⟩ := Place.exists_forall_ord_eq (insert Q D₀.support)
    (fun v => if v = Q then (1 : ℤ) else 0)
  have ht₀Q : Q.ord t₀ = 1 := by simpa using ht₀ Q (Finset.mem_insert_self _ _)
  obtain ⟨D₁, hD₁, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) t₀ ht₀0

  let B : Finset (Place K F) := D₁.support.filter fun v => D₁ v < 0 ∧ x ∈ v.toValuationSubring
  have hBz : ∀ v ∈ B, v ≠ Q ∧ v.ord z = 0 := by
    intro v hv
    obtain ⟨-, hv1, -⟩ := Finset.mem_filter.mp hv
    have hvS : v ∉ insert Q D₀.support := fun hvS => by
      have := ht₀ v hvS
      rw [← hD₁] at this
      split_ifs at this <;> omega
    rwa [Finset.mem_insert, not_or, Finsupp.mem_support_iff, not_not, hD₀] at hvS

  have hw : ∀ v : Place K F, ∃ w : F, w ≠ 0 ∧
      (∀ Q' : Place K F, x ∈ Q'.toValuationSubring → w ∈ Q'.toValuationSubring) ∧
      Q.ord w = 0 ∧ (v ∈ B → 0 < v.ord w) := by
    intro v
    by_cases hvB : v ∈ B
    · obtain ⟨-, -, hxv⟩ := Finset.mem_filter.mp hvB
      obtain ⟨cv, hcv⟩ := exists_sub_algebraMap_mem_nonunits v hxv
      have hw0 : x - algebraMap K F cv ≠ 0 := fun h =>
        hx (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap cv)
      refine ⟨x - algebraMap K F cv, hw0, fun Q' hQ' => sub_mem hQ' (Q'.algebraMap_mem' cv), ?_,
        fun _ => (mem_nonunits_iff v hw0).mp hcv⟩
      have hne : c₀ ≠ cv := by
        rintro rfl
        have := (mem_nonunits_iff v hz0).mp hcv
        exact absurd (hBz v hvB).2 this.ne'
      have heq : x - algebraMap K F cv = algebraMap K F (c₀ - cv) + z := by
        rw [hz, map_sub]; ring
      rw [heq]
      exact (ord_add_eq_zero Q (Q.algebraMap_mem' _) (Q.ord_algebraMap _)
        ((_root_.map_ne_zero _).mpr (sub_ne_zero.mpr hne)) hc₀).1
    · exact ⟨1, one_ne_zero, fun Q' _ => one_mem _, Q.ord_one, fun h => absurd h hvB⟩
  choose w hw0 hwmem hwQ hwv using hw
  let t : F := t₀ * ∏ v ∈ B, w v ^ (-D₁ v).toNat
  have hprod0 : ∏ v ∈ B, w v ^ (-D₁ v).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hw0 v)
  have ht0 : t ≠ 0 := mul_ne_zero ht₀0 hprod0
  refine ⟨t, isIntegral_of_forall_mem x t fun Q' hxQ' => ?_, ?_⟩
  · rw [Q'.mem_iff_ord_nonneg ht0, Q'.ord_mul ht₀0 hprod0, ← hD₁,
      ord_prod Q' B _ fun v _ => pow_ne_zero _ (hw0 v)]
    have hnn : ∀ v ∈ B, 0 ≤ Q'.ord (w v ^ (-D₁ v).toNat) := fun v _ => by
      rw [ord_pow]
      exact mul_nonneg (Int.natCast_nonneg _) (ord_nonneg_of_mem Q' (hwmem v Q' hxQ'))
    by_cases hQ'B : Q' ∈ B
    · have h1 : -D₁ Q' ≤ Q'.ord (w Q' ^ (-D₁ Q').toNat) := by
        rw [ord_pow]
        have := hwv Q' hQ'B
        obtain ⟨-, hneg, -⟩ := Finset.mem_filter.mp hQ'B
        calc -D₁ Q' = ((-D₁ Q').toNat : ℤ) * 1 := by
              rw [mul_one, Int.toNat_of_nonneg (by omega)]
          _ ≤ ((-D₁ Q').toNat : ℤ) * Q'.ord (w Q') :=
            mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
      have h2 := Finset.single_le_sum (f := fun v => Q'.ord (w v ^ (-D₁ v).toNat)) hnn hQ'B
      omega
    · have h2 := Finset.sum_nonneg hnn
      have : 0 ≤ D₁ Q' := by
        by_contra hneg
        exact hQ'B (Finset.mem_filter.mpr
          ⟨Finsupp.mem_support_iff.mpr (by omega), by omega, hxQ'⟩)
      omega
  · rw [Q.ord_mul ht₀0 hprod0, ht₀Q, ord_prod Q B _ fun v _ => pow_ne_zero _ (hw0 v),
      Finset.sum_eq_zero fun v _ => by rw [ord_pow, hwQ, mul_zero], add_zero]

theorem le_ord_of_mem_pow (P : Place K F) (r : ℕ) (y : P.toValuationSubring)
    (hy : y ∈ (maximalIdeal P.toValuationSubring) ^ r) :
    (y : F) = 0 ∨ (r : ℤ) ≤ P.ord (y : F) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, rfl⟩ := hy
  by_cases ha : (a : F) = 0
  · left; push_cast; rw [ha, zero_mul]
  · right
    have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    push_cast
    rw [P.ord_mul ha (pow_ne_zero _ hϖ0), ord_pow, P.ord_coe_irreducible hϖ, mul_one]
    have := ord_nonneg_of_mem P a.2
    omega

theorem finite_quotient_pow [IsAlgClosed K] [IsCurveOver K F] (P : Place K F) (r : ℕ) :
    Module.Finite K (P.toValuationSubring ⧸ (maximalIdeal P.toValuationSubring) ^ r) ∧
      Module.finrank K (P.toValuationSubring ⧸ (maximalIdeal P.toValuationSubring) ^ r) ≤ r := by
  classical
  set O := P.toValuationSubring
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O

  have key : ∀ s : ℕ, ∀ y : O, ∃ a : ℕ → K,
      y - ∑ i ∈ Finset.range s, algebraMap K O (a i) * ϖ ^ i ∈ (maximalIdeal O) ^ s := by
    intro s
    induction s with
    | zero => intro y; exact ⟨fun _ => 0, by simp⟩
    | succ s ih =>
      intro y
      obtain ⟨a, ha⟩ := ih y
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, hb⟩ := ha
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem P b
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hc
      obtain ⟨d, hd⟩ := hc
      refine ⟨Function.update a s c, ?_⟩
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      refine ⟨d, ?_⟩
      rw [Finset.sum_range_succ, Function.update_self,
        Finset.sum_congr rfl fun i hi =>
          by rw [Function.update_of_ne (Finset.mem_range.mp hi).ne],
        ← sub_sub, ← hb]
      linear_combination (ϖ ^ s) * hd

  let φ : (Fin r → K) →ₗ[K] O ⧸ (maximalIdeal O) ^ r :=
    Fintype.linearCombination K fun i : Fin r =>
      Ideal.Quotient.mkₐ K ((maximalIdeal O) ^ r) (ϖ ^ (i : ℕ))
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective K _ q
    obtain ⟨a, ha⟩ := key r y
    refine ⟨fun i => a i, ?_⟩
    simp only [φ, Fintype.linearCombination_apply, ← map_smul, ← map_sum]
    rw [eq_comm, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    convert ha using 2
    rw [← Fin.sum_univ_eq_sum_range (fun i => algebraMap K O (a i) * ϖ ^ i) r]
    exact Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _
  haveI : Module.Finite K (O ⧸ (maximalIdeal O) ^ r) := Module.Finite.of_surjective φ hφ
  exact ⟨this, (LinearMap.finrank_le_finrank_of_surjective hφ).trans (Module.finrank_fin_fun K).le⟩

theorem eq_zero_of_le_ord (Q : Place K F) {t : F} (ht : Q.ord t = 1) :
    ∀ (m : ℕ) (e : Fin m → K),
      ((∑ i, algebraMap K F (e i) * t ^ (i : ℕ)) = 0 ∨
        (m : ℤ) ≤ Q.ord (∑ i, algebraMap K F (e i) * t ^ (i : ℕ))) → ∀ i, e i = 0 := by
  have ht0 : t ≠ 0 := fun h => by rw [h, Q.ord_zero] at ht; exact zero_ne_one ht
  have htO : t ∈ Q.toValuationSubring := (Q.mem_iff_ord_nonneg ht0).mpr (by omega)
  have htn : t ∈ Q.toValuationSubring.nonunits := (mem_nonunits_iff Q ht0).mpr (by omega)
  intro m
  induction m with
  | zero => intro e _ i; exact i.elim0
  | succ m ih =>
    intro e he
    set s : F := ∑ i : Fin m, algebraMap K F (e i.succ) * t ^ (i : ℕ) with hs
    have hsO : s ∈ Q.toValuationSubring :=
      sum_mem fun i _ => mul_mem (Q.algebraMap_mem' _) (pow_mem htO _)
    have hsplit : ∑ i : Fin (m + 1), algebraMap K F (e i) * t ^ (i : ℕ) =
        algebraMap K F (e 0) + t * s := by
      rw [Fin.sum_univ_succ, hs, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit] at he
    have htsn : t * s ∈ Q.toValuationSubring.nonunits := by
      rcases eq_or_ne s 0 with h0 | h0
      · rw [h0, mul_zero]; exact zero_mem_nonunits Q
      · rw [mem_nonunits_iff Q (mul_ne_zero ht0 h0), Q.ord_mul ht0 h0, ht]
        have := ord_nonneg_of_mem Q hsO
        omega

    have he0 : e 0 = 0 := by
      by_contra hne
      have h := ord_add_eq_zero Q (Q.algebraMap_mem' (e 0)) (Q.ord_algebraMap _)
        ((_root_.map_ne_zero _).mpr hne) htsn
      rcases he with he | he
      · exact h.2 he
      · rw [h.1] at he; push_cast at he; omega
    rw [he0, map_zero, zero_add] at he

    have hs' : s = 0 ∨ (m : ℤ) ≤ Q.ord s := by
      rcases eq_or_ne s 0 with h0 | h0
      · exact Or.inl h0
      · right
        rcases he with he | he
        · exact absurd he (mul_ne_zero ht0 h0)
        · rw [Q.ord_mul ht0 h0, ht] at he; push_cast at he; omega
    have ih' := ih (fun i => e i.succ) hs'
    intro i
    refine Fin.cases he0 (fun j => ih' j) i

theorem exists_rescale_fun {L : Type*} [Field L] (A : ValuationSubring L) {m : ℕ}
    (c : Fin m → L) (hc : ∃ i, c i ≠ 0) :
    ∃ j, c j ≠ 0 ∧ ∃ d : Fin m → A, (∀ i, (d i : L) = (c j)⁻¹ * c i) ∧ d j = 1 := by
  classical
  obtain ⟨i, hi⟩ := hc
  obtain ⟨j, -, hmax⟩ := Finset.univ.exists_max_image (fun i => A.valuation (c i))
    ⟨i, Finset.mem_univ _⟩
  have hcj : c j ≠ 0 := fun h => hi (by
    have := hmax i (Finset.mem_univ _)
    rwa [h, map_zero, le_zero_iff, Valuation.zero_iff] at this)
  have hmem : ∀ i, (c j)⁻¹ * c i ∈ A := fun i => by
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀,
      inv_mul_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hcj))]
    exact hmax i (Finset.mem_univ _)
  refine ⟨j, hcj, fun i => ⟨_, hmem i⟩, fun i => rfl, Subtype.ext ?_⟩
  simp [hcj]

end local_lemmas

end AlgebraicCurve.RegularProlongation.ORLS
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.AlgebraicCurve.RegularProlongation.ORLS"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.AlgebraicCurve"

open AlgebraicCurve.RegularProlongation.ORLS in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits)) :
    Q.ord (R.residue f) ≤ ∑ P ∈ T, D P := by
  classical
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : FiniteDimensional
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin

  have hxT : ∀ P ∈ T, (x : F) ∈ P.toValuationSubring := by
    intro P hP
    obtain ⟨-, ⟨a, ha⟩, -⟩ := (hT P).mp hP
    have h1 := add_mem (P.toValuationSubring.nonunits_subset ha) (P.algebraMap_mem' (a : L))
    rwa [sub_add_cancel] at h1
  have hDnn : ∀ P ∈ T, 0 ≤ D P := fun P hP => by
    rw [hD]
    exact ord_nonneg_of_mem P (P.mem_toValuationSubring_of_isIntegral_adjoin (hxT P hP) hfi)
  by_contra hlt
  rw [not_le] at hlt
  have hsum_nn : 0 ≤ ∑ P ∈ T, D P := Finset.sum_nonneg hDnn
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = Q.ord (R.residue f) :=
    ⟨_, Int.toNat_of_nonneg (by omega)⟩

  obtain ⟨tbar, htbar, htQ⟩ := exists_integral_uniformizer (R.residue x) hx Q hQ
  obtain ⟨t, ht, hrt⟩ := hchart tbar htbar
  have htP : ∀ P : ↥T, (t : F) ∈ P.1.toValuationSubring := fun P =>
    P.1.mem_toValuationSubring_of_isIntegral_adjoin (hxT P.1 P.2) ht

  let r : ↥T → ℕ := fun P => (D P.1).toNat
  haveI hfin' : ∀ P : ↥T, Module.Finite L
      (P.1.toValuationSubring ⧸ (maximalIdeal P.1.toValuationSubring) ^ r P) :=
    fun P => (finite_quotient_pow P.1 (r P)).1
  let tO : ∀ P : ↥T, P.1.toValuationSubring := fun P => ⟨(t : F), htP P⟩
  let Ψ : (Fin m → L) →ₗ[L]
      (∀ P : ↥T, P.1.toValuationSubring ⧸ (maximalIdeal P.1.toValuationSubring) ^ r P) :=
    Fintype.linearCombination L fun (i : Fin m) (P : ↥T) =>
      Ideal.Quotient.mkₐ L ((maximalIdeal P.1.toValuationSubring) ^ r P) (tO P ^ (i : ℕ))

  have hrank : Module.finrank L
      (∀ P : ↥T, P.1.toValuationSubring ⧸ (maximalIdeal P.1.toValuationSubring) ^ r P) <
      Module.finrank L (Fin m → L) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    have h1 : ((∑ P : ↥T, Module.finrank L
        (P.1.toValuationSubring ⧸ (maximalIdeal P.1.toValuationSubring) ^ r P) : ℕ) : ℤ) ≤
        ∑ P ∈ T, D P := by
      rw [Nat.cast_sum, ← Finset.sum_coe_sort T (fun P => D P)]
      refine Finset.sum_le_sum fun P _ => ?_
      have h3 := (finite_quotient_pow (K := L) P.1 (r P)).2
      have h2 : ((r P : ℕ) : ℤ) = D P.1 := Int.toNat_of_nonneg (hDnn P.1 P.2)
      omega
    omega

  obtain ⟨c, hcker, hc0⟩ := (Submodule.ne_bot_iff _).mp (Ψ.ker_ne_bot_of_finrank_lt hrank)
  have hcker' : ∀ P : ↥T, (∑ i : Fin m, c i • tO P ^ (i : ℕ)) ∈
      (maximalIdeal P.1.toValuationSubring) ^ r P := by
    intro P
    have := congrFun (LinearMap.mem_ker.mp hcker) P
    simp only [Ψ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      ← map_smul, ← map_sum] at this
    rw [Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  obtain ⟨j, hcj, d, hd, hdj⟩ := exists_rescale_fun A c (Function.ne_iff.mp hc0)
  let h : R.integers := ∑ i : Fin m, cst R (d i) * t ^ (i : ℕ)
  have hhF' : (h : F) = ∑ i : Fin m, (cst R (d i) : F) * (t : F) ^ (i : ℕ) := by
    simp only [h, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hhint : IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) := by
    rw [hhF']
    exact IsIntegral.sum _ fun i _ => (isIntegral_cst R x (d i)).mul (ht.pow _)
  have hhF : (h : F) = algebraMap L F (c j)⁻¹ *
      ∑ i : Fin m, algebraMap L F (c i) * (t : F) ^ (i : ℕ) := by
    rw [hhF', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_cst, hd i, map_mul, mul_assoc]

  have hvan : ∀ P : ↥T, (h : F) = 0 ∨ D P.1 ≤ P.1.ord (h : F) := by
    intro P
    have hy := le_ord_of_mem_pow P.1 (r P) _ (hcker' P)
    have hyF : ((∑ i : Fin m, c i • tO P ^ (i : ℕ) : P.1.toValuationSubring) : F) =
        ∑ i : Fin m, algebraMap L F (c i) * (t : F) ^ (i : ℕ) := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, MulMemClass.coe_mul, SubmonoidClass.coe_pow, Place.coe_algebraMap]
    rw [hhF]
    rcases eq_or_ne (∑ i : Fin m, algebraMap L F (c i) * (t : F) ^ (i : ℕ)) 0 with hs0 | hs0
    · left; rw [hs0, mul_zero]
    · right
      rcases hy with hy | hy
      · exact absurd (hyF.symm.trans hy) hs0
      · rw [P.1.ord_mul ((_root_.map_ne_zero _).mpr (inv_ne_zero hcj)) hs0, P.1.ord_algebraMap,
          zero_add, ← hyF]
        have h2 : ((r P : ℕ) : ℤ) = D P.1 := Int.toNat_of_nonneg (hDnn P.1 P.2)
        omega

  have hpk := pole_killing R x hx hfin hdeg hchart f hfi hf Q hQ D hD T hT h hhint
    (fun P hP => hvan ⟨P, hP⟩)

  have hres : R.residue h = ∑ i : Fin m,
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A (d i)) * tbar ^ (i : ℕ) := by
    simp only [h, map_sum, map_mul, map_pow, residue_cst, hrt]
  have hzero := eq_zero_of_le_ord Q htQ m (fun i => IsLocalRing.residue A (d i)) (by
    rw [← hres]
    rcases hpk with hpk | hpk
    · exact Or.inl hpk
    · right; omega)
  have h1 : IsLocalRing.residue A (d j) = 0 := hzero j
  rw [hdj, map_one] at h1
  exact one_ne_zero h1

end S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin (solution)
