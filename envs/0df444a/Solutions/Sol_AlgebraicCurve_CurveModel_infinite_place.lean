-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.infinite_place
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a534e0d2-2bcd-568f-883b-b95c7170424b

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_infinite_place
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

universe u v

open AlgebraicGeometry AlgebraicCurve

namespace InfinitePlace604

set_option linter.unusedSectionVars false

open IsLocalRing AlgebraicCurve

section FieldSide

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

theorem ord_nonneg_of_mem (v : Place K L) {f : L} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hϖ
  have hcoe : f = ((u : v.toValuationSubring) : L) * ((ϖ : L) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hϖ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K L) {f : L} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (ϖ : v.toValuationSubring).2 _)

theorem ord_coe_eq_zero_iff_isUnit (v : Place K L) (a : v.toValuationSubring) (ha : (a : L) ≠ 0) :
    v.ord (a : L) = 0 ↔ IsUnit a := by
  rw [← v.adicValuation_coe_eq_one_iff]
  have hne := v.adicValuation_ne_zero ha
  show -(WithZero.log (v.adicValuation (a : L))) = 0 ↔ _
  constructor
  · intro h
    have h' : WithZero.log (v.adicValuation (a : L)) = 0 := by omega
    rw [← WithZero.exp_log hne, h', WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one, neg_zero]

theorem mem_maximalIdeal_iff_ord_pos (v : Place K L) (a : v.toValuationSubring) (ha : (a : L) ≠ 0) :
    a ∈ maximalIdeal v.toValuationSubring ↔ 0 < v.ord (a : L) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← ord_coe_eq_zero_iff_isUnit v a ha]
  have := ord_nonneg_of_mem v a.2
  omega

def VanishesAt (w : Place K L) (z : L) : Prop :=
  ∃ h : z ∈ w.toValuationSubring, (⟨z, h⟩ : w.toValuationSubring) ∈ maximalIdeal w.toValuationSubring

theorem VanishesAt.sub {w : Place K L} {a b : L} (ha : VanishesAt w a) (hb : VanishesAt w b) :
    VanishesAt w (a - b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  exact ⟨sub_mem ha1 hb1, sub_mem ha2 hb2⟩

theorem vanishesAt_zero (w : Place K L) : VanishesAt w (0 : L) :=
  ⟨zero_mem _, by
    have h0 : (⟨(0 : L), zero_mem _⟩ : w.toValuationSubring) = 0 := rfl
    rw [h0]
    exact zero_mem _⟩

theorem vanishesAt_of_mem_maximalIdeal {w : Place K L} {a : w.toValuationSubring}
    (ha : a ∈ maximalIdeal w.toValuationSubring) : VanishesAt w (a : L) :=
  ⟨a.2, by simpa using ha⟩

theorem vanishesAt_of_ord_pos {w : Place K L} {z : L} (hz : 0 < w.ord z) : VanishesAt w z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact vanishesAt_zero w
  · have hmem := mem_of_ord_nonneg w hz0 hz.le
    exact ⟨hmem, (mem_maximalIdeal_iff_ord_pos w ⟨z, hmem⟩ hz0).2 hz⟩

theorem VanishesAt.eq_zero_or_ord_pos {w : Place K L} {z : L} (h : VanishesAt w z) :
    z = 0 ∨ 0 < w.ord z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact Or.inl rfl
  · obtain ⟨h1, h2⟩ := h
    exact Or.inr ((mem_maximalIdeal_iff_ord_pos w ⟨z, h1⟩ hz0).1 h2)

theorem finite_setOf_ord_ne_zero [HasPrincipalDivisors K L] {g : L} (hg : g ≠ 0) :
    {w : Place K L | w.ord g ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  refine Set.Finite.subset D.support.finite_toSet fun w hw => ?_
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD w]
  exact hw

theorem exists_sub_algebraMap_mem_maximalIdeal [IsAlgClosed K] (v : Place K L)
    [Module.Finite K v.ResidueField] (a : v.toValuationSubring) :
    ∃ c : K, a - algebraMap K v.toValuationSubring c ∈ maximalIdeal v.toValuationSubring := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨c, hc⟩ := hbij.2 (residue v.toValuationSubring a)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc]
  exact IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c

theorem exists_ord_pos_of_ord_neg [IsAlgClosed K] [IsCurveOver K L] {g : L} (hg : g ≠ 0)
    {w₀ : Place K L} (hneg : w₀.ord g < 0) : ∃ w : Place K L, 0 < w.ord g := by
  classical
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  by_contra hcon
  push_neg at hcon
  have hdeg1 : ∀ w : Place K L, w.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hw0 : w₀ ∈ D.support := by
    rw [Finsupp.mem_support_iff, hD]
    omega
  have hlt : Divisor.degree D < 0 := by
    have hsum : Divisor.degree D = D.sum (fun v n => n * (v.deg : ℤ)) := by
      simp only [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight]
    rw [hsum]
    simp only [hdeg1, Nat.cast_one, mul_one]
    rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hw0]
    have h1 : D w₀ < 0 := by rw [hD]; exact hneg
    have h2 : ∑ v ∈ D.support.erase w₀, D v ≤ 0 :=
      Finset.sum_nonpos fun v _ => by rw [hD]; exact hcon v
    omega
  omega

theorem infinite_place [IsAlgClosed K] [IsCurveOver K L] (w₀ : Place K L) : Infinite (Place K L) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w₀.toValuationSubring
  set t : L := ((ϖ : L))⁻¹ with ht_def
  have ht : w₀.ord t = -1 := by rw [ht_def, Place.ord_inv, w₀.ord_coe_irreducible hϖ]
  have ht_not_mem : t ∉ w₀.toValuationSubring := fun h => by
    have := ord_nonneg_of_mem w₀ h
    omega
  have hne : ∀ c : K, t - algebraMap K L c ≠ 0 := fun c h0 =>
    ht_not_mem (by rw [sub_eq_zero.mp h0]; exact w₀.algebraMap_mem' c)
  have hneg : ∀ c : K, w₀.ord (t - algebraMap K L c) < 0 := by
    intro c
    by_contra h
    push_neg at h
    have hmem : t - algebraMap K L c ∈ w₀.toValuationSubring := mem_of_ord_nonneg w₀ (hne c) h
    exact ht_not_mem (by simpa using add_mem hmem (w₀.algebraMap_mem' c))
  choose wc hwc using fun c => exists_ord_pos_of_ord_neg (hne c) (hneg c)
  haveI : Infinite K := inferInstance
  refine Infinite.of_injective wc fun c c' h => ?_
  by_contra hcc
  have h1 : 0 < (wc c).ord (t - algebraMap K L c) := hwc c
  have h2 : 0 < (wc c).ord (t - algebraMap K L c') := by rw [h]; exact hwc c'
  have hd := (vanishesAt_of_ord_pos h2).sub (vanishesAt_of_ord_pos h1)
  have hval : t - algebraMap K L c' - (t - algebraMap K L c) = algebraMap K L (c - c') := by
    rw [map_sub]; ring
  rw [hval] at hd
  rcases hd.eq_zero_or_ord_pos with h0 | hpos
  · exact hcc (sub_eq_zero.mp ((map_eq_zero _).mp h0)).symm.symm
  ·
    have hu : IsUnit (algebraMap K (wc c).toValuationSubring (c - c')) :=
      (IsUnit.mk0 _ (sub_ne_zero.2 (fun e => hcc e))).map _
    have hz : ((algebraMap K (wc c).toValuationSubring (c - c') : (wc c).toValuationSubring) : L) ≠ 0 := by
      rw [Place.coe_algebraMap]; exact (map_ne_zero _).2 (sub_ne_zero.2 fun e => hcc e)
    have := (ord_coe_eq_zero_iff_isUnit (wc c) _ hz).2 hu
    rw [Place.coe_algebraMap] at this
    omega

theorem eq_zero_of_vanishesAt_off_finite [IsAlgClosed K] [IsCurveOver K L] [Nonempty (Place K L)]
    {g : L} (S : Set (Place K L)) (hS : S.Finite) (h : ∀ w, w ∉ S → VanishesAt w g) : g = 0 := by
  by_contra hg
  haveI := infinite_place (K := K) (Classical.arbitrary (Place K L))
  have hT := finite_setOf_ord_ne_zero (K := K) hg
  have hsub : (Set.univ : Set (Place K L)) ⊆ S ∪ {w | w.ord g ≠ 0} := fun w _ => by
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · rcases (h w hw).eq_zero_or_ord_pos with h0 | hpos
      · exact absurd h0 hg
      · exact Or.inr hpos.ne'
  exact Set.infinite_univ ((hS.union hT).subset hsub)

theorem mem_maximalIdeal_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (x : R) :
    x ∈ maximalIdeal R ↔ e x ∈ maximalIdeal S := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx hu; exact hx (by simpa using hu.map e.symm)
  · intro hx hu; exact hx (hu.map e)

end FieldSide

section ModelSide

open CategoryTheory AlgebraicGeometry AlgebraicCurve

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

theorem nonempty_place [IsAlgClosed K] (M : CurveModel K L) : Nonempty (Place K L) := by
  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  have hne : (closedPoints M.C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hJ := JacobsonSpace.closure_inter_closedPoints (X := M.C) (Z := Set.univ) isClosed_univ
    rw [h, Set.inter_empty, closure_empty] at hJ
    exact Set.empty_ne_univ hJ
  obtain ⟨z, hz⟩ := hne
  exact ⟨M.placeOfPoint ⟨z, hz⟩⟩

end ModelSide

end InfinitePlace604

open AlgebraicGeometry AlgebraicCurve in
theorem solution {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]
    (M : CurveModel K F) : Infinite (Place K F) := by
  haveI : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨w₀⟩ := InfinitePlace604.nonempty_place M
  exact InfinitePlace604.infinite_place w₀

end S_AlgebraicCurve_CurveModel_infinite_place
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_infinite_place (solution)
