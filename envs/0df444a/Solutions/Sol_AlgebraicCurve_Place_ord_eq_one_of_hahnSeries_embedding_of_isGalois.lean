-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_eq_one_of_hahnSeries_embedding_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/98747852-e4ea-56a3-bf0e-50befe5d051b

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_HahnSeries_RamificationBound
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_eq_one_of_hahnSeries_embedding_of_isGalois
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ord_eq_one_of_hahnSeries_embedding_of_isGalois.AlgebraicCurve Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace Place.exists_ord_mul_eq_order_of_hasRamBound Place.ramificationIndex_eq_of_restrict_eq RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty RationalFunctionField.ord_placeInfty_algebraMap"
namespace Place
p2m_export "AlgebraicCurve.Place" "ord ord_coe_irreducible toValuationSubring ramificationIndex ramificationIndex_pos restrict ord_restrict ord_ofHeightOneSpectrum_ne_zero_iff exists_ord_mul_eq_order_of_hasRamBound ramificationIndex_eq_of_restrict_eq"
namespace HahnUnramAux
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

theorem algebraMap_hahn_eq_C {K L : Type*} [Field K] [Field L] [Algebra K L] (c : K) :
    (algebraMap K (HahnSeries ℚ L)) c = HahnSeries.C (algebraMap K L c) := by
  first
  | exact HahnSeries.algebraMap_apply
  | rw [HahnSeries.algebraMap_apply', IsScalarTower.algebraMap_apply K L (PowerSeries L),
      PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
  | (rw [HahnSeries.algebraMap_apply']
     have h2 : algebraMap K (PowerSeries L) c = PowerSeries.C (algebraMap K L c) := by
       simp [IsScalarTower.algebraMap_apply K L (PowerSeries L)]
     rw [h2, HahnSeries.ofPowerSeries_C])

theorem eval₂_C_single_one {L : Type*} [Field L] (q : L[X]) :
    q.eval₂ (HahnSeries.C : L →+* HahnSeries ℚ L) (HahnSeries.single (1 : ℚ) (1 : L))
      = HahnSeries.ofPowerSeries ℚ L (q : PowerSeries L) := by
  have heq : (Polynomial.eval₂RingHom (HahnSeries.C : L →+* HahnSeries ℚ L)
        (HahnSeries.single (1 : ℚ) (1 : L)))
      = (HahnSeries.ofPowerSeries ℚ L).comp (Polynomial.coeToPowerSeries.ringHom (R := L)) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, HahnSeries.ofPowerSeries_X]
  have := congrArg (fun f : L[X] →+* HahnSeries ℚ L => f q) heq
  simpa [Polynomial.coeToPowerSeries.ringHom_apply] using this

theorem order_ofPowerSeries_eq_one {L : Type*} [Field L] (q : L[X]) (h0 : q.coeff 0 = 0)
    (h1 : q.coeff 1 ≠ 0) :
    (HahnSeries.ofPowerSeries ℚ L (q : PowerSeries L)).order = 1 := by
  set x := HahnSeries.ofPowerSeries ℚ L (q : PowerSeries L) with hx
  have hc1 : x.coeff (1 : ℚ) ≠ 0 := by
    have : x.coeff ((1 : ℕ) : ℚ) = q.coeff 1 := by
      rw [hx, HahnSeries.ofPowerSeries_apply_coeff, Polynomial.coeff_coe]
    rw [Nat.cast_one] at this
    rwa [this]
  have hx0 : x ≠ 0 := fun h => hc1 (by rw [h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc1) ?_

  have hsupp : x.order ∈ x.support := by
    rw [HahnSeries.mem_support]; exact fun h => hx0 (HahnSeries.coeff_order_eq_zero.mp h)
  have hrange : x.support ⊆ Set.range (fun n : ℕ => (n : ℚ)) := by
    intro g hg
    by_contra hng
    rw [HahnSeries.mem_support, hx, HahnSeries.ofPowerSeries_apply] at hg
    exact hg (HahnSeries.embDomain_notin_range (by simpa using hng))
  obtain ⟨n, hn⟩ := hrange hsupp
  have hcn : x.coeff (n : ℚ) = q.coeff n := by
    rw [hx, HahnSeries.ofPowerSeries_apply_coeff, Polynomial.coeff_coe]
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [HahnSeries.mem_support, ← hn, hcn, h0] at hsupp
    exact hsupp rfl
  rw [← hn]
  show (1 : ℚ) ≤ (n : ℚ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0

theorem taylor_coeffs {K L : Type*} [Field K] [Field L] [Algebra K L] (p : K[X]) (a : L)
    (ha : aeval a p = 0) (ha' : aeval a (derivative p) ≠ 0) :
    ((p.map (algebraMap K L)).comp (X + C a)).coeff 0 = 0 ∧
      ((p.map (algebraMap K L)).comp (X + C a)).coeff 1 ≠ 0 := by
  set pL := p.map (algebraMap K L) with hpL
  constructor
  · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, zero_add, hpL, Polynomial.eval_map,
      ← Polynomial.aeval_def, ha]
  · have hd : ((pL.comp (X + C a)).coeff 1 : L) = (derivative (pL.comp (X + C a))).coeff 0 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [hd, Polynomial.derivative_comp]
    simp only [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
      add_zero, mul_one, one_mul]
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, zero_add, hpL, Polynomial.derivative_map,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    exact ha'

open AlgebraicCurve.RationalFunctionField in

theorem eq_finitePlace_of_ord_pos {K : Type*} [Field K] {p : K[X]} (hp : Irreducible p)
    (v : Place K (RatFunc K)) (hv : 0 < v.ord (algebraMap K[X] (RatFunc K) p)) :
    v = finitePlace K hp := by
  classical
  rcases AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty v with
    ⟨w, rfl⟩ | rfl
  · have hmem : p ∈ w.asIdeal :=
      (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp.ne_zero).mp
        hv.ne'
    have hle : Ideal.span {p} ≤ w.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hmem
    have hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
    have heq : Ideal.span {p} = w.asIdeal := hmax.eq_of_le w.isPrime.ne_top hle
    have hw : w = heightOneSpectrumOfIrreducible K hp := by
      ext1; rw [← heq, heightOneSpectrumOfIrreducible_asIdeal]
    rw [hw, finitePlace_def]
  · exfalso
    rw [AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap hp.ne_zero] at hv
    have := p.natDegree.cast_nonneg (α := ℤ)
    omega

end AlgebraicCurve.Place.HahnUnramAux

open AlgebraicCurve.Place.HahnUnramAux in

theorem solution
    {K L M : Type*} [Field K] [Field L] [Algebra K L] [Field M] [Algebra K M]
    [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
    [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]
    (p : Polynomial K) (hp : Irreducible p) (a : L)
    (ha : Polynomial.aeval a p = 0) (ha' : Polynomial.aeval a (Polynomial.derivative p) ≠ 0)
    (ψ : M →ₐ[K] HahnSeries ℚ L)
    (hψX : ψ (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
      = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L))
    (hψ : ∀ m : M, HahnSeries.HasRamBound 1 (ψ m))
    (W : AlgebraicCurve.Place K M)
    (hW : 0 < W.ord (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p))) :
    W.ord (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p)) = 1 := by
  classical
  set f₀ : RatFunc K := algebraMap (Polynomial K) (RatFunc K) p with hf₀
  set f : M := algebraMap (RatFunc K) M f₀ with hf

  set ρ : K[X] →+* HahnSeries ℚ L :=
    ψ.toRingHom.comp ((algebraMap (RatFunc K) M).comp (algebraMap K[X] (RatFunc K))) with hρ
  have hρC : ∀ c : K, ρ (C c) = HahnSeries.C (algebraMap K L c) := by
    intro c
    simp only [hρ, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
      ← IsScalarTower.algebraMap_apply K (RatFunc K) M, ψ.commutes, algebraMap_hahn_eq_C]
  have hρX : ρ X = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L) := by
    simp only [hρ, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    exact hψX
  have hρeq : ρ = Polynomial.eval₂RingHom ((HahnSeries.C : L →+* HahnSeries ℚ L).comp
      (algebraMap K L)) (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L)) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [hρC, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.coe_comp,
        Function.comp_apply]
    · rw [hρX, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  set q : L[X] := (p.map (algebraMap K L)).comp (X + C a) with hq
  have hψf : ψ f = HahnSeries.ofPowerSeries ℚ L (q : PowerSeries L) := by
    have h1 : ψ f = ρ p := by simp [hρ, hf, hf₀]
    rw [h1, hρeq, Polynomial.coe_eval₂RingHom, ← Polynomial.eval₂_map, ← eval₂_C_single_one,
      hq, Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
      add_comm]

  obtain ⟨hq0, hq1⟩ := taylor_coeffs p a ha ha'
  have horder : (ψ f).order = 1 := by
    rw [hψf]; exact order_ofPowerSeries_eq_one q hq0 hq1

  obtain ⟨W₀, g, hg, hW₀⟩ :=
    AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound ψ Nat.one_pos hψ
      ⟨f, by rw [horder]; exact one_ne_zero⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W₀.toValuationSubring
  have hϖ0 : (ϖ : M) ≠ 0 := by
    have := hϖ.ne_zero
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using this
  have hψϖ0 : ψ (ϖ : M) ≠ 0 := (map_ne_zero_iff ψ ψ.toRingHom.injective).mpr hϖ0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (ψ (ϖ : M)).order = k := by
    have hmem : (ψ (ϖ : M)).order ∈ (ψ (ϖ : M)).support := by
      rw [HahnSeries.mem_support]; exact fun h => hψϖ0 (HahnSeries.coeff_order_eq_zero.mp h)
    obtain ⟨k, hk⟩ := hψ (ϖ : M) hmem
    exact ⟨k, by rw [← hk]; simp⟩
  have hgk : g = k := by
    have := hW₀ (ϖ : M)
    rw [W₀.ord_coe_irreducible hϖ, Int.cast_one, one_mul, hk] at this
    exact this
  have hkpos : 0 < k := by exact_mod_cast (hgk ▸ hg : (0 : ℚ) < k)
  have hW₀f : W₀.ord f = 1 := by
    have h := hW₀ f
    rw [horder, hgk, ← Int.cast_mul, ← Int.cast_one, Int.cast_inj] at h
    have hk1 : k = 1 := Int.eq_one_of_mul_eq_one_left hkpos.le h
    rw [hk1, mul_one] at h
    exact h

  have hvW : W.restrict (RatFunc K) = RationalFunctionField.finitePlace K hp := by
    refine eq_finitePlace_of_ord_pos hp _ ?_
    have h := W.ord_restrict (F := RatFunc K) f₀
    have he := W.ramificationIndex_pos (F := RatFunc K)
    rw [← hf] at h
    by_contra hneg
    push_neg at hneg
    have : W.ord f ≤ 0 := by
      rw [h]; exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast he.le) hneg
    omega
  have hvW₀ : W₀.restrict (RatFunc K) = RationalFunctionField.finitePlace K hp := by
    refine eq_finitePlace_of_ord_pos hp _ ?_
    have h := W₀.ord_restrict (F := RatFunc K) f₀
    have he := W₀.ramificationIndex_pos (F := RatFunc K)
    rw [← hf, hW₀f] at h
    by_contra hneg
    push_neg at hneg
    have : (1 : ℤ) ≤ 0 := by
      rw [h]; exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast he.le) hneg
    omega
  have hres : W.restrict (RatFunc K) = W₀.restrict (RatFunc K) := hvW.trans hvW₀.symm
  have he : W.ramificationIndex (RatFunc K) = W₀.ramificationIndex (RatFunc K) :=
    AlgebraicCurve.Place.ramificationIndex_eq_of_restrict_eq W₀ W hres
  have h1 := W.ord_restrict (F := RatFunc K) f₀
  have h2 := W₀.ord_restrict (F := RatFunc K) f₀
  rw [← hf] at h1 h2
  rw [h1, he, hres, ← h2, hW₀f]

end

end S_AlgebraicCurve_Place_ord_eq_one_of_hahnSeries_embedding_of_isGalois
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_eq_one_of_hahnSeries_embedding_of_isGalois (solution)
