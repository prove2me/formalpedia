-- Prove2me | solution 1 for AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord_sub_pred
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a207b9f4-74c8-5f1c-90ba-baca011cbd26

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_sub_pred
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_sub_pred.AlgebraicCurve"

section Generic

open nonZeroDivisors

namespace Algebra p2m_export "Algebra" "trace algebraMap mem_top mem_iInf traceForm_apply smul_def mem_bot" end Algebra
p2m_open_scoped "Algebra" in

theorem Algebra.trace_mem_of_mul_differentIdeal_subset
    {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    (h : L) (H : ∀ d ∈ differentIdeal A B, ∃ c : B, algebraMap B L c = h * algebraMap B L d) :
    ∃ a : A, algebraMap A K a = Algebra.trace K L h := by
  have hD : ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L)
      = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹ :=
    coeIdeal_differentIdeal A K L B
  have hdual : FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)
      = ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L)⁻¹ := by
    rw [hD, inv_inv]
  have hne : ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L) ≠ 0 := by
    rw [hD]; exact inv_ne_zero (FractionalIdeal.dual_ne_zero A K one_ne_zero)
  have hmem : h ∈ FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) := by
    rw [hdual, FractionalIdeal.mem_inv_iff hne]
    intro y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal B⁰).mp hy
    obtain ⟨c, hc⟩ := H d hd
    exact (FractionalIdeal.mem_one_iff B⁰).mpr ⟨c, hc⟩
  have h1 : (1 : L) ∈ (1 : FractionalIdeal B⁰ L) :=
    (FractionalIdeal.mem_one_iff B⁰).mpr ⟨1, map_one _⟩
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_dual (I := (1 : FractionalIdeal B⁰ L)) one_ne_zero).mp hmem 1 h1
  refine ⟨a, ?_⟩
  rw [ha, Algebra.traceForm_apply, mul_one]

theorem mem_pow_ramificationIdx_sub_one_of_mem_differentIdeal
    {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [Module.Finite A B]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B)
    {d : B} (hd : d ∈ differentIdeal A B) :
    d ∈ P ^ (p.ramificationIdx' P - 1) := by
  by_cases he : p.ramificationIdx' P = 0
  · rw [he, Nat.zero_sub, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  have hdvd : P ^ (p.ramificationIdx' P - 1) ∣ differentIdeal A B :=
    pow_sub_one_dvd_differentIdeal_aux A K L P he hp
      (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)
  exact Ideal.dvd_iff_le.mp hdvd hd

end Generic

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FiniteAlong Place.ramificationIndexAlong Place.ord_restrictAlong SeparableAlong Place Place.ord_zero IsCurveOver Place.integralClosureAt Place.mem_iff_ord_nonneg Place.ramificationIndex_eq_ramificationIdx_fiberCenter"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong ord_restrictAlong ramificationIndex ramificationIndex_pos restrict ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow toValuationSubring center integralClosureAt maximalIdeal_ne_bot fiberCenter toValuationSubring_eq_of_restrict_eq placeOfPrime placeOfPrime_toValuationSubring restrict_placeOfPrime mem_iff_ord_nonneg ramificationIndex_eq_ramificationIdx_fiberCenter"
namespace TraceCodiff
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone

  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega

  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega

  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring

  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega

  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega

  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel

  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  refine eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  ·
    intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  ·
    obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  ·
    intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    show 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
    have hmem : y ∈ w.toValuationSubring ↔ (fiberCenter F' v hw).valuation F' y ≤ 1 := by
      rw [toValuationSubring_eq_of_restrict_eq hw,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact Iff.rfl
    rw [hmem]
    constructor
    · intro h
      calc (fiberCenter F' v hw).valuation F' y
          = exp (log ((fiberCenter F' v hw).valuation F' y)) := (exp_log hy0).symm
        _ ≤ exp 0 := by rw [exp_le_exp]; omega
        _ = 1 := exp_zero
    · intro h
      have h1 : exp (log ((fiberCenter F' v hw).valuation F' y)) ≤ exp 0 := by
        rw [exp_log hy0, exp_zero]
        exact h
      rw [exp_le_exp] at h1
      omega

theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n := by
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hc
  rw [← neg_log_valuation_fiberCenter_eq_ord hw hcF,
    HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have h0 : (fiberCenter F' v hw).intValuation c ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ c hc
  constructor
  · intro h
    calc (fiberCenter F' v hw).intValuation c
        = exp (log ((fiberCenter F' v hw).intValuation c)) := (exp_log h0).symm
      _ ≤ exp (-(n : ℤ)) := by rw [exp_le_exp]; omega
  · intro h
    have h1 : exp (log ((fiberCenter F' v hw).intValuation c)) ≤ exp (-(n : ℤ)) := by
      rw [exp_log h0]
      exact h
    rw [exp_le_exp] at h1
    omega

end ValuationDictionary

section Core

variable {v : Place K F}

theorem sub_one_le_ord_of_mem_differentIdeal {w : Place K F'} (hw : w.restrict F = v)
    {d : integralClosureAt F' v}
    (hd : d ∈ differentIdeal v.toValuationSubring (integralClosureAt F' v)) (hd0 : d ≠ 0) :
    (w.ramificationIndex F : ℤ) - 1 ≤ w.ord (algebraMap (integralClosureAt F' v) F' d) := by
  have hE := ramificationIndex_eq_ramificationIdx_fiberCenter v hw
  have hmem : d ∈ (fiberCenter F' v hw).asIdeal ^
      ((IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal - 1) :=
    mem_pow_ramificationIdx_sub_one_of_mem_differentIdeal (K := F) (L := F')
      (maximalIdeal_ne_bot v) _ hd
  have h1 := (le_ord_iff_mem_pow_fiberCenter hw hd0 _).mpr hmem
  have hpos : 0 < w.ramificationIndex F := w.ramificationIndex_pos
  rw [← hE] at h1
  rw [Nat.cast_sub (by omega)] at h1
  simpa using h1

theorem exists_integralClosureAt_eq_of_forall_mem (v : Place K F) {f : F'}
    (hf : ∀ w : Place K F', w.restrict F = v → f ∈ w.toValuationSubring) :
    ∃ c : integralClosureAt F' v, algebraMap (integralClosureAt F' v) F' c = f := by
  have hmem : f ∈ (⊥ : Subalgebra (integralClosureAt F' v) F') := by
    rw [← IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot (integralClosureAt F' v) F',
      Algebra.mem_iInf]
    intro P
    have h1 : f ∈ (placeOfPrime (K := K) P).toValuationSubring := hf _ (restrict_placeOfPrime P)
    rw [placeOfPrime_toValuationSubring] at h1
    exact h1
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hmem
  exact ⟨c, hc⟩

theorem trace_mem_of_forall_neg_sub_one_le_ord (v : Place K F) (h : F')
    (hh : ∀ w : Place K F', w.restrict F = v → -((w.ramificationIndex F : ℤ) - 1) ≤ w.ord h) :
    Algebra.trace F F' h ∈ v.toValuationSubring := by
  have H : ∀ d ∈ differentIdeal v.toValuationSubring (integralClosureAt F' v),
      ∃ c : integralClosureAt F' v, algebraMap (integralClosureAt F' v) F' c
        = h * algebraMap (integralClosureAt F' v) F' d := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact ⟨0, by simp⟩
    rcases eq_or_ne h 0 with rfl | hh0
    · exact ⟨0, by simp⟩
    apply exists_integralClosureAt_eq_of_forall_mem v
    intro w hw
    have hdF : algebraMap (integralClosureAt F' v) F' d ≠ 0 := by
      simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hd0
    apply (w.mem_iff_ord_nonneg (mul_ne_zero hh0 hdF)).mpr
    rw [w.ord_mul hh0 hdF]
    have h1 := hh w hw
    have h2 := sub_one_le_ord_of_mem_differentIdeal hw hd hd0
    linarith
  obtain ⟨a, ha⟩ := Algebra.trace_mem_of_mul_differentIdeal_subset
    (A := v.toValuationSubring) (K := F) (L := F') (B := integralClosureAt F' v) h H
  rw [← ha]
  exact a.2

end Core

end AlgebraicCurve.Place.TraceCodiff

end

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FiniteAlong Place.ramificationIndexAlong Place.ord_restrictAlong SeparableAlong Place Place.ord_zero IsCurveOver Place.integralClosureAt Place.mem_iff_ord_nonneg Place.ramificationIndex_eq_ramificationIdx_fiberCenter"
namespace TraceCodiffAlong
p2m_open "AlgebraicCurve"

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']

theorem exists_ord_eq_one (x : Place k F) : ∃ π : F, x.ord π = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  exact ⟨(π : F), x.ord_coe_irreducible hπ⟩

theorem ord_nonneg_of_mem' (v : Place k F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases h0 : f = 0
  · rw [h0, Place.ord_zero]
  · exact (Place.mem_iff_ord_nonneg v h0).mp hf

theorem ord_pow' (v : Place k F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

theorem main (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ)
    (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (a : ℤ) (ha : 0 ≤ a) (g : F')
    (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a)
      - ((Place.ramificationIndexAlong φ y : ℤ) - 1) ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    -a ≤ x.ord (Algebra.trace F F' g) := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : FiniteDimensional F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  show -a ≤ x.ord (Algebra.trace F F' g)

  by_cases hT0 : Algebra.trace F F' g = 0
  · rw [hT0, Place.ord_zero]; linarith
  have hg0 : g ≠ 0 := by
    intro h; apply hT0; rw [h, map_zero]

  obtain ⟨π, hπ⟩ := exists_ord_eq_one x
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hπ; exact zero_ne_one hπ
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha

  set u : F' := φ (π ^ n) * g with hu
  have hφπ : φ (π ^ n) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ ((map_ne_zero φ).mpr hπ0)
  have hu0 : u ≠ 0 := mul_ne_zero hφπ hg0
  have hbound : ∀ y : Place k F', y.restrict F = x →
      -((y.ramificationIndex F : ℤ) - 1) ≤ y.ord u := by
    intro y hy
    have hy' : y.restrictAlong φ hφ = x := hy
    have hyS : y ∈ S := (hS y).mpr hy'
    have he : Place.ramificationIndexAlong φ y = y.ramificationIndex F := rfl
    rw [hu, y.ord_mul hφπ hg0, Place.ord_restrictAlong φ hφ y (π ^ n), hy', ord_pow', hπ, mul_one, he]
    have := hg y hyS
    rw [he] at this
    push_cast at this ⊢
    linarith

  have htr : Algebra.trace F F' u ∈ x.toValuationSubring :=
    Place.TraceCodiff.trace_mem_of_forall_neg_sub_one_le_ord x u hbound

  have hTu : Algebra.trace F F' u = π ^ n * Algebra.trace F F' g := by
    have e1 : u = (π ^ n) • g := by rw [hu, Algebra.smul_def]; rfl
    rw [e1, map_smul, smul_eq_mul]
  rw [hTu] at htr
  have h0 := ord_nonneg_of_mem' x htr
  rw [x.ord_mul (pow_ne_zero _ hπ0) hT0, ord_pow', hπ, mul_one] at h0
  linarith

end AlgebraicCurve.TraceCodiffAlong

theorem solution
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (a : ℤ) (ha : 0 ≤ a) (g : F')
    (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) - ((Place.ramificationIndexAlong φ y : ℤ) - 1) ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    -a ≤ x.ord (Algebra.trace F F' g) :=
  AlgebraicCurve.TraceCodiffAlong.main φ hφ hfin hsep x S hS a ha g hg

end S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_sub_pred
end P2MW
export P2MW.S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_sub_pred (solution)
