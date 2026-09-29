-- Prove2me | solution 1 for AlgebraicCurve.traceIntegralAlong_of_separableAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/040d5dc9-b21f-543d-aa36-4ee2d56672f1

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_traceIntegralAlong_of_separableAlong

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring algebraAlong isScalarTower_along FiniteAlong SeparableAlong traceFunAlong_apply TraceIntegralAlong"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ord ord_mul ord_inv ord_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' toValuationSubring restrictAlong mem_toValuationSubring_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place"

private theorem _root_.AlgebraicCurve.Place.ord_neg_of_not_mem (v : Place K F) {x : F} (hx : x ∉ v.toValuationSubring) : v.ord x < 0 := by
  by_contra h
  exact hx (v.mem_toValuationSubring_of_ord_nonneg (not_lt.mp h))

p2m_export "AlgebraicCurve.Place" "ord_neg_of_not_mem"

theorem eq_of_toValuationSubring_le {v v' : Place K F}
    (h : v.toValuationSubring ≤ v'.toValuationSubring) : v' = v := by
  apply Place.ext
  refine le_antisymm ?_ h
  intro x hx'
  by_contra hx

  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ zero_mem _)
  have hax : v.ord x < 0 := v.ord_neg_of_not_mem hx

  obtain ⟨y, hy'⟩ : ∃ y : F, y ∉ v'.toValuationSubring := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact v'.ne_top' (eq_top_iff.mpr fun y _ => hall y)
  have hy : y ∉ v.toValuationSubring := fun hy => hy' (h hy)
  have hy0 : y ≠ 0 := fun h0 => hy (h0 ▸ zero_mem _)
  have hby : v.ord y < 0 := v.ord_neg_of_not_mem hy

  set a : ℕ := (-v.ord x).toNat with ha
  set b : ℕ := (-v.ord y).toNat with hb
  have haZ : (a : ℤ) = -v.ord x := by rw [ha, Int.toNat_of_nonneg (by omega)]
  have hbZ : (b : ℤ) = -v.ord y := by rw [hb, Int.toNat_of_nonneg (by omega)]
  have ha1 : 1 ≤ a := by omega
  set z : F := y ^ a * (x ^ b)⁻¹ with hz
  have hz_ord : v.ord z = 0 := by
    rw [hz, v.ord_mul (pow_ne_zero _ hy0) (inv_ne_zero (pow_ne_zero _ hx0)), v.ord_inv,
      ← zpow_natCast, ← zpow_natCast, v.ord_zpow, v.ord_zpow, haZ, hbZ]
    ring
  have hz_mem : z ∈ v'.toValuationSubring :=
    h (v.mem_toValuationSubring_of_ord_nonneg (le_of_eq hz_ord.symm))

  have hya : y ^ a ∈ v'.toValuationSubring := by
    have : y ^ a = z * x ^ b := by
      rw [hz, inv_mul_cancel_right₀ (pow_ne_zero _ hx0)]
    rw [this]
    exact mul_mem hz_mem (pow_mem hx' _)

  apply hy'
  rcases v'.toValuationSubring.mem_or_inv_mem y with hyy | hyinv
  · exact hyy
  · have : y = y ^ a * (y⁻¹) ^ (a - 1) := by
      rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hy0, Nat.cast_sub ha1]
      simp
    rw [this]
    exact mul_mem hya (pow_mem hyinv _)

end Place

theorem traceIntegralAlong_of_separableAlong' {F' : Type*} [Field F'] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) :
    TraceIntegralAlong φ hφ := by
  intro v f' hf'
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep

  set A := v.toValuationSubring with hA
  letI : Algebra A F' := ((algebraMap F F').comp (algebraMap A F)).toAlgebra
  haveI : IsScalarTower A F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsDedekindDomain (integralClosure A F') := integralClosure.isDedekindDomain A F F'
  haveI : IsFractionRing (integralClosure A F') F' :=
    integralClosure.isFractionRing_of_finite_extension F F'
  letI : Algebra K (integralClosure A F') :=
    ((algebraMap A (integralClosure A F')).comp (algebraMap K A)).toAlgebra
  haveI : IsScalarTower K (integralClosure A F') F' := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    show algebraMap K F' k = algebraMap F F' ((algebraMap K A k : A) : F)
    rw [Place.coe_algebraMap, IsScalarTower.algebraMap_apply K F F']

  have hres : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (integralClosure A F'),
      (Place.ofHeightOneSpectrum (K := K) (F := F') 𝔭).restrictAlong φ hφ = v := by
    intro 𝔭
    apply Place.eq_of_toValuationSubring_le
    intro a ha
    show algebraMap F F' a ∈ (Place.ofHeightOneSpectrum (K := K) (F := F') 𝔭).toValuationSubring
    rw [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
    have : algebraMap F F' a = algebraMap (integralClosure A F') F' (algebraMap A _ ⟨a, ha⟩) := rfl
    rw [this]
    exact 𝔭.valuation_le_one _

  have hint : IsIntegral A f' := by
    have hmem : f' ∈ (⊥ : Subalgebra (integralClosure A F') F') := by
      rw [← IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot (integralClosure A F') F',
        Algebra.mem_iInf]
      intro 𝔭
      have h1 : f' ∈ (Place.ofHeightOneSpectrum (K := K) (F := F') 𝔭).toValuationSubring :=
        hf' _ (hres 𝔭)
      rw [Place.ofHeightOneSpectrum_toValuationSubring,
        ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h1
      exact h1
    obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hmem
    rw [← hb]
    exact b.2

  have htr : IsIntegral A (Algebra.trace F F' f') := Algebra.isIntegral_trace hint
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := F)).mp htr
  rw [traceFunAlong_apply]
  show Algebra.trace F F' f' ∈ A
  rw [← hc]
  exact c.2

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_traceIntegralAlong_of_separableAlong.AlgebraicCurve in
theorem solution {K : Type*} {F : Type*} {F' : Type*}
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) :
    TraceIntegralAlong φ hφ :=
  traceIntegralAlong_of_separableAlong' φ hφ hfin hsep

end S_AlgebraicCurve_traceIntegralAlong_of_separableAlong
end P2MW
export P2MW.S_AlgebraicCurve_traceIntegralAlong_of_separableAlong (solution)
