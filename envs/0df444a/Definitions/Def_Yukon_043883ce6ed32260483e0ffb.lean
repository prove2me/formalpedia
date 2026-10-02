-- Prove2me | Definitions.Def_Yukon_043883ce6ed32260483e0ffb
-- name    : Yukon_043883ce6ed32260483e0ffb
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T07:08:29.861032+00:00
-- url     : https://prove2.me/theorems/7c9946c4-3c29-4e6a-b3d9-53a5eb938c1b
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailPole.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailPole.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailPole.lean
--
--   yukon-proof-operation:foundation-direct-2fc2de584590dfef2f246c4b30ffefd64d1fdd4271f58e2d6fc0106aeb540256
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYmExZDQzNzdkYzlmNmNhMGQ5MDJlZDlhODQzM2VmYTg0Njg5Nzk5Y2JmMzU0ZWEwYTQ1MjViYjQ0ZjZkM2JhNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTJmYzJkZTU4NDU5MGRmZWYyZjI0NmM0YjMwZmZlZmQ2NGQxZmRkNDI3MWY1OGUyZDZmYzAxMDZhZWI1NDAyNTYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8wNDM4ODNjZTZlZDMyMjYwNDgzZTBmZmIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_aa49d06014b5907015f56d9e

import Definitions.Def_Yukon_f1e62401ad2926c27064c41d

import Definitions.Def_Yukon_08c0531aef5b29722afdb50a













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN057 RCN095 RCN136 RCN156 RCN204 RCN234 RCN313
open BoundaryTailCoefficientFacts
open scoped BigOperators

noncomputable section
variable {K Ω L : Type} [Field K] [Field Ω] [Field L]

theorem map_baseNumerator_refined (ev : MvPolynomial (Fin 4) K →+* L)
    (F : MvPolynomial (Fin 4) K) (m : ℕ) :
    ev (baseNumerator F m) =
      ∑ i : Fin (m + 2), BoundaryTail.refinedMonomial (m + 2) i.val
        (ev (polyH K F)) (ev (polyG K F)) (ev (boundaryJ F))
        (ev (refinedCoefficients F m i.val)) := by
  rw [baseNumerator_refined_sum, map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [refinedMonomial, map_mul, map_pow, BoundaryTail.refinedMonomial,
    sExponent, Nat.max_zero, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega]

theorem boundary_flag_poles (V : Valuation L (WithZero (Multiplicative ℤ)))
    (x : Fin 3 → L) (r v z : ℕ) (hr : 3 ≤ r) (hv : 1 ≤ v) :
    let A := flagPole V x (⟨z, v, r - 1⟩ : FlagDegree)
    let u := flagPole V x unitAllFlag
    let t := flagPole V x unitYZFlag
    0 ≤ t ∧ t ≤ u ∧ u ≤ A ∧
      flagPole V x (⟨z, v, r - 2⟩ : FlagDegree) = A - u ∧
      flagPole V x (⟨z, v - 1, r + 1⟩ : FlagDegree) = A + 2 * u - t := by
  dsimp
  have hr1 : 1 ≤ r := by omega
  have hr2 : 2 ≤ r := by omega
  have hu0 := flagPole_nonneg V x unitAllFlag
  have ht0 := flagPole_nonneg V x unitYZFlag
  have hz0 : 0 ≤ RCN187.poleOrder V (x 2) := le_max_left _ _
  simp only [flagPole, unitAllFlag, unitYZFlag, Nat.cast_add, Nat.cast_sub hr1,
    Nat.cast_sub hr2, Nat.cast_sub hv, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat,
    zero_mul, one_mul, zero_add, add_zero] at *
  refine ⟨ht0, le_max_right _ _, ?_, ?_, ?_⟩
  · have := mul_nonneg (show 0 ≤ (r : ℤ) - 2 by omega) hu0
    have := mul_nonneg (show 0 ≤ (v : ℤ) by omega) ht0
    have := mul_nonneg (show 0 ≤ (z : ℤ) by omega) hz0
    nlinarith
  · ring
  · ring

theorem actual_tail_normalized_pole_le
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a : Ω, a ≠ 0 → V (coeff a) = 1)
    (x : Fin 3 → L) (φ : Polynomial K →+* Ω)
    (F : MvPolynomial (Fin 4) K) (m₀ m r v z p : ℕ) [CharP K p]
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) (hchar : 2 * m₀ < p)
    (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (hH : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)) ≠ 0)
    (hfirst : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (baseNumerator F m₀)) = 0) :
    let ev := (MvPolynomial.eval₂Hom coeff x).comp (surfaceMap φ)
    let A := flagPole V x (⟨z, v, r - 1⟩ : FlagDegree)
    let t := flagPole V x unitYZFlag
    let u := flagPole V x unitAllFlag
    2 * max (V (ev (polyH K F) ^ 3 * ev (baseNumerator F m) /
      ev (polyH K F) ^ (m + 1))).log 0 ≤
      2 * (((m : ℤ) + 3) * A - ((m : ℤ) + 1) * t) +
        ((m : ℤ) + 2) * max (2 * u) (t + max (V (ev (polyG K F) / ev (polyH K F))).log 0) := by
  classical
  let ev := (MvPolynomial.eval₂Hom coeff x).comp (surfaceMap φ)
  let H := ev (polyH K F)
  let G := ev (polyG K F)
  let J := ev (boundaryJ F)
  let A := flagPole V x (⟨z, v, r - 1⟩ : FlagDegree)
  let u := flagPole V x unitAllFlag
  let t := flagPole V x unitYZFlag
  have hc : ∀ a : Ω, V (coeff a) ≤ 1 := by
    intro a
    letI : Decidable (a = 0) := Classical.propDecidable _
    by_cases ha : a = 0
    · simp [ha]
    · rw [hcoeff a ha]
  obtain ⟨ht0, htu, huA, hJcap, hGcap⟩ := boundary_flag_poles V x r v z hr (by omega)
  obtain ⟨hHF, hGF, hJF⟩ := boundary_surfaceMap_flags φ F r v z (by omega) (by omega) hR hYR hAll
  have log_cap (P : MvPolynomial (Fin 3) Ω) (cap : FlagDegree)
      (hP : PolynomialInFlag cap P) (hne : MvPolynomial.eval₂Hom coeff x P ≠ 0) :
      (V (MvPolynomial.eval₂Hom coeff x P)).log ≤ flagPole V x cap := by
    have hh := valuation_eval_le_flag V coeff hc x cap P hP
    simpa only [WithZero.log_exp] using
      (WithZero.log_le_log ((Valuation.ne_zero_iff V).mpr hne) WithZero.exp_ne_zero).mpr hh
  have hA : (V H).log ≤ A := log_cap _ _ hHF hH
  have hB : G ≠ 0 → (V G).log ≤ A + 2 * u - t := by
    intro hn
    rw [← hGcap]
    exact log_cap _ _ hGF hn
  have hD : J ≠ 0 → (V J).log ≤ A - u := by
    intro hn
    rw [← hJcap]
    exact log_cap _ _ hJF hn
  have hcoeffs (k : ℕ) (hk : 1 ≤ k) (i : Fin (k + 2)) :
      V (ev (refinedCoefficients F k i.val)) ≤ WithZero.exp
        ((i.val : ℤ) * (2 * u - t) +
          ((min (2 * i.val) k : ℕ) : ℤ) * (A - u)) := by
    rw [← hJcap]
    exact refinedCoefficients_value_le V coeff hc x φ F k i.val r v z hk
      (by omega) (by omega) hv hR hYR hAll
  have hconstraint : G ≠ 0 → J ≠ 0 →
      (A - (V H).log) - (A + 2 * u - t - (V G).log) ≤ 2 * (A - u - (V J).log) := by
    intro hG hJ
    apply BoundaryTail.first_tail_shifted_constraint V (n := m₀ + 2) (by omega)
      H G J hH hG hJ (fun i => ev (refinedCoefficients F m₀ i.val)) A (A + 2 * u - t) (A - u) (hD hJ)
    · intro i
      simpa only [show m₀ + 2 - 2 = m₀ by omega,
        show A + 2 * u - t - A = 2 * u - t by ring] using hcoeffs m₀ hm₀ i
    · simp only [ev, RingHom.comp_apply, refinedCoefficients_zero,
        surfaceMap_C, MvPolynomial.eval₂Hom_C]
      apply hcoeff
      have hn := signedOddScalar_ne_zero (K := K) m₀ hchar
      intro hz
      apply hn
      apply (φ.comp Polynomial.C).injective
      simpa using hz
    · rw [← map_baseNumerator_refined ev F m₀]
      exact hfirst
  have hresult := BoundaryTail.normalized_tail_pole_le V (n := m + 2) (by omega) H G J hH
    (fun i => ev (refinedCoefficients F m i.val)) A u t ht0 htu huA hA hB hD hconstraint
    (by intro i; simpa only [Nat.add_sub_cancel] using hcoeffs m hm i)
  rw [← map_baseNumerator_refined ev F m] at hresult
  simp only [show m + 2 - 1 = m + 1 by omega] at hresult
  convert hresult using 1 <;> push_cast <;> ring

def normalFlag (m r v z : ℕ) : FlagDegree :=
  ⟨(m + 3) * z, (m + 3) * v - (m + 1), (m + 3) * (r - 1)⟩

theorem normalFlag_pole (V : Valuation L (WithZero (Multiplicative ℤ)))
    (x : Fin 3 → L) (m r v z : ℕ) (hv : 1 ≤ v) :
    flagPole V x (normalFlag m r v z) =
      ((m : ℤ) + 3) * flagPole V x (⟨z, v, r - 1⟩ : FlagDegree) -
        ((m : ℤ) + 1) * flagPole V x unitYZFlag := by
  have hsub : m + 1 ≤ (m + 3) * v := by nlinarith
  simp only [normalFlag, flagPole, unitYZFlag, Nat.cast_sub hsub,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  ring

theorem global_tail_value (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a : Ω, a ≠ 0 → V (coeff a) = 1)
    (x : Fin 3 → L) (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (m : ℕ) :
    V (MvPolynomial.eval₂Hom coeff x (RCN086.globalTailCut φ F (m + 2)) /
      (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F))) ^ (m + 1)) =
    V ((MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F))) ^ 3 *
      MvPolynomial.eval₂Hom coeff x (surfaceMap φ (baseNumerator F m)) /
      (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F))) ^ (m + 1)) := by
  have hunit := hcoeff _ (RCN086.tail_scalar_ne_zero φ hφ (m + 2))
  simp only [map_pow] at hunit
  rw [RCN086.globalTailCut_eq, numerator_eq_H_cube]
  simp only [map_mul, map_pow, MvPolynomial.eval₂Hom_C, map_div₀, hunit, mul_one]

theorem global_tail_normalized_pole_le
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a : Ω, a ≠ 0 → V (coeff a) = 1)
    (x : Fin 3 → L) (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (m₀ m r v z p : ℕ) [CharP K p]
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) (hchar : 2 * m₀ < p)
    (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (hH : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)) ≠ 0)
    (hfirst : MvPolynomial.eval₂Hom coeff x (RCN086.globalTailCut φ F (m₀ + 2)) = 0) :
    2 * RCN187.poleOrder V
      (MvPolynomial.eval₂Hom coeff x (RCN086.globalTailCut φ F (m + 2)) /
        (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F))) ^ (m + 1)) ≤
      2 * flagPole V x (normalFlag m r v z) + ((m : ℤ) + 2) *
        max (2 * flagPole V x unitAllFlag) (flagPole V x unitYZFlag +
          RCN187.poleOrder V (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyG K F)) /
            MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)))) := by
  have hscalar : coeff ((-φ Polynomial.X) ^ (m₀ + 2)) ≠ 0 := by
    intro hz
    have hh := hcoeff _ (RCN086.tail_scalar_ne_zero φ hφ (m₀ + 2))
    rw [hz, map_zero] at hh
    exact zero_ne_one hh
  simp only [map_pow] at hscalar
  have hbase : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (baseNumerator F m₀)) = 0 := by
    rw [RCN086.globalTailCut_eq, numerator_eq_H_cube] at hfirst
    simp only [map_mul, map_pow, MvPolynomial.eval₂Hom_C] at hfirst
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hfirst).resolve_right hscalar)).resolve_left
      (pow_ne_zero 3 hH)
  have h := actual_tail_normalized_pole_le V coeff hcoeff x φ F m₀ m r v z p
    hm₀ hm hchar hr hv hR hYR hAll hH hbase
  rw [normalFlag_pole V x m r v z (by omega)]
  simp only [RCN187.poleOrder, global_tail_value V coeff hcoeff x φ hφ F m, max_comm]
  simpa only [max_comm, RingHom.comp_apply] using h

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra


