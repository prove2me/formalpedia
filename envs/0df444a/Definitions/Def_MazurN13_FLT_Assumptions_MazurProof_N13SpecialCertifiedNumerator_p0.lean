-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCertifiedNumerator_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialCertifiedNumerator_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T04:03:27.350916+00:00
-- url     : https://prove2.me/theorems/d40b849b-c9f3-4031-a4a8-718fa30bd3f4
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialCertifiedNumerator source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialCertifiedNumerator

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialCertifiedNumerator
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Encode the actual small numerator supplied by a SpecialComparison in the
finite coefficient arrays, and feed its proved norm-support condition into
the finite kernel certificate. No bounded-function enumeration is assumed.
-/

namespace MazurProof.N13SpecialCertifiedNumerator

noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair

theorem numerator_coefficients (p : K[X]) (hp : p.natDegree ≤ 4) :
    numerator (fun i : Fin 5 => p.coeff i) = p := by
  unfold numerator
  rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i) 5]
  simpa only [C_mul_X_pow_eq_monomial] using (p.as_sum_range' 5 (by omega)).symm

theorem ordinate_coefficients (q : K[X]) (hq : q.natDegree ≤ 1) :
    ordinate (fun i : Fin 2 => q.coeff i) = q := by
  have hh := (q.as_sum_range' 2 (by omega)).symm
  simpa [ordinate, Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial] using hh

theorem dvd_fixed_support (p : K[X]) (i j : ℕ) (hij : i + j ≤ 16)
    (hp : p ∣ X ^ i * (X - 1) ^ j) : p ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply dvd_trans hp
  refine ⟨X ^ (16 - i) * (X - 1) ^ (16 - j), ?_⟩
  have hi : i + (16 - i) = 16 := by omega
  have hj : j + (16 - j) = 16 := by omega
  calc
    (X : K[X]) ^ 16 * (X - 1) ^ 16 =
        (X ^ i * X ^ (16 - i)) * ((X - 1) ^ j * (X - 1) ^ (16 - j)) := by
          rw [← pow_add, ← pow_add, hi, hj]
    _ = _ := by ring

theorem exists_certified_numerator
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ (a : Fin 5 → K) (b : Fin 2 → K),
      N13SpecialAffineNorm.linear (numerator a) (ordinate b) ≠ 0 ∧
      h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) =
        h.aDen * N13SpecialAffineNorm.linear (numerator a) (ordinate b) ∧
      (∀ i : Fin 6, sixJetOrders a b i < 9 ∧
        (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
        ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0) ∧
      weightedJetCode a b = 0 := by
  obtain ⟨p, q, i, j, hp, hq, hij, hn, hcross, _, hnorm⟩ :=
    N13SpecialSmallNumerator.exists_small_supported_numerator D E F H h
  let a : Fin 5 → K := fun i => p.coeff i
  let b : Fin 2 → K := fun i => q.coeff i
  have ha : numerator a = p := numerator_coefficients p hp
  have hb : ordinate b = q := ordinate_coefficients q hq
  have hs : N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
      (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
    rw [ha, hb]
    exact dvd_fixed_support _ i j hij hnorm
  obtain ⟨hjets, hcode⟩ := supported_small_function_certificate a b hs
  exact ⟨a, b, by rwa [ha, hb], by rwa [ha, hb], hjets, hcode⟩

end
end MazurProof.N13SpecialCertifiedNumerator


