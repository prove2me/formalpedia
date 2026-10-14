-- Prove2me | Definitions.Def_dusart_psi_433_20261014_IntegratedPsi
-- name    : dusart_psi_433_20261014_IntegratedPsi
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:18:38.557985+00:00
-- url     : https://prove2.me/theorems/4d9c4beb-01ec-42e0-8d27-68afa4777e56
-- title:
--   Dusart smoothing: Integrated Psi
-- statement:
--   This module gives the complete integrated psi component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ArithmeticKernels
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace DusartSmoothing

noncomputable def finitePsi (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n * primeStep n x

noncomputable def secondPsiPrimitive (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N,
    ArithmeticFunction.vonMangoldt n * (max (x - n) 0) ^ 2 / 2

lemma finitePsi_eq_psi (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hxN : x ≤ N) :
    finitePsi N x = Chebyshev.psi x := by
  have hN : ⌊x⌋₊ ≤ N := Nat.floor_le_of_le hxN
  have hsub : Finset.Ioc 0 ⌊x⌋₊ ⊆ Finset.Ioc 0 N :=
    Finset.Ioc_subset_Ioc le_rfl hN
  dsimp [finitePsi, Chebyshev.psi]
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n * primeStep n x := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hn'
      have hnf : ¬n ≤ ⌊x⌋₊ := by
        intro hnf
        exact hn' (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, hnf⟩)
      have hnx : ¬(n : ℝ) ≤ x := by
        intro hnx
        exact hnf ((Nat.le_floor_iff hx).mpr hnx)
      simp only [primeStep, if_neg hnx, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2
      simp only [primeStep, if_pos hnx, mul_one]

lemma integral_finitePsi (N : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    (∫ v in (0 : ℝ)..h, finitePsi N (x + v)) =
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n *
        (max (x + h - n) 0 - max (x - n) 0) := by
  dsimp [finitePsi]
  have hi : ∀ n ∈ Finset.Ioc 0 N, IntervalIntegrable
      (fun v : ℝ => ArithmeticFunction.vonMangoldt n * primeStep n (x + v)) volume 0 h := by
    intro n hn
    exact (((primeStep_mono n).comp (monotone_const.add monotone_id)).intervalIntegrable).const_mul _
  rw [intervalIntegral.integral_finsetSum hi]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul, integral_primeStep_shift x n h hh]

theorem double_integral_finitePsi (N : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    (∫ u in (0 : ℝ)..h, ∫ v in (0 : ℝ)..h, finitePsi N (x + u + v)) =
      secondPsiPrimitive N (x + 2 * h) - 2 * secondPsiPrimitive N (x + h) +
        secondPsiPrimitive N x := by
  have he : (fun u : ℝ => ∫ v in (0 : ℝ)..h, finitePsi N (x + u + v)) =
      (fun u => ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n *
        (max (x + u + h - n) 0 - max (x + u - n) 0)) := by
    funext u
    exact integral_finitePsi N (x + u) h hh
  rw [he]
  have hi : ∀ n ∈ Finset.Ioc 0 N, IntervalIntegrable
      (fun u : ℝ => ArithmeticFunction.vonMangoldt n *
        (max (x + u + h - n) 0 - max (x + u - n) 0)) volume 0 h := by
    intro n hn
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum hi]
  have hn (n : ℕ) : (∫ u in (0 : ℝ)..h, ArithmeticFunction.vonMangoldt n *
      (max (x + u + h - n) 0 - max (x + u - n) 0)) =
      ArithmeticFunction.vonMangoldt n *
        (max (x + 2 * h - n) 0 ^ 2 - 2 * max (x + h - n) 0 ^ 2 +
          max (x - n) 0 ^ 2) / 2 := by
    rw [intervalIntegral.integral_const_mul]
    have he' : (fun u : ℝ => max (x + u + h - n) 0 - max (x + u - n) 0) =
        (fun u => ∫ v in (0 : ℝ)..h, primeStep n (x + u + v)) := by
      funext u
      exact (integral_primeStep_shift (x + u) n h hh).symm
    rw [he', double_integral_primeStep x n h hh]
    ring
  simp_rw [hn]
  dsimp [secondPsiPrimitive]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hmem
  ring

theorem double_integral_psi (N : ℕ) (x h : ℝ) (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hxN : x + 2 * h ≤ N) :
    (∫ u in (0 : ℝ)..h, ∫ v in (0 : ℝ)..h, Chebyshev.psi (x + u + v)) =
      secondPsiPrimitive N (x + 2 * h) - 2 * secondPsiPrimitive N (x + h) +
        secondPsiPrimitive N x := by
  have he : (∫ u in (0 : ℝ)..h, ∫ v in (0 : ℝ)..h, Chebyshev.psi (x + u + v)) =
      ∫ u in (0 : ℝ)..h, ∫ v in (0 : ℝ)..h, finitePsi N (x + u + v) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hh] at hu
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hh] at hv
    exact (finitePsi_eq_psi N (x + u + v)
      (by linarith [hu.1, hv.1]) (by linarith [hu.2, hv.2])).symm
  rw [he]
  exact double_integral_finitePsi N x h hh

theorem doubleBoxAverage_psi_eq_second_difference (N : ℕ) (x h : ℝ)
    (hx : 0 ≤ x) (hh : 0 < h) (hxN : x + 2 * h ≤ N) :
    doubleBoxAverage Chebyshev.psi x h =
      (secondPsiPrimitive N (x + 2 * h) - 2 * secondPsiPrimitive N (x + h) +
        secondPsiPrimitive N x) / h ^ 2 := by
  dsimp [doubleBoxAverage, boxAverage]
  rw [intervalIntegral.integral_div, double_integral_psi N x h hx hh.le hxN]
  field_simp

end DusartSmoothing


