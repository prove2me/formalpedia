-- Prove2me | solution 1 for Arxiv2205_09234.conventional_fwi_special_case
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:56:56.909029+00:00
-- url     : https://prove2.me/submissions/63e6450c-60a0-4c89-a9c0-abcd46fd7fcb

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

set_option autoImplicit false

open Complex

namespace S73CF
open Arxiv2205_09234

lemma z_ne_one (N : ℕ) (hN : 0 < N) (j l : Fin N) (h : j ≠ l) :
    Complex.exp (2 * Real.pi * I * (((l : ℕ) : ℂ) - ((j : ℕ) : ℂ)) / (N : ℂ)) ≠ 1 := by
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have e : (((l : ℕ) : ℂ) - ((j : ℕ) : ℂ)) = n * N := by
    field_simp at hn
    linear_combination hn
  have e' : ((l : ℕ) : ℤ) - ((j : ℕ) : ℤ) = n * N := by exact_mod_cast e
  have hl := l.2; have hj := j.2
  have : n = 0 := by
    rcases lt_trichotomy n 0 with h1 | h1 | h1
    · have : n * (N:ℤ) ≤ -N := by nlinarith
      omega
    · exact h1
    · have : (N:ℤ) ≤ n * N := by nlinarith
      omega
  subst this
  apply h; ext; omega

lemma orth (N : ℕ) (hN : 0 < N) (j l : Fin N) :
    ∑ k : Fin N, dftMat N k j * starRingEnd ℂ (dftMat N k l) = if j = l then (N : ℂ) else 0 := by
  set z := Complex.exp (2 * Real.pi * I * (((l : ℕ) : ℂ) - ((j : ℕ) : ℂ)) / (N : ℂ)) with hz
  have hterm : ∀ k : Fin N, dftMat N k j * starRingEnd ℂ (dftMat N k l) = z ^ (k : ℕ) := by
    intro k
    unfold dftMat
    rw [← Complex.exp_conj, ← Complex.exp_add, hz, ← Complex.exp_nat_mul]
    congr 1
    simp only [map_neg, map_div₀, map_mul, map_natCast, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun k => z ^ k) N]
  split_ifs with h
  · subst h
    have : z = 1 := by rw [hz]; simp
    simp [this]
  · have hz1 := z_ne_one N hN j l h
    rw [geom_sum_eq hz1]
    have : z ^ N = 1 := by
      rw [hz, ← Complex.exp_nat_mul]
      rw [Complex.exp_eq_one_iff]
      refine ⟨(l : ℤ) - (j : ℤ), ?_⟩
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      push_cast
      ring
    rw [this]; simp

lemma parseval (N : ℕ) (hN : 0 < N) (a : Fin N → ℝ) :
    ∑ k, ‖dft N a k‖ ^ 2 = N * ∑ j, a j ^ 2 := by
  have hc : ((∑ k, ‖dft N a k‖ ^ 2 : ℝ) : ℂ) = ((N * ∑ j, a j ^ 2 : ℝ) : ℂ) := by
    push_cast
    have h1 : ∀ k, ((‖dft N a k‖ : ℂ)) ^ 2 = dft N a k * starRingEnd ℂ (dft N a k) := by
      intro k
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    simp only [h1]
    have hd : ∀ k, dft N a k = ∑ j, dftMat N k j * (a j : ℂ) := fun k => rfl
    calc ∑ k, dft N a k * starRingEnd ℂ (dft N a k)
        = ∑ k, ∑ j, ∑ l, (dftMat N k j * (a j : ℂ)) * (starRingEnd ℂ (dftMat N k l) * (a l : ℂ)) := by
          congr 1; funext k
          rw [hd, map_sum, Finset.sum_mul_sum]
          simp only [map_mul, Complex.conj_ofReal]
      _ = ∑ j, ∑ l, ∑ k, (dftMat N k j * (a j : ℂ)) * (starRingEnd ℂ (dftMat N k l) * (a l : ℂ)) := by
          rw [Finset.sum_comm]; congr 1; funext j; rw [Finset.sum_comm]
      _ = ∑ j, ∑ l, (a j : ℂ) * (a l : ℂ) * (if j = l then (N : ℂ) else 0) := by
          congr 1; funext j; congr 1; funext l
          rw [← orth N hN j l, Finset.mul_sum]
          congr 1; funext k; ring
      _ = (N : ℂ) * ∑ j, (a j : ℂ) ^ 2 := by
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [Finset.mul_sum]
          congr 1; funext j; ring
  exact_mod_cast hc

end S73CF

open Arxiv2205_09234 S73CF in
theorem solution (N : ℕ) (hN : 0 < N) (dt : ℝ) (hdt : 0 < dt)
    (w : Fin N → ℝ) (hw : IsFreqWeight N dt 0 w) (dm dobs : Fin N → ℝ) :
    (∀ k, w k = 1) ∧ discreteMetric N 2 w dm dobs ^ 2 = N * ∑ j, (dm j - dobs j) ^ 2 := by
  have hw1 : ∀ k, w k = 1 := fun k => by rw [hw.2 k (Or.inr le_rfl), Real.rpow_zero]
  refine ⟨hw1, ?_⟩
  have hsub : ∀ k, dft N dm k - dft N dobs k = dft N (fun j => dm j - dobs j) k := by
    intro k
    have hd : ∀ (x : Fin N → ℝ) k, dft N x k = ∑ j, dftMat N k j * (x j : ℂ) := fun x k => rfl
    rw [hd, hd, hd, ← Finset.sum_sub_distrib]
    congr 1; funext j; push_cast; ring
  unfold discreteMetric
  simp only [hw1, one_mul, hsub]
  have e : ∀ k, ‖dft N (fun j => dm j - dobs j) k‖ ^ (2:ℝ) = ‖dft N (fun j => dm j - dobs j) k‖ ^ (2:ℕ) := by
    intro k; exact_mod_cast Real.rpow_natCast _ 2
  simp only [e]
  rw [parseval N hN]
  have hnn : 0 ≤ (N:ℝ) * ∑ j, (dm j - dobs j) ^ 2 := by positivity
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
