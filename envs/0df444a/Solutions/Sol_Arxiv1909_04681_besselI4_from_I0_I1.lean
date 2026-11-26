-- Prove2me | solution 1 for Arxiv1909_04681.besselI4_from_I0_I1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:55:20.602018+00:00
-- url     : https://prove2.me/submissions/e6ae17a9-803c-412e-b9d5-611089570d55

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

set_option autoImplicit false

open Filter Topology

namespace S78BI
open Arxiv1909_04681

lemma cval (n k : ℕ) (j : ℤ) (hj : j = n + 2 * k) :
    besselCoeff j n = 1 / ((2:ℝ) ^ (n + 2 * k) * ((k.factorial : ℝ) * ((n + k).factorial : ℝ))) := by
  subst hj
  unfold besselCoeff
  rw [if_pos ⟨by omega, ⟨k, by ring⟩⟩]
  have h1 : (((n:ℤ) + 2 * k - n) / 2) = ((k : ℕ) : ℤ) := by omega
  have h2 : (((n:ℤ) + 2 * k + n) / 2) = ((n + k : ℕ) : ℤ) := by push_cast; omega
  have h3 : ((n:ℤ) + 2 * k) = ((n + 2 * k : ℕ) : ℤ) := by push_cast; ring
  rw [h1, h2, Int.toNat_natCast, Int.toNat_natCast, h3, Int.toNat_natCast]

lemma cz (j : ℤ) (n : ℕ) (h : ¬((n:ℤ) ≤ j ∧ Even (j - n))) : besselCoeff j n = 0 := if_neg h

lemma summ (n : ℕ) (z : ℝ) :
    Summable (fun k : ℕ => (z ^ 2 / 4) ^ k / ((k.factorial : ℝ) * ((n + k).factorial : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (Real.summable_pow_div_factorial (z ^ 2 / 4))
  have h1 : (1 : ℝ) ≤ ((n + k).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  apply div_le_div_of_nonneg_left (by positivity) h2
  nlinarith

lemma hasI (n : ℕ) (z : ℝ) :
    HasSum (fun k : ℕ => besselCoeff ((n + 2 * k : ℕ) : ℤ) n * z ^ (n + 2 * k)) (besselI n z) := by
  have := (summ n z).hasSum.mul_left ((z / 2) ^ n)
  rw [show (fun k : ℕ => besselCoeff ((n + 2 * k : ℕ) : ℤ) n * z ^ (n + 2 * k)) =
      (fun k : ℕ => (z / 2) ^ n * ((z ^ 2 / 4) ^ k / ((k.factorial : ℝ) * ((n + k).factorial : ℝ))))
      from funext fun k => ?_]
  · exact this
  · rw [cval n k _ (by push_cast; ring)]
    have h2 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have h3 : (0 : ℝ) < ((n + k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_pow, div_pow, ← pow_mul, pow_add, pow_add, pow_mul, pow_mul]
    field_simp
    ring

lemma fac3 (m : ℕ) : (((m + 3).factorial : ℕ) : ℝ) = (m + 3) * (m + 2) * (m + 1) * m.factorial := by
  rw [show m + 3 = (m + 2) + 1 from rfl, Nat.factorial_succ, show m + 2 = (m + 1) + 1 from rfl,
    Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring

lemma iden (j : ℤ) : 1 * besselCoeff j 0 + (-8) * besselCoeff (j + 1) 1 + 24 * besselCoeff (j + 2) 0 +
        (-48) * besselCoeff (j + 3) 1 = besselCoeff j 4 := by
  rcases Int.even_or_odd' j with ⟨t, rfl | rfl⟩
  · by_cases ht : t ≤ -2
    · rw [cz _ _ (fun ⟨h, _⟩ => by omega), cz _ _ (fun ⟨h, _⟩ => by omega),
        cz _ _ (fun ⟨h, _⟩ => by omega), cz _ _ (fun ⟨h, _⟩ => by omega),
        cz _ _ (fun ⟨h, _⟩ => by omega)]; ring
    by_cases h1 : t = -1
    · subst h1; norm_num [besselCoeff, Int.even_iff] <;> simp only [Int.reduceToNat] <;> norm_num [Nat.factorial]
    by_cases h0 : t = 0
    · subst h0; norm_num [besselCoeff, Int.even_iff] <;> simp only [Int.reduceToNat] <;> norm_num [Nat.factorial]
    by_cases h1' : t = 1
    · subst h1'; norm_num [besselCoeff, Int.even_iff] <;> simp only [Int.reduceToNat] <;> norm_num [Nat.factorial]
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, t = m + 2 := ⟨(t - 2).toNat, by omega⟩
    rw [cval 0 (m + 2) _ (by push_cast; ring), cval 1 (m + 2) _ (by push_cast; ring),
      cval 0 (m + 3) _ (by push_cast; ring), cval 1 (m + 3) _ (by push_cast; ring),
      cval 4 m _ (by push_cast; ring)]
    rw [show 0 + (m + 2) = (m + 1) + 1 by ring, show 1 + (m + 2) = m + 3 by ring,
      show 0 + (m + 3) = m + 3 by ring, show 1 + (m + 3) = (m + 3) + 1 by ring,
      show 4 + m = (m + 3) + 1 by ring]
    simp only [Nat.factorial_succ (m + 1), Nat.factorial_succ (m + 3), Nat.factorial_succ m]
    push_cast
    rw [fac3]
    have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    field_simp
    ring
  · rw [cz _ _ (fun ⟨_, ⟨r, hr⟩⟩ => by omega), cz _ _ (fun ⟨_, ⟨r, hr⟩⟩ => by omega),
      cz _ _ (fun ⟨_, ⟨r, hr⟩⟩ => by omega), cz _ _ (fun ⟨_, ⟨r, hr⟩⟩ => by omega),
      cz _ _ (fun ⟨_, ⟨r, hr⟩⟩ => by omega)]; ring


lemma part5 (z : ℝ) (hz : 0 < z) : besselI 4 z = besselI4Tilde 1 (-8) 24 (-48) z := by
  have hz0 : z ≠ 0 := hz.ne'
  set c0 : ℕ → ℝ := fun k => besselCoeff (2 * (k : ℤ)) 0 with hc0
  set c1 : ℕ → ℝ := fun k => besselCoeff (2 * (k : ℤ) + 1) 1 with hc1
  have h0 : HasSum (fun k : ℕ => c0 k * z ^ (2 * k)) (besselI 0 z) := by
    have := hasI 0 z
    refine this.congr_fun (fun k => ?_)
    simp only [hc0, zero_add]; push_cast; rfl
  have h1 : HasSum (fun k : ℕ => c1 k * z ^ (2 * k)) (besselI 1 z / z) := by
    have := (hasI 1 z).div_const z
    refine this.congr_fun (fun k => ?_)
    simp only [hc1]; push_cast
    rw [show (1 : ℤ) + 2 * k = 2 * k + 1 by ring, pow_add, pow_one]; field_simp
  set a : ℕ → ℝ := fun k => (c0 k - 8 * c1 k) * z ^ (2 * k) with ha_def
  set b : ℕ → ℝ := fun k => (24 * c0 k - 48 * c1 k) * z ^ (2 * k) / z ^ 2 with hb_def
  have ha : HasSum a (besselI 0 z - 8 * (besselI 1 z / z)) := by
    have := h0.sub (h1.mul_left 8)
    refine this.congr_fun (fun k => ?_)
    simp only [ha_def]; ring
  have hb : HasSum b ((24 * besselI 0 z - 48 * (besselI 1 z / z)) / z ^ 2) := by
    have := ((h0.mul_left 24).sub (h1.mul_left 48)).div_const (z ^ 2)
    refine this.congr_fun (fun k => ?_)
    simp only [hb_def]; ring
  have hb0 : b 0 = 0 := by
    simp only [hb_def, hc0, hc1]
    norm_num [besselCoeff, Int.even_iff]
  have hb1 := (hasSum_nat_add_iff' 1).2 hb
  simp only [Finset.range_one, Finset.sum_singleton, hb0, sub_zero] at hb1
  have hg := ha.add hb1
  set g : ℕ → ℝ := fun k => besselCoeff (2 * (k : ℤ)) 4 * z ^ (2 * k) with hg_def
  have hg' : HasSum g (besselI 0 z - 8 * (besselI 1 z / z) +
      (24 * besselI 0 z - 48 * (besselI 1 z / z)) / z ^ 2) := by
    refine hg.congr_fun (fun k => ?_)
    simp only [ha_def, hb_def, hg_def, hc0, hc1]
    have e := iden (2 * (k : ℤ))
    rw [← e]
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    field_simp
    push_cast
    ring_nf
  have hg2 := (hasSum_nat_add_iff' 2).2 hg'
  have hgz : ∑ i ∈ Finset.range 2, g i = 0 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, hg_def]
    norm_num [besselCoeff, Int.even_iff]
  rw [hgz, sub_zero] at hg2
  have h4 := hasI 4 z
  have : (fun k : ℕ => g (k + 2)) = (fun k : ℕ => besselCoeff ((4 + 2 * k : ℕ) : ℤ) 4 * z ^ (4 + 2 * k)) := by
    funext k; simp only [hg_def]
    rw [show (2 * ((k + 2 : ℕ) : ℤ)) = ((4 + 2 * k : ℕ) : ℤ) by push_cast; ring,
      show 2 * (k + 2) = 4 + 2 * k by ring]
  rw [this] at hg2
  rw [h4.unique hg2, besselI4Tilde]
  field_simp
  ring

end S78BI

open Arxiv1909_04681 in
theorem solution :
    (besselCoeff 4 4 = 1 / 384 ∧ besselCoeff 6 4 = 1 / 7680 ∧
      besselCoeff 8 4 = 1 / 368640 ∧ besselCoeff 10 4 = 1 / 30965760) ∧
    (∀ z : ℝ, HasSum (fun k : ℕ => besselCoeff (4 + 2 * k) 4 * z ^ (4 + 2 * k)) (besselI 4 z)) ∧
    (∀ A B C D : ℝ,
      (∀ j ∈ ({-2, 0, 2, 4} : Finset ℤ),
        A * besselCoeff j 0 + B * besselCoeff (j + 1) 1 + C * besselCoeff (j + 2) 0 +
          D * besselCoeff (j + 3) 1 = besselCoeff j 4) ↔
      (A = 1 ∧ B = -8 ∧ C = 24 ∧ D = -48)) ∧
    (∀ j : ℤ, 1 * besselCoeff j 0 + (-8) * besselCoeff (j + 1) 1 + 24 * besselCoeff (j + 2) 0 +
        (-48) * besselCoeff (j + 3) 1 = besselCoeff j 4) ∧
    (∀ z : ℝ, 0 < z → besselI 4 z = besselI4Tilde 1 (-8) 24 (-48) z) := by
  refine ⟨?_, ?_, ?_, S78BI.iden, S78BI.part5⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [besselCoeff, Int.even_iff] <;> simp only [Int.reduceToNat] <;> norm_num [Nat.factorial]
  · intro z
    have := S78BI.hasI 4 z
    refine this.congr_fun (fun k => ?_)
    push_cast; rfl
  · intro A B C D
    constructor
    · intro h
      have e1 := h (-2) (by simp)
      have e2 := h 0 (by simp)
      have e3 := h 2 (by simp)
      have e4 := h 4 (by simp)
      norm_num [besselCoeff, Int.even_iff] at e1 e2 e3 e4
      simp only [Int.reduceToNat] at e1 e2 e3 e4
      norm_num [Nat.factorial] at e1 e2 e3 e4
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩ j _
      exact S78BI.iden j
