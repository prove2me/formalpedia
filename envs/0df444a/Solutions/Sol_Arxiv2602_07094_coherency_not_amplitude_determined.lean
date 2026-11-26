-- Prove2me | solution 1 for Arxiv2602_07094.coherency_not_amplitude_determined
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:46:05.877822+00:00
-- url     : https://prove2.me/submissions/ca9ec961-361e-41ce-a366-5b6aedc9aedb

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

set_option autoImplicit false

namespace S73CO
open Arxiv2602_07094

lemma const (N : ℕ) (hN : 1 ≤ N) (S : SinclairMatrix) (a b : Fin 3) :
    sampleCoherency (fun _ : Fin N => pauliVector S) a b =
      pauliVector S a * star (pauliVector S b) := by
  unfold sampleCoherency
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (show N ≠ 0 by omega)), one_mul]

lemma gen (N : ℕ) (hN : 1 ≤ N) (a b : Fin 3) (S S' : SinclairMatrix)
    (hS : IsReciprocal S) (hS' : IsReciprocal S')
    (hA : channelAmplitudes S = channelAmplitudes S')
    (hne : pauliVector S a * star (pauliVector S b) ≠ pauliVector S' a * star (pauliVector S' b)) :
    ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℂ, ∀ S : Fin N → SinclairMatrix,
      (∀ i, IsReciprocal (S i)) →
        sampleCoherency (fun i => pauliVector (S i)) a b = F (fun i => channelAmplitudes (S i)) := by
  rintro ⟨F, hF⟩
  have h1 := hF (fun _ => S) (fun _ => hS)
  have h2 := hF (fun _ => S') (fun _ => hS')
  simp only [hA] at h1
  rw [const N hN, ← h2, const N hN] at h1
  exact hne h1

lemma sq2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma s2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'

def A1 : SinclairMatrix := !![1, 0; 0, 1]
def A2 : SinclairMatrix := !![1, 0; 0, -1]
def B1 : SinclairMatrix := !![1, 0; 0, Complex.I]
def B2 : SinclairMatrix := !![1, 0; 0, -Complex.I]
def C1 : SinclairMatrix := !![1, 1; 1, 1]
def C2 : SinclairMatrix := !![1, -1; -1, 1]
def D1 : SinclairMatrix := !![1, 1; 1, -1]
def D2 : SinclairMatrix := !![1, -1; -1, -1]

lemma amp {S S' : SinclairMatrix} (h : ∀ i j, ‖S i j‖ = ‖S' i j‖) :
    channelAmplitudes S = channelAmplitudes S' := by
  ext i j; exact h i j

end S73CO

open Arxiv2602_07094 S73CO in
theorem solution (N : ℕ) (hN : 1 ≤ N) (a b : Fin 3)
    (hab : ¬ (a = 2 ∧ b = 2)) :
    ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℂ, ∀ S : Fin N → SinclairMatrix,
      (∀ i, IsReciprocal (S i)) →
        sampleCoherency (fun i => pauliVector (S i)) a b = F (fun i => channelAmplitudes (S i)) := by
  have hs := s2
  have hq := sq2
  fin_cases a <;> fin_cases b
  · apply gen N hN _ _ A1 A2 (by simp [IsReciprocal, A1]) (by simp [IsReciprocal, A2])
      (amp (by intro i j; fin_cases i <;> fin_cases j <;> simp [A1, A2]))
    simp [pauliVector, pauliAlpha, A1, A2]
    (all_goals (try field_simp)
     all_goals (try norm_num)
     all_goals (try (intro h; have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h; simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2))
     all_goals (try norm_num at *))
  · apply gen N hN _ _ B1 B2 (by simp [IsReciprocal, B1]) (by simp [IsReciprocal, B2])
      (amp (by intro i j; fin_cases i <;> fin_cases j <;> simp [B1, B2]))
    simp [pauliVector, pauliAlpha, pauliBeta, B1, B2]
    (all_goals (try field_simp)
     all_goals (try norm_num)
     all_goals (try (intro h; have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h; simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2))
     all_goals (try norm_num at *))
  · apply gen N hN _ _ C1 C2 (by simp [IsReciprocal, C1]) (by simp [IsReciprocal, C2])
      (amp (by intro i j; fin_cases i <;> fin_cases j <;> simp [C1, C2]))
    simp [pauliVector, pauliAlpha, pauliGamma, C1, C2]
    (all_goals (try field_simp)
     all_goals (try norm_num)
     all_goals (try (intro h; have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h; simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2))
     all_goals (try norm_num at *))
  · apply gen N hN _ _ B1 B2 (by simp [IsReciprocal, B1]) (by simp [IsReciprocal, B2])
      (amp (by intro i j; fin_cases i <;> fin_cases j <;> simp [B1, B2]))
    simp [pauliVector, pauliAlpha, pauliBeta, B1, B2]
    (all_goals (try field_simp)
     all_goals (try norm_num)
     all_goals (try (intro h; have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h; simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2))
     all_goals (try norm_num at *))
  · apply gen N hN _ _ A1 A2 (by simp [IsReciprocal, A1]) (by simp [IsReciprocal, A2])
      (amp (by intro i j; fin_cases i <;> fin_cases j <;> simp [A1, A2]))
    simp [pauliVector, pauliBeta, A1, A2]
    (all_goals (try field_simp)
     all_goals (try norm_num)
     all_goals (try (intro h; have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h; simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2))
     all_goals (try norm_num at *))
  · apply gen N hN _ _ D1 D2 (by simp [IsReciprocal, D1]) (by simp [IsReciprocal, D2])
      (amp (by intro i j; fin_cases i <;> fin_cases j <;> simp [D1, D2]))
    simp [pauliVector, pauliBeta, pauliGamma, D1, D2]
    (all_goals (try field_simp)
     all_goals (try norm_num)
     all_goals (try (intro h; have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h; simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2))
     all_goals (try norm_num at *))
  · apply gen N hN _ _ C1 C2 (by simp [IsReciprocal, C1]) (by simp [IsReciprocal, C2])
      (amp (by intro i j; fin_cases i <;> fin_cases j <;> simp [C1, C2]))
    simp [pauliVector, pauliAlpha, pauliGamma, C1, C2]
    (all_goals (try field_simp)
     all_goals (try norm_num)
     all_goals (try (intro h; have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h; simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2))
     all_goals (try norm_num at *))
  · apply gen N hN _ _ D1 D2 (by simp [IsReciprocal, D1]) (by simp [IsReciprocal, D2])
      (amp (by intro i j; fin_cases i <;> fin_cases j <;> simp [D1, D2]))
    simp [pauliVector, pauliBeta, pauliGamma, D1, D2]
    (all_goals (try field_simp)
     all_goals (try norm_num)
     all_goals (try (intro h; have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h; simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2))
     all_goals (try norm_num at *))
  · exact absurd ⟨rfl, rfl⟩ hab
