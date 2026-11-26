-- Prove2me | solution 1 for Arxiv1705_08274.symmetric_response_sufficient_condition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T05:15:04.019647+00:00
-- url     : https://prove2.me/submissions/754db47a-a913-4b62-b779-802d32ace5a5

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace S79SR
open Arxiv1705_08274
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma blk1 (P11 P21 a b : Matrix n n ℝ) (ha : (P11 - P21) * a = 1) (hb : (P11 + P21) * b = 1) :
    P11 * ((1 / 2 : ℝ) • (a + b)) + -P21 * ((1 / 2 : ℝ) • (a - b)) = 1 := by
  have : P11 * ((1 / 2 : ℝ) • (a + b)) + -P21 * ((1 / 2 : ℝ) • (a - b)) =
      (1 / 2 : ℝ) • ((P11 - P21) * a + (P11 + P21) * b) := by
    simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul,
      Matrix.neg_mul, smul_add, smul_sub]
    module
  rw [this, ha, hb, ← two_smul ℝ (1 : Matrix n n ℝ), smul_smul]; norm_num

lemma blk2 (P11 P21 a b : Matrix n n ℝ) (ha : (P11 - P21) * a = 1) (hb : (P11 + P21) * b = 1) :
    P11 * ((1 / 2 : ℝ) • (a - b)) + -P21 * ((1 / 2 : ℝ) • (a + b)) = 0 := by
  have : P11 * ((1 / 2 : ℝ) • (a - b)) + -P21 * ((1 / 2 : ℝ) • (a + b)) =
      (1 / 2 : ℝ) • ((P11 - P21) * a - (P11 + P21) * b) := by
    simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul,
      Matrix.neg_mul, smul_add, smul_sub]
    module
  rw [this, ha, hb]; simp

end S79SR

open Arxiv1705_08274 S79SR in
theorem solution {N : ℕ}
    (Ps P : Matrix (Dir N ⊕ Dir N) (Dir N ⊕ Dir N) ℝ)
    (hP : P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁)
    (hm : IsUnit (Ps.toBlocks₁₁ - Ps.toBlocks₂₁).det)
    (hp : IsUnit (Ps.toBlocks₁₁ + Ps.toBlocks₂₁).det) :
    let P11 := Ps.toBlocks₁₁
    let P12 := Ps.toBlocks₁₂
    let P21 := Ps.toBlocks₂₁
    let P22 := Ps.toBlocks₂₂
    let T1 := (1 / 2 : ℝ) • ((P11 - P21)⁻¹ + (P11 + P21)⁻¹)
    let T2 := (1 / 2 : ℝ) • ((P11 - P21)⁻¹ - (P11 + P21)⁻¹)
    let Tn := (1 / 2 : ℝ) • ((P11 - P21)⁻¹ * (P22 - P12) + (P11 + P21)⁻¹ * (P22 + P12))
    let Rf := (1 / 2 : ℝ) • ((P11 - P21)⁻¹ * (P22 - P12) - (P11 + P21)⁻¹ * (P22 + P12))
    respOfPair Ps P = (fromBlocks (-P21) P11 (-P11) P21)⁻¹ * fromBlocks (-P12) P22 (-P22) P12 ∧
    (fromBlocks P11 (-P21) (-P21) P11)⁻¹ = fromBlocks T1 T2 T2 T1 ∧
    respOfPair Ps P = fromBlocks T1 T2 T2 T1 * fromBlocks P22 (-P12) (-P12) P22 ∧
    respOfPair Ps P = fromBlocks Tn Rf Rf Tn := by
  intro P11 P12 P21 P22 T1 T2 Tn Rf
  have ha : (P11 - P21) * (P11 - P21)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hm
  have hb : (P11 + P21) * (P11 + P21)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hp
  have h1 : respOfPair Ps P =
      (fromBlocks (-P21) P11 (-P11) P21)⁻¹ * fromBlocks (-P12) P22 (-P22) P12 := by
    rw [respOfPair, hP]; simp [P11, P12, P21, P22]
  have hC : fromBlocks P11 (-P21) (-P21) P11 * fromBlocks T1 T2 T2 T1 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · exact blk1 P11 P21 _ _ ha hb
    · exact blk2 P11 P21 _ _ ha hb
    · rw [add_comm]; exact blk2 P11 P21 _ _ ha hb
    · rw [add_comm]; exact blk1 P11 P21 _ _ ha hb
  have h2 : (fromBlocks P11 (-P21) (-P21) P11)⁻¹ = fromBlocks T1 T2 T2 T1 :=
    Matrix.inv_eq_right_inv hC
  let J : Matrix (Dir N ⊕ Dir N) (Dir N ⊕ Dir N) ℝ := fromBlocks 0 1 (-1) 0
  have hJ : J * -J = 1 := by
    simp only [J, fromBlocks_neg, fromBlocks_multiply, ← fromBlocks_one]; simp
  have hJi : J⁻¹ = -J := Matrix.inv_eq_right_inv hJ
  have hA : fromBlocks (-P21) P11 (-P11) P21 = J * fromBlocks P11 (-P21) (-P21) P11 := by
    simp only [J, fromBlocks_multiply]; simp
  have hB : fromBlocks (-P12) P22 (-P22) P12 = J * fromBlocks P22 (-P12) (-P12) P22 := by
    simp only [J, fromBlocks_multiply]; simp
  have h3 : respOfPair Ps P = fromBlocks T1 T2 T2 T1 * fromBlocks P22 (-P12) (-P12) P22 := by
    rw [h1, hA, hB, Matrix.mul_inv_rev, h2, hJi, Matrix.mul_assoc, ← Matrix.mul_assoc (-J),
      Matrix.neg_mul, ← Matrix.mul_neg, hJ, Matrix.one_mul]
  refine ⟨h1, h2, h3, ?_⟩
  rw [h3, fromBlocks_multiply]
  congr 1
  all_goals
    simp only [T1, T2, Tn, Rf, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_sub, smul_neg]
    abel
