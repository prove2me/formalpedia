-- Prove2me | solution 1 for Arxiv2602_07094.entropy_not_amplitude_determined
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:56:50.654498+00:00
-- url     : https://prove2.me/submissions/ad26a7d1-5d90-447d-8d44-eb5dcaefc973

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

set_option autoImplicit false

namespace S74EN
open Arxiv2602_07094 Polynomial

lemma sum_eig (d : Fin 3 → ℝ) (hT : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hT.eigenvalues i) = ∑ i, g (d i) := by
  have h1 := hT.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal] at h1
  have h2 : (∏ i, (X - C ((d i : ℂ)))).roots = Multiset.map (fun i => (d i : ℂ)) Finset.univ.val := by
    rw [Finset.prod_eq_multiset_prod]
    have : Finset.univ.val.map (fun i => X - C ((d i : ℂ))) =
        (Finset.univ.val.map (fun i => (d i : ℂ))).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [this, Polynomial.roots_multiset_prod_X_sub_C]
  rw [h2] at h1
  have h3 : Finset.univ.val.map d = Finset.univ.val.map hT.eigenvalues := by
    apply Multiset.map_injective Complex.ofReal_injective
    rw [Multiset.map_map, Multiset.map_map]
    exact h1
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  have e1 : Multiset.map (fun i => g (hT.eigenvalues i)) Finset.univ.val =
      (Multiset.map hT.eigenvalues Finset.univ.val).map g := by rw [Multiset.map_map]; rfl
  have e2 : Multiset.map (fun i => g (d i)) Finset.univ.val =
      (Multiset.map d Finset.univ.val).map g := by rw [Multiset.map_map]; rfl
  rw [e1, e2, h3]

lemma ent_diag (d : Fin 3 → ℝ) :
    entropyH (Matrix.diagonal (fun i => (d i : ℂ))) =
      -∑ i, (d i / ∑ j, d j) * Real.logb 3 (d i / ∑ j, d j) := by
  have hT : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i; simp [IsSelfAdjoint, Complex.conj_ofReal]
  unfold entropyH
  rw [dif_pos hT]
  unfold pseudoProb
  have hs : ∑ j, hT.eigenvalues j = ∑ j, d j := sum_eig d hT id
  rw [hs]
  congr 1
  exact sum_eig d hT (fun x => (x / ∑ j, d j) * Real.logb 3 (x / ∑ j, d j))


def S0 : SinclairMatrix := !![1, 0; 0, 1]
def S1 : SinclairMatrix := !![1, 0; 0, -1]

lemma pv0 : pauliVector S0 = ![((Real.sqrt 2 : ℝ) : ℂ), 0, 0] := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt 2 := by positivity
    exact_mod_cast this.ne'
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  funext a; fin_cases a
  · simp only [pauliVector, pauliAlpha, S0]; simp
    field_simp; rw [sq, hs]; norm_num
  · simp [pauliVector, pauliBeta, S0]
  · simp [pauliVector, pauliGamma, S0]

lemma pv1 : pauliVector S1 = ![0, ((Real.sqrt 2 : ℝ) : ℂ), 0] := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt 2 := by positivity
    exact_mod_cast this.ne'
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  funext a; fin_cases a
  · simp [pauliVector, pauliAlpha, S1]
  · simp only [pauliVector, pauliBeta, S1]; simp
    field_simp; rw [sq, hs]; norm_num
  · simp [pauliVector, pauliGamma, S1]

lemma amp_eq : channelAmplitudes S0 = channelAmplitudes S1 := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [channelAmplitudes, S0, S1]

lemma sum_ite_split {N : ℕ} (i0 : Fin N) (x y : ℂ) :
    ∑ i : Fin N, (if i = i0 then x else y) = x + ((N : ℂ) - 1) * y := by
  have : ∀ i : Fin N, (if i = i0 then x else y) = y + (if i = i0 then x - y else 0) := by
    intro i; split_ifs <;> ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul]
  ring

end S74EN

open Arxiv2602_07094 S74EN in
theorem solution (N : ℕ) (hN : 2 ≤ N) :
    ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℝ, ∀ S : Fin N → SinclairMatrix,
      (∀ i, IsReciprocal (S i)) → (∃ i, S i ≠ 0) →
        entropyH (sampleCoherency (fun i => pauliVector (S i))) =
          F (fun i => channelAmplitudes (S i)) := by
  rintro ⟨F, hF⟩
  set i0 : Fin N := ⟨0, by omega⟩
  have hS0 : S0 ≠ 0 := by
    intro h; have := congrFun (congrFun h 0) 0; simp [S0] at this
  have hrec0 : IsReciprocal S0 := by simp [IsReciprocal, S0]
  have hrec1 : IsReciprocal S1 := by simp [IsReciprocal, S1]
  have hA := hF (fun _ => S0) (fun _ => hrec0) ⟨i0, hS0⟩
  have hB := hF (fun i => if i = i0 then S0 else S1)
    (fun i => by split_ifs; exacts [hrec0, hrec1]) ⟨i0, by simp [hS0]⟩
  have hamp : (fun i : Fin N => channelAmplitudes (if i = i0 then S0 else S1)) =
      fun _ => channelAmplitudes S0 := by
    funext i; split_ifs; rfl; exact amp_eq.symm
  rw [hamp, ← hA] at hB
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have TA : sampleCoherency (fun _ : Fin N => pauliVector S0) =
      Matrix.diagonal (fun i => (((![2, 0, 0] : Fin 3 → ℝ) i : ℝ) : ℂ)) := by
    ext a b
    unfold sampleCoherency
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hNc, one_mul, pv0]
    fin_cases a <;> fin_cases b <;> simp [Complex.conj_ofReal, hs]
  have TB : sampleCoherency (fun i : Fin N => pauliVector (if i = i0 then S0 else S1)) =
      Matrix.diagonal (fun i => (((![2 / (N:ℝ), 2 * ((N:ℝ) - 1) / N, 0] : Fin 3 → ℝ) i : ℝ) : ℂ)) := by
    ext a b
    unfold sampleCoherency
    have : ∀ i : Fin N, pauliVector (if i = i0 then S0 else S1) a *
        star (pauliVector (if i = i0 then S0 else S1) b) =
        if i = i0 then pauliVector S0 a * star (pauliVector S0 b)
        else pauliVector S1 a * star (pauliVector S1 b) := by
      intro i; split_ifs <;> rfl
    simp only [this]
    rw [sum_ite_split, pv0, pv1]
    fin_cases a <;> fin_cases b <;>
      simp [Complex.conj_ofReal, hs, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub] <;>
      (try field_simp) <;> (try ring)
  rw [TA, TB, ent_diag, ent_diag] at hB
  simp [Fin.sum_univ_three] at hB
  have hq : (2:ℝ) / N + 2 * (N - 1) / N = 2 := by field_simp; ring
  rw [hq] at hB
  have hN0 : (0:ℝ) < N := by linarith
  have a1 : 0 < 2 * ((N:ℝ) - 1) / N / 2 := by
    apply div_pos (div_pos (by linarith) hN0) (by norm_num)
  have a2 : 2 * ((N:ℝ) - 1) / N / 2 < 1 := by
    rw [div_lt_one (by norm_num), div_lt_iff₀ hN0]; linarith
  have b1 : 0 < 2 / (N:ℝ) / 2 := by positivity
  have b2 : 2 / (N:ℝ) / 2 < 1 := by
    rw [div_lt_one (by norm_num), div_lt_iff₀ hN0]; linarith
  have t1 := mul_neg_of_pos_of_neg a1 (Real.logb_neg (b := 3) (by norm_num) a1 a2)
  have t2 := mul_neg_of_pos_of_neg b1 (Real.logb_neg (b := 3) (by norm_num) b1 b2)
  linarith
