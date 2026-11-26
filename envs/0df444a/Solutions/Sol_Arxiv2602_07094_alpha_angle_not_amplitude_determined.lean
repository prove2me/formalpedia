-- Prove2me | solution 1 for Arxiv2602_07094.alpha_angle_not_amplitude_determined
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:59:18.31226+00:00
-- url     : https://prove2.me/submissions/57b0abd7-7dc3-42d5-bc41-9746e98f424e

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

set_option autoImplicit false

namespace S74AL
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


lemma roots_diag (d : Fin 3 → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).charpoly.roots =
      Multiset.map (fun i => (d i : ℂ)) Finset.univ.val := by
  rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod]
  have : Finset.univ.val.map (fun i => X - C ((d i : ℂ))) =
      (Finset.univ.val.map (fun i => (d i : ℂ))).map (fun a => X - C a) := by
    rw [Multiset.map_map]; rfl
  rw [this, Polynomial.roots_multiset_prod_X_sub_C]

lemma herm_diag (d : Fin 3 → ℝ) : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  intro i; simp [IsSelfAdjoint, Complex.conj_ofReal]

lemma alpha_diag (d : Fin 3 → ℝ) (j : Fin 3) (hd : ∀ m, m ≠ j → d m = 0) (hj : 0 < d j) :
    alphaAngle (Matrix.diagonal (fun i => (d i : ℂ))) =
      Real.arccos (if j = 0 then 1 else 0) := by
  have hT := herm_diag d
  unfold alphaAngle
  rw [dif_pos hT]
  unfold pseudoProb
  have hs : ∑ j, hT.eigenvalues j = ∑ j, d j := sum_eig d hT id
  have hsj : ∑ m, d m = d j := by
    rw [Finset.sum_eq_single j (fun m _ hm => hd m hm) (by simp)]
  rw [hs, hsj]
  have key : ∀ i, hT.eigenvalues i / d j *
      Real.arccos ‖(hT.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) 0 i‖ =
      hT.eigenvalues i / d j * Real.arccos (if j = 0 then 1 else 0) := by
    intro i
    by_cases hl : hT.eigenvalues i = 0
    · simp [hl]
    congr 2
    rw [Matrix.IsHermitian.eigenvectorUnitary_apply]
    have hv := hT.mulVec_eigenvectorBasis i
    have hz : ∀ m, m ≠ j → (hT.eigenvectorBasis i) m = 0 := by
      intro m hm
      have h1 := congrFun hv m
      rw [Matrix.mulVec_diagonal, hd m hm] at h1
      simp at h1
      rcases h1 with h1 | h1
      · exact absurd h1 hl
      · exact h1
    have hn : ‖hT.eigenvectorBasis i‖ = 1 := hT.eigenvectorBasis.orthonormal.1 i
    rw [EuclideanSpace.norm_eq, Finset.sum_eq_single j (fun m _ hm => by rw [hz m hm]; simp)
      (by simp), Real.sqrt_sq (norm_nonneg _)] at hn
    split_ifs with h0
    · subst h0; exact hn
    · rw [hz 0 (Ne.symm h0)]; simp
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.sum_mul, ← Finset.sum_div, hs, hsj,
    div_self hj.ne', one_mul]

lemma simple_diag (d : Fin 3 → ℝ) (j : Fin 3) (hd : ∀ m, m ≠ j → d m = 0) (hj : 0 < d j) :
    HasSimplePositiveSpectrum (Matrix.diagonal (fun i => (d i : ℂ))) := by
  unfold HasSimplePositiveSpectrum
  rw [roots_diag, Fin.univ_val_map]
  have hc : ((d j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
  fin_cases j <;> simp [List.ofFn_succ, hd] <;> simp_all

end S74AL

open Arxiv2602_07094 S74AL in
theorem solution (N : ℕ) (hN : 1 ≤ N) :
    ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℝ, ∀ S : Fin N → SinclairMatrix,
      (∀ i, IsReciprocal (S i)) → (∃ i, S i ≠ 0) →
        HasSimplePositiveSpectrum (sampleCoherency (fun i => pauliVector (S i))) →
        alphaAngle (sampleCoherency (fun i => pauliVector (S i))) =
          F (fun i => channelAmplitudes (S i)) := by
  rintro ⟨F, hF⟩
  set i0 : Fin N := ⟨0, by omega⟩
  have hS0 : S0 ≠ 0 := by
    intro h; have := congrFun (congrFun h 0) 0; simp [S0] at this
  have hS1 : S1 ≠ 0 := by
    intro h; have := congrFun (congrFun h 0) 0; simp [S1] at this
  have hrec0 : IsReciprocal S0 := by simp [IsReciprocal, S0]
  have hrec1 : IsReciprocal S1 := by simp [IsReciprocal, S1]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have TA : sampleCoherency (fun _ : Fin N => pauliVector S0) =
      Matrix.diagonal (fun i => (((![2, 0, 0] : Fin 3 → ℝ) i : ℝ) : ℂ)) := by
    ext a b
    unfold sampleCoherency
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hNc, one_mul, pv0]
    fin_cases a <;> fin_cases b <;> simp [Complex.conj_ofReal, hs]
  have TB : sampleCoherency (fun _ : Fin N => pauliVector S1) =
      Matrix.diagonal (fun i => (((![0, 2, 0] : Fin 3 → ℝ) i : ℝ) : ℂ)) := by
    ext a b
    unfold sampleCoherency
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hNc, one_mul, pv1]
    fin_cases a <;> fin_cases b <;> simp [Complex.conj_ofReal, hs]
  have dA : ∀ m : Fin 3, m ≠ 0 → (![2, 0, 0] : Fin 3 → ℝ) m = 0 := by
    intro m hm; fin_cases m <;> simp_all
  have dB : ∀ m : Fin 3, m ≠ 1 → (![0, 2, 0] : Fin 3 → ℝ) m = 0 := by
    intro m hm; fin_cases m <;> simp_all
  have pA : (0:ℝ) < (![2, 0, 0] : Fin 3 → ℝ) 0 := by simp
  have pB : (0:ℝ) < (![0, 2, 0] : Fin 3 → ℝ) 1 := by simp
  have hA := hF (fun _ => S0) (fun _ => hrec0) ⟨i0, hS0⟩ (by rw [TA]; exact simple_diag _ 0 dA pA)
  have hB := hF (fun _ => S1) (fun _ => hrec1) ⟨i0, hS1⟩ (by rw [TB]; exact simple_diag _ 1 dB pB)
  have hamp : (fun _ : Fin N => channelAmplitudes S1) = fun _ => channelAmplitudes S0 := by
    funext i; exact amp_eq.symm
  rw [hamp, ← hA, TA, TB, alpha_diag _ 0 dA pA, alpha_diag _ 1 dB pB] at hB
  simp at hB
