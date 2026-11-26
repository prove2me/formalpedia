-- Prove2me | solution 1 for Arxiv2602_07094.amplitude_only_models_cannot_preserve
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T01:01:31.229439+00:00
-- url     : https://prove2.me/submissions/3745d232-4b59-46b5-8652-2220e49f1e75

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

set_option autoImplicit false

namespace S74AO
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


lemma r2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma r2ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have : (0:ℝ) < Real.sqrt 2 := by positivity
  exact_mod_cast this.ne'

lemma q1 (x y : ℂ) : x / ((Real.sqrt 2 : ℝ) : ℂ) * star (y / ((Real.sqrt 2 : ℝ) : ℂ)) =
    x * star y / 2 := by
  rw [star_div₀, Complex.star_def, Complex.conj_ofReal, ← r2]; field_simp [r2ne]
lemma q2 (x y : ℂ) : ((Real.sqrt 2 : ℝ) : ℂ) * x * star (((Real.sqrt 2 : ℝ) : ℂ) * y) =
    2 * x * star y := by
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← r2]; ring
lemma q3 (x y : ℂ) : x / ((Real.sqrt 2 : ℝ) : ℂ) * star (((Real.sqrt 2 : ℝ) : ℂ) * y) =
    x * star y := by
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]; field_simp [r2ne]
lemma q4 (x y : ℂ) : ((Real.sqrt 2 : ℝ) : ℂ) * x * star (y / ((Real.sqrt 2 : ℝ) : ℂ)) =
    x * star y := by
  rw [star_div₀, Complex.star_def, Complex.conj_ofReal]; field_simp [r2ne]

lemma gen {N : ℕ} (hN : 1 ≤ N) (a b : Fin 3) (S S' : SinclairMatrix)
    (hr : IsReciprocal S) (hr' : IsReciprocal S')
    (hamp : channelAmplitudes S = channelAmplitudes S')
    (hne : pauliVector S a * star (pauliVector S b) ≠ pauliVector S' a * star (pauliVector S' b)) :
    ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℂ, ∀ S : Fin N → SinclairMatrix,
        (∀ i, IsReciprocal (S i)) →
          sampleCoherency (fun i => pauliVector (S i)) a b =
            F (fun i => channelAmplitudes (S i)) := by
  rintro ⟨F, hF⟩
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have c : ∀ T : SinclairMatrix, sampleCoherency (fun _ : Fin N => pauliVector T) a b =
      pauliVector T a * star (pauliVector T b) := by
    intro T; unfold sampleCoherency
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hNc, one_mul]
  have hA := hF (fun _ => S) (fun _ => hr)
  have hB := hF (fun _ => S') (fun _ => hr')
  rw [c] at hA hB
  rw [hamp, ← hB] at hA
  exact hne hA

def P1 : SinclairMatrix := !![1, 0; 0, Complex.I]
def P2 : SinclairMatrix := !![1, 0; 0, -Complex.I]
def R1 : SinclairMatrix := !![1, 1; 1, 1]
def R2 : SinclairMatrix := !![1, -1; -1, 1]
def U1 : SinclairMatrix := !![1, 1; 1, -1]
def U2 : SinclairMatrix := !![1, -1; -1, -1]

lemma ampP : channelAmplitudes P1 = channelAmplitudes P2 := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [channelAmplitudes, P1, P2]
lemma ampR : channelAmplitudes R1 = channelAmplitudes R2 := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [channelAmplitudes, R1, R2]
lemma ampU : channelAmplitudes U1 = channelAmplitudes U2 := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [channelAmplitudes, U1, U2]

lemma cI : (Complex.I) ≠ -Complex.I := by
  intro h; have := congrArg Complex.im h; simp at this; norm_num at this

end S74AO


open Arxiv2602_07094 S74AO in
theorem S74EN_entropy (N : ℕ) (hN : 2 ≤ N) :
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



open Arxiv2602_07094 S74AO in
theorem S74AL_alpha (N : ℕ) (hN : 1 ≤ N) :
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



open Arxiv2602_07094 S74AO in
theorem solution :
    (¬ ∃ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, ∀ S : SinclairMatrix, IsReciprocal S →
        ‖pauliAlpha S‖ = F (channelAmplitudes S)) ∧
    (¬ ∃ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, ∀ S : SinclairMatrix, IsReciprocal S →
        ‖pauliBeta S‖ = F (channelAmplitudes S)) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ a b : Fin 3, ¬ (a = 2 ∧ b = 2) →
      ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℂ, ∀ S : Fin N → SinclairMatrix,
        (∀ i, IsReciprocal (S i)) →
          sampleCoherency (fun i => pauliVector (S i)) a b =
            F (fun i => channelAmplitudes (S i))) ∧
    (∀ N : ℕ, 2 ≤ N →
      ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℝ, ∀ S : Fin N → SinclairMatrix,
        (∀ i, IsReciprocal (S i)) → (∃ i, S i ≠ 0) →
          entropyH (sampleCoherency (fun i => pauliVector (S i))) =
            F (fun i => channelAmplitudes (S i))) ∧
    (∀ N : ℕ, 1 ≤ N →
      ¬ ∃ F : (Fin N → Matrix (Fin 2) (Fin 2) ℝ) → ℝ, ∀ S : Fin N → SinclairMatrix,
        (∀ i, IsReciprocal (S i)) → (∃ i, S i ≠ 0) →
          HasSimplePositiveSpectrum (sampleCoherency (fun i => pauliVector (S i))) →
          alphaAngle (sampleCoherency (fun i => pauliVector (S i))) =
            F (fun i => channelAmplitudes (S i))) := by
  have hrec0 : IsReciprocal S0 := by simp [IsReciprocal, S0]
  have hrec1 : IsReciprocal S1 := by simp [IsReciprocal, S1]
  refine ⟨?_, ?_, ?_, S74EN_entropy, S74AL_alpha⟩
  · rintro ⟨F, hF⟩
    have h0 := hF S0 hrec0
    rw [amp_eq, ← hF S1 hrec1] at h0
    have e0 : pauliAlpha S0 = ((Real.sqrt 2 : ℝ) : ℂ) := by
      have := congrFun pv0 0; simpa [pauliVector] using this
    have e1 : pauliAlpha S1 = 0 := by
      have := congrFun pv1 0; simpa [pauliVector] using this
    rw [e0, e1] at h0; simp at h0
  · rintro ⟨F, hF⟩
    have h0 := hF S0 hrec0
    rw [amp_eq, ← hF S1 hrec1] at h0
    have e0 : pauliBeta S0 = 0 := by
      have := congrFun pv0 1; simpa [pauliVector] using this
    have e1 : pauliBeta S1 = ((Real.sqrt 2 : ℝ) : ℂ) := by
      have := congrFun pv1 1; simpa [pauliVector] using this
    rw [e0, e1] at h0; simp at h0
    have : (0:ℝ) < Real.sqrt 2 := by positivity
    rw [abs_of_pos this] at h0; linarith
  · intro N hN a b hab
    have hrP1 : IsReciprocal P1 := by simp [IsReciprocal, P1]
    have hrP2 : IsReciprocal P2 := by simp [IsReciprocal, P2]
    have hrR1 : IsReciprocal R1 := by simp [IsReciprocal, R1]
    have hrR2 : IsReciprocal R2 := by simp [IsReciprocal, R2]
    have hrU1 : IsReciprocal U1 := by simp [IsReciprocal, U1]
    have hrU2 : IsReciprocal U2 := by simp [IsReciprocal, U2]
    fin_cases a <;> fin_cases b
    · apply gen hN _ _ S0 S1 hrec0 hrec1 amp_eq; rw [pv0, pv1]; simp [r2]
    · apply gen hN _ _ P1 P2 hrP1 hrP2 ampP
      simp only [pauliVector, pauliAlpha, pauliBeta, P1, P2]; simp [q1] <;> first | (intro h; rw [div_mul_div_comm, div_mul_div_comm, r2, div_left_inj' two_ne_zero] at h; ring_nf at h; norm_num [Complex.ext_iff] at h; done) | (intro h; rw [mul_div_cancel₀ _ r2ne] at h; norm_num at h; done) | (intro h; field_simp at h; norm_num at h; done) | (norm_num; done)
    · apply gen hN _ _ R1 R2 hrR1 hrR2 ampR
      simp only [pauliVector, pauliAlpha, pauliGamma, R1, R2]; simp [q3] <;> first | (intro h; rw [div_mul_div_comm, div_mul_div_comm, r2, div_left_inj' two_ne_zero] at h; ring_nf at h; norm_num [Complex.ext_iff] at h; done) | (intro h; rw [mul_div_cancel₀ _ r2ne] at h; norm_num at h; done) | (intro h; field_simp at h; norm_num at h; done) | (norm_num; done)
    · apply gen hN _ _ P1 P2 hrP1 hrP2 ampP
      simp only [pauliVector, pauliAlpha, pauliBeta, P1, P2]; simp [q1] <;> first | (intro h; rw [div_mul_div_comm, div_mul_div_comm, r2, div_left_inj' two_ne_zero] at h; ring_nf at h; norm_num [Complex.ext_iff] at h; done) | (intro h; rw [mul_div_cancel₀ _ r2ne] at h; norm_num at h; done) | (intro h; field_simp at h; norm_num at h; done) | (norm_num; done)
    · apply gen hN _ _ S0 S1 hrec0 hrec1 amp_eq; rw [pv0, pv1]; simp [r2]
    · apply gen hN _ _ U1 U2 hrU1 hrU2 ampU
      simp only [pauliVector, pauliBeta, pauliGamma, U1, U2]; simp [q3] <;> first | (intro h; rw [div_mul_div_comm, div_mul_div_comm, r2, div_left_inj' two_ne_zero] at h; ring_nf at h; norm_num [Complex.ext_iff] at h; done) | (intro h; rw [mul_div_cancel₀ _ r2ne] at h; norm_num at h; done) | (intro h; field_simp at h; norm_num at h; done) | (norm_num; done)
    · apply gen hN _ _ R1 R2 hrR1 hrR2 ampR
      simp only [pauliVector, pauliAlpha, pauliGamma, R1, R2]; simp [q4] <;> first | (intro h; rw [div_mul_div_comm, div_mul_div_comm, r2, div_left_inj' two_ne_zero] at h; ring_nf at h; norm_num [Complex.ext_iff] at h; done) | (intro h; rw [mul_div_cancel₀ _ r2ne] at h; norm_num at h; done) | (intro h; field_simp at h; norm_num at h; done) | (norm_num; done)
    · apply gen hN _ _ U1 U2 hrU1 hrU2 ampU
      simp only [pauliVector, pauliBeta, pauliGamma, U1, U2]; simp [q4] <;> first | (intro h; rw [div_mul_div_comm, div_mul_div_comm, r2, div_left_inj' two_ne_zero] at h; ring_nf at h; norm_num [Complex.ext_iff] at h; done) | (intro h; rw [mul_div_cancel₀ _ r2ne] at h; norm_num at h; done) | (intro h; field_simp at h; norm_num at h; done) | (norm_num; done)
    · exact absurd ⟨rfl, rfl⟩ hab
