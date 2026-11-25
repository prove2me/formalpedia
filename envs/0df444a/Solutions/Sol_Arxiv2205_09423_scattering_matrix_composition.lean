-- Prove2me | solution 1 for Arxiv2205_09423.scattering_matrix_composition
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:17:57.67379+00:00
-- url     : https://prove2.me/submissions/b33e2a8c-fc22-41f2-85d8-d6355dd58a70

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix
open Arxiv2205_09423

section
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma sm_conj2 (P A B : Matrix V V ℂ) (hP : P * P = 1) :
    (P * A * P) * (P * B * P) = P * (A * B) * P := by
  calc (P * A * P) * (P * B * P) = P * A * (P * P) * B * P := by simp only [Matrix.mul_assoc]
    _ = P * (A * B) * P := by rw [hP, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma sm_key (r1 t1p t1 r1p r2 t2p t2 r2p P : Matrix V V ℂ) (hP : P * P = 1)
    (ht1 : t1p = P * t1ᵀ * P) (ht2 : t2p = P * t2ᵀ * P)
    (hr1 : r1p = P * r1pᵀ * P) (hr2 : r2 = P * r2ᵀ * P)
    (hQ : IsUnit (1 - r1p * r2).det) :
    P * (t2 * (1 - r1p * r2)⁻¹ * t1)ᵀ * P = t1p * (1 + r2 * (1 - r1p * r2)⁻¹ * r1p) * t2p := by
  set Q := (1 - r1p * r2)⁻¹ with hQdef
  have hQ1 : (1 - r1p * r2) * Q = 1 := Matrix.mul_nonsing_inv _ hQ
  set N := 1 - r2 * r1p with hNdef
  set Y := 1 + r2 * Q * r1p with hYdef
  have hNY : N * Y = 1 := by
    calc N * Y = 1 - r2 * r1p + r2 * ((1 - r1p * r2) * Q) * r1p := by
          rw [hNdef, hYdef]; noncomm_ring
      _ = 1 := by rw [hQ1]; noncomm_ring
  have hN : N = P * (1 - r2ᵀ * r1pᵀ) * P := by
    have e : r2 * r1p = P * (r2ᵀ * r1pᵀ) * P := by
      rw [← sm_conj2 P _ _ hP, ← hr2, ← hr1]
    rw [hNdef, e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]
  have hT : Qᵀ * (1 - r2ᵀ * r1pᵀ) = 1 := by
    have := congrArg Matrix.transpose hQ1
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_mul] at this
    exact this
  have hWN : (P * Qᵀ * P) * N = 1 := by
    rw [hN, sm_conj2 P _ _ hP, hT, Matrix.mul_one, hP]
  have hW : P * Qᵀ * P = Y := by
    calc P * Qᵀ * P = (P * Qᵀ * P) * (N * Y) := by rw [hNY, Matrix.mul_one]
      _ = ((P * Qᵀ * P) * N) * Y := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [hWN, Matrix.one_mul]
  have htr : (t2 * Q * t1)ᵀ = t1ᵀ * (Qᵀ * t2ᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
  rw [htr, ← sm_conj2 P _ _ hP, ← sm_conj2 P _ _ hP, ← ht1, ← ht2, hW]
  simp only [Matrix.mul_assoc]

lemma sm_main (r1 t1p t1 r1p r2 t2p t2 r2p P : Matrix V V ℂ) (hP : P * P = 1)
    (ht1 : t1p = P * t1ᵀ * P) (ht2 : t2p = P * t2ᵀ * P)
    (hr1 : r1p = P * r1pᵀ * P) (hr2 : r2 = P * r2ᵀ * P)
    (hQ : IsUnit (1 - r1p * r2).det) (S : Matrix (V ⊕ V) (V ⊕ V) ℂ) :
    IsCascade (Matrix.fromBlocks r1 t1p t1 r1p) (Matrix.fromBlocks r2 t2p t2 r2p) S ↔
      S = Matrix.fromBlocks (r1 + t1p * r2 * (1 - r1p * r2)⁻¹ * t1)
        (P * (t2 * (1 - r1p * r2)⁻¹ * t1).transpose * P) (t2 * (1 - r1p * r2)⁻¹ * t1)
        (r2p + t2 * (1 - r1p * r2)⁻¹ * r1p * t2p) := by
  have hX := sm_key r1 t1p t1 r1p r2 t2p t2 r2p P hP ht1 ht2 hr1 hr2 hQ
  set Q := (1 - r1p * r2)⁻¹ with hQdef
  have hQ1 : (1 - r1p * r2) * Q = 1 := Matrix.mul_nonsing_inv _ hQ
  have hQ2 : Q * (1 - r1p * r2) = 1 := Matrix.nonsing_inv_mul _ hQ
  set M := Matrix.fromBlocks (r1 + t1p * r2 * Q * t1) (P * (t2 * Q * t1).transpose * P)
    (t2 * Q * t1) (r2p + t2 * Q * r1p * t2p) with hM
  -- key computation
  have hK : ∀ a d : V → ℂ,
      M *ᵥ Sum.elim a d =
        Sum.elim (r1 *ᵥ a + t1p *ᵥ (r2 *ᵥ (Q *ᵥ (t1 *ᵥ a + (r1p * t2p) *ᵥ d)) + t2p *ᵥ d))
          (t2 *ᵥ (Q *ᵥ (t1 *ᵥ a + (r1p * t2p) *ᵥ d)) + r2p *ᵥ d) := by
    intro a d
    rw [hM, Matrix.fromBlocks_mulVec, hX]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    congr 1
    · simp only [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    · simp only [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
  unfold IsCascade
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  constructor
  · intro h
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    obtain ⟨b, c, hb, hc, hS⟩ := h (v ∘ Sum.inl) (v ∘ Sum.inr)
    have hv : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := Sum.elim_comp_inl_inr v
    have hb' : (1 - r1p * r2) *ᵥ b = t1 *ᵥ (v ∘ Sum.inl) + (r1p * t2p) *ᵥ (v ∘ Sum.inr) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      have e : b = t1 *ᵥ (v ∘ Sum.inl) + ((r1p * r2) *ᵥ b + (r1p * t2p) *ᵥ (v ∘ Sum.inr)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hc]; exact hb
      rw [sub_eq_iff_eq_add]
      conv_lhs => rw [e]
      abel
    have hb0 : b = Q *ᵥ (t1 *ᵥ (v ∘ Sum.inl) + (r1p * t2p) *ᵥ (v ∘ Sum.inr)) := by
      rw [← hb', Matrix.mulVec_mulVec, hQ2, Matrix.one_mulVec]
    rw [← hv, hS, hK, ← hb0, ← hc]
  · intro hS a d
    obtain ⟨b0, hb0⟩ : ∃ b0, b0 = Q *ᵥ (t1 *ᵥ a + (r1p * t2p) *ᵥ d) := ⟨_, rfl⟩
    refine ⟨b0, r2 *ᵥ b0 + t2p *ᵥ d, ?_, rfl, ?_⟩
    · have hb : (1 - r1p * r2) *ᵥ b0 = t1 *ᵥ a + (r1p * t2p) *ᵥ d := by
        rw [hb0, Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hb
      have e : b0 = t1 *ᵥ a + (r1p * t2p) *ᵥ d + (r1p * r2) *ᵥ b0 := by
        rw [← hb]; abel
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      conv_lhs => rw [e]
      abel
    · rw [hS, hK, ← hb0]
end

lemma sm_recip {Nk : ℕ} (S : Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ)
    (h : IsReciprocal S) :
    S.toBlocks₁₂ = piMat Nk * S.toBlocks₂₁ᵀ * piMat Nk ∧
    S.toBlocks₁₁ = piMat Nk * S.toBlocks₁₁ᵀ * piMat Nk ∧
    S.toBlocks₂₂ = piMat Nk * S.toBlocks₂₂ᵀ * piMat Nk := by
  unfold IsReciprocal at h
  have h' : S = Matrix.fromBlocks (piMat Nk) 0 0 (piMat Nk) *
      (Matrix.fromBlocks S.toBlocks₁₁ S.toBlocks₁₂ S.toBlocks₂₁ S.toBlocks₂₂)ᵀ *
      Matrix.fromBlocks (piMat Nk) 0 0 (piMat Nk) := by
    rw [Matrix.fromBlocks_toBlocks]; exact h
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h'
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg Matrix.toBlocks₁₂ h'
    simpa using this
  · have := congrArg Matrix.toBlocks₁₁ h'
    simpa using this
  · have := congrArg Matrix.toBlocks₂₂ h'
    simpa using this

lemma exch_sq (n : ℕ) : exch n * exch n = 1 := by
  ext i j
  simp only [exch, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.rev i)]
  · simp only [Fin.rev_rev, if_true, one_mul]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg, if_neg hij]
      intro h; apply hij; rw [Fin.rev_eq_iff] at h; rw [Fin.rev_rev] at h; exact h
  · intro k _ hk
    rw [if_neg]; · simp
    intro h; apply hk; rw [h, Fin.rev_rev]
  · simp

lemma sigmaZ_sq : sigmaZ * sigmaZ = 1 := by
  rw [sigmaZ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i; fin_cases i <;> simp

lemma piMat_sq (Nk : ℕ) : piMat Nk * piMat Nk = 1 := by
  unfold piMat
  rw [← Matrix.mul_kronecker_mul, exch_sq, sigmaZ_sq, Matrix.one_kronecker_one]

theorem solution {Nk : ℕ}
    (S1 S2 : Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ)
    (h1 : IsReciprocal S1) (h2 : IsReciprocal S2)
    (hQ : IsUnit (1 - S1.toBlocks₂₂ * S2.toBlocks₁₁).det)
    (S : Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ) :
    let r1 := S1.toBlocks₁₁
    let t1p := S1.toBlocks₁₂
    let t1 := S1.toBlocks₂₁
    let r1p := S1.toBlocks₂₂
    let r2 := S2.toBlocks₁₁
    let t2p := S2.toBlocks₁₂
    let t2 := S2.toBlocks₂₁
    let r2p := S2.toBlocks₂₂
    let Q := (1 - r1p * r2)⁻¹
    IsCascade S1 S2 S ↔
      S = Matrix.fromBlocks (r1 + t1p * r2 * Q * t1)
        (piMat Nk * (t2 * Q * t1).transpose * piMat Nk) (t2 * Q * t1) (r2p + t2 * Q * r1p * t2p) := by
  intro r1 t1p t1 r1p r2 t2p t2 r2p Q
  obtain ⟨a1, _, c1⟩ := sm_recip S1 h1
  obtain ⟨a2, b2, _⟩ := sm_recip S2 h2
  have := sm_main S1.toBlocks₁₁ S1.toBlocks₁₂ S1.toBlocks₂₁ S1.toBlocks₂₂
    S2.toBlocks₁₁ S2.toBlocks₁₂ S2.toBlocks₂₁ S2.toBlocks₂₂ (piMat Nk) (piMat_sq Nk)
    a1 a2 c1 b2 hQ S
  rw [Matrix.fromBlocks_toBlocks, Matrix.fromBlocks_toBlocks] at this
  exact this

