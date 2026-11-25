-- Prove2me | solution 1 for Arxiv1003_4724.time_correlations_real
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:43:11.742794+00:00
-- url     : https://prove2.me/submissions/68c0c50f-a0a9-4ebe-a6e8-d326de7529d5

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology
namespace Arxiv1003_4724

lemma tc_herm {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (ω : A →ₗ[ℂ] ℂ) (hω : IsState ω) (Y : A) : ω (star Y) = star (ω Y) := by
  obtain ⟨-, hpos⟩ := hω
  have h1 := (hpos (1 + Y)).1
  have h2 := (hpos (1 + Complex.I • Y)).1
  have e1 : star (1 + Y) * (1 + Y) = 1 + Y + star Y + star Y * Y := by
    simp [star_add, star_one, add_mul, mul_add]; abel
  have e2 : star (1 + Complex.I • Y) * (1 + Complex.I • Y) =
      1 + Complex.I • Y - Complex.I • star Y + star Y * Y := by
    simp [star_add, star_one, add_mul, mul_add, star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    abel
  rw [e1, map_add, map_add, map_add] at h1
  rw [e2, map_add, map_sub, map_add, map_smul, map_smul] at h2
  have h0 := (hpos 1).1
  have h3 := (hpos Y).1
  simp only [star_one, one_mul] at h0
  simp only [Complex.add_im, Complex.sub_im, smul_eq_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im] at h1 h2
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; linarith
  · simp only [Complex.star_def, Complex.conj_im]; linarith

lemma tc_re {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (ω : A →ₗ[ℂ] ℂ) (hω : IsState ω) (X Y : A) (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    (ω ⁅X, Y⁆).re = 0 := by
  have hs : star ⁅X, Y⁆ = -⁅X, Y⁆ := by
    rw [Ring.lie_def, star_sub, star_mul, star_mul, hX.star_eq, hY.star_eq]; abel
  have := tc_herm ω hω ⁅X, Y⁆
  rw [hs, map_neg] at this
  have := congrArg Complex.re this
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
  linarith

theorem time_correlations_real {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A]
    (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A)
    (hM : IsLongWaveModel ω τ Dip Cur) (hbar V : ℝ) (hhbar : 0 < hbar) (hV : 0 < V) :
    ∀ t : ℝ,
      (sigmaCorr ω τ hbar V Dip Cur t).im = 0 ∧ (phiCorr ω τ hbar V Cur t).im = 0 := by
  obtain ⟨hst, -, -, hsa, -⟩ := hM
  intro t
  have key : ∀ X Y : A, IsSelfAdjoint X → IsSelfAdjoint Y → (commCorr ω τ X Y t).re = 0 := by
    intro X Y hX hY
    unfold commCorr
    exact tc_re ω hst _ _ (by
      show star (τ t X) = τ t X
      rw [← map_star, hX.star_eq]) hY
  have hsum : ∀ (F : Fin 3 → A) (G : Fin 3 → A), (∀ β, IsSelfAdjoint (F β)) →
      (∀ β, IsSelfAdjoint (G β)) → (∑ β, commCorr ω τ (F β) (G β) t).re = 0 := by
    intro F G hF hG
    rw [Complex.re_sum]
    exact Finset.sum_eq_zero fun β _ => key _ _ (hF β) (hG β)
  have hr : ((3 : ℂ) * hbar * V).im = 0 := by simp
  have hr' : ((3 : ℂ) * hbar * V).re = 3 * hbar * V := by simp
  constructor
  · unfold sigmaCorr
    have := hsum Cur Dip (fun β => (hsa β).2) (fun β => (hsa β).1)
    rw [Complex.mul_im, Complex.div_re, Complex.div_im, this]
    simp
  · unfold phiCorr
    have := hsum Cur Cur (fun β => (hsa β).2) (fun β => (hsa β).2)
    rw [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im, this]
    simp

end Arxiv1003_4724
open Arxiv1003_4724 in
theorem solution {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A]
    (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A)
    (hM : IsLongWaveModel ω τ Dip Cur) (hbar V : ℝ) (hhbar : 0 < hbar) (hV : 0 < V) :
    ∀ t : ℝ,
      (sigmaCorr ω τ hbar V Dip Cur t).im = 0 ∧ (phiCorr ω τ hbar V Cur t).im = 0 :=
  time_correlations_real ω τ Dip Cur hM hbar V hhbar hV
