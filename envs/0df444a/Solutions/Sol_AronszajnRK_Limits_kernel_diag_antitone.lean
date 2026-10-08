-- Prove2me | solution 1 for AronszajnRK.Limits.kernel_diag_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:54:53.167169+00:00
-- url     : https://prove2.me/submissions/1d8acf99-999d-48c2-8849-68242c4fec95

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

set_option autoImplicit false

namespace B33037Aux

open scoped InnerProductSpace

lemma kerFun_inner_one {Y : Type*} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G Y ℂ] (x : Y) (f : G) :
    ⟪RKHS.kerFun G x 1, f⟫_ℂ = f x := by
  rw [RKHS.kerFun_inner]; simp

lemma diag_eq {Y : Type*} (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G Y ℂ] (x : Y) :
    AronszajnRK.Sum.kernelFn G x x = ((‖RKHS.kerFun G x (1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : AronszajnRK.Sum.kernelFn G x x = ⟪RKHS.kerFun G x 1, RKHS.kerFun G x 1⟫_ℂ := by
    rw [kerFun_inner_one, RKHS.kerFun_apply]
    rfl
  rw [h1]
  exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (RKHS.kerFun G x (1 : ℂ))

lemma diag_le {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : AronszajnRK.Limits.IsDecreasingRKSequence E H)
    {m n : ℕ} (hmn : m ≤ n) (y : X) (hm : y ∈ E m) (hn : y ∈ E n) :
    ‖RKHS.kerFun (H n) (⟨y, hn⟩ : E n) (1 : ℂ)‖ ≤ ‖RKHS.kerFun (H m) (⟨y, hm⟩ : E m) (1 : ℂ)‖ := by
  obtain ⟨v, hv⟩ : ∃ w : H n, w = RKHS.kerFun (H n) (⟨y, hn⟩ : E n) (1 : ℂ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ w : H m, w = RKHS.kerFun (H m) (⟨y, hm⟩ : E m) (1 : ℂ) := ⟨_, rfl⟩
  rw [← hv, ← hu]
  obtain ⟨g, hg⟩ := hS.restrict_mem hmn v
  have hgv : ‖g‖ ≤ ‖v‖ := hS.norm_restrict_le hmn v g hg
  have hvv : ⟪v, v⟫_ℂ = ⟪u, g⟫_ℂ := by
    nth_rewrite 1 [hv]
    rw [hu, kerFun_inner_one, kerFun_inner_one, hg y hm hn]
  have hv2 : ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  have h1 : ‖v‖ ^ 2 ≤ ‖u‖ * ‖v‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) u g
    rw [← hvv, hv2, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    nlinarith [norm_nonneg u]
  nlinarith [norm_nonneg u, norm_nonneg v, sq_nonneg (‖v‖ - ‖u‖)]

end B33037Aux

open AronszajnRK.Limits ComplexOrder in
theorem solution {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) (k : ℕ) (y : X)
    (hy : y ∈ E k) :
    Antitone (fun j : ℕ => AronszajnRK.Sum.kernelFn (H (k + j)) ⟨y, hS.mono (Nat.le_add_right k j) hy⟩
        ⟨y, hS.mono (Nat.le_add_right k j) hy⟩) ∧
      ∀ j : ℕ, 0 ≤ AronszajnRK.Sum.kernelFn (H (k + j)) ⟨y, hS.mono (Nat.le_add_right k j) hy⟩
        ⟨y, hS.mono (Nat.le_add_right k j) hy⟩ := by
  constructor
  · apply antitone_nat_of_succ_le
    intro j
    rw [B33037Aux.diag_eq, B33037Aux.diag_eq]
    exact Complex.real_le_real.mpr (pow_le_pow_left₀ (norm_nonneg _)
      (B33037Aux.diag_le E H hS (by omega) y _ _) 2)
  · intro j
    rw [B33037Aux.diag_eq]
    exact Complex.zero_le_real.mpr (by positivity)
