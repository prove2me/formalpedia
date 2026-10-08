-- Prove2me | solution 1 for AronszajnRK.Limits.restricted_kernel_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:51:14.331432+00:00
-- url     : https://prove2.me/submissions/480eb1c5-46ac-4d4a-af69-3d5f26b2f722

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

set_option autoImplicit false

namespace Df15cfc7Aux

open scoped InnerProductSpace

lemma kerFun_inner_one {Y : Type*} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G Y ℂ] (x : Y) (f : G) :
    ⟪RKHS.kerFun G x 1, f⟫_ℂ = f x := by
  rw [RKHS.kerFun_inner]; simp

lemma kerFun_apply_one {Y : Type*} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G Y ℂ] (x y : Y) :
    RKHS.kerFun G y (1 : ℂ) x = AronszajnRK.Sum.kernelFn G x y := by
  rw [RKHS.kerFun_apply]
  rfl

lemma diag_eq {Y : Type*} (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G Y ℂ] (x : Y) :
    AronszajnRK.Sum.kernelFn G x x = ((‖RKHS.kerFun G x (1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : AronszajnRK.Sum.kernelFn G x x = ⟪RKHS.kerFun G x 1, RKHS.kerFun G x 1⟫_ℂ := by
    rw [kerFun_inner_one, kerFun_apply_one]
  rw [h1]
  exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (RKHS.kerFun G x (1 : ℂ))

end Df15cfc7Aux

open AronszajnRK.Limits ComplexOrder InnerProductSpace in
theorem solution {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) {k m n : ℕ} (hkm : k ≤ m)
    (hmn : m ≤ n) (y : X) (hy : y ∈ E k) (a b : H k)
    (ha : ∀ x : E k, a x = AronszajnRK.Sum.kernelFn (H m) (Set.inclusion (hS.mono hkm) x) ⟨y, hS.mono hkm hy⟩)
    (hb : ∀ x : E k, b x = AronszajnRK.Sum.kernelFn (H n) (Set.inclusion (hS.mono (hkm.trans hmn)) x)
      ⟨y, hS.mono (hkm.trans hmn) hy⟩) :
    ((‖a - b‖ ^ 2 : ℝ) : ℂ) ≤ AronszajnRK.Sum.kernelFn (H m) ⟨y, hS.mono hkm hy⟩ ⟨y, hS.mono hkm hy⟩ -
      AronszajnRK.Sum.kernelFn (H n) ⟨y, hS.mono (hkm.trans hmn) hy⟩ ⟨y, hS.mono (hkm.trans hmn) hy⟩ := by
  have hym : y ∈ E m := hS.mono hkm hy
  have hyn : y ∈ E n := hS.mono (hkm.trans hmn) hy
  obtain ⟨u, hu⟩ : ∃ w : H m, w = RKHS.kerFun (H m) (⟨y, hym⟩ : E m) (1 : ℂ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ w : H n, w = RKHS.kerFun (H n) (⟨y, hyn⟩ : E n) (1 : ℂ) := ⟨_, rfl⟩
  rw [Df15cfc7Aux.diag_eq, Df15cfc7Aux.diag_eq, ← hu, ← hv, ← Complex.ofReal_sub]
  apply Complex.real_le_real.mpr
  -- c : restriction of v to E m
  obtain ⟨c, hc⟩ := hS.restrict_mem hmn v
  have hcv : ‖c‖ ≤ ‖v‖ := hS.norm_restrict_le hmn v c hc
  -- a - b is the restriction of u - c to E k
  have hab : ‖a - b‖ ≤ ‖u - c‖ := by
    refine hS.norm_restrict_le hkm (u - c) (a - b) ?_
    intro x hxk hxm
    have h1 : u ⟨x, hxm⟩ = AronszajnRK.Sum.kernelFn (H m) ⟨x, hxm⟩ ⟨y, hym⟩ := by
      rw [hu, Df15cfc7Aux.kerFun_apply_one]
    have h2 : c ⟨x, hxm⟩ = AronszajnRK.Sum.kernelFn (H n) ⟨x, hS.mono hmn hxm⟩ ⟨y, hyn⟩ := by
      rw [hc x hxm (hS.mono hmn hxm), hv, Df15cfc7Aux.kerFun_apply_one]
    have h3 := ha ⟨x, hxk⟩
    have h4 := hb ⟨x, hxk⟩
    simp only [Set.inclusion] at h3 h4
    rw [show (a - b) ⟨x, hxk⟩ = a ⟨x, hxk⟩ - b ⟨x, hxk⟩ from by simp,
      show (u - c) ⟨x, hxm⟩ = u ⟨x, hxm⟩ - c ⟨x, hxm⟩ from by simp, h3, h4, h1, h2]
  -- ⟪u, c⟫ = c y = v y = ⟪v, v⟫
  have huc : ⟪u, c⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hu, Df15cfc7Aux.kerFun_inner_one, hc y hym hyn]
    have : v ⟨y, hyn⟩ = ⟪v, v⟫_ℂ := by
      nth_rewrite 2 [hv]
      rw [Df15cfc7Aux.kerFun_inner_one]
    rw [this]
    exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  have hre : RCLike.re ⟪u, c⟫_ℂ = ‖v‖ ^ 2 := by
    rw [huc, RCLike.re_to_complex, Complex.ofReal_re]
  have hsq : ‖u - c‖ ^ 2 = ‖u‖ ^ 2 - 2 * ‖v‖ ^ 2 + ‖c‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), hre]
  have hab2 : ‖a - b‖ ^ 2 ≤ ‖u - c‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hab 2
  have hc2 : ‖c‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcv 2
  linarith
