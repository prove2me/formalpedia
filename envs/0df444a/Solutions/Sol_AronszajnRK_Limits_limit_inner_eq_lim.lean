-- Prove2me | solution 1 for AronszajnRK.Limits.limit_inner_eq_lim
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:09:22.265284+00:00
-- url     : https://prove2.me/submissions/4ec1fc5d-e45d-4230-b367-2b4c9b8204e4

import Mathlib
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace

open AronszajnRK.Limits Filter Topology InnerProductSpace in
theorem solution {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H)
    (H₀ : Type*) [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [RKHS ℂ H₀ X ℂ]
    (hnorm : ∀ (f₀ : H₀) (g : ∀ n, H n), (∀ (n : ℕ) (x : E n), g n x = f₀ x.1) →
      Tendsto (fun n => ‖g n‖) atTop (𝓝 ‖f₀‖))
    (f₀ g₀ : H₀) (a b : ∀ n, H n) (ha : ∀ (n : ℕ) (x : E n), a n x = f₀ x.1)
    (hb : ∀ (n : ℕ) (x : E n), b n x = g₀ x.1) :
    Tendsto (fun n => ⟪b n, a n⟫_ℂ) atTop (𝓝 ⟪g₀, f₀⟫_ℂ) := by
  have key : ∀ (u : H₀) (v : ∀ n, H n), (∀ (n : ℕ) (x : E n), v n x = u x.1) →
      Tendsto (fun n => ((‖v n‖ : ℂ)) ^ 2) atTop (𝓝 ((‖u‖ : ℂ) ^ 2)) := fun u v hv =>
    ((Complex.continuous_ofReal.tendsto _).comp (hnorm u v hv)).pow 2
  have h1 := key (g₀ + f₀) (fun n => b n + a n) (by intro n x; simp [ha, hb])
  have h2 := key (g₀ - f₀) (fun n => b n - a n) (by intro n x; simp [ha, hb])
  have h3 := key (g₀ - (RCLike.I : ℂ) • f₀) (fun n => b n - (RCLike.I : ℂ) • a n)
    (by intro n x; simp [ha, hb])
  have h4 := key (g₀ + (RCLike.I : ℂ) • f₀) (fun n => b n + (RCLike.I : ℂ) • a n)
    (by intro n x; simp [ha, hb])
  have hlim := (((h1.sub h2).add ((h3.sub h4).mul_const (RCLike.I : ℂ))).div_const 4)
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) g₀ f₀]
  refine hlim.congr (fun n => ?_)
  exact (inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (b n) (a n)).symm
