-- Prove2me | solution 1 for Arxiv1110_5134.layered_clausius_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:37:01.252898+00:00
-- url     : https://prove2.me/submissions/23630423-eec5-4445-928f-3e2d933a0cb6

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n₁ n₂ I₁ I₂ θ₁ θ₂' : ℝ) (θ₂ : ℝ → ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hsnell : ∀ᶠ t in 𝓝 θ₁, n₁ * Real.sin t = n₂ * Real.sin (θ₂ t))
    (hθ₂ : HasDerivAt θ₂ θ₂' θ₁)
    (henergy : I₁ * Real.cos θ₁ * Real.sin θ₁ =
      I₂ * Real.cos (θ₂ θ₁) * Real.sin (θ₂ θ₁) * θ₂') :
    HasDerivAt (fun t => n₂ ^ 2 * Real.cos (θ₂ t) ^ 2)
      (n₁ ^ 2 * (-(2 * Real.cos θ₁ * Real.sin θ₁))) θ₁ ∧
    I₁ / n₁ ^ 2 = I₂ / n₂ ^ 2 := by
  have heq : (fun t => n₂ ^ 2 * Real.cos (θ₂ t) ^ 2) =ᶠ[𝓝 θ₁]
      (fun t => n₂ ^ 2 - n₁ ^ 2 * Real.sin t ^ 2) := by
    filter_upwards [hsnell] with t ht
    have hcs : Real.cos (θ₂ t) ^ 2 = 1 - Real.sin (θ₂ t) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (θ₂ t)]
    calc
      n₂ ^ 2 * Real.cos (θ₂ t) ^ 2 = n₂ ^ 2 * (1 - Real.sin (θ₂ t) ^ 2) := by rw [hcs]
      _ = n₂ ^ 2 - (n₂ * Real.sin (θ₂ t)) ^ 2 := by ring
      _ = n₂ ^ 2 - (n₁ * Real.sin t) ^ 2 := by rw [← ht]
      _ = n₂ ^ 2 - n₁ ^ 2 * Real.sin t ^ 2 := by ring
  have hd_rhs : HasDerivAt (fun t => n₂ ^ 2 - n₁ ^ 2 * Real.sin t ^ 2)
      (n₁ ^ 2 * (-(2 * Real.cos θ₁ * Real.sin θ₁))) θ₁ := by
    have hsin2 := ((Real.hasDerivAt_sin θ₁).pow 2).const_mul (n₁ ^ 2)
    have hsub := (hasDerivAt_const θ₁ (n₂ ^ 2)).sub hsin2
    have hfn : (fun t => n₂ ^ 2 - n₁ ^ 2 * Real.sin t ^ 2) =
        ((fun _ => n₂ ^ 2) - fun t => n₁ ^ 2 * Real.sin t ^ 2) := by
      ext t; rfl
    have hval : n₁ ^ 2 * (-(2 * Real.cos θ₁ * Real.sin θ₁)) =
        0 - n₁ ^ 2 * (↑2 * Real.sin θ₁ ^ (2 - 1) * Real.cos θ₁) := by
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
    rw [hfn, hval]
    exact hsub
  have hd1 : HasDerivAt (fun t => n₂ ^ 2 * Real.cos (θ₂ t) ^ 2)
      (n₁ ^ 2 * (-(2 * Real.cos θ₁ * Real.sin θ₁))) θ₁ :=
    hd_rhs.congr_of_eventuallyEq heq
  refine ⟨hd1, ?_⟩
  have hcos : HasDerivAt (fun t => Real.cos (θ₂ t)) (-Real.sin (θ₂ θ₁) * θ₂') θ₁ :=
    hθ₂.cos
  have hd2 : HasDerivAt (fun t => n₂ ^ 2 * Real.cos (θ₂ t) ^ 2)
      (n₂ ^ 2 * (2 * Real.cos (θ₂ θ₁) ^ (2 - 1) * (-Real.sin (θ₂ θ₁) * θ₂'))) θ₁ :=
    (hcos.pow 2).const_mul (n₂ ^ 2)
  have huniq : n₁ ^ 2 * (-(2 * Real.cos θ₁ * Real.sin θ₁)) =
      n₂ ^ 2 * (2 * Real.cos (θ₂ θ₁) ^ (2 - 1) * (-Real.sin (θ₂ θ₁) * θ₂')) :=
    hd1.unique hd2
  have hrel : n₁ ^ 2 * (Real.cos θ₁ * Real.sin θ₁) =
      n₂ ^ 2 * (Real.cos (θ₂ θ₁) * Real.sin (θ₂ θ₁) * θ₂') := by
    norm_num at huniq
    linarith
  have hsin_pos : 0 < Real.sin θ₁ :=
    Real.sin_pos_of_pos_of_lt_pi hθ₁.1 (by linarith [hθ₁.2, Real.pi_pos])
  have hcos_pos : 0 < Real.cos θ₁ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ₁.1, Real.pi_pos], hθ₁.2⟩
  have hcs_ne : Real.cos θ₁ * Real.sin θ₁ ≠ 0 := mul_ne_zero hcos_pos.ne' hsin_pos.ne'
  have hcross : I₁ * n₂ ^ 2 * (Real.cos θ₁ * Real.sin θ₁) =
      I₂ * n₁ ^ 2 * (Real.cos θ₁ * Real.sin θ₁) := by
    calc
      I₁ * n₂ ^ 2 * (Real.cos θ₁ * Real.sin θ₁)
          = n₂ ^ 2 * (I₁ * Real.cos θ₁ * Real.sin θ₁) := by ring
      _ = n₂ ^ 2 * (I₂ * Real.cos (θ₂ θ₁) * Real.sin (θ₂ θ₁) * θ₂') := by rw [henergy]
      _ = I₂ * (n₂ ^ 2 * (Real.cos (θ₂ θ₁) * Real.sin (θ₂ θ₁) * θ₂')) := by ring
      _ = I₂ * (n₁ ^ 2 * (Real.cos θ₁ * Real.sin θ₁)) := by rw [← hrel]
      _ = I₂ * n₁ ^ 2 * (Real.cos θ₁ * Real.sin θ₁) := by ring
  have hmul : I₁ * n₂ ^ 2 = I₂ * n₁ ^ 2 := mul_right_cancel₀ hcs_ne hcross
  have hn1_ne : n₁ ^ 2 ≠ 0 := pow_ne_zero 2 hn₁.ne'
  have hn2_ne : n₂ ^ 2 ≠ 0 := pow_ne_zero 2 hn₂.ne'
  rw [div_eq_div_iff hn1_ne hn2_ne]
  exact hmul
