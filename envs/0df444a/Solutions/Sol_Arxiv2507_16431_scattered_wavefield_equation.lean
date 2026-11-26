-- Prove2me | solution 1 for Arxiv2507_16431.scattered_wavefield_equation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:47:30.75071+00:00
-- url     : https://prove2.me/submissions/da712fb9-300e-4393-bd72-2dcd8956867c

import Mathlib
import Definitions.Def_Arxiv2507_16431_Basic

set_option autoImplicit false

open Arxiv2507_16431 in
theorem solution (Ω : Set Plane) (hΩ : IsOpen Ω) (ω : ℝ) (hω : 0 < ω)
    (v v0 : Plane → ℝ) (hv : ∀ x ∈ Ω, 0 < v x) (hv0 : ∀ x ∈ Ω, 0 < v0 x)
    (f U U0 : Plane → ℂ) (hU : ContDiffOn ℝ 2 U Ω) (hU0 : ContDiffOn ℝ 2 U0 Ω)
    (hUeq : ∀ x ∈ Ω, helmholtzOp v ω U x = f x)
    (hU0eq : ∀ x ∈ Ω, helmholtzOp v0 ω U0 x = f x) :
    ∀ x ∈ Ω, ((ω ^ 2 / v x ^ 2 : ℝ) : ℂ) * scatteredField U U0 x
        + Laplacian.laplacian (scatteredField U U0) x
        + ((ω ^ 2 * (1 / v x ^ 2 - 1 / v0 x ^ 2) : ℝ) : ℂ) * U0 x = 0 := by
  intro x hx
  have h1 : ContDiffAt ℝ 2 U x := hU.contDiffAt (hΩ.mem_nhds hx)
  have h2 : ContDiffAt ℝ 2 U0 x := hU0.contDiffAt (hΩ.mem_nhds hx)
  have e : scatteredField U U0 = U - U0 := rfl
  have a := hUeq x hx
  have b := hU0eq x hx
  unfold helmholtzOp at a b
  rw [e, h1.laplacian_sub h2]
  simp only [Pi.sub_apply]
  push_cast at a b ⊢
  linear_combination a - b
