-- Prove2me | solution 1 for Arxiv2608_05214.traveltime_webster_horn
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:43:31.892357+00:00
-- url     : https://prove2.me/submissions/3d516413-781d-48fc-8798-3483f2ccc49b

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

set_option autoImplicit false

open Arxiv2608_05214 in
theorem solution (ρ c Z : ℝ → ℝ) (w : ℝ → ℝ → ℝ)
    (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    (hZ : ∀ x, ρ x * c x = Z (travelTime c x))
    (hw : ∀ τ t, DifferentiableAt ℝ (fun τ => w τ t) τ)
    (hflux : ∀ τ t, DifferentiableAt ℝ (fun τ => Z τ * deriv (fun τ => w τ t) τ) τ) :
    ∀ x t : ℝ,
      c x * waveEqLHS ρ c (fun x t => w (travelTime c x) t) x t = hornEqLHS Z w (travelTime c x) t ∧
      (waveEqLHS ρ c (fun x t => w (travelTime c x) t) x t = 0 ↔
        hornEqLHS Z w (travelTime c x) t = 0) := by
  have hcont : Continuous (fun y => 1 / c y) :=
    continuous_const.div hc (fun y => (hcpos y).ne')
  have hτ : ∀ x, HasDerivAt (travelTime c) (1 / c x) x := by
    intro x
    exact (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have key : ∀ x t : ℝ,
      c x * waveEqLHS ρ c (fun x t => w (travelTime c x) t) x t = hornEqLHS Z w (travelTime c x) t := by
    intro x t
    have hu : ∀ y, deriv (fun y => w (travelTime c y) t) y =
        deriv (fun τ => w τ t) (travelTime c y) * (1 / c y) := by
      intro y
      exact ((hw (travelTime c y) t).hasDerivAt.comp y (hτ y)).deriv
    have hfun : (fun y => ρ y * c y ^ 2 * deriv (fun y => w (travelTime c y) t) y) =
        fun y => Z (travelTime c y) * deriv (fun τ => w τ t) (travelTime c y) := by
      funext y
      rw [hu y, ← hZ y]
      have := (hcpos y).ne'
      field_simp
    have hd : deriv (fun y => Z (travelTime c y) * deriv (fun τ => w τ t) (travelTime c y)) x =
        deriv (fun τ => Z τ * deriv (fun τ => w τ t) τ) (travelTime c x) * (1 / c x) :=
      ((hflux (travelTime c x) t).hasDerivAt.comp x (hτ x)).deriv
    unfold waveEqLHS hornEqLHS
    simp only
    rw [hfun, hd, ← hZ x]
    have := (hcpos x).ne'
    field_simp
  intro x t
  refine ⟨key x t, ?_⟩
  rw [← key x t]
  have := (hcpos x).ne'
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.1 h).resolve_left this
