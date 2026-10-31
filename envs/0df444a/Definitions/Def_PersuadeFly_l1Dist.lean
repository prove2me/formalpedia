-- Prove2me | Definitions.Def_PersuadeFly_l1Dist
-- name    : PersuadeFly_l1Dist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:09.645991+00:00
-- url     : https://prove2.me/theorems/691b7543-7508-4f79-93a6-50d8f4d45a8b
-- title:
--   The $\ell_1$ distance $\|\mu-\nu\|_1$
-- statement:
--   The $\ell_1$ distance between two functions on $\Omega$:
--   $$
--   \|\mu-\nu\|_1=\sum_{\omega\in\Omega}|\mu(\omega)-\nu(\omega)|.
--   $$
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §3, p.21

import Mathlib

namespace PersuadeFly

/-- **The `ℓ₁` distance `‖μ − ν‖₁`.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §3, p.21: `‖μ − ν‖₁ = ∑_{ω ∈ Ω} |μ(ω) − ν(ω)|`. -/
def l1Dist {Ω : Type} [Fintype Ω] (μ ν : Ω → ℝ) : ℝ :=
  ∑ ω, |μ ω - ν ω|

end PersuadeFly


