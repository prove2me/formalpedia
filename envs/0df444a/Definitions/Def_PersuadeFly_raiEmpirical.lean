-- Prove2me | Definitions.Def_PersuadeFly_raiEmpirical
-- name    : PersuadeFly_raiEmpirical
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:03.824808+00:00
-- url     : https://prove2.me/theorems/e68ee8de-6766-4e46-833e-2dfdc8880212
-- title:
--   The estimate $\gamma_t$ used by Rai
-- statement:
--   The estimate of Algorithm 1 (Rai) at time $t$ after history $h_t$: the parameter $\gamma_0\in\mathcal B_0$ at $t=0$, and the empirical distribution $\gamma_t$ of the states in $h_t$ for $t\ge1$.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Algorithm 1, p.21

import Mathlib
import Definitions.Def_PersuadeFly_empiricalDist

namespace PersuadeFly

/-- **The estimate `γ_t` used by Rai.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Algorithm 1, p.21: the parameter `γ₀ ∈ B₀` at `t = 0`,
and the empirical distribution of the states of the history `h_t` at `t ≥ 1`. -/
noncomputable def raiEmpirical {Ω A : Type} [DecidableEq Ω] (γ0 : Ω → ℝ) (t : ℕ)
    (h : Fin t → Ω × A) : Ω → ℝ :=
  if t = 0 then γ0 else empiricalDist t (fun τ => (h τ).1)

end PersuadeFly


