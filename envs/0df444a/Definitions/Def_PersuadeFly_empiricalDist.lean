-- Prove2me | Definitions.Def_PersuadeFly_empiricalDist
-- name    : PersuadeFly_empiricalDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:12.701997+00:00
-- url     : https://prove2.me/theorems/928311ec-1efc-4826-beab-36f70aa54fc1
-- title:
--   The empirical distribution $\gamma_t$
-- statement:
--   The empirical distribution of $t$ observed states $\omega_0,\dots,\omega_{t-1}$:
--   $$
--   \gamma_t(\omega)=\frac1t\sum_{\tau<t}\mathbf I\{\omega_\tau=\omega\}.
--   $$
--
--   **Formalization Note** Used for $t\ge1$ only.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2.2, p.15; Algorithm 1, p.21

import Mathlib

namespace PersuadeFly

/-- **The empirical distribution of `t` states.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2.2, p.15, and Algorithm 1, p.21:
`γ_t(ω) = (1/t) ∑_{τ<t} I{ω_τ = ω}`.

**Formalization Note** Used at `t ≥ 1` only; at `t = 0` Lean's `x / 0 = 0` would give the zero
function, and the algorithm uses its parameter `γ₀` there instead. -/
noncomputable def empiricalDist {Ω : Type} [DecidableEq Ω] (t : ℕ) (s : Fin t → Ω) : Ω → ℝ :=
  fun ω => ((Finset.univ.filter fun τ => s τ = ω).card : ℝ) / t

end PersuadeFly


