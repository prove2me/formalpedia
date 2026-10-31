-- Prove2me | Definitions.Def_PersuadeFly_raiSet
-- name    : PersuadeFly_raiSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:07.994303+00:00
-- url     : https://prove2.me/theorems/b40acdf0-9f92-4a01-8851-8c0439e6d81e
-- title:
--   The confidence sets $\mathcal B_t$ of Rai
-- statement:
--   The confidence set of Rai at time $t$ after history $h_t$:
--   $$
--   \mathcal B_t=\mathsf B_1(\gamma_t,\epsilon_t)\quad(t\ge1),\qquad \mathcal B_0=\mathcal C_0,
--   $$
--   for a first-round set $\mathcal C_0$ and a radius sequence $(\epsilon_t)$.
--
--   **Formalization Note** Algorithm 1 sets only $\mathcal B_{t+1}$, so its first set reads as the instance's $\mathcal B_0$; the text of p.20 and the proofs use $\mathsf B_1(\gamma_0,2)=\Delta(\Omega)$. The first set is therefore a parameter $\mathcal C_0$, and the theorems assume $\mathcal B_0\subseteq\mathcal C_0\subseteq\Delta(\Omega)$, which covers both readings.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Algorithm 1, p.21; §3, pp.20–21

import Mathlib
import Definitions.Def_PersuadeFly_ball1
import Definitions.Def_PersuadeFly_raiEmpirical

namespace PersuadeFly

/-- **The confidence sets `B_t` of Rai.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Algorithm 1, p.21, and §3, pp.20–21:
`B_t = B₁(γ_t, ϵ_t)` for `t ≥ 1`, and a first-round set `C₀` at `t = 0`.

**Formalization Note** Algorithm 1 never sets `B₀` explicitly (its loop sets `B_{t+1}`), so at
`t = 0` it reads as the instance's `B₀`; the text of p.20 and the proofs (pp.33, 38, 41) instead use
`B₁(γ₀, ϵ₀) = Δ(Ω)` with `ϵ₀ = 2`. Both readings are covered: the first set is a parameter `C₀`, and
the theorems assume `B₀ ⊆ C₀ ⊆ Δ(Ω)`. The radius sequence `ε` is a parameter (Algorithm 1's
`{ϵ_t > 0}`); `ε 0` is never read. -/
noncomputable def raiSet {Ω A : Type} [Fintype Ω] [DecidableEq Ω] (γ0 : Ω → ℝ)
    (C0 : Set (Ω → ℝ)) (ε : ℕ → ℝ) (t : ℕ) (h : Fin t → Ω × A) : Set (Ω → ℝ) :=
  if t = 0 then C0 else ball1 (raiEmpirical γ0 t h) (ε t)

end PersuadeFly


