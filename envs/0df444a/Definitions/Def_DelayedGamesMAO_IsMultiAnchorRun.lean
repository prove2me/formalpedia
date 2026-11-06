-- Prove2me | Definitions.Def_DelayedGamesMAO_IsMultiAnchorRun
-- name    : DelayedGamesMAO_IsMultiAnchorRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:07.023713+00:00
-- url     : https://prove2.me/theorems/099d52da-1fed-4426-ab40-f2a5e9dc135e
-- title:
--   A run of the multi-anchor update (MAO)
-- statement:
--   Let $W$ be a set, $\psi$ a regularizer with gradient field $d\psi$, $w_0$ a reference point, $T$ a horizon, $(\ell_t)$ loss vectors and $(c^{(t)}_k)$ anchor weights. A sequence $(w_t)$ is a **run of the multi-anchor update** if $w$ starts at $w_0$ and, for every $t\in\{0,\dots,T\}$,
--   $$
--   w_{t+1}\in\arg\min_{w\in W}\Bigl\{\langle\ell_t,w\rangle+\sum_{k=0}^{t}c^{(t+1)}_kD_\psi(w\mid w_k)\Bigr\}.
--   $$
--   With $\ell_t=h_{t+1}+\sum_{s\in N_t}(g_s-h_s)$ this is the update (MAO) of the paper; Proposition 2 uses general $\ell_t$.
--
--   **Formalization Note** The arg min is a relation: $w_{t+1}$ is any minimizer over $W$. $D_\psi$ is `TimeVaryingGames.bregman ψ dψ`.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), (MAO), p.9; Proposition 2, p.14

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **A run of the multi-anchor mirror-descent update** from `w_0`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), (MAO) p.9 and Proposition 2, p.14: for every `t ∈ {0, …, T}`,
`w_{t+1} ∈ arg min_{w∈W} {⟨ℓ_t, w⟩ + ∑_{k=0}^t c_k^{(t+1)} D_ψ(w | w_k)}`.

`ℓ t` is the loss vector of the update computing `w_{t+1}`, `c t k = c_k^{(t)}`, and
`D_ψ = TimeVaryingGames.bregman ψ dψ`.

**Formalization Note.** `w 0 = w0` is the initial anchor; `arg min` is relational (any
minimizer over `W` is allowed). (MAO) with `ℓ_t = h_{t+1} + ∑_{s∈N_t}(g_s − h_s)` is this
predicate with `ℓ = optLoss d g h`. -/
def IsMultiAnchorRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Set E)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (w0 : E) (T : ℕ) (ℓ : ℕ → E →L[ℝ] ℝ)
    (c : ℕ → ℕ → ℝ) (w : ℕ → E) : Prop :=
  w 0 = w0 ∧ ∀ t ∈ Finset.range (T + 1), w (t + 1) ∈ W ∧ ∀ v ∈ W,
    ℓ t (w (t + 1)) +
        ∑ k ∈ Finset.range (t + 1), c (t + 1) k * TimeVaryingGames.bregman ψ dψ (w (t + 1)) (w k) ≤
      ℓ t v + ∑ k ∈ Finset.range (t + 1), c (t + 1) k * TimeVaryingGames.bregman ψ dψ v (w k)

end DelayedGamesMAO


