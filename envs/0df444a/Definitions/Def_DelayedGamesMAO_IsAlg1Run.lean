-- Prove2me | Definitions.Def_DelayedGamesMAO_IsAlg1Run
-- name    : DelayedGamesMAO_IsAlg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:09.998453+00:00
-- url     : https://prove2.me/theorems/f1c69fd5-ea41-4e8d-9620-9fe061bf9640
-- title:
--   A run of Algorithm 1 (MAO-OMD for delayed feedback)
-- statement:
--   Let $W$ be a set, $\psi$ a regularizer with gradient field $d\psi$, $w_0$ a reference point, $\gamma>0$ an optimism weight, $T$ a horizon, $(d_t)$ delays, $\alpha$ an allocation schedule, $(\eta_t)$ learning rates and $(g_t)$ the gradients revealed by the environment. A sequence of actions $(w_t)$ is a **run of Algorithm 1** if $w_1=w_0$ and, for every round $t\in[T]$,
--   $$
--   w_{t+1}\in\arg\min_{w\in W}\Bigl\{\langle\ell_t,w\rangle+\sum_{s=0}^{t}c^{(t+1)}_sD_\psi(w\mid w_s)+\gamma\,D_\psi(w\mid w_{s_{t+1}})\Bigr\},
--   $$
--   where $\ell_t=h_{t+1}+\sum_{s\in N_t}(g_s-h_s)$, $h_t$ are the hints, $s_{t+1}$ the hint source and $c^{(t+1)}_s$ the coefficients (8) built from $\gamma,\eta,\alpha$.
--
--   The update reads only gradients already revealed: those of rounds in $N_t$ and of the hint source $s_{t+1}\in O_{t+1}$.
--
--   **Formalization Note** $w_0$ is stored as the term of index $0$ of the sequence. The arg min is relational (any minimizer). Theorem 1 fixes $\alpha$ by (10), $\eta$ by (9) and $\gamma=\max\{4L,2G/\sqrt M\}$ (`IsMAOOMDRun`).
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, Algorithm 1, p.12

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF
import Definitions.Def_DelayedGamesMAO_hint
import Definitions.Def_DelayedGamesMAO_optLoss
import Definitions.Def_DelayedGamesMAO_coef

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **A run of Algorithm 1 (MAO-OMD for delayed feedback)** with a given optimism weight `γ`,
allocation schedule `α` and learning rates `η`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, Algorithm 1, p.12: "Input: `w_0 ∈ W`, regularizer `ψ`, optimism weight `γ > 0`,
allocation schedule `(α_s^{(t)})_{s≤t}`, learning rates `0 = η_1 ≤ ⋯ ≤ η_{T+1}`. Initialize:
`w_1 = w_0`, `s_1 = 0`, `h_1 = 0`, `g_0 = 0`. for `t = 1, …, T` do … Set
`s_{t+1} = min O_{t+1} \ {s_1, …, s_t}` (0 if empty) and `h_{t+1} = g_{s_{t+1}}` (0 if `t = T`).
… set `c_k^{(t+1)}` for `0 ≤ k ≤ t` as in (8). Set `ℓ_t = h_{t+1} + ∑_{s∈N_t}(g_s − h_s)`. Update
`w_{t+1} ∈ arg min_{w∈W} {⟨ℓ_t, w⟩ + ∑_{s=0}^t c_s^{(t+1)} D_ψ(w | w_s) + γ D_ψ(w | w_{s_{t+1}})}`."

`g t` is the gradient revealed for round `t` (at the end of round `t + d_t`); `w t` is the
action of round `t` (`w 0 = w_0` is the reference anchor).

**Formalization Note.** The run is a relation on the realized sequences: `w_{t+1}` is any
minimizer over `W` of the displayed objective. The objective reads `g_s` only for observed
rounds (`s ∈ N_t`, `s_{t+1} ∈ O_{t+1}`), as in the protocol. Hints are `hint d T g`, hint
sources `hintSrc d`, coefficients `coef d γ η α` ((8)), `D_ψ = TimeVaryingGames.bregman ψ dψ`.
The learning rates `η` and the schedule `α` are parameters here; Theorem 1 fixes them by (9)
and (10) (`IsMAOOMDRun`). -/
def IsAlg1Run {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Set E)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (w0 : E) (γ : ℝ) (T : ℕ) (d : ℕ → ℕ)
    (α : ℕ → ℕ → ℝ) (η : ℕ → ℝ) (g : ℕ → E →L[ℝ] ℝ) (w : ℕ → E) : Prop :=
  w 0 = w0 ∧ w 1 = w0 ∧ ∀ t ∈ Finset.Icc 1 T, w (t + 1) ∈ W ∧ ∀ v ∈ W,
    optLoss d g (hint d T g) t (w (t + 1)) +
        ∑ s ∈ Finset.range (t + 1),
          coef d γ η α (t + 1) s * TimeVaryingGames.bregman ψ dψ (w (t + 1)) (w s) +
        γ * TimeVaryingGames.bregman ψ dψ (w (t + 1)) (w (hintSrc d (t + 1))) ≤
      optLoss d g (hint d T g) t v +
        ∑ s ∈ Finset.range (t + 1), coef d γ η α (t + 1) s * TimeVaryingGames.bregman ψ dψ v (w s) +
        γ * TimeVaryingGames.bregman ψ dψ v (w (hintSrc d (t + 1)))

end DelayedGamesMAO


