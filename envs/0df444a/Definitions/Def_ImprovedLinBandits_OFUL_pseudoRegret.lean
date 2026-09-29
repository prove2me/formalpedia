-- Prove2me | Definitions.Def_ImprovedLinBandits_OFUL_pseudoRegret
-- name    : ImprovedLinBandits_OFUL_pseudoRegret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:19:57.629683+00:00
-- url     : https://prove2.me/theorems/9b731f23-c272-438d-98be-57beec777541
-- title:
--   Pseudo-regret $R_n = \sum_{t\le n}\langle x^*_t - X_t, \theta_*\rangle$
-- statement:
--   Let $D_1, D_2, \dots \subseteq \mathbb R^d$ be the decision sets, $X_t \in D_t$ the actions and $\theta_* \in \mathbb R^d$ the unknown parameter. The **pseudo-regret** after $n$ rounds is
--
--   $$R_n = \sum_{t=1}^n \langle x^*_t - X_t, \theta_* \rangle = \sum_{t=1}^n \Big( \sup_{x \in D_t} \langle x, \theta_* \rangle - \langle X_t, \theta_* \rangle \Big),$$
--
--   where $x^*_t = \operatorname{argmax}_{x \in D_t} \langle x, \theta_*\rangle$ is the optimal action of round $t$. $R_0 = 0$.
--
--   It is the difference between the total expected reward of the optimal strategy and that of the learner, and is the quantity bounded in Theorem 3.
--
--   **Formalization Note** $\langle x^*_t, \theta_*\rangle$ is written as the real supremum of $\langle x, \theta_*\rangle$ over $D_t$, which equals the paper's maximum when the maximum is attained. Lean's supremum is $0$ on an empty or unbounded-above set; the theorems using $R_n$ assume $D_t$ nonempty and $\langle x, \theta_*\rangle \le 1$ on $D_t$, so this never occurs there.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, pp. 2–3, §1.2 (definition of the pseudo-regret $R_n$)

import Mathlib

open Matrix

namespace ImprovedLinBandits.OFUL

/-- The pseudo-regret (Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011, pp. 2–3):
`R_n = ∑_{t=1}^n ⟨x*_t - X_t, θ*⟩`, where `⟨x*_t, θ*⟩ = max_{x ∈ D_t} ⟨x, θ*⟩`. The optimal
expected reward is written as the real supremum `sSup {⟨x, θ*⟩ : x ∈ D_t}`, which equals the
paper's maximum whenever that maximum is attained. It is meaningful when `D_t` is nonempty and
`⟨·, θ*⟩` is bounded above on it (Lean's `sSup` returns `0` otherwise). Rounds are indexed
`t + 1` for `t ∈ Finset.range n`; `pseudoRegret d D X θstar 0 ω = 0`. -/
noncomputable def pseudoRegret {Ω : Type*} (d : ℕ) (D : ℕ → Ω → Set (Fin d → ℝ))
    (X : ℕ → Ω → Fin d → ℝ) (θstar : Fin d → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n,
    (sSup ((fun x => x ⬝ᵥ θstar) '' D (t + 1) ω) - X (t + 1) ω ⬝ᵥ θstar)

end ImprovedLinBandits.OFUL


