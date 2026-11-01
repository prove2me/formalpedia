-- Prove2me | Definitions.Def_OfflineToOnline_Approaches
-- name    : OfflineToOnline_Approaches
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:01.423541+00:00
-- url     : https://prove2.me/theorems/71a57a6c-45a0-41d0-bf9e-45bbc25f80f8
-- title:
--   $\ell_\infty$ approachability at horizon $T$ by a given strategy
-- statement:
--   Let $(\mathcal X,\mathcal Y,\boldsymbol p)$ be a Blackwell game, $S\subseteq\mathbb R^d$ a target set, $T\ge1$ a horizon and $g\in\mathbb R$. A payoff-based strategy $\mathrm{AlgB}$ **approaches $S$ at horizon $T$ with rate $g$** if its actions lie in $\mathcal X$ and, against every sequence $y_1,\dots,y_T\in\mathcal Y$, its play $x_1,\dots,x_T$ satisfies
--
--   $$
--   d_\infty\Big(\frac1T\sum_{t=1}^T\boldsymbol p(x_t,y_t),\ S\Big)\le g,\qquad d_\infty(w,S)=\inf_{v\in S}\|w-v\|_\infty .
--   $$
--
--   This is Definition 3 ($S$ is $g(T)$-approachable) for a fixed strategy and a fixed horizon, with the paper's $\ell_\infty$ distance.
--
--   **Formalization Note** `Metric.infDist` in `Fin d → ℝ` is the $\ell_\infty$ distance. The strategy may depend on $T$ (Algorithm 2 receives $T$ as input).
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 3, p.12

import Mathlib
import Definitions.Def_OfflineToOnline_payoffPlay

namespace OfflineToOnline

/-- ℓ∞ approachability at horizon `T` (Definition 3, p.12) by a given payoff-based strategy: `A`
plays in `X`, and against every sequence of player 2 actions in `Y`,
`d∞((1/T) ∑_{t=1}^T p(x_t, y_t), S) ≤ g`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 3, p.12 (with `g = g(T)`).

Formalization Note: `Metric.infDist` in `Fin d → ℝ` is the ℓ∞ distance `d∞(w, S) = inf_{v ∈ S}
‖w − v‖_∞`. Rounds are `0, …, T − 1`. The strategy may depend on `T`. Against a deterministic
strategy "every player 2 strategy" is "every sequence of actions in `Y`". -/
def Approaches {m k d : ℕ} (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ))
    (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ)) (S : Set (Fin d → ℝ)) (A : PayoffStrategy m d)
    (T : ℕ) (g : ℝ) : Prop :=
  (∀ (t : ℕ) (h : Fin t → (Fin m → ℝ) × (Fin d → ℝ)), A t h ∈ X) ∧
  ∀ y : ℕ → Fin k → ℝ, (∀ t < T, y t ∈ Y) →
    Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, p (payoffPlay p A y t) (y t)) S ≤ g

end OfflineToOnline


