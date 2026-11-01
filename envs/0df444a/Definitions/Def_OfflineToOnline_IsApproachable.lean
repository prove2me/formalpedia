-- Prove2me | Definitions.Def_OfflineToOnline_IsApproachable
-- name    : OfflineToOnline_IsApproachable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:08.886706+00:00
-- url     : https://prove2.me/theorems/11187afa-748d-4c6d-aaa0-2297b197919f
-- title:
--   Approachable target set
-- statement:
--   A target set $S\subseteq\mathbb R^d$ is **approachable** in the Blackwell game $(\mathcal X,\mathcal Y,\boldsymbol p)$ if it is $g(T)$-approachable (Definition 3) for some rate $g(T)\to0$. Equivalently: for every $\varepsilon>0$ there is $T_0$ such that for every horizon $T\ge T_0$ some player 1 strategy with actions in $\mathcal X$ guarantees
--
--   $$
--   d_\infty\Big(\frac1T\sum_{t=1}^T\boldsymbol p(x_t,y_t),\ S\Big)\le\varepsilon
--   $$
--
--   against every sequence $y_1,\dots,y_T\in\mathcal Y$.
--
--   This is "the approachability condition" to which Proposition 1 compares satisfiability and its variants.
--
--   **Formalization Note** Strategies are deterministic and full-history; the distance is the $\ell_\infty$ distance (`Metric.infDist` in `Fin d → ℝ`).
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 3, p.12; Proposition 1, p.45

import Mathlib
import Definitions.Def_OfflineToOnline_fullHistoryPlay

namespace OfflineToOnline

/-- (Asymptotic) approachability, "the approachability condition (Definition 3)" of
Proposition 1, p.45: `S` is `g(T)`-approachable for some `g(T) → 0`. Equivalently: for every
`ε > 0` there is `T₀` such that for every horizon `T ≥ T₀` some player 1 strategy with actions in
`X` keeps `d∞((1/T) ∑_t p(x_t, y_t), S) ≤ ε` against every sequence of player 2 actions in `Y`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 3, p.12, and p.12 ("g(T) in Definition 3 converges to 0"); Proposition 1, p.45.

Formalization Note: strategies are deterministic and full-history; `Metric.infDist` in
`Fin d → ℝ` is the ℓ∞ distance. -/
def IsApproachable {m k d : ℕ} (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ))
    (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ)) (S : Set (Fin d → ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → 1 ≤ T →
    ∃ B : FullHistoryStrategy m k, (∀ (t : ℕ) (h : Fin t → (Fin m → ℝ) × (Fin k → ℝ)), B t h ∈ X) ∧
      ∀ y : ℕ → Fin k → ℝ, (∀ t < T, y t ∈ Y) →
        Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, p (fullHistoryPlay B y t) (y t)) S ≤ ε

end OfflineToOnline


