-- Prove2me | Definitions.Def_OfflineToOnline_payoffDiam
-- name    : OfflineToOnline_payoffDiam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:57.123864+00:00
-- url     : https://prove2.me/theorems/af17af78-0a28-4297-b7b7-32ba8955016b
-- title:
--   $\ell_\infty$ diameter $D(\boldsymbol p)$ of the payoff
-- statement:
--   For a Blackwell game $(\mathcal X,\mathcal Y,\boldsymbol p)$ the **$\ell_\infty$ diameter of the payoff** is
--
--   $$
--   D(\boldsymbol p)=\max_{x\in\mathcal X,\;y\in\mathcal Y}\ \|\boldsymbol p(x,y)\|_\infty .
--   $$
--
--   It is the scale of the problem: every approachability rate and every regret bound of the paper is proportional to $D(\boldsymbol p)$.
--
--   **Formalization Note** The maximum is written as the supremum of the image of $\mathcal X\times\mathcal Y$; the norm of `Fin d → ℝ` in Mathlib is the sup norm. The supremum is attained whenever $\mathcal X,\mathcal Y$ are nonempty, compact and convex and $\boldsymbol p$ is biaffine, which every statement using it assumes; on an empty product the value is $0$.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, equation (2), p.12

import Mathlib

namespace OfflineToOnline

/-- The ℓ∞ diameter of the vector payoff, equation (2), p.12:
`D(p) = max_{x ∈ X, y ∈ Y} ‖p(x, y)‖_∞`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, (2), p.12.

Formalization Note: the norm of `Fin d → ℝ` in Mathlib is the sup norm, so `‖p x y‖` is
`‖p(x, y)‖_∞`. The maximum is written as `sSup` of the image of `X × Y`; it is attained when `X`, `Y`
are nonempty compact convex and `p` is biaffine (then `p` is continuous), which every theorem using
it assumes. On an empty `X × Y` the value is `0`. -/
noncomputable def payoffDiam {m k d : ℕ} (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ))
    (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ)) : ℝ :=
  sSup ((fun q : (Fin m → ℝ) × (Fin k → ℝ) => ‖p q.1 q.2‖) '' (X ×ˢ Y))

end OfflineToOnline


