-- Prove2me | Definitions.Def_OfflineToOnline_IsResponseSatisfiable
-- name    : OfflineToOnline_IsResponseSatisfiable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:02.798516+00:00
-- url     : https://prove2.me/theorems/3d4f2753-9564-4f22-a318-89d02e94b201
-- title:
--   Response-satisfiable target set
-- statement:
--   A target set $S\subseteq\mathbb R^d$ is **response-satisfiable** in the Blackwell game $(\mathcal X,\mathcal Y,\boldsymbol p)$ if every player 2 action has a player 1 response whose payoff lies in $S$:
--
--   $$
--   \forall\,y\in\mathcal Y\quad\exists\,x\in\mathcal X:\qquad \boldsymbol p(x,y)\in S .
--   $$
--
--   By Blackwell's theorem (Theorem 1 of the paper) a closed convex target set is approachable exactly when it is response-satisfiable.
--
--   **Formalization Note** Definition 4 speaks of closed convex target sets; closedness and convexity are stated as separate hypotheses wherever the paper assumes them.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 4, p.12

import Mathlib

namespace OfflineToOnline

/-- Response-satisfiability, Definition 4, p.12: `S` is response-satisfiable in the Blackwell game
`(X, Y, p)` if for every player 2 action `y ∈ Y` there is a player 1 action `x ∈ X` with
`p(x, y) ∈ S`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 4, p.12.

Formalization Note: Definition 4 speaks of a closed and convex target set; closedness and
convexity of `S` are stated as separate hypotheses wherever the paper has them. -/
def IsResponseSatisfiable {m k d : ℕ} (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
    (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)) (S : Set (Fin d → ℝ)) : Prop :=
  ∀ y ∈ Y, ∃ x ∈ X, p x y ∈ S

end OfflineToOnline


