-- Prove2me | Definitions.Def_OfflineToOnline_IsSatisfiable
-- name    : OfflineToOnline_IsSatisfiable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:59.48526+00:00
-- url     : https://prove2.me/theorems/8ee44622-006f-495b-b629-3dc6b8986bc2
-- title:
--   Satisfiable target set
-- statement:
--   A target set $S\subseteq\mathbb R^d$ is **satisfiable** in the Blackwell game $(\mathcal X,\mathcal Y,\boldsymbol p)$ if a single player 1 action guarantees a payoff in $S$ against every player 2 action:
--
--   $$
--   \exists\,x\in\mathcal X\quad\forall\,y\in\mathcal Y:\qquad \boldsymbol p(x,y)\in S .
--   $$
--
--   This is the first condition listed in Proposition 1; it is sufficient, but not necessary, for approachability.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Proposition 1 item 1, p.45

import Mathlib

namespace OfflineToOnline

/-- Satisfiability (Proposition 1, item 1, p.45): a target set `S` is satisfiable in the Blackwell
game `(X, Y, p)` if there is a player 1 action `x ∈ X` such that `p(x, y) ∈ S` for every player 2
action `y ∈ Y`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Proposition 1 item 1, p.45. -/
def IsSatisfiable {m k d : ℕ} (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
    (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)) (S : Set (Fin d → ℝ)) : Prop :=
  ∃ x ∈ X, ∀ y ∈ Y, p x y ∈ S

end OfflineToOnline


