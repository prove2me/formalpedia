-- Prove2me | Definitions.Def_CardinalMatching_ModParams_theta
-- name    : CardinalMatching_ModParams_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:45.528965+00:00
-- url     : https://prove2.me/theorems/c9fbb277-0efa-4c2c-b1da-8bc66f50d088
-- title:
--   Optimal bundles at budget $t$ and the sets $\theta_i(t)$
-- statement:
--   With the prices $p$ of Step 2, a bundle $y$ is an **optimum solution of LP (1)** for agent $i$ at budget $t$ if it maximizes $u'_i\cdot y$ subject to
--   $$
--   \sum_{j\in G'} y_j\le 1,\qquad p\cdot y\le t,\qquad y\ge 0 .
--   $$
--   For $t\ge 0$, $\theta_i(t)$ is the set of goods $j$ such that $y_j$ can be positive in an optimum solution of LP (1); that is, the goods that can take part in an optimal bundle of agent $i$ at budget $t$.
--
--   Lemma 13 says each agent's allocated bundle is optimal for LP (1) at its own budget; Lemmas 21–22 compare agents through the functions $\theta_i$.
--
--   **Formalization Note** The printed definition says "goods $j\in G$", but LP (1) is over $G'$, so $\theta_i(t)\subseteq G'$. The module defines `IsOptBundle` and `theta`.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Definition 20 and LP (1), p.11; Lemma 13, p.9

import Mathlib
import Definitions.Def_CardinalMatching_ModParams

namespace CardinalMatching

namespace ModParams

variable {n : ℕ} (P : ModParams n)

/-- `y` is an **optimum solution of LP (1)** for agent `i` at budget `t` and prices `p`
(Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, Definition 20, p.11,
and Lemma 13, p.9): `y` maximizes `u_i · y` subject to `∑_{j∈G′} y_j ≤ 1`, `p · y ≤ t`, `y ≥ 0`. -/
def IsOptBundle (p : P.Good → ℝ) (i : P.Agent) (t : ℝ) (y : P.Good → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ 1 ∧ ∑ j, p j * y j ≤ t ∧
    ∀ y' : P.Good → ℝ, (∀ j, 0 ≤ y' j) → ∑ j, y' j ≤ 1 → ∑ j, p j * y' j ≤ t →
      ∑ j, P.util i j * y' j ≤ ∑ j, P.util i j * y j

/-- **`θ_i(t)`** (Definition 20, p.11): the set of all goods `j` such that `y_j` can be positive in
an optimum solution of LP (1) for agent `i` at budget `t`.

**Formalization Note** The printed definition says "goods j ∈ G", but LP (1) ranges over `G′`
(its constraint sums over `j ∈ G′`), so `θ_i(t) ⊆ G′`. The paper uses `θ_i` for `t ≥ 0`; the
value for `t < 0` (the empty set) is never used. -/
def theta (p : P.Good → ℝ) (i : P.Agent) (t : ℝ) : Set P.Good :=
  {j | ∃ y, P.IsOptBundle p i t y ∧ 0 < y j}

end ModParams

end CardinalMatching


