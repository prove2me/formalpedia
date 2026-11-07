-- Prove2me | Definitions.Def_BalancedKneser_IsConnectedUpTo
-- name    : BalancedKneser_IsConnectedUpTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:15.438771+00:00
-- url     : https://prove2.me/theorems/5a107e1c-0dc8-45e7-a6c7-f2f3a608cc42
-- title:
--   $t$-connected spaces (nonempty, and every map $S^j\to X$, $0\le j\le t$, extends over the ball)
-- statement:
--   Let $X$ be a topological space and $t\ge 0$ an integer. $X$ is **$t$-connected** if it is nonempty and, for every $0\le j\le t$, every continuous map from the sphere $S^j$ into $X$ extends to a continuous map from the closed ball $D^{j+1}$:
--   $$
--   \forall\, j\le t,\ \forall f:S^j\to X\ \exists g:D^{j+1}\to X,\quad g|_{S^j}=f .
--   $$
--   Here $S^j$ is the unit sphere and $D^{j+1}$ the closed unit ball of $\mathbb R^{j+1}$. In particular $0$-connected means nonempty and path-connected.
--
--   The source defines: "A space is t-connected if every map from $S^j$ into it extends over a ball for $0\le j\le t$." The nonemptiness clause is the standard convention of topological combinatorics, in which "$(-1)$-connected" means nonempty. It is added because, read literally, the printed definition makes the empty space $t$-connected for every $t$, and Lemma 3.1 then fails (one-vertex graph, $d=1$).
--
--   **Formalization Note** $S^j$ and $D^{j+1}$ are `Metric.sphere 0 1` and `Metric.closedBall 0 1` in `EuclideanSpace ℝ (Fin (j+1))`.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §3.1, p.6 (PDF p.8): t-connected

import Mathlib

namespace BalancedKneser

/-- **t-connectivity** (Alipour–Jafari, arXiv:2611.04486v1, §3.1, p.6 (PDF p.8): "A space is
t-connected if every map from S^j into it extends over a ball for 0 ≤ j ≤ t"), in the standard
convention of topological combinatorics, which also requires the space to be nonempty. Here
`S^j` is the unit sphere of `ℝ^{j+1}` (`EuclideanSpace ℝ (Fin (j+1))`) and the ball is the closed
unit ball.

Formalization Note: the clause `Nonempty X` is a correction of the printed definition. Read
literally, the empty space would be t-connected for every `t` (there are no maps into it), and
Lemma 3.1 would fail for the one-vertex graph; see the mission notes. With this convention,
0-connected means nonempty and path-connected. -/
def IsConnectedUpTo (X : Type*) [TopologicalSpace X] (t : ℕ) : Prop :=
  Nonempty X ∧ ∀ j ≤ t,
    ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1, X),
      ∃ g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1, X),
        ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1,
          g ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ = f x

end BalancedKneser


