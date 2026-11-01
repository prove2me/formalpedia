-- Prove2me | Definitions.Def_AdditiveConvexity_serialSet
-- name    : AdditiveConvexity_serialSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:03.029436+00:00
-- url     : https://prove2.me/theorems/af18fa2f-ce00-4fb2-b5a6-e582ac62f96b
-- title:
--   Feasible set $\hat{\mathbb C}(x)$ of the serial problem
-- statement:
--   Let $x\in V$ and $0\le k\le n$. The feasible set of the serial problem (4) of the paper is
--   $$
--   \hat{\mathbb C}(x)=\{y\in I\times\mathbb R^k \mid y_0\le y_1\le\cdots\le y_k\le x_{k+1},\ y_i\ge x_i,\ i=0,1,\dots,k\}.
--   $$
--   It relaxes $\mathbb C(x)$ by dropping the ordering of the differences $y_i-x_i$.
--
--   **Formalization Note** As for $\mathbb C(x)$, $y$ and the unchanged tail form one vector $z\in V$, and at $k=n$ there is no bound $y_k\le x_{k+1}$.
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Lemma 1, p.5 (PDF p.5)

import Mathlib
import Definitions.Def_AdditiveConvexity_chainDomain

namespace AdditiveConvexity

/-- The feasible set `Ĉ(x)` of the serial problem (4) of Gong–Wang, Preservation of Additive
Convexity, SSRN 3217007 (accepted manuscript), Lemma 1, p.5 (PDF p.5):
`Ĉ(x) = {y ∈ I × ℝᵏ | y₀ ≤ ⋯ ≤ y_k ≤ x_{k+1}, yᵢ ≥ xᵢ, i = 0, 1, …, k}`.

**Formalization Note.** As in `transformSet`, `y` and the unchanged tail form one vector `z`, and
at `k = n` there is no bound `y_k ≤ x_{k+1}`. -/
def serialSet (I : Set ℝ) {n : ℕ} (k : ℕ) (x : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {z | z ∈ chainDomain I n ∧ (∀ i : Fin (n + 1), k < i.val → z i = x i) ∧
    ∀ i : Fin (n + 1), i.val ≤ k → x i ≤ z i}

end AdditiveConvexity


