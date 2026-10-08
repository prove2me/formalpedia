-- Prove2me | Definitions.Def_FedergruenTzur_MinPred_Omega
-- name    : FedergruenTzur_MinPred_Omega
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:36:26.26148+00:00
-- url     : https://prove2.me/theorems/d5fedab6-f176-4d8e-8978-8140dc0e1d7f
-- title:
--   Potential costs and the jth Minimal Optimal Predecessors list Ω(j) (open-interval reading)
-- statement:
--   Fix an iteration $j \ge 1$ of the forward algorithm of Federgruen and Tzur. The future demands $d_{j+1}, d_{j+2}, \dots$ are treated as unknown, so the cumulative demand of a horizon $t \ge j$ is a **potential** value $x \ge D(j)$. For a last setup in period $l \le j$ the cost (2) of such a horizon, minus the carrying cost $S(j,t)$ of the post-$j$ demand from period $j$ on (which is the same for every $l \le j$), is the **potential cost**
--   $$
--   \pi_j(l, x) = F(l-1) + K_l + S(l, j) + c_l\,(x - D(l-1)) + (x - D(j))\,\bigl(H(j-1) - H(l-1)\bigr),
--   $$
--   so that $F(l,t) = \pi_j(l, D(t)) + S(j,t)$ for every actual horizon $t \ge j$.
--
--   Say that $l$ is the **lowest-index optimum at $x$** if $\pi_j(l,x) \le \pi_j(i,x)$ for every $i \in \{1,\dots,j\}$ and $\pi_j(l,x) < \pi_j(i,x)$ for every $i \in \{1,\dots,j\}$ with $i < l$. The **$j$th Minimal Optimal Predecessors list** is
--   $$
--   \Omega(j) = \bigl\{\, 1 \le l \le j : \exists\, a < b \text{ with } D(j) \le a \text{ such that } l \text{ is the lowest-index optimum at every } x \in (a, b) \,\bigr\}.
--   $$
--
--   $\Omega(j)$ is the set of periods that can still be the best last setup period for some future horizon; the paper's algorithm maintains it as a ranked list.
--
--   **Formalization Note (open-interval reading).** The paper defines $\Omega(j)$ with a single potential cumulative demand $D \ge D(j)$ at which $l$ is the lowest index minimizing $F(\cdot, t)$ over $\{1, \dots, j\}$. Under that literal reading Theorem 1(a) ("only if") and Theorem 1(c) are false whenever two lines tie exactly at a breakpoint (example: $j = 5$, $d = (1,2,1,1,2)$, $h = (1,0,1,0,\cdot)$, $c = (2,1,3,2,0)$, $K = (1,2,6,6,4)$, where period 2 is the lowest optimum only at $D = 7$ and period 5 is the unique optimum for $D > 7$). This definition requires $l$ to be the lowest-index optimum on a nondegenerate open interval of potential cumulative demands above $D(j)$, which is the paper's own description of the list two sentences later: "the $k$th element of the list is the unique optimal last setup period for any horizon $t \ge j$ with potential cumulative demand $g(k) < D < g(k+1)$". The potential cost drops the term $S(j,t)$ common to all $l \le j$; the theorem `potCost_spec` of this mission certifies the identity $F(l,t) = \pi_j(l, D(t)) + S(j,t)$.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, pp. 914–915, §2, definition of Ω(j) and the paragraph following it (open-interval reading from p. 915, third paragraph of §2: 'g(k) < D < g(k + 1)')

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Model

/-!
# Federgruen–Tzur (1991), §2: potential costs and the Minimal Optimal Predecessors list `Ω(j)`

A. Federgruen and M. Tzur, Management Science 37(8), 1991, §2, pp. 914–915.

At iteration `j` the future demands `d_{j+1}, d_{j+2}, …` are unknown parameters, so the cumulative
demand of a horizon `t ≥ j` is a *potential* value `x ≥ D(j)`.

* `potCost j l x = F(l-1) + K_l + S(l, j) + c_l (x - D(l-1)) + (x - D(j)) (H(j-1) - H(l-1))` is the
  cost (2) of a last setup in `l ≤ j` for a horizon `t ≥ j` with `D(t) = x`, minus the carrying cost
  `S(j, t)` of the post-`j` demand from period `j` on, which is the same for every `l ≤ j`
  (so `F(l, t) = potCost j l (D t) + S(j, t)`; this is (2) rewritten with (1a)).
* `IsLowestOptimal j l x`: `l` is the lowest index `i ∈ {1, …, j}` minimizing `potCost j i x`.
* `Omega j`: the periods `1 ≤ l ≤ j` for which there are reals `a < b` with `D(j) ≤ a` such that `l`
  is the lowest-index optimum for every potential cumulative demand `x ∈ (a, b)`.

**Formalization Note (open-interval reading of `Ω(j)`).** The page defines `Ω(j)` with a single
potential cumulative demand `D ≥ D(j)` at which `l` is the lowest index with
`F(l, t) = min_{1 ≤ i ≤ j} F(i, t)`. With that literal reading Theorem 1(a) ("⇒") and (c) fail
whenever two lines tie exactly at a breakpoint. The definition here requires `l` to be the lowest
optimal index on a nondegenerate open interval of potential cumulative demands above `D(j)`, which is
the paper's own description of the list on p. 915: "the `k`th element of the list is the unique
optimal last setup period for any horizon `t ≥ j` with potential cumulative demand
`g(k) < D < g(k + 1)`".
-/

namespace FedergruenTzur.MinPred

namespace LotSizing

variable (P : LotSizing)

/-- Cost of a last setup in period `l ≤ j` at potential cumulative demand `x` for a horizon beyond
`j`, without the `l`-independent term `S(j, t)`. -/
noncomputable def potCost (j l : ℕ) (x : ℝ) : ℝ :=
  P.Fopt (l - 1) + P.K l + P.S l j + P.c l * (x - P.D (l - 1))
    + (x - P.D j) * (P.H (j - 1) - P.H (l - 1))

/-- `l` is the lowest index in `{1, …, j}` attaining `min_{1 ≤ i ≤ j} potCost j i x`. -/
def IsLowestOptimal (j l : ℕ) (x : ℝ) : Prop :=
  (∀ i ∈ Finset.Icc 1 j, P.potCost j l x ≤ P.potCost j i x) ∧
    (∀ i ∈ Finset.Icc 1 j, i < l → P.potCost j l x < P.potCost j i x)

/-- The `j`th Minimal Optimal Predecessors list `Ω(j)` (open-interval reading). -/
noncomputable def Omega (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 j).filter fun l =>
    ∃ a b : ℝ, P.D j ≤ a ∧ a < b ∧ ∀ x ∈ Set.Ioo a b, P.IsLowestOptimal j l x

end LotSizing

end FedergruenTzur.MinPred


