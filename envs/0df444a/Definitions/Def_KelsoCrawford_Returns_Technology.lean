-- Prove2me | Definitions.Def_KelsoCrawford_Returns_Technology
-- name    : KelsoCrawford_Returns_Technology
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:13.442258+00:00
-- url     : https://prove2.me/theorems/b0b9a8c4-48bf-4866-ad26-6e4bfc1d4eee
-- title:
--   Section 6, pp. 1499–1500 — nonincreasing returns to workers (DR) and subadditivity of a technology
-- statement:
--   **Nonincreasing returns to workers.** When workers are alike in production, a firm's product depends only on the number of workers it hires: $y(C) = \bar y(|C|)$ for a function $\bar y : \mathbb{N} \to \mathbb{R}$. With $m$ workers in the market, $\bar y$ satisfies **(DR)** if
--   $$\bar y(w + 1) - \bar y(w) \le \bar y(w) - \bar y(w - 1) \qquad \text{for every integer } w \text{ with } 1 \le w \le m - 1 ,$$
--   that is, the marginal product of an additional worker is nonincreasing on $\{0, 1, \dots, m\}$.
--
--   **Subadditivity.** A technology $y : 2^W \to \mathbb{R}$ is **subadditive** if unions of disjoint sets of workers produce no more than the sum of the products of those sets taken separately:
--   $$y(C \cup D) \le y(C) + y(D) \qquad \text{whenever } C \cap D = \emptyset .$$
--
--   (DR) is the condition of Theorem 6; subadditivity is the condition the paper compares with (GS) in the heterogeneous case.
--
--   **Formalization Note** (DR) is stated for natural numbers $w$ with $1 \le w$ and $w + 1 \le m$, the paper's range $1 \le w \le m - 1$ written so that $w - 1$ and $m - 1$ never truncate; for $m \le 1$ the condition is vacuous. Values $\bar y(n)$ for $n > m$ play no role. Subadditivity is the "weak" notion the paper defines, with $\le$.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1499, Section 6, condition (DR); p. 1500, definition of subadditivity

import Mathlib

namespace KelsoCrawford.Returns

/-- (DR), nonincreasing returns to workers (Kelso–Crawford 1982, p. 1499): for a technology
`y^j(C) = ȳ(|C|)` and `m` workers,
`ȳ(w + 1) - ȳ(w) ≤ ȳ(w) - ȳ(w - 1)` for every integer `w` with `1 ≤ w ≤ m - 1`. -/
def DR (m : ℕ) (ybar : ℕ → ℝ) : Prop :=
  ∀ w : ℕ, 1 ≤ w → w + 1 ≤ m → ybar (w + 1) - ybar w ≤ ybar w - ybar (w - 1)

/-- Subadditivity of a production technology (p. 1500): unions of disjoint sets of workers
produce no more than the sum of the products of those sets taken separately. -/
def Subadditive {W : Type} [DecidableEq W] (y : Finset W → ℝ) : Prop :=
  ∀ C D : Finset W, Disjoint C D → y (C ∪ D) ≤ y C + y D

end KelsoCrawford.Returns


