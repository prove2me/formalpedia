-- Prove2me | Definitions.Def_Sherbrooke_lowerHull
-- name    : Sherbrooke_lowerHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:47.262954+00:00
-- url     : https://prove2.me/theorems/2a345306-2092-4e9f-b2e1-6f78e3033ade
-- title:
--   Convexified item function $\Xi'$: lower boundary of the convex hull of $\Xi$ on $\mathbb N$
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be a sequence. An **affine minorant** of $\Xi$ is a line $k\mapsto ak+b$ ($a,b\in\mathbb R$) with $ak+b\le\Xi(k)$ for every $k\in\mathbb N$. The **convexified function** $\Xi'$ is the pointwise supremum of the affine minorants:
--
--   $$
--   \Xi'(m)=\sup\{\,am+b \;:\; a,b\in\mathbb R,\ ak+b\le\Xi(k)\ \text{for all }k\in\mathbb N\,\},\qquad m\in\mathbb N .
--   $$
--
--   This is the lower boundary of the convex hull of the points $\{(k,\Xi(k)):k\in\mathbb N\}$, evaluated at the integers. In Sherbrooke's words, "at any point where $\Xi_i(m)$ is not convex the function is decreased to the point of convexity in forming the new function $\Xi_i'(m)$. At all other points $\Xi_i(m)$ coincides with $\Xi_i'(m)$." It is the function in which the optimality conditions (12) of the METRIC Appendix Theorem are written.
--
--   **Formalization Note** When $\Xi$ is bounded below, the set is nonempty (it contains the constant $\inf\Xi$) and bounded above by $\Xi(m)$, so the supremum is a genuine real number; on $\mathbb N$ it equals the greatest discretely convex minorant of $\Xi$ and $\min\bigl(\Xi(m),\ \inf_{a<m<b}\tfrac{(b-m)\Xi(a)+(m-a)\Xi(b)}{b-a}\bigr)$. Lean's `sSup` returns $0$ on an empty set, so every statement of this mission that uses $\Xi'$ assumes that $\Xi$ is bounded below.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, unnumbered, pp. 135–136 (definition of Ξ_i′ on the boundary of the convex hull of Ξ_i(m)); Appendix, Theorem, p. 140 ("Define Ξ_i′(m_i) on the boundary of the convex hull of Ξ_i(m_i) such that Ξ_i′(m_i) ≤ Ξ_i(m_i)")

import Mathlib

namespace Sherbrooke

/-- **The convexified item function `Ξ′` (lower boundary of the convex hull of `Ξ`).**
Sherbrooke, *METRIC: A Multi-Echelon Technique for Recoverable Item Control*, Operations
Research 16 (1968), doi:10.1287/opre.16.1.122, unnumbered, pp. 135–136: "Let us define a new
function Ξ_i′(m) which lies on the boundary of the convex hull of Ξ_i(m). In other words at any
point where Ξ_i(m) is not convex the function is decreased to the point of convexity in forming
the new function Ξ_i′(m). At all other points Ξ_i(m) coincides with Ξ_i′(m)." The Appendix
(Theorem, p. 140) repeats: "Define Ξ_i′(m_i) on the boundary of the convex hull of Ξ_i(m_i) such
that Ξ_i′(m_i) ≤ Ξ_i(m_i)."

For `Ξ : ℕ → ℝ`, `lowerHull Ξ m` is the supremum, over all affine functions `k ↦ a k + b` lying
below `Ξ` at every `k ∈ ℕ`, of their value `a m + b`.

**Formalization Note.** This is the lower boundary of the closed convex hull of the points
`{(k, Ξ k) : k ∈ ℕ}`, evaluated at the integer `m`. When `Ξ` is bounded below (the paper's
"finite lower bound", carried as a hypothesis by every statement that uses `lowerHull`), the set
is nonempty (it contains the constant `inf Ξ`) and bounded above by `Ξ m`, so the `sSup` is an
honest supremum. On `ℕ` it equals both the greatest discretely convex minorant of `Ξ` and
`min (Ξ m, inf_{a < m < b} ((b − m) Ξ a + (m − a) Ξ b) / (b − a))`, the two-point description of
the hull's lower boundary. Without a lower bound the set is empty and the value is the junk
`sSup ∅ = 0`; no statement of this mission uses `lowerHull` without `BddBelow (Set.range Ξ)`. -/
noncomputable def lowerHull (Ξ : ℕ → ℝ) (m : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧ y = a * (m : ℝ) + b}

end Sherbrooke


