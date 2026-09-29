-- Prove2me | Definitions.Def_BiconvexProg_BranchBound_gradNormMax
-- name    : BiconvexProg_BranchBound_gradNormMax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T17:53:23.586987+00:00
-- url     : https://prove2.me/theorems/94dcab10-d8d6-440a-be47-d8cb58d48178
-- title:
--   The maximum gradient norm $\gamma = \max\{\|\nabla xy\| : (x,y) \in [l,L]\times[m,M]\}$ and the Euclidean distance on $\mathbb{R}^{2n}$
-- statement:
--   For a rectangle $[l, L] \times [m, M] \subseteq \mathbb{R}^2$, let
--
--   $$\gamma = \max\{\|\nabla (xy)\| : l \le x \le L,\ m \le y \le M\} = \max\left\{\sqrt{y^2 + x^2} : l \le x \le L,\ m \le y \le M\right\},$$
--
--   since $\nabla(xy) = (y, x)$ and $\|\cdot\|$ is the Euclidean norm. For points $z = (x,y)$ and $w = (u,v)$ of $\mathbb{R}^n \times \mathbb{R}^n$, the **Euclidean distance** is
--
--   $$\|z - w\| = \sqrt{\textstyle\sum_{i=1}^n \big((x_i - u_i)^2 + (y_i - v_i)^2\big)}.$$
--
--   The constants $\gamma_i$ for the rectangles $\Omega_i$ appear in the equicontinuity argument of the convergence proof of Al-Khayyal and Falk, where $\delta = \varepsilon/(n\gamma)$ with $\gamma = \max_i \gamma_i$.
--
--   **Formalization Note** $\gamma$ is the real `sSup` of the norm over the rectangle. For a nonempty rectangle this set is compact and the supremum is a maximum. For an empty rectangle the value is the default $0$. Mathlib's default metric on $(\mathrm{Fin}\ n \to \mathbb{R}) \times (\mathrm{Fin}\ n \to \mathbb{R})$ is the sup metric, so the Euclidean distance is written out.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 281, Convergence proof (γ_i, maximum norm problem; δ = ε/nγ)

import Mathlib

namespace BiconvexProg.BranchBound

/-- The maximum-norm value `γ = max {‖∇(xy)‖ : l ≤ x ≤ L, m ≤ y ≤ M}` of p. 281: since
`∇(xy) = (y, x)`, it is the supremum of the Euclidean norm `√(y² + x²)` over the rectangle.
Junk value: `0` if the rectangle is empty (`L < l` or `M < m`). -/
noncomputable def gradNormMax (l L m M : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => Real.sqrt (p.2 ^ 2 + p.1 ^ 2)) '' (Set.Icc l L ×ˢ Set.Icc m M))

/-- The Euclidean distance on `ℝⁿ × ℝⁿ = ℝ²ⁿ`:
`‖(x, y) − (u, v)‖ = √(∑ᵢ ((xᵢ − uᵢ)² + (yᵢ − vᵢ)²))`. (Mathlib's default metric on these
types is the sup metric, so the Euclidean one is written out.) -/
noncomputable def eucDist {n : ℕ} (z w : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  Real.sqrt (∑ i, ((z.1 i - w.1 i) ^ 2 + (z.2 i - w.2 i) ^ 2))

end BiconvexProg.BranchBound


