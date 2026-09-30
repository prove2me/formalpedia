-- Prove2me | Definitions.Def_SolodovSvaiterVI_Alg21_halfspace
-- name    : SolodovSvaiterVI_Alg21_halfspace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:58:26.753224+00:00
-- url     : https://prove2.me/theorems/3e1eebcc-77b7-4642-b1d6-a9d4e1c1a69b
-- title:
--   Closed halfspace $\{y : \langle w, y - z \rangle \le 0\}$
-- statement:
--   For $w, z \in \mathbb{R}^n$, the closed halfspace
--
--   $$\{\, y \in \mathbb{R}^n \mid \langle w, y - z \rangle \le 0 \,\}$$
--
--   consists of the points on the side of the hyperplane through $z$ with normal $w$ opposite to $w$. With $w = F(z^i)$ and $z = z^i$ it is the halfspace $H_i = \{x \in \mathbb{R}^n \mid \langle F(z^i), x - z^i\rangle \le 0\}$ of Algorithm 2.1, which contains the solution set and excludes the current iterate.
--
--   **Formalization Note** When $w = 0$ the set is all of $\mathbb{R}^n$; this case does not arise in Algorithm 2.1 under the hypotheses of the theorems, since there $\langle F(z^i), x^i - z^i \rangle > 0$.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 768, Algorithm 2.1, definition of H_i

import Mathlib

open scoped InnerProductSpace

namespace SolodovSvaiterVI.Alg21

/-- The closed halfspace `{y ∈ ℝⁿ | ⟨w, y − z⟩ ≤ 0}`. With `w = F(zⁱ)` and `z = zⁱ` it is the
halfspace `Hᵢ = {x ∈ ℜⁿ | ⟨F(zⁱ), x − zⁱ⟩ ≤ 0}` of Algorithm 2.1 (Solodov–Svaiter, p. 768). -/
def halfspace {n : ℕ} (w z : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ⟪w, y - z⟫_ℝ ≤ 0}

end SolodovSvaiterVI.Alg21


