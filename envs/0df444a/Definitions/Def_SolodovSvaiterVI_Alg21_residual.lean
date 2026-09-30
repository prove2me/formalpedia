-- Prove2me | Definitions.Def_SolodovSvaiterVI_Alg21_residual
-- name    : SolodovSvaiterVI_Alg21_residual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:56:11.51014+00:00
-- url     : https://prove2.me/theorems/71f600e9-f4ca-4d55-8b09-c615a6feb455
-- title:
--   Projected residual $r(x) = x - P_C[x - F(x)]$
-- statement:
--   Let $C \subseteq \mathbb{R}^n$ and $F : \mathbb{R}^n \to \mathbb{R}^n$. The **projected residual** of $\mathrm{VI}(F, C)$ at $x \in \mathbb{R}^n$ is
--
--   $$r(x) := x - P_C[x - F(x)],$$
--
--   where $P_C$ is the Euclidean projection onto $C$. For nonempty closed convex $C$ the zeros of $r$ are exactly the solutions of $\mathrm{VI}(F, C)$, so $\|r(x)\|$ measures how far $x$ is from solving the problem. Algorithm 2.1 stops when $r(x^i) = 0$ and otherwise searches along the direction $-r(x^i)$.
--
--   **Formalization Note** $P_C$ is `projOnto C`, which agrees with the projection whenever $C$ is nonempty, closed and convex.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 767, Section 2, definition of r(x)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto

namespace SolodovSvaiterVI.Alg21

/-- The projected residual `r(x) := x − P_C[x − F(x)]` of Solodov–Svaiter (p. 767, Section 2).

**Formalization Note.** `P_C` is `projOnto C`, which is the true projection whenever `C` is
nonempty, closed and convex. -/
noncomputable def residual {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  x - projOnto C (x - F x)

end SolodovSvaiterVI.Alg21


