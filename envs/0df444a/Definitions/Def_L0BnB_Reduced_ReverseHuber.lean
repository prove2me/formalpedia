-- Prove2me | Definitions.Def_L0BnB_Reduced_ReverseHuber
-- name    : L0BnB_Reduced_ReverseHuber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:39.219926+00:00
-- url     : https://prove2.me/theorems/2a14d341-b68a-4575-b761-7e9eac86f6f2
-- title:
--   The reverse Huber penalty $\mathcal B$ (4)
-- statement:
--   The **reverse Huber penalty** is the function $\mathcal B:\mathbb R\to\mathbb R$ given by
--
--   $$
--   \mathcal B(t)=\begin{cases} |t| & |t|\le 1,\\[2pt] \dfrac{t^2+1}{2} & |t|\ge 1.\end{cases}
--   $$
--
--   The two branches agree at $|t|=1$, where both equal $1$. The penalty is a hybrid of the $\ell_1$ penalty (near the origin) and the squared $\ell_2$ penalty (away from it); it is convex and continuous.
--
--   It is the building block of the penalty $\psi_1$ of Theorem 1, which arises when the perspective relaxation of $\ell_0\ell_2$-regularized least squares is projected onto the space of regression coefficients.
--
--   **Formalization Note** Lean writes the function with a single `if |t| ≤ 1 then |t| else (t^2 + 1)/2`; since the branches agree on $|t| = 1$ this is the paper's definition.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 6, (4)

import Mathlib

namespace L0BnB.Reduced

/-- The reverse Huber penalty `B : ℝ → ℝ` of Hazimeh, Mazumder, Saab, *Sparse Regression at Scale:
Branch-and-Bound rooted in First-Order Optimization*, arXiv:2004.06152v2, (4), p. 6:
`B(t) = |t|` if `|t| ≤ 1` and `B(t) = (t² + 1)/2` if `|t| ≥ 1`.
The two branches agree at `|t| = 1`, so the `if` reproduces the paper's definition. -/
noncomputable def reverseHuber (t : ℝ) : ℝ :=
  if |t| ≤ 1 then |t| else (t ^ 2 + 1) / 2

end L0BnB.Reduced


