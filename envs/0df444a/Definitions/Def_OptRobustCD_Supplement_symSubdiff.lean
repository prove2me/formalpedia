-- Prove2me | Definitions.Def_OptRobustCD_Supplement_symSubdiff
-- name    : OptRobustCD_Supplement_symSubdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:51:18.831201+00:00
-- url     : https://prove2.me/theorems/c4641e29-4e29-410a-a4ce-f9cca90b1a5f
-- title:
--   The subdifferential $\partial F(X)$ over the real symmetric matrices
-- statement:
--   Let $n\ge 1$ and write $\langle B,C\rangle=\operatorname{Tr}(B^{\mathsf T}C)$ for real $n\times n$ matrices. For a convex function $F$ on the real symmetric $n\times n$ matrices and a real symmetric matrix $X$, the **subdifferential** of $F$ at $X$ is the set
--   $$
--   \partial F(X)=\bigl\{H\in\mathbb R^{n\times n}\ \text{symmetric}\ :\ F(U)\ge F(X)+\langle H,U-X\rangle\ \text{for every real symmetric } U\bigr\}.
--   $$
--   Its elements are the **subgradients** of $F$ at $X$: symmetric matrices whose linear functional supports $F$ from below at $X$ over the whole space of symmetric matrices (not only over the density matrices).
--
--   This is the subgradient notion of §8.2 used by the nearby-point entropy descent (Theorem 8.3), the first-order oracle of the fast SDP solver.
--
--   **Formalization Note** $F$ is a real-valued function on all of $\mathbb R^{n\times n}$; only its values on symmetric matrices enter. The set is defined for every $F$ and $X$; the paper uses it only for convex $F$ and symmetric $X$, and the theorems that use it carry those hypotheses.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), §8.2, p.40 (pdf p.42); ⟨B, C⟩ = Tr(BᵀC) from §8, p.37 (pdf p.39)

import Mathlib

namespace OptRobustCD

namespace Supplement

/-- **The subdifferential `∂F(X)` over the real symmetric matrices.** Hopkins, Hua, Mohanty,
Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of
November 3, 2026, sha256 3d287d54…), §8.2, p.40 (pdf p.42): "For a convex function `F` on all real
symmetric matrices and a real symmetric matrix `X`, let `∂F(X)` denote the set of symmetric matrices
`H` satisfying `F(U) ⩾ F(X) + ⟨H, U − X⟩` for every real symmetric matrix `U`", with
`⟨B, C⟩ = Tr(BᵀC)` (§8, p.37).

**Formalization Note.** `F` is a real-valued function on all of `R^{n×n}`; only its values on
symmetric matrices enter. The set is defined for every `F` and `X`; the paper uses it only for
convex `F` and symmetric `X`, and the statements that use it carry those hypotheses. -/
def symSubdiff {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {H | H.IsSymm ∧ ∀ U : Matrix (Fin n) (Fin n) ℝ, U.IsSymm →
    F X + (H.transpose * (U - X)).trace ≤ F U}

end Supplement

end OptRobustCD


