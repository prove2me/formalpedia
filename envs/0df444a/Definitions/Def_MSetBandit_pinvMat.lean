-- Prove2me | Definitions.Def_MSetBandit_pinvMat
-- name    : MSetBandit_pinvMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:07.177802+00:00
-- url     : https://prove2.me/theorems/39d87495-116f-4289-81ab-909473a1b5ab
-- title:
--   Moore–Penrose pseudoinverse $A^+$ of a matrix
-- statement:
--   For a square real matrix $A\in\mathbb R^{d\times d}$ and $y\in\mathbb R^d$, $A^+y$ denotes the **Moore–Penrose pseudoinverse** of $A$ applied to $y$: the unique vector $z$ orthogonal to $\ker A$ with $Az=Py$, where $P$ is the orthogonal projection onto $\operatorname{range}(A)$ (standard inner product of $\mathbb R^d$).
--
--   The paper uses it for the covariance pseudoinverse $\Sigma^+$.
--
--   **Formalization Note** The matrix is read as the linear map $z\mapsto Az$ on Euclidean space, and the published operator pseudoinverse `HarmonicGames.Decomposition.pinv` is applied to it.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.3

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv

namespace MSetBandit

/-- **Moore–Penrose pseudoinverse `A⁺` of a square real matrix, applied to a vector.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231,
Section 2, p.3: "its Moore-Penrose pseudoinverse by `A⁺`".

`pinvMat A y` is `A⁺ y`: the matrix `A` is read as the linear map `z ↦ Az` of Euclidean space
`ℝ^d` (standard inner product), and `A⁺` is the published Moore–Penrose pseudoinverse
`HarmonicGames.Decomposition.pinv` of that map.

**Formalization Note.** Mathlib has no matrix pseudoinverse at the pinned commit, so the operator
pseudoinverse with respect to the standard Euclidean inner product is used; for a matrix this is
the usual Moore–Penrose pseudoinverse. Vectors are converted between `Fin d → ℝ` and
`EuclideanSpace ℝ (Fin d)` by `WithLp.toLp` / `WithLp.ofLp`. -/
noncomputable def pinvMat {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin A) (WithLp.toLp 2 y)).ofLp

end MSetBandit


