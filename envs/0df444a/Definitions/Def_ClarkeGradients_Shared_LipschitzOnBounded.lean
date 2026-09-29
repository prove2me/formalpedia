-- Prove2me | Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
-- name    : ClarkeGradients_Shared_LipschitzOnBounded
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:39:37.351127+00:00
-- url     : https://prove2.me/theorems/a972b6da-8fe8-4fed-b256-25b9060ebaaa
-- title:
--   §1 standing assumption — f is locally Lipschitz (Lipschitz on bounded sets)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$. Following Clarke, $f$ is called **locally Lipschitz** if for each bounded subset $B$ of $\mathbb R^n$ there is a constant $K\ge 0$ such that
--
--   $$
--   |f(x_1)-f(x_2)|\le K\,|x_1-x_2|\qquad\text{for all } x_1,x_2\in B,
--   $$
--
--   where $|\cdot|$ is the Euclidean norm.
--
--   This is the standing assumption of §1 of the paper: every function whose generalized gradient is considered there is locally Lipschitz in this sense. By Rademacher's theorem such a function is differentiable almost everywhere, which is what makes the generalized gradient meaningful.
--
--   It serves chunk 01-max-functions (Clarke p. 247, §1; hypothesis of Proposition (1.4) p. 248, Corollary (1.10) p. 249 and Theorem (2.1) pp. 251–252) and chunk 02-flow-invariance (Clarke p. 247, §1; hypothesis of Proposition (1.4) p. 248, applied to the distance function $d_E$, which is Lipschitz with constant 1).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The constant $K$ is a nonnegative real (`NNReal`), as Mathlib's `LipschitzOnWith` requires. On $\mathbb R^n$ this notion is equivalent to Mathlib's `LocallyLipschitz` (Lipschitz on a neighbourhood of each point), but the paper's bounded-set form is used.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 247, §1 (standing assumption)

import Mathlib

namespace ClarkeGradients.Shared

/-- Clarke (1975), §1, p. 247: `f : ℝⁿ → ℝ` is *locally Lipschitz* in the paper's sense,
i.e. for each bounded subset `B` of `ℝⁿ` there is a constant `K` with
`|f x₁ - f x₂| ≤ K |x₁ - x₂|` for all `x₁, x₂ ∈ B`. -/
def LipschitzOnBounded {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
    ∃ K : NNReal, LipschitzOnWith K f B

end ClarkeGradients.Shared


