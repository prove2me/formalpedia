-- Prove2me | Definitions.Def_KatyushaNs_IsConvexLSmooth
-- name    : KatyushaNs_IsConvexLSmooth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:38.703481+00:00
-- url     : https://prove2.me/theorems/0763963f-31aa-40a9-9453-5182399d696e
-- title:
--   Convex and $L$-smooth function (Definition 1.2)
-- statement:
--   Let $L \in \mathbb{R}$ and $\varphi : \mathbb{R}^d \to \mathbb{R}$. We say that $\varphi$ is **convex and $L$-smooth** if
--
--   1. $\varphi$ is convex on $\mathbb{R}^d$;
--   2. $\varphi$ is differentiable;
--   3. for all $x, y \in \mathbb{R}^d$,
--   $$\|\nabla \varphi(x) - \nabla \varphi(y)\| \le L\,\|x - y\|.$$
--
--   This is the assumption on every summand $f_i$ of the finite-sum problem (1.1) in Theorem 4.1.
--
--   **Formalization Note** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` and $\nabla$ is Mathlib's `gradient`; differentiability makes `gradient` the true gradient. Positivity of $L$ is not part of the definition.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Definition 1.2, p. 6

import Mathlib

namespace KatyushaNs

/-- **Convex and `L`-smooth (Definition 1.2).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Definition 1.2, p. 6 (PDF p. 7): "For a convex function f : Rn → R, …
f is L-smooth if ∀x, y ∈ Rn, it satisfies ‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖."

`IsConvexLSmooth L φ` says: `φ` is convex on `ℝᵈ`, differentiable, and its gradient is
`L`-Lipschitz: `‖∇φ(x) − ∇φ(y)‖ ≤ L‖x − y‖` for all `x, y`. This is the hypothesis on each
summand `fᵢ` of Problem (1.1) in Theorem 4.1 ("each fi(x) is convex, L-smooth").

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)` and `∇` is Mathlib's `gradient`; the
clause `Differentiable ℝ φ` makes `gradient φ` the true gradient (Mathlib's `gradient` is `0` at
points of non-differentiability). `0 < L` is not bundled; the theorems state it separately. -/
def IsConvexLSmooth {d : ℕ} (L : ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ConvexOn ℝ Set.univ φ ∧ Differentiable ℝ φ ∧
    ∀ x y : EuclideanSpace ℝ (Fin d), ‖gradient φ x - gradient φ y‖ ≤ L * ‖x - y‖

end KatyushaNs


