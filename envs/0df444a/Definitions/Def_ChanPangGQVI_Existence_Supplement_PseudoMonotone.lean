-- Prove2me | Definitions.Def_ChanPangGQVI_Existence_Supplement_PseudoMonotone
-- name    : ChanPangGQVI_Existence_Supplement_PseudoMonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:54:01.129521+00:00
-- url     : https://prove2.me/theorems/2dbda103-a953-40f4-b158-ec0c01adefad
-- title:
--   Pseudo-monotonicity of a point-to-set mapping with respect to K (§4)
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean inner product $x^T y$. Let $\mu$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself. The mapping $\mu$ is **pseudo-monotone with respect to $K$** if for every pair of points $x, x'$ with
--
--   $$
--   x\in K(x),\qquad x'\in K(x'),
--   $$
--
--   and every $y\in\mu(x)$, $y'\in\mu(x')$, the implication
--
--   $$
--   (x'-x)^T y\ \ge\ 0\ \Longrightarrow\ (x'-x)^T y'\ \ge\ 0
--   $$
--
--   holds. Only fixed points of $K$ (points with $x\in K(x)$) are compared, as in the paper's "for any $(x,x')\in K(x)\times K(x')$".
--
--   For a constant $K$ and single-valued $\mu$ this is the usual pseudo-monotonicity of variational-inequality theory. It is the monotonicity hypothesis of the existence result Theorem 4.3 for the generalized quasi-variational inequality $\mathrm{GQVI}(K,f)$.
--
--   **Formalization Note** The predicate is `IsPseudoMonotoneWRT μ K` on `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 219, Section 4 (definition preceding Theorem 4.3)

import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence.Supplement

/-- Chan and Pang, *The generalized quasi-variational inequality problem*, Math. Oper. Res. 7
(1982), p. 219, §4: a point-to-set mapping `μ` of `ℝⁿ` is *pseudo-monotone with respect to* a
point-to-set mapping `K` if for any `(x, x') ∈ K(x) × K(x')` and `(y, y') ∈ μ(x) × μ(x')`,
`(x' - x)ᵀ y ≥ 0 ⇒ (x' - x)ᵀ y' ≥ 0`.

The pair `(x, x') ∈ K(x) × K(x')` means `x ∈ K(x)` and `x' ∈ K(x')`: only fixed points of `K` are
compared. -/
def IsPseudoMonotoneWRT {n : ℕ}
    (μ K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x x' : EuclideanSpace ℝ (Fin n), x ∈ K x → x' ∈ K x' →
    ∀ y ∈ μ x, ∀ y' ∈ μ x', 0 ≤ ⟪x' - x, y⟫ → 0 ≤ ⟪x' - x, y'⟫

end ChanPangGQVI.Existence.Supplement


