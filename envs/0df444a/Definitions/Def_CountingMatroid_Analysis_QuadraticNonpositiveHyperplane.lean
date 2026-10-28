-- Prove2me | Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
-- name    : CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:23.024123+00:00
-- url     : https://prove2.me/theorems/995e2829-a969-4eab-a538-5ef30b185d5e
-- title:
--   A nonpositive subspace of codimension at most one
-- statement:
--   Let $V$ be a real vector space and let $Q:V\to\mathbb R$ be a quadratic form. The predicate $\operatorname{HasNonpositiveHyperplane}(Q)$ is
--   $$\exists\,\ell:V\to\mathbb R\text{ linear},\qquad
--   \forall v\in V,\quad \ell(v)=0\Longrightarrow Q(v)\leq0.$$
--   The witness identifies a subspace $\ker\ell$ on which the quadratic form is nonpositive. The linear functional may be zero, so the allowed codimension is at most one. No finite-dimensionality or nonzero-functional assumption is part of the predicate.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/QuadraticNonpositiveHyperplane.lean#L16-L21

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

section


set_option autoImplicit false

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

/-- INTERNAL: A witness for the codimension-at-most-one nonpositive subspace
needed in the quadratic signature argument.
TEXLINE: main.tex:326-348 -/
def HasNonpositiveHyperplane {V : Type} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) : Prop :=
  ∃ l : V →ₗ[ℝ] ℝ, ∀ v, l v = 0 → Q v ≤ 0









end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

end


