-- Prove2me | Definitions.Def_MonoABPWidth_Hierarchy_projection
-- name    : MonoABPWidth_Hierarchy_projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:14:55.725159+00:00
-- url     : https://prove2.me/theorems/0f9168e3-aba9-46a3-96f9-5cdccbafed93
-- title:
--   Monotone projections between polynomial variable sets
-- statement:
--   Let $\sigma$ and $\tau$ be source and target variable sets. A monotone projection assigns each $x\in\sigma$ either a variable of $\tau$ or a nonnegative real scalar, and extends to polynomials by substitution:
--   $$
--   \pi(f)=f\bigl((\pi(x))_{x\in\sigma}\bigr).
--   $$
--   Constants include $0$ and $1$, distinct source variables may be identified, and the two variable sets can differ. There is no part-preservation condition. This is the full projection notion of §2.1, allowing the boundary renaming in Lemma 4.7. The published SetMultCost projection permits only zero or a variable, so cannot supply this interface.
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), §2.1, p.4, PDF5; Lemma 4.7 and its proof, pp.10–11, PDF11–12

import Mathlib

namespace MonoABPWidth.Hierarchy

/-- §2.1, p.4: each source variable maps to a target variable or any nonnegative
real constant. Source and target variable types can differ; identification is allowed. -/
structure MonotoneProjection (σ τ : Type) where
  image : σ → τ ⊕ NNReal

/-- Polynomial substitution extending the specified variable images. -/
noncomputable def MonotoneProjection.apply {σ τ : Type} (π : MonotoneProjection σ τ)
    (f : MvPolynomial σ ℝ) : MvPolynomial τ ℝ :=
  MvPolynomial.bind₁ (fun x => match π.image x with
    | Sum.inl y => MvPolynomial.X y
    | Sum.inr c => MvPolynomial.C (c : ℝ)) f

end MonoABPWidth.Hierarchy


