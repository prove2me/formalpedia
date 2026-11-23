-- Prove2me | Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Duality
-- name    : ProjSelfConcordant_ConicExt_Supplement_Duality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:17:41.976316+00:00
-- url     : https://prove2.me/theorems/0b45d62a-99d4-45fd-bc87-b227533f5c27
-- title:
--   Definition 5.2, p. 13 — q_p(x) = f(x) + log(1 + ⟨x, p⟩), the dual domain and dual function f∗, the duality map x ↦ −f′(x)/(1 + ⟨f′(x), x⟩)
-- statement:
--   This file fixes the objects of the duality theory of §5 of Hildebrand's paper.
--
--   Let $E$ be a real inner product space (in the theorems $E=\mathbb R^n$), $X\subset E$ with interior $X^o$, and $f:E\to\mathbb R$.
--
--   1. **The function $q_p$.** $q_p(x)=f(x)+\log(1+\langle x,p\rangle)$.
--   2. **Domain of the dual.** The domain of definition of $f_*$ is the set of points $p$ such that $q_p$ is defined on $X^o$, i.e. $1+\langle x,p\rangle>0$ for every $x\in X^o$, and has a critical point in $X^o$.
--   3. **Dual function.** $$f_*(p)=-\min_{x\in X^o}\bigl(f(x)+\log(1+\langle x,p\rangle)\bigr).$$
--   4. **Duality map.** $P(x)=-\dfrac{f'(x)}{1+\langle f'(x),x\rangle}$, and the set $\{x\in X^o\mid 1+\langle f'(x),x\rangle>0\}$ on which Lemma 5.4 considers it.
--
--   These are the objects of Lemmas 5.3, 5.4, Corollary 5.5 and Theorem 5.6. The polar $X^\circ=\{p\mid\langle x,p\rangle\le1\ \forall x\in X\}$ of Definition 5.2 is not redefined: Theorem 5.6 uses the published definition `ConeLifts.Shared.polar`, which is exactly this one-sided polar in $\mathbb R^n$.
--
--   **Formalization Note** The minimum is written as the real infimum of $q_p$ over $X^o$; on the domain of $f_*$ it is attained (Lemma 5.3), so it is the minimum of Definition 5.2; outside that domain the value is not used. Positivity of $1+\langle x,p\rangle$ on all of $X^o$ is part of the domain, so Lean's total logarithm is never evaluated at a nonpositive argument there. $f'(x)$ is the gradient vector `gradient f x`, so $\langle f'(x),x\rangle$ is its inner product with $x$.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 13, Definition 5.2 and the paragraph after it; Lemmas 5.3, 5.4 (the map x ↦ p)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt.Supplement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 5.2, p. 13: `q_p(x) = f(x) + log(1 + ⟨x, p⟩)`. -/
noncomputable def qfun (f : E → ℝ) (p : E) (x : E) : ℝ :=
  f x + Real.log (1 + inner ℝ x p)

/-- Definition 5.2, p. 13: the domain of definition of the dual function `f∗`: the points `p`
such that `q_p` is defined on `Xᵒ` (i.e. `1 + ⟨x, p⟩ > 0` for every `x ∈ Xᵒ`) and has a critical
point in `Xᵒ`. -/
def dualDomain (X : Set E) (f : E → ℝ) : Set E :=
  {p | (∀ x ∈ interior X, 0 < 1 + inner ℝ x p) ∧
    ∃ x ∈ interior X, fderiv ℝ (qfun f p) x = 0}

/-- Definition 5.2, p. 13: the dual function `f∗(p) = −min_{x ∈ Xᵒ} (f(x) + log(1 + ⟨x, p⟩))`.
The value is meaningful on `dualDomain X f`, where the minimum is attained (Lemma 5.3). -/
noncomputable def fstar (X : Set E) (f : E → ℝ) (p : E) : ℝ :=
  -(⨅ x : interior X, qfun f p x)

/-- Lemmas 5.3–5.4, p. 13: the duality map `x ↦ p = −f′(x)/(1 + ⟨f′(x), x⟩)`. -/
noncomputable def projGrad [CompleteSpace E] (f : E → ℝ) (x : E) : E :=
  -(1 + inner ℝ (gradient f x) x)⁻¹ • gradient f x

/-- Lemma 5.4, p. 13: the set `{x ∈ Xᵒ | 1 + ⟨f′(x), x⟩ > 0}`. -/
def admissibleSet [CompleteSpace E] (X : Set E) (f : E → ℝ) : Set E :=
  {x | x ∈ interior X ∧ 0 < 1 + inner ℝ (gradient f x) x}

end ProjSelfConcordant.ConicExt.Supplement


