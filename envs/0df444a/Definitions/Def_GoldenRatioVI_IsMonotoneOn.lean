-- Prove2me | Definitions.Def_GoldenRatioVI_IsMonotoneOn
-- name    : GoldenRatioVI_IsMonotoneOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:21:59.745471+00:00
-- url     : https://prove2.me/theorems/bc57528e-5a34-4c91-8255-9f7b4bc8a2d6
-- title:
--   Condition (C3): $F$ is monotone on $\operatorname{dom} g$
-- statement:
--   Let $D\subseteq\mathcal E$ and $F:\mathcal E\to\mathcal E$. The operator $F$ is **monotone on $D$** if
--   $$\langle F(u)-F(v),\,u-v\rangle\ \ge\ 0\qquad\text{for all } u,v\in D.$$
--   With $D=\operatorname{dom} g$ this is the standing assumption (C3) of the paper.
--
--   This is monotonicity in the sense of monotone operator theory (not order monotonicity); gradients of convex functions and skew-symmetric linear maps (saddle-point problems) are examples.
--
--   **Formalization Note** $F$ is a total function on $\mathcal E$; only its values on $D$ are constrained.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), §1, p. 1, condition (C3)

import Mathlib

namespace GoldenRatioVI

/-- **Condition (C3): `F` is monotone on `dom g`.**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), §1, p. 1,
(C3): "F: dom g → E is monotone: ⟨F(u) − F(v), u − v⟩ ≥ 0 ∀u, v ∈ dom g."

`IsMonotoneOn D F` says `0 ≤ ⟪F u − F v, u − v⟫` for all `u, v ∈ D`.

**Formalization Note.** This is monotonicity of an operator in the sense of variational analysis,
not Mathlib's order-theoretic `Monotone`. `F` is a function on all of `E`; only its values on `D`
are constrained. -/
def IsMonotoneOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Set E) (F : E → E) : Prop :=
  ∀ u ∈ D, ∀ v ∈ D, 0 ≤ inner ℝ (F u - F v) (u - v)

end GoldenRatioVI


