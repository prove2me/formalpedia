-- Prove2me | Definitions.Def_DiffCtrlRobust_IsMinimizingSelector
-- name    : DiffCtrlRobust_IsMinimizingSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:53.759224+00:00
-- url     : https://prove2.me/theorems/c1957067-c40a-4331-84c4-cb09e2c73ff5
-- title:
--   Measurable minimizing selectors of the HJB equation
-- statement:
--   A control $v\in\mathfrak U_{\mathsf{sm}}$ is a measurable minimizing selector for $V$ if
--
--   $$
--   b(x,v(x))\cdot\nabla V(x)+c(x,v(x))=\min_{\zeta\in\mathbb U}\big[b(x,\zeta)\cdot\nabla V(x)+c(x,\zeta)\big]\qquad\text{a.e. }x\in\mathbb R^d.
--   $$
--
--   This is (3.2), and (3.4) for an approximating model. Here $b(x,v(x))$ and $c(x,v(x))$ are the relaxed integrals against the measure $v(x)$.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, p.10, (3.2), and p.11, (3.4)

import Definitions.Def_DiffCtrlRobust_relaxed
import Definitions.Def_DiffCtrlRobust_Usm

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- `v ∈ 𝔘sm` is a measurable minimizing selector of the HJB equation with solution `V`: (3.2), and
(3.4) for an approximating model (arXiv:2205.05894v2, p.10 and p.11),
`b(x, v(x)) · ∇V(x) + c(x, v(x)) = min_{ζ∈U} [b(x, ζ) · ∇V(x) + c(x, ζ)]` for a.e. `x`.

**Formalization Note.** `b(x, v(x))` and `c(x, v(x))` are the relaxed integrals against the measure
`v(x)`. Measurability is carried by the type `Usm`. "a.e." is for Lebesgue measure on `ℝ^d`. -/
def IsMinimizingSelector {d : ℕ} {U : Type*} [MeasurableSpace U]
    (b : SDEState d → U → SDEState d) (c : SDEState d → U → ℝ) (V : SDEState d → ℝ)
    (v : Usm d U) : Prop :=
  ∀ᵐ x, fderiv ℝ V x (relaxed b x (v.1 x)) + relaxed c x (v.1 x) =
    ⨅ ζ, fderiv ℝ V x (b x ζ) + c x ζ

end DiffCtrlRobust


