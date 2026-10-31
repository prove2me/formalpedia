-- Prove2me | Definitions.Def_DiffCtrlRobust_IsHJBSolution
-- name    : DiffCtrlRobust_IsHJBSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:49.693976+00:00
-- url     : https://prove2.me/theorems/2314ab21-3660-43da-b335-b14f8efcaf9e
-- title:
--   Solutions in $\mathcal C^2\cap\mathcal C_b$ of the discounted HJB equation
-- statement:
--   A function $V\in\mathcal C^2(\mathbb R^d)\cap\mathcal C_b(\mathbb R^d)$ solves the discounted Hamilton–Jacobi–Bellman equation of the model $(b,\sigma,c)$ if
--
--   $$
--   \min_{\zeta\in\mathbb U}\big[\mathcal L_\zeta V(x)+c(x,\zeta)\big]=\alpha V(x)\qquad\text{for all }x\in\mathbb R^d.
--   $$
--
--   This is (3.1), and (3.3) for an approximating model.
--
--   **Formalization Note** The minimum is written as an infimum over $\mathbb U$. For a $\mathcal C^2$ function and continuous coefficients the expression is continuous in $\zeta$ on the nonempty compact $\mathbb U$, so the infimum is attained.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, p.10, (3.1), and p.11, (3.3)

import Definitions.Def_DiffCtrlRobust_generator

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- `V ∈ C²(ℝ^d) ∩ C_b(ℝ^d)` solves the HJB equation
`min_{ζ∈U} [𝓛_ζ V(x) + c(x, ζ)] = α V(x)` for all `x ∈ ℝ^d`, which is (3.1), and (3.3) for an
approximating model (arXiv:2205.05894v2, p.10 and p.11).

**Formalization Note.** `min` is `⨅ ζ`. For a `C²` function `V` and coefficients as in (A1), (A4), the
expression is continuous in `ζ` on the nonempty compact `U`, so the infimum is attained and the
real `⨅` is the printed minimum. Continuity of `V` is part of `ContDiff ℝ 2 V`. -/
structure IsHJBSolution {d : ℕ} {U : Type*} (α : ℝ) (b : SDEState d → U → SDEState d)
    (σ : SDEState d → SDEDiffusion d) (c : SDEState d → U → ℝ) (V : SDEState d → ℝ) : Prop where
  /-- `V ∈ C²(ℝ^d)`. -/
  contDiff : ContDiff ℝ 2 V
  /-- `V` is bounded. -/
  bounded : ∃ K : ℝ, ∀ x, |V x| ≤ K
  /-- The equation holds at every `x`. -/
  hjb : ∀ x, (⨅ ζ, generator b σ ζ V x + c x ζ) = α * V x

end DiffCtrlRobust


