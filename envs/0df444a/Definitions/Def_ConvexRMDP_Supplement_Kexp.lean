-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_Kexp
-- name    : ConvexRMDP_Supplement_Kexp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:51:28.102663+00:00
-- url     : https://prove2.me/theorems/53ded9d7-ab9d-4d96-82f8-a921effaa7df
-- title:
--   Exponential cone $\mathcal K_{\exp}\subset\mathbb R^3$ (two-piece form)
-- statement:
--   The **exponential cone** is the subset of $\mathbb R^3$
--
--   $$
--   \mathcal K_{\exp} := \{(x_1,x_2,x_3) : x_3 \le x_2 \log(x_1/x_2),\ x_1, x_2 > 0\} \cup \{(x_1, 0, x_3) : x_3 \le 0,\ x_1 \ge 0\}.
--   $$
--
--   It is a closed convex cone. For $x \ge 1$, $\alpha \ge 0$ and $z, u \in \mathbb R$ it encodes $z \le \alpha \log(x/\alpha)$ as $(x, \alpha, z) \in \mathcal K_{\exp}$ and $u \le \alpha \log(1/\alpha)$ as $(1, \alpha, u) \in \mathcal K_{\exp}$, with $\alpha \log \alpha = 0$ at $\alpha = 0$; this is how the conic programs (5.3), (5.10) and (6.4) are written.
--
--   **Formalization Note** $\mathbb R^3$ is `ℝ × ℝ × ℝ`. The platform's `ExpConeIPM.Curvature.Kexp` describes the same set as a closure on `EuclideanSpace ℝ (Fin 3)`; the printed two-piece form is used here.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §5.1, p.16 (definition of K_exp)

import Mathlib

namespace ConvexRMDP

namespace Supplement

/-- **The exponential cone** `𝒦_exp ⊂ ℝ³` (Grand-Clément & Petrik, arXiv:2209.10187v2, §5.1, p.16),
in the printed two-piece form
`𝒦_exp := {(x₁,x₂,x₃) | x₃ ≤ x₂ log(x₁/x₂), x₁, x₂ > 0} ∪ {(x₁,0,x₃) | x₃ ≤ 0, x₁ ≥ 0}`.

**Formalization Note.** `ℝ³` is `ℝ × ℝ × ℝ`, with `(x₁, x₂, x₃) = (x.1, x.2.1, x.2.2)`. -/
def Kexp : Set (ℝ × ℝ × ℝ) :=
  {x | 0 < x.1 ∧ 0 < x.2.1 ∧ x.2.2 ≤ x.2.1 * Real.log (x.1 / x.2.1)} ∪
    {x | 0 ≤ x.1 ∧ x.2.1 = 0 ∧ x.2.2 ≤ 0}

end Supplement

end ConvexRMDP


