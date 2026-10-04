-- Prove2me | Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
-- name    : MeanFieldOpt_FullSupport_IsTerminal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:44.992914+00:00
-- url     : https://prove2.me/theorems/3160f3c7-996e-4bcc-8f3c-dc99089c5ab5
-- title:
--   Admissible terminal condition $f_0$ of the Parisi PDE
-- statement:
--   A function $f_0 : \mathbb R \to \mathbb R$ is an **admissible terminal condition** if it is
--
--   1. convex and continuous,
--   2. non-negative and even: $f_0(-x) = f_0(x) \ge 0$,
--   3. differentiable for $x \neq 0$, with $0 \le f_0'(x) \le 1$ for all $x > 0$.
--
--   These are the standing assumptions of Section 6.1 on the terminal condition $\Phi(1,x) = f_0(x)$ of the Parisi PDE (6.2). The case of interest for the Parisi formula is $f_0(x) = |x|$.
--
--   **Formalization Note** Convexity is `ConvexOn ℝ Set.univ`, and $f_0'(x)$ for $x>0$ is Lean's `deriv f₀ x` (a genuine derivative there, by clause 3).
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 23, Section 6.1 (assumptions on f_0 after Eq. (6.2))

import Mathlib

namespace MeanFieldOpt.FullSupport

/-- The standing assumptions on the terminal condition `f₀` of the PDE (6.2)
(arXiv:2001.00904v1, p. 23): `f₀` is convex, continuous, non-negative, even, differentiable
for `x ≠ 0`, with `0 ≤ f₀'(x) ≤ 1` for all `x > 0`. -/
def IsTerminal (f₀ : ℝ → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f₀ ∧ Continuous f₀ ∧ (∀ x, 0 ≤ f₀ x) ∧ (∀ x, f₀ (-x) = f₀ x) ∧
    (∀ x, x ≠ 0 → DifferentiableAt ℝ f₀ x) ∧ (∀ x, 0 < x → 0 ≤ deriv f₀ x ∧ deriv f₀ x ≤ 1)

end MeanFieldOpt.FullSupport


