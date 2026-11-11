-- Prove2me | Definitions.Def_SumReLU_gaussL2
-- name    : SumReLU_gaussL2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:21.400967+00:00
-- url     : https://prove2.me/theorems/3031dd8f-ec67-4389-a5ef-085e538e47a5
-- title:
--   The Gaussian $L^2$ norm $\|g\|_{L^2}$
-- statement:
--   For a function $g:\mathbb R^d\to\mathbb R$,
--   $$
--   \|g\|_{L^2}=\Big(\mathbb E_{x\sim N(0,I_d)}\big[g(x)^2\big]\Big)^{1/2}.
--   $$
--   The learning guarantee of the paper is measured in this norm, both in relative form $\|h-f\|_{L^2}\le\epsilon\|f\|_{L^2}$ and in absolute form $\|h-f\|_{L^2}^2\le\epsilon$.
--
--   **Formalization Note** The expectation is the Bochner integral against Mathlib's standard Gaussian `stdGaussian` on $\mathbb R^d$. Since that integral is $0$ for a non-integrable integrand, every statement that bounds this norm from above also asserts the integrability of the square.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), §1.1, p.1 (PDF p.3); §2, p.10 (PDF p.12)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- The Gaussian `L²` norm `‖g‖_{L²} = (E_{x∼N(0,I_d)}[g(x)²])^{1/2}`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), §1.1, p.1 (PDF p.3): "For a function g : ℝᵈ → ℝ, we write ‖g‖_{L2} := (E_{x∼N(0,I_d)}[g(x)²])^{1/2}."

**Formalization Note.** `stdGaussian` is Mathlib's standard Gaussian on the finite-dimensional
inner product space `ℝᵈ`, i.e. `N(0, I_d)`. The Bochner integral is `0` for a non-integrable
`g²`; every statement that bounds `gaussL2` from above also asserts the integrability of the
square it bounds. -/
noncomputable def gaussL2 {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  Real.sqrt (∫ x, g x ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))

end SumReLU


