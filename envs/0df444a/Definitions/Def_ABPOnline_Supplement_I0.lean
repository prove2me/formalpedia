-- Prove2me | Definitions.Def_ABPOnline_Supplement_I0
-- name    : ABPOnline_Supplement_I0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:35:25.940316+00:00
-- url     : https://prove2.me/theorems/4b57f017-d9b9-4823-9e01-e9d3b82daacb
-- title:
--   The constant $I_0=\int_0^\infty\sqrt{2\Phi(-\sqrt{s/2})}\,ds$ of (56)
-- statement:
--   With $\Phi$ the standard normal distribution function,
--   $$
--   I_0:=\int_0^\infty\sqrt{2\Phi\big(-\sqrt{s/2}\big)}\,ds .
--   $$
--
--   This constant enters the leading constants of the large-negative-margin asymptotics of $E_\star$ and $\alpha_{\mathrm{on}}$ (Theorem 5.13).
--
--   **Formalization Note** $\Phi$ is the distribution function of the standard Gaussian measure. The integral is a Lebesgue integral over $(0,\infty)$; the integrand is bounded by $\sqrt2\,e^{-s/8}$, so the integral is finite. The numerical value $5.06296\ldots$ is not part of the definition.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), §5.3, (56), p.25 (PDF p.26)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ABPOnline.Supplement

/-- The constant `I₀ := ∫₀^∞ √(2Φ(−√(s/2))) ds` of (56) (Jo–Lee, arXiv:2609.02124, §5.3, (56),
printed p.25, PDF p.26), with `Φ` the standard normal distribution function.

**Formalization Note** `Φ` is Mathlib's `cdf (gaussianReal 0 1)`. The integral is the Bochner
integral over `(0, ∞)`; the integrand is continuous, nonnegative and bounded by `√2·e^{−s/8}`, so it
is integrable and `I₀` is the paper's finite positive constant (numerically `5.06296…`, a value
that is not part of the definition). -/
noncomputable def I0 : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), Real.sqrt (2 * cdf (gaussianReal 0 1) (-Real.sqrt (s / 2)))

end ABPOnline.Supplement


