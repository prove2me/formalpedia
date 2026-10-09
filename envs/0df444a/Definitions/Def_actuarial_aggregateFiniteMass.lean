-- Prove2me | Definitions.Def_actuarial_aggregateFiniteMass
-- name    : actuarial_aggregateFiniteMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:24:41.475153+00:00
-- url     : https://prove2.me/theorems/6b055948-4bf7-4066-8335-9107b30bc6b7
-- title:
--   Total probability over an explicitly bounded loss grid
-- statement:
--   The finite mass of a discrete loss distribution is the sum of all probability coefficients at integer losses from zero through the upper bound. Normalisation on this finite grid is useful only together with the fact that the distribution has no support beyond the selected bound.
--
--   **Mathematical statement**
--
--   $$
--   M_B(f)=\sum_{s=0}^{B}f(s)
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib

namespace ActuarialValuation

noncomputable def aggregateFiniteMass (f : ℕ → ℝ) (bound : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1), f s

end ActuarialValuation


