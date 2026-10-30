-- Prove2me | Definitions.Def_KuhnWass2019_Reformulation_RegularLoss
-- name    : KuhnWass2019_Reformulation_RegularLoss
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T03:14:34.805995+00:00
-- url     : https://prove2.me/theorems/5a000d3a-1fd0-4510-847d-d44ebc9d8936
-- title:
--   Measurable, upper semicontinuous and nominally absolutely integrable loss
-- statement:
--   For a nominal law $P_N$, an extended-real loss $\ell$ is regular if it is measurable, upper semicontinuous, and $\int |\ell|\,dP_N<\infty$. The absolute integral is the nonnegative Lebesgue integral of $\ell^++\ell^-$. No integrability is imposed under other laws.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), pp. 1–2 and 9, Assumption 1

import Mathlib

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- Measurability (p. 1) and Assumption 1 (p. 9), including absolute integrability. -/
def RegularLoss {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (PN : Measure E) (ℓ : E → EReal) : Prop :=
  Measurable ℓ ∧ UpperSemicontinuous ℓ ∧
    (∫⁻ x, ((ℓ x).toENNReal + (-ℓ x).toENNReal) ∂PN) < ⊤

end KuhnWass2019.Reformulation


