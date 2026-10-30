-- Prove2me | Definitions.Def_StatComplexityDMAudit_OnlineEstimation_Densities
-- name    : StatComplexityDMAudit_OnlineEstimation_Densities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:03:38.016761+00:00
-- url     : https://prove2.me/theorems/6e2e0311-37bf-44aa-9c27-f4db409da3a3
-- title:
--   Conditional densities, Hellinger integrals and extended log loss
-- statement:
--   Let $H,X,Y$ be arbitrary measurable spaces and let $\nu(dy\mid x)$ be a kernel. A conditional density $g(y\mid x;h)$ is jointly measurable, finite and nonnegative, and satisfies
--   $$\int_Y g(y\mid x;h)\,\nu(dy\mid x)=1\quad\text{for every }h,x.$$
--   For finite nonnegative densities $p,q$, define
--   $$D_{\mathrm H}^2(p,q)=\int(\sqrt p-\sqrt q)^2\,d\nu,\qquad A(p,q)=\int\sqrt{pq}\,d\nu,\qquad \ell_{\log}(q)=-\log q.$$
--   The square-root likelihood ratio is $\sqrt{q/p}$ on $\{p>0\}$ and zero elsewhere. Log loss at zero is $+\infty$; Hellinger distance has no factor of $1/2$.
--
--   These definitions supply the shared general-measure objects used by the online statements. Normalization and joint measurability are the only density constraints. Fibrewise sigma-finiteness of the kernel is a hypothesis of the theorem items, not a stronger uniform kernel typeclass.
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3 (11 July 2023), https://arxiv.org/abs/2112.13487v3, §2, equation (5), printed/PDF p. 10; §A.3, p. 75; §A.3.5, proof of Lemma A.14, p. 79.

import Mathlib

set_option autoImplicit false
open scoped ENNReal NNReal

namespace StatComplexityDMAudit.OnlineEstimation

open MeasureTheory ProbabilityTheory

/-- A jointly measurable, finite nonnegative conditional density, with parameter `H`.
The base is Mathlib's general kernel; no uniform sigma-finiteness is imposed. -/
structure ConditionalDensity (H X Y : Type*) [MeasurableSpace H]
    [MeasurableSpace X] [MeasurableSpace Y] (ν : Kernel X Y) where
  value : H × (X × Y) → ℝ≥0
  measurable_value : Measurable value
  normalized : ∀ h x, ∫⁻ y, (value (h, (x, y)) : ℝ≥0∞) ∂ν x = 1

/-- Equation (5), without a factor of one half. Nonnegative integration never
assigns zero to a nonintegrable positive function. -/
noncomputable def hellingerSq {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (p q : Y → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((Real.sqrt (p y : ℝ) - Real.sqrt (q y : ℝ)) ^ 2) ∂ν

/-- The conditional affinity integrand integrated against the base measure. -/
noncomputable def affinity {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (p q : Y → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (Real.sqrt ((p y : ℝ) * (q y : ℝ))) ∂ν

/-- Square-root likelihood ratio on the true support, extended by zero off it. -/
noncomputable def sqrtRatio (p q : ℝ≥0) : ℝ≥0∞ :=
  if p = 0 then 0 else ENNReal.ofReal (Real.sqrt ((q : ℝ) / (p : ℝ)))

/-- Log loss is positive infinity at density zero; it can be negative at density > 1. -/
noncomputable def logLoss (q : ℝ≥0) : EReal := -ENNReal.log (q : ℝ≥0∞)

end StatComplexityDMAudit.OnlineEstimation


