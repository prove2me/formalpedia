-- Prove2me | Definitions.Def_ZOGlobalLB_Supplement_GoldsteinAdmissible
-- name    : ZOGlobalLB_Supplement_GoldsteinAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:48:24.152591+00:00
-- url     : https://prove2.me/theorems/bcde8cc4-f874-45a1-90da-7a42ad7f6677
-- title:
--   Nonsmooth stochastic class for the Goldstein lower bound
-- statement:
--   A nonempty finite family $(f_\xi)_{\xi\in\Xi}$ is admissible for the stochastic Goldstein theorem when its population mean $f=|\Xi|^{-1}\sum_\xi f_\xi$ is globally Lipschitz and bounded below, satisfies $f(0)-\inf f\le\Delta$, and
--
--   $$
--   \frac1{|\Xi|}\sum_{\xi\in\Xi}\operatorname{Lip}(f_\xi)^2\le L_0^2.
--   $$
--
--   The population objective may be nonsmooth; no differentiability or $H$-smoothness is imposed.
--
--   **Formalization Note** The finite label set is `Fin n`. Extended nonnegative Lipschitz constants ensure that non-Lipschitz samples cannot pass through a default real supremum.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem 2.2, p.5

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible
import Definitions.Def_ZOGlobalLB_lipConst

open scoped ENNReal

namespace ZOGlobalLB

namespace Supplement

/-- The nonsmooth stochastic class of Theorem 2.2 in Xia--Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*,
arXiv:2610.19652, p.5: a nonempty finite sample family whose population mean is globally
Lipschitz (but need not be differentiable), is bounded below with initial gap at most `Δ`, and
whose average squared sample Lipschitz constants is at most `L₀²`.

**Formalization Note.** This is deliberately not the published smooth class `Admissible`: no
differentiability or `H`-smoothness is imposed. The finite label set is `Fin n`, and `lipConst`
takes values in `ℝ≥0∞`, so non-Lipschitz functions cannot pass through a junk real supremum. -/
def GoldsteinAdmissible {d n : ℕ} (Δ L₀ : ℝ) (F : Fin n → E d → ℝ) : Prop :=
  0 < n ∧
  BddBelow (Set.range (popMean F)) ∧
  popMean F 0 - ⨅ x, popMean F x ≤ Δ ∧
  (n : ℝ≥0∞)⁻¹ * ∑ i, lipConst (F i) ^ 2 ≤ ENNReal.ofReal (L₀ ^ 2)

end Supplement

end ZOGlobalLB


