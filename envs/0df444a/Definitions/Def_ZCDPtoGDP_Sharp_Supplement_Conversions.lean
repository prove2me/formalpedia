-- Prove2me | Definitions.Def_ZCDPtoGDP_Sharp_Supplement_Conversions
-- name    : ZCDPtoGDP_Sharp_Supplement_Conversions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:09:03.752517+00:00
-- url     : https://prove2.me/theorems/c56bcacc-8dde-43b5-a81b-1536a23726e7
-- title:
--   Explicit forward zCDP and bounded-range conversion maps
-- statement:
--   For a nonnegative budget $\rho$, let $t_\rho$ be the unique nonnegative solution of $t\tanh(t/2)=\rho$, whose existence and uniqueness are part of the published goal (Theorem 6). Define
--   $$\mu_{\mathrm{zCDP}}(\rho)=2\Phi^{-1}(\sigma(t_\rho)),\qquad \mu_{\mathrm{BR}}(\varepsilon)=2\Phi^{-1}(\sigma(\varepsilon/2)),$$
--   where $\Phi$ is the standard normal CDF and $\sigma(t)=(1+e^{-t})^{-1}$. Both maps vanish at zero. These explicit maps supply the functions in the shape theorems; neither is defined by optimizing over privacy classes.
--
--   **Formalization Note** The root is the real infimum of the singleton nonnegative root set for $\rho\ge0$, and is extended by zero for negative budgets. All zCDP shape assertions are restricted to nonnegative budgets. The existing published $g=\Phi^{-1}\circ\sigma$ is reused, so the quantile arguments lie in $(0,1)$. No open theorem is imported into this definition.
-- source:
--   Yu-Wei Chen, Aaradhya Pandey, Jordan Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), Theorem 6, eq. (1); Theorem 13, p. 6, 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

namespace ZCDPtoGDP.Sharp.Supplement

/-! Source: Chen–Pandey–Awan, STOC 2027 submission #235 (October 2026),
Theorem 6, eq. (1), p. 6, and Theorem 13, p. 8. -/

/-- The nonnegative calibration root. The set is a singleton for `ρ ≥ 0`,
by the calibration clause of published Theorem 6. Thus its real infimum is
that root, not an optimization over privacy guarantees. On `ρ < 0` we extend by zero.
In particular the root at zero is zero. No open theorem is imported into this definition. -/
noncomputable def tRho (ρ : ℝ) : ℝ :=
  if 0 ≤ ρ then sInf {t : ℝ | 0 ≤ t ∧ t * Real.tanh (t / 2) = ρ} else 0

/-- The explicit forward conversion of Theorem 6, used on `[0,∞)`.
The existing `gFun` uses the normal quantile only at sigmoid values in `(0,1)`. -/
noncomputable def muZCDP (ρ : ℝ) : ℝ := 2 * gFun (tRho ρ)

/-- The explicit bounded-range/logistic conversion of Theorem 13, used on `[0,∞)`.
It has value zero at zero. -/
noncomputable def muBR (ε : ℝ) : ℝ := 2 * gFun (ε / 2)

end ZCDPtoGDP.Sharp.Supplement


