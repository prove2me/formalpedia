-- Prove2me | Definitions.Def_HoneycombCodes_M2
-- name    : HoneycombCodes_M2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:29.005761+00:00
-- url     : https://prove2.me/theorems/65a6ec44-43de-46a8-b771-3867bd5843e2
-- title:
--   MRRW exponents $M_1(\delta)$ and $M_2(\delta)=\min_{0\le\tau\le1-2\delta}F_\delta(\tau)$
-- statement:
--   For $0<\delta<1/2$ the two McEliece–Rodemich–Rumsey–Welch exponents are
--
--   $$
--   M_1(\delta)=H_2\Bigl(\tfrac12-\sqrt{\delta(1-\delta)}\Bigr),\qquad
--   M_2(\delta)=\min_{0\le\tau\le 1-2\delta}F_\delta(\tau),\qquad
--   F_\delta(\tau)=1+g(\tau^2)-g(\tau^2+2\delta\tau+2\delta),
--   $$
--
--   with $g$ as in the definition of $H_2$, $J$, $g$. $M_2$ is the benchmark that the honeycomb exponent contains (Proposition 6.5) and that 2MQC improves (eq. (128)).
--
--   **Formalization Note** $M_2$ is the real infimum of the image of $[0,1-2\delta]$ under $F_\delta$; the interval is nonempty and compact and $F_\delta$ is continuous there, so this is the printed minimum. Mirrors the published `MetricCodes.Johnson.mrrwRate` and `MetricCodes.Hamming.classicalRate`.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), eqs. (1)–(2), p.1 (PDF 3)

import Mathlib
import Definitions.Def_HoneycombCodes_H2

set_option autoImplicit false

namespace HoneycombCodes

/-- The **first MRRW exponent** `M₁(δ) = H₂(1/2 − √(δ(1 − δ)))`, Gay, Granha Jeronimo, Liu,
*The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), eq. (1),
p.1 (PDF 3). Mirrors the published `MetricCodes.Hamming.classicalRate`. -/
noncomputable def M1 (δ : ℝ) : ℝ :=
  H2 (1 / 2 - Real.sqrt (δ * (1 - δ)))

/-- The second MRRW objective `F_δ(τ) = 1 + g(τ²) − g(τ² + 2δτ + 2δ)`, arXiv:2608.20287v2,
eq. (2), p.1 (PDF 3). Mirrors the published `MetricCodes.Johnson.mrrwObjective`. -/
noncomputable def Fdelta (δ τ : ℝ) : ℝ :=
  1 + g (τ ^ 2) - g (τ ^ 2 + 2 * δ * τ + 2 * δ)

/-- The **second MRRW exponent** `M₂(δ) = min_{0 ≤ τ ≤ 1 − 2δ} F_δ(τ)`, arXiv:2608.20287v2,
eq. (2), p.1 (PDF 3).

**Formalization Note.** The minimum is written as the real `sInf` of the image of the closed
interval `[0, 1 − 2δ]`; for `0 < δ < 1/2` the interval is nonempty and compact and `F_δ` is
continuous on it, so this is the printed minimum. Mirrors the published
`MetricCodes.Johnson.mrrwRate`. -/
noncomputable def M2 (δ : ℝ) : ℝ :=
  sInf (Fdelta δ '' Set.Icc 0 (1 - 2 * δ))

end HoneycombCodes


