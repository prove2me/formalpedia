-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_delayFn
-- name    : DimCallCenters_Rationalized_delayFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:04:13.264921+00:00
-- url     : https://prove2.me/theorems/2194a864-0795-4c59-833b-f30a513c4bf8
-- title:
--   Halfin–Whitt delay function $P(x)$
-- statement:
--   Let $\phi(x) = e^{-x^2/2}/\sqrt{2\pi}$ be the standard normal density, $\Phi(x) = \int_{-\infty}^x \phi(y)\,dy$ its distribution function, and $h(x) = \phi(x)/(1-\Phi(x))$ its hazard rate. For $x > 0$,
--
--   $$P(x) = \frac{1}{1 + \dfrac{x}{h(-x)}},$$
--
--   display (11). It is the limit of the probability of waiting in the Halfin–Whitt regime $N = \lambda/\mu + x\sqrt{\lambda/\mu}$ (Lemma 4.1).
--
--   **Formalization Note** The normal density, distribution function and hazard rate are written out explicitly. The formula also gives $P(0) = 1$, which the paper uses in Lemma 4.1.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 15, Section 4, Eq. (11)

import Mathlib

namespace DimCallCenters.Rationalized

/-- The standard normal density `φ(x) = e^{-x²/2} / √(2π)` (p. 15). -/
noncomputable def stdPdf (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)

/-- The standard normal distribution function `Φ(x) = ∫_{-∞}^x φ(y) dy` (p. 15). -/
noncomputable def stdCdf (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, stdPdf y

/-- The hazard rate `h(x) = φ(x) / (1 - Φ(x))` of the standard normal distribution (p. 15). -/
noncomputable def hazard (x : ℝ) : ℝ :=
  stdPdf x / (1 - stdCdf x)

/-- The Halfin–Whitt delay function `P(x) = 1 / (1 + x / h(-x))`, (11) on p. 15. -/
noncomputable def delayFn (x : ℝ) : ℝ :=
  1 / (1 + x / hazard (-x))

end DimCallCenters.Rationalized


