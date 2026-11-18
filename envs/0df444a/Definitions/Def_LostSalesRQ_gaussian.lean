-- Prove2me | Definitions.Def_LostSalesRQ_gaussian
-- name    : LostSalesRQ_gaussian
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-17T18:22:58.365666+00:00
-- url     : https://prove2.me/theorems/b42c5823-48d6-45c3-99bb-cd2b7dbd0c02
-- title:
--   Gaussian profiles $\phi$, $\Phi$, $w$ and $G$
-- statement:
--   The standard normal density $\phi(z)=e^{-z^2/2}/\sqrt{2\pi}$ and distribution function $\Phi(z)=\int_{-\infty}^{z}\phi(x)\,dx$, together with two profiles used in the appendix comparisons:
--
--   1. the Brownian profile of Appendix D,
--   $$w(z)=\phi(z)-z\,[1-\Phi(z)]+\frac{\Phi(z)-1/2}{z}\quad(z>0),\qquad w(0)=\sqrt{2/\pi};$$
--   2. the Gaussian rank profile of Lemma G.1,
--   $$G(s)=\inf_{z\in\mathbb R}\big\{\phi(z)+z\,\Phi(z)+s\,[1-\Phi(z)]\big\}.$$
--
--   $\sqrt T\,w(\ell\sqrt T)$ is the expected running maximum of a Brownian motion with drift $-\ell$ over $[0,T]$ (Lemma D.1), and $\sqrt\mu\,G(\eta/\sqrt\mu)$ is a Gaussian counterpart of the rank bound $B_\mu(\eta)$ (Lemma G.1).
--
--   **Formalization Note** $\Phi$ is the integral of $\phi$ over $(-\infty,z]$ against Lebesgue measure. The formula for $w$ is also applied for $z<0$; the paper uses only $z\ge0$. $G(s)$ is a real infimum, bounded below by $0$ for $s\ge0$.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Appendix D (p. A7); Lemma G.1 (p. A12).

import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian profiles used in the appendix comparisons

The standard normal density `φ` and distribution function `Φ`, the Brownian profile `w`
(Appendix D) and the Gaussian rank profile `G` (Appendix G).
-/

namespace LostSalesRQ

open MeasureTheory Set

/-- Standard normal density `φ(z) = e^{-z²/2} / √(2π)`. -/
noncomputable def stdNormalPdf (z : ℝ) : ℝ :=
  Real.exp (-(z ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- Standard normal distribution function `Φ(z) = ∫_{-∞}^{z} φ(x) dx`. -/
noncomputable def stdNormalCdf (z : ℝ) : ℝ :=
  ∫ x in Iic z, stdNormalPdf x

/-- Brownian profile `w(z) = φ(z) - z (1 - Φ(z)) + (Φ(z) - 1/2) / z` for `z ≠ 0`,
with `w(0) = √(2/π)` (Appendix D). -/
noncomputable def brownianProfile (z : ℝ) : ℝ :=
  if z = 0 then Real.sqrt (2 / Real.pi)
  else stdNormalPdf z - z * (1 - stdNormalCdf z) + (stdNormalCdf z - 1 / 2) / z

/-- Gaussian rank profile `G(s) = inf_{z ∈ ℝ} {φ(z) + z Φ(z) + s (1 - Φ(z))}` (Lemma G.1). -/
noncomputable def gaussianRankProfile (s : ℝ) : ℝ :=
  ⨅ z : ℝ, (stdNormalPdf z + z * stdNormalCdf z + s * (1 - stdNormalCdf z))

end LostSalesRQ


