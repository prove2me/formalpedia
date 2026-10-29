-- Prove2me | Definitions.Def_PeskirShiryaev_UltimateMaximum_gaussianBoundary
-- name    : PeskirShiryaev_UltimateMaximum_gaussianBoundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:38.333275+00:00
-- url     : https://prove2.me/theorems/d276e59a-93ca-4f93-afbb-69676ec0f210
-- title:
--   Gaussian functions and the analytic prediction boundary
-- statement:
--   Let $\varphi$ and $\Phi$ be the standard normal density and distribution function. Set
--   $$\varphi(x)=\frac{e^{-x^2/2}}{\sqrt{2\pi}},\quad \Phi(x)=\int_{-\infty}^x\varphi(y)\,dy,\quad F(x)=4\Phi(x)-3.$$
--   Define $r(z)=4\Phi(z)-2z\varphi(z)-3$ and $z_*=\inf\{z\ge0:r(z)=0\}$. The analytic candidate is
--   $$W(z)=\begin{cases}\Phi(z_*)(1+z^2)-|z|\varphi(|z|)+(1-z^2)\Phi(|z|)-3/2,&|z|\le z_*,\\0,&|z|>z_* .\end{cases}$$
--   These definitions specify the boundary equation and the even, zero-extended candidate, independently of any optimal stopping value. Existence and uniqueness of the root and the free-boundary equations are theorem obligations.
--
--   **Formalization Note** All functions are real-valued. The real infimum defining $z_*$ is total; the candidate-equations theorem establishes that its defining set is a nonempty singleton. The CDF uses a Lebesgue integral over $(-\infty,x]$; inclusion of the endpoint has no effect.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 441 (PDF p. 457), Eq. (30.1.3); p. 442 / PDF 458, Eq. (30.1.5); pp. 444–445 / PDF 460–461, Eqs. (30.1.21)–(30.1.27)

import Mathlib

open MeasureTheory Set

namespace PeskirShiryaev.UltimateMaximum

noncomputable def phi (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

noncomputable def Phi (x : ℝ) : ℝ := ∫ y in Iic x, phi y

noncomputable def runningCost (x : ℝ) : ℝ := 4 * Phi x - 3

noncomputable def rootEquation (z : ℝ) : ℝ := 4 * Phi z - 2 * z * phi z - 3

noncomputable def criticalLevel : ℝ := sInf {z : ℝ | 0 ≤ z ∧ rootEquation z = 0}

noncomputable def candidate (z : ℝ) : ℝ :=
  if |z| ≤ criticalLevel then
    Phi criticalLevel * (1 + z ^ 2) - |z| * phi |z| +
      (1 - z ^ 2) * Phi |z| - 3 / 2
  else 0

end PeskirShiryaev.UltimateMaximum


