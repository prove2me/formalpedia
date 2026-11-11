-- Prove2me | Definitions.Def_DiscIsoCurvature_Cube_GaussProfile
-- name    : DiscIsoCurvature_Cube_GaussProfile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:06:49.918221+00:00
-- url     : https://prove2.me/theorems/d1d4e256-4f6b-407f-ad2a-58dc9940443b
-- title:
--   The Gaussian isoperimetric profile I = φ ∘ Φ⁻¹ on (0, 1), with I(0) = I(1) = 0
-- statement:
--   Let $\varphi(y)=e^{-y^2/2}/\sqrt{2\pi}$ and $\Phi(y)=\int_{-\infty}^y\varphi$ be the standard normal density and distribution function. The **Gaussian isoperimetric profile** (Definition 3.17) is
--   $$\mathcal I(a)=\varphi\big(\Phi^{-1}(a)\big)\quad(0<a<1),\qquad \mathcal I(0)=\mathcal I(1)=0.$$
--   It is the isoperimetric function of the Gaussian measure and appears in the local Bobkov inequality (Theorem 5.1) and Fact 3.18.
--
--   **Formalization Note.** $\Phi^{-1}(a)$ is `sInf {y | a ≤ Φ y}`, the inverse of $\Phi$ for $a\in(0,1)$. The paper's $\mathcal I$ lives on $[0,1]$; the Lean function lives on $\mathbb R$ and is $0$ outside $(0,1)$. Values outside $[0,1]$ are never used.
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 17, Definition 3.17

import Mathlib

namespace DiscIsoCurvature.Cube

/-!
# The Gaussian isoperimetric profile

Chen, Chen, Zhang, *Discrete Isoperimetric Inequalities via Curvature*, arXiv:2609.24687
(version of November 3, 2026, sha256 ec30d304…), Definition 3.17, p. 17.

`I(x) = φ(Φ⁻¹(x))` for `x ∈ (0, 1)` and `I(0) = I(1) = 0`, with `φ`, `Φ` the standard normal
density and distribution function. `Φ⁻¹(a)` is taken as `inf {y | a ≤ Φ(y)}`, which for
`a ∈ (0, 1)` is the unique `y` with `Φ(y) = a` (`Φ` is continuous and strictly increasing from `0`
to `1`). The paper's `I` is a function on `[0, 1]`; in Lean it is a function on `ℝ` that is `0`
outside `(0, 1)` (in particular `I(0) = I(1) = 0`); values outside `[0, 1]` are never used.
-/

/-- Standard normal density `φ(y) = e^{−y²/2} / √(2π)`. -/
noncomputable def stdNormalPDF (y : ℝ) : ℝ :=
  Real.exp (-(y ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- Standard normal distribution function `Φ(y) = ∫_{-∞}^{y} φ(s) ds`. -/
noncomputable def stdNormalCDF (y : ℝ) : ℝ :=
  ∫ s in Set.Iic y, stdNormalPDF s

/-- `Φ⁻¹(a) = inf {y | a ≤ Φ(y)}`; for `a ∈ (0, 1)` this is the inverse of `Φ` at `a`. -/
noncomputable def stdNormalQuantile (a : ℝ) : ℝ :=
  sInf {y : ℝ | a ≤ stdNormalCDF y}

/-- The Gaussian isoperimetric profile (Definition 3.17): `I(a) = φ(Φ⁻¹(a))` for `0 < a < 1`,
and `I(a) = 0` otherwise (so `I(0) = I(1) = 0`). -/
noncomputable def gaussProfile (a : ℝ) : ℝ :=
  if 0 < a ∧ a < 1 then stdNormalPDF (stdNormalQuantile a) else 0

end DiscIsoCurvature.Cube


