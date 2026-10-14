-- Prove2me | Definitions.Def_UnphysicalHilbert_Position
-- name    : UnphysicalHilbert_Position
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T21:03:24.833137+00:00
-- url     : https://prove2.me/theorems/31b40cf2-ef92-4c39-9afc-0466f9dfb418
-- title:
--   Changes of variables on the line and the Gaussian/Lorentzian wave functions
-- statement:
--   1. **Orientation-preserving diffeomorphism.** A bijection $f:\mathbb R\to\mathbb R$ is an orientation-preserving diffeomorphism if $f$ and $f^{-1}$ are $C^\infty$ and $f$ is strictly increasing.
--   2. **Transformed wave function.** For such $f$ and $\psi:\mathbb R\to\mathbb C$,
--   $$(U_f\psi)(y)=\psi\bigl(f^{-1}(y)\bigr)\sqrt{\left|\tfrac{d f^{-1}}{dy}(y)\right|}.$$
--   3. **Error function.** $\operatorname{erf}(x)=\dfrac{2}{\sqrt\pi}\displaystyle\int_0^x e^{-t^2}\,dt$.
--   4. **Gaussian wave function** (eq. (27)): $\psi(x)=\sqrt{e^{-x^2}/\sqrt\pi}$.
--   5. **Lorentzian wave function** (eq. (28)): $\phi(y)=1/\sqrt{\pi(y^2+1)}$, whose density $|\phi|^2$ is the standard Cauchy density.
--   6. **The coordinate change of eq. (29):** $y(x)=\tan\bigl(\tfrac\pi2\operatorname{erf}(x)\bigr)$.
--
--   These are the objects used in Section VI of the paper to exhibit a change of coordinates that turns finite expectation values into infinite ones.
--
--   **Formalization Note** In item 2 the paper writes the Jacobian factor as $|df^{-1}/dx|$; the factor that makes the map preserve the $L^2$ norm (paper's eq. (25)) is the derivative of $f^{-1}$ evaluated at $y$, which is what is used. Wave functions in items 4–6 are real-valued functions on $\mathbb R$.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Section VI, pp. 11–12 (Proposition 24, eqs. (26)–(29))

import Mathlib

/-!
# Unphysicality of Hilbert spaces — wave functions and changes of variables on `ℝ`

Definitions used by Proposition 24 and equations (27)–(29) of
G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*,
arXiv:2308.06669v3, Section VI.
-/

namespace UnphysicalHilbert

open scoped ContDiff Real

/-- `f : ℝ ≃ ℝ` is an orientation-preserving (smooth) diffeomorphism of the real line. -/
def IsOrientationPreservingDiffeo (f : ℝ ≃ ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ f.symm ∧ StrictMono f

/-- The wave function transformed by the change of variables `y = f(x)`
(paper, Prop. 24): `(Uψ)(y) = ψ(f⁻¹(y)) · √|d f⁻¹/dy (y)|`. -/
noncomputable def changeOfVariables (f : ℝ ≃ ℝ) (ψ : ℝ → ℂ) (y : ℝ) : ℂ :=
  ψ (f.symm y) * (Real.sqrt |deriv f.symm y| : ℂ)

/-- The error function `erf x = (2/√π) ∫₀ˣ e^{-t²} dt`. -/
noncomputable def erf (x : ℝ) : ℝ :=
  2 / Real.sqrt π * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- The Gaussian wave function `ψ(x) = √(e^{-x²}/√π)` (paper, eq. (27)). -/
noncomputable def gaussianWave (x : ℝ) : ℝ :=
  Real.sqrt (Real.exp (-x ^ 2) / Real.sqrt π)

/-- The wave function `ϕ(y) = 1/√(π(y²+1))` (paper, eq. (28)), whose probability density
is the standard Cauchy (Lorentzian) density. -/
noncomputable def lorentzianWave (y : ℝ) : ℝ :=
  1 / Real.sqrt (π * (y ^ 2 + 1))

/-- The change of variables `y(x) = tan((π/2) erf x)` (paper, eq. (29)). -/
noncomputable def erfTanCoordinate (x : ℝ) : ℝ :=
  Real.tan (π / 2 * erf x)

end UnphysicalHilbert


