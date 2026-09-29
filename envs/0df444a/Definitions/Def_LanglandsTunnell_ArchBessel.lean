-- Prove2me | Definitions.Def_LanglandsTunnell_ArchBessel
-- name    : LanglandsTunnell_ArchBessel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/a50f4b82-c6f7-53cd-9da8-67951003eddd
-- title:
--   The archimedean Bessel kernel as an integral
-- statement:
--   For a complex parameter $\nu$ and a real number $x$, `besselKernel` is defined to be the Bochner integral
--   $$\int_{(0,\infty)} e^{-x(t+t^{-1})/2}\,t^{\nu-1}\,dt,$$
--   taken over the set $(0,\infty)$ of reals with respect to the volume measure: the integrand is the real exponential $\exp\bigl(-(x(t+t^{-1})/2)\bigr)$, coerced into $\mathbb{C}$, multiplied by the complex power $(t:\mathbb{C})^{\nu-1}$ of the coercion of $t$ (principal branch, which on positive reals is the usual $t^{\nu-1}$). Both arguments are unrestricted: $x$ ranges over all of $\mathbb{R}$ and $\nu$ over all of $\mathbb{C}$, and since a Bochner integral of a non-integrable function is $0$ by convention, `besselKernel ν x` is defined for every pair $(\nu,x)$, with the integral having its naive meaning exactly when the integrand is integrable on $(0,\infty)$ — which for $x>0$ is the case for every $\nu$. With this normalisation the value is twice the Macdonald function, $\mathrm{besselKernel}(\nu,x)=2K_\nu(x)$ for $x>0$. The module consists of this definition together with `besselKernel_def`, which restates the defining integral formula and is available for rewriting; no convergence, symmetry in $\nu$, or evaluation statement is made here.
--
--   **Relation to Mathlib.** Mathlib has no modified Bessel (Macdonald) function; this is the project's own definition, phrased purely as a Lebesgue integral so that its properties can be derived with Mathlib's integration and Mellin-transform API.
--
--   **Where it is used.** The kernel provides the archimedean local input for the Langlands–Tunnell part of the argument: Whittaker profiles of principal-series type on $\mathrm{GL}_2(\mathbb{R})$, of the shape $y\mapsto |y|^{m}K_\nu(2\pi|y|)$, and the Mellin transforms $\int_0^\infty K_\nu(x)x^{s-1}\,dx$ and $\int_0^\infty K_\mu(x)K_\nu(x)x^{s-1}\,dx$ occurring in archimedean Rankin–Selberg factors, are stated and computed in terms of this integral by real-variable Fubini and Gamma-integral arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ArchBessel.lean

import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.ArchBessel

open MeasureTheory Set

def besselKernel (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))

theorem besselKernel_def (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ), (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1)) :=
  rfl

end LanglandsTunnell.ArchBessel

end


