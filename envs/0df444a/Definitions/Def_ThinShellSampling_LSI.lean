-- Prove2me | Definitions.Def_ThinShellSampling_LSI
-- name    : ThinShellSampling_LSI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:30.100429+00:00
-- url     : https://prove2.me/theorems/1f560555-190a-426a-b450-a559163c7974
-- title:
--   Logarithmic Sobolev inequality with constant $C$
-- statement:
--   For a probability measure $\pi$ on $\mathbb R^n$ and a nonnegative integrable $g$, the **entropy** is $\mathrm{Ent}_\pi(g)=\int g\log g\,d\pi-\int g\,d\pi\cdot\log\int g\,d\pi\in[0,\infty]$.
--
--   The measure $\pi$ satisfies a **logarithmic Sobolev inequality** (LSI) with constant $C$ if for every locally Lipschitz $f\in L^2(\pi)$,
--
--   $$
--   \mathrm{Ent}_\pi(f^2)\le 2C\int|\nabla f|^2\,d\pi,
--   $$
--
--   where $|\nabla f|(x)=\limsup_{y\to x}|f(y)-f(x)|/\|y-x\|$ is the local slope. The smallest such $C$ is the log-Sobolev constant $C_{\mathsf{LSI}}(\pi)$.
--
--   (LSI) is the hypothesis of the hypercontractivity theorem (Theorem 1.2) and controls the mixing of the proximal sampler (Corollary 1.3).
--
--   **Formalization Note** Both sides are in $[0,\infty]$. The entropy is computed as $\int\big(g\log(g/m)-g+m\big)\,d\pi$ with $m=\int g\,d\pi$, whose integrand is nonnegative, so a non-integrable $g\log g$ gives $+\infty$ and not a junk value. The local slope and $\int|\nabla f|^2d\pi$ are the published `FunctionalInequalities.Energy.LocalSlope.apply` and `.energy`; Mathlib's `fderiv` is not used, because it vanishes at non-differentiable points and the measure need not be absolutely continuous.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.3, display (LSI), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Basic

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **Entropy** `Ent_μ(g) = ∫ g log g dμ − ∫ g dμ · log ∫ g dμ` of a nonnegative function `g`,
valued in `[0, ∞]`.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…), §1.3, display (LSI), p.13 (PDF p.15), with `g = f²`.

**Formalization Note.** With `m = ∫ g dμ`, the value is `∫ (g log(g/m) − g + m) dμ` as a lower
Lebesgue integral. The integrand is pointwise nonnegative (`x ↦ x log(x/m) − x + m` is convex with
minimum `0` at `x = m`), and for a probability measure and integrable `g ≥ 0` with `m > 0` the
integral equals `∫ g log g − m log m` whenever `g log g` is integrable, and `∞` otherwise. If
`m = 0` then `g = 0` a.e. and the value is `0`. This avoids the Bochner-integral junk value `0` of a
non-integrable `g log g`. -/
noncomputable def entropy {E : Type*} [MeasurableSpace E] (μ : Measure E) (g : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (g x * Real.log (g x / ∫ y, g y ∂μ) - g x + ∫ y, g y ∂μ) ∂μ

/-- **Logarithmic Sobolev inequality** (LSI) with constant `C` for a probability measure `ν`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.3, p.13 (PDF p.15): "A
probability measure `π` on `ℝⁿ` is said to satisfy a logarithmic Sobolev inequality with constant `C`
if for any locally Lipschitz function `f ∈ L²(π)`,
`Ent_π(f²) := ∫ f² log f² dπ − ∫ f² dπ · log ∫ f² dπ ≤ 2C ∫ |∇f|² dπ`."

**Formalization Note.** `|∇f|` is the local slope
`|∇f|(x) = limsup_{y→x} |f(y) − f(x)|/‖y − x‖` of the published definition
`FunctionalInequalities.Energy.LocalSlope.apply` (it equals `‖∇f(x)‖` wherever `f` is
differentiable), and `∫ |∇f|² dπ` is the published `FunctionalInequalities.Energy.LocalSlope.energy`.
Mathlib's `fderiv` is not used: it is `0` at non-differentiable points, which on a singular `π` would
shrink the right-hand side. Both sides are in `[0, ∞]`. The paper's `C_LSI(π)` is the least such `C`;
the theorems of this mission are stated for every `C > 0` with `LSI C π`. -/
def LSI {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (C : ℝ) (ν : ProbabilityMeasure E) : Prop :=
  ∀ f : E → ℝ, LocallyLipschitz f → MemLp f 2 (ν : Measure E) →
    entropy (ν : Measure E) (fun x => f x ^ 2) ≤
      ENNReal.ofReal (2 * C) * FunctionalInequalities.Energy.LocalSlope.energy ν f

end ThinShellSampling


