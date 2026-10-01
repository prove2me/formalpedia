-- Prove2me | Definitions.Def_ChapterWeylCauchyRiemann
-- name    : ChapterWeylCauchyRiemann
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:50:25.276354+00:00
-- url     : https://prove2.me/theorems/70e02c83-db4e-47c7-97cc-fd0ef3ef389d
-- title:
--   Chapter WeylCauchyRiemann
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWeylCauchyRiemann.lean`): generated def bundle for ChapterWeylCauchyRiemann. See BookProof/ChapterWeylCauchyRiemann.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWeylCauchyRiemann.lean

import Definitions.Def_ChapterRadialMollifier
import Mathlib


/-!
# Weyl's lemma for the Cauchy–Riemann operator — the *Holomorphic fields* remark

`book.tex`, section *"Holomorphic fields"* (line ~4105), states:

> *"Note that if a complex function of complex variable is locally integrable in
> an open domain, and satisfies the Cauchy–Riemann equations weakly, then the
> function agrees almost everywhere with an analytic function in such open
> domain."*

`BookProof/ChapterHolomorphic.lean` formalizes the classical (pointwise
derivative) core and the Morera form for *continuous* functions, and records the
distributional statement above as its remaining boundary.  This file closes that
boundary.

* `dbar φ z` — the (unnormalized) Cauchy–Riemann operator `∂φ/∂x + i ∂φ/∂y` of a
  real-differentiable function, and `dbarR` for a real-valued function;
* `WeakCauchyRiemannOn f U` — `f` satisfies the Cauchy–Riemann equations *weakly*
  on `U`: `∫ f · ∂̄φ = 0` for every smooth `φ` compactly supported in `U`;
* `weak_cauchyRiemann_ae_eq_analytic` — **the book's statement**: a function
  locally integrable on an open set `U` and weakly Cauchy–Riemann there agrees
  almost everywhere on `U` with a function analytic on `U`;
* `weakCauchyRiemannOn_of_analyticOn` — the converse: a function analytic on `U`
  is weakly Cauchy–Riemann there;
* `weak_cauchyRiemann_iff_ae_eq_analytic` — the two together, as an
  `iff` characterization of the locally integrable weak solutions of `∂̄f = 0`.

The proof is the classical mollification argument.  Convolving (a truncation of)
`f` with any smooth compactly supported kernel produces a smooth function whose
`∂̄` vanishes — the weak equation applied to the reflected kernel — hence a
holomorphic function.  Mathlib's Lebesgue-differentiation theorem for bump
functions (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`)
makes the bump mollifications converge to `f` almost everywhere, while the
*radial* mollifier of `BookProof/ChapterRadialMollifier.lean` reproduces
holomorphic functions exactly (disc mean value property).  Comparing the two
families identifies the almost-everywhere limit with one fixed holomorphic
mollification.
-/

namespace BookProof.WeylCauchyRiemann

open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

/-- The (unnormalized) Cauchy–Riemann operator `∂̄φ = ∂φ/∂x + i ∂φ/∂y`, written
with the real Fréchet derivative of `φ`. A real-differentiable `φ` is complex
differentiable at `z` exactly when `dbar φ z = 0`. -/
def dbar (φ : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I

/-- The Cauchy–Riemann operator applied to a real-valued function. -/
def dbarR (χ : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((fderiv ℝ χ z 1 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ χ z Complex.I : ℝ) : ℂ)

/-- `f` satisfies the Cauchy–Riemann equations **weakly** (in the distributional
sense) on the open set `U`: its pairing with `∂̄φ` vanishes for every smooth test
function `φ` compactly supported inside `U`. -/
def WeakCauchyRiemannOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ z : ℂ, f z * dbar φ z = 0

/-- Mollification: convolution of `F` with a real kernel `χ`. -/
def mollify (F : ℂ → ℂ) (χ : ℂ → ℝ) : ℂ → ℂ := fun z => ∫ w : ℂ, (χ (z - w) : ℂ) * F w



















/-- The bump family used to extract almost-everywhere convergence. -/
def bumpSeq (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / (n + 2)
  rOut := 2 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [div_lt_div_iff_of_pos_right h]
    norm_num




















/-! ## The converse: an analytic function is weakly Cauchy–Riemann

The remaining half of the characterization.  For a smooth compactly supported
`ψ` the integral of `∂̄ψ` over the plane vanishes (Fubini and the fundamental
theorem of calculus in each of the two real directions); applying this to
`ψ = g · φ`, with `g` analytic on `U` and `φ` a test function supported in `U`,
gives the weak Cauchy–Riemann equation for `g`.
-/







































end

end BookProof.WeylCauchyRiemann


