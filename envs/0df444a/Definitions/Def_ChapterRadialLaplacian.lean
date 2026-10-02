-- Prove2me | Definitions.Def_ChapterRadialLaplacian
-- name    : ChapterRadialLaplacian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:25:19.171576+00:00
-- url     : https://prove2.me/theorems/ac20e926-a1b7-4676-ba4f-147ab8169ea8
-- title:
--   Chapter RadialLaplacian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterRadialLaplacian.lean`): generated def bundle for ChapterRadialLaplacian. See BookProof/ChapterRadialLaplacian.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterRadialLaplacian.lean

import Definitions.Def_ChapterSphericalBesselODE
import Mathlib


/-!
# The Laplacian of a radial function, and the `s`-wave form of Note 68

Source: `book.tex`, §A.5, subsection *"Hankel–Majorana Transform"*, **Note 68**
(`book.tex` line ~5860), which asserts for the inverse spherical transform

`−∂⃗² 𝓗_P⁻¹{ψ}(x⃗) = 𝓗_P⁻¹{p²ψ}(x⃗)`.

`BookProof.ChapterSphericalBesselODE` proved the *radial* half of this identity
(the spherical Bessel equation, for every angular momentum `l`).  What was still
missing to state the identity in space, rather than in the radial variable, is
the classical formula for the Laplacian of a radial function.  Mathlib has the
Laplacian `Δ` on a real inner product space but no formula for radial functions,
so this module develops it.

## Contents

* `innerCLM` — the real inner product as a continuous linear map
  `E →L[ℝ] (E →L[ℝ] ℝ)` (Mathlib's `innerSL` is conjugate-linear in its first
  slot, which makes it unusable as the derivative of `y ↦ ⟪y, ·⟫`);
* `laplacian_comp_normSq` — for `G` twice continuously differentiable at `‖x‖²`,
  `Δ (fun y ↦ G ‖y‖²) x = 4‖x‖² G''(‖x‖²) + 2n G'(‖x‖²)`, `n = dim E`;
* `deriv_sqrt_comp` — the one-variable chain rule that converts the squared-norm
  parametrization into the radial one;
* `laplacian_radial` — **the classical formula**: for `x ≠ 0` and `g` twice
  continuously differentiable at `‖x‖`,
  `Δ (fun y ↦ g ‖y‖) x = g''(‖x‖) + ((n−1)/‖x‖) · g'(‖x‖)`;
* `laplacian_sbessel_zero`, `helmholtz_sbessel_zero` — **Note 68 in the `s`-wave
  sector**: on a three-dimensional real inner product space, away from the
  origin, `u(x⃗) = j₀(p‖x⃗‖) = sin(p‖x⃗‖)/(p‖x⃗‖)` satisfies `−∂⃗²u = p²u`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterRadialLaplacian

open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real inner product as a continuous linear map `E →L[ℝ] (E →L[ℝ] ℝ)`.
This is `innerSL` with both slots linear, which is what is needed to
differentiate `y ↦ ⟪y, ·⟫`. -/
noncomputable def innerCLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  (innerₗ E).mkContinuous₂ 1 (fun x y => by simpa using abs_real_inner_le_norm x y)

















/-! ## Note 68 in the `s`-wave sector -/

open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE









end BookProof.ChapterRadialLaplacian


