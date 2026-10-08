-- Prove2me | Definitions.Def_ChapterSolidHarmonic
-- name    : ChapterSolidHarmonic
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:51:14.889467+00:00
-- url     : https://prove2.me/theorems/71b777d6-8301-4e7e-ae8c-05894b857445
-- title:
--   Chapter SolidHarmonic
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSolidHarmonic.lean`): generated def bundle for ChapterSolidHarmonic. See BookProof/ChapterSolidHarmonic.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSolidHarmonic.lean

import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterRadialLaplacian
import Mathlib


/-!
# Solid harmonics: `rˡ Y_{lμ}` is harmonic and homogeneous of degree `l`

This module closes the boundary recorded in `BookProof.ChapterBesselHarmonic`:
the identification of the associated Legendre functions / spherical harmonics
`Y_{lμ}` of `book.tex` §A.5 with harmonic functions homogeneous of degree `l`,
for *all* `l` and `μ ≤ l`.

The setting is a three-dimensional real inner product space with an orthonormal
triple `(u, v, e)`; on `ℝ³` this is the standard frame, `⟪u,x⟫ = x¹`,
`⟪v,x⟫ = x²`, `⟪e,x⟫ = x³`.  Write `w(x) = ⟪u,x⟫ + i⟪v,x⟫` (this is
`ρ e^{iφ}` in cylindrical coordinates), `z(x) = ⟪e,x⟫` and `s(x) = ‖x‖²`.

The **solid harmonic** of degree `l` and order `μ` is

`S_{lμ}(x) = Re(w(x)^μ) · ∑ₘ P_l^{(μ)}[l−μ−2m] z(x)^{l−μ−2m} s(x)^m`

(and the same with `Im`), where `P_l^{(μ)}[k]` is the `k`-th coefficient of the
`μ`-th derivative of the Legendre polynomial.  In spherical coordinates this is
exactly `rˡ (sin θ)^μ P_l^{(μ)}(cos θ) cos(μφ)`, i.e. `rˡ Y_{lμ}` up to
normalization (`solidHarmonic_spherical`).

## Contents

* `nullCLM` — the null linear form `w = ⟪u,·⟫ + i⟪v,·⟫`, with
  `sum_nullCLM_sq : ∑ᵢ w(bᵢ)² = 0`;
* `angular_harmonic`, `angular_euler`, `angular_axis` — the angular factor
  `Re(wᵘ)` is harmonic, homogeneous of degree `μ` and constant along the axis;
* `solidHarmonic`, `solidHarmonicIm` — the solid harmonics;
* `solidHarmonic_harmonic`, `solidHarmonic_euler` — **they are harmonic and
  homogeneous of degree `l`**, for every `l` and every `μ ≤ l`;
* `solidHarmonic_spherical` — in spherical coordinates the solid harmonic is
  `rˡ (sin θ)^μ P_l^{(μ)}(cos θ) cos(μ φ)`, the classical `rˡ Y_{lμ}`;
* `assocLegendre` — the associated Legendre function
  `P_l^μ(t) = (1−t²)^{μ/2} P_l^{(μ)}(t)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterSolidHarmonic

open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The null linear form and the angular factor -/

/-- The complex linear form `w = ⟪u,·⟫ + i⟪v,·⟫`. -/
noncomputable def nullCLM (u v : E) : E →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerCLM E u) + Complex.I • (Complex.ofRealCLM.comp (innerCLM E v))

@[simp] theorem nullCLM_apply (u v x : E) :
    nullCLM u v x = (⟪u, x⟫_ℝ : ℂ) + Complex.I * (⟪v, x⟫_ℝ : ℂ) := rfl



/-- The angular factor `A(x) = Re(w(x)^μ)`. -/
noncomputable def angular (u v : E) (μ : ℕ) (x : E) : ℝ := ((nullCLM u v x) ^ μ).re

/-- The angular factor `Im(w(x)^μ)`. -/
noncomputable def angularIm (u v : E) (μ : ℕ) (x : E) : ℝ := ((nullCLM u v x) ^ μ).im





















/-! ## The radial (cylindrical) factor and the solid harmonics -/

/-- The polynomial factor `∑ₘ P_l^{(μ)}[l−μ−2m] ⟪e,x⟫^{l−μ−2m} (‖x‖²)ᵐ`, which is
the homogeneous extension of `P_l^{(μ)}(cos θ)`. -/
noncomputable def radialFactor (e : E) (l μ : ℕ) (x : E) : ℝ :=
  ∑ m ∈ Finset.range ((l - μ) / 2 + 1),
    (derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)
      * ((⟪e, x⟫_ℝ) ^ (l - μ - 2 * m) * (‖x‖ ^ 2) ^ m)

/-- **The solid harmonic** `rˡ Y_{lμ}` (real part convention). -/
noncomputable def solidHarmonic (u v e : E) (l μ : ℕ) (x : E) : ℝ :=
  angular u v μ x * radialFactor e l μ x

/-- **The solid harmonic** `rˡ Y_{lμ}` (imaginary part convention). -/
noncomputable def solidHarmonicIm (u v e : E) (l μ : ℕ) (x : E) : ℝ :=
  angularIm u v μ x * radialFactor e l μ x













/-! ## Homogeneity -/















/-! ## The radial factor is the homogeneous extension of `P_l^{(μ)}(cos θ)` -/



/-! ## Spherical coordinates: the solid harmonic is `rˡ Y_{lμ}` -/

/-- **The associated Legendre function** `P_l^μ(t) = (1−t²)^{μ/2} P_l^{(μ)}(t)`
(without the Condon–Shortley phase `(−1)^μ`). -/
noncomputable def assocLegendre (l μ : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (1 - t ^ 2) ^ μ * (derivative^[μ] (legendre l)).eval t

/-- The point of spherical coordinates `(r, θ, φ)` in the frame `(u, v, e)`. -/
noncomputable def spherePt (u v e : E) (r θ φ : ℝ) : E :=
  (r * Real.sin θ * Real.cos φ) • u + (r * Real.sin θ * Real.sin φ) • v + (r * Real.cos θ) • e

section Frame

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)

include hu hv he huv hue hve











end Frame

end BookProof.ChapterSolidHarmonic


