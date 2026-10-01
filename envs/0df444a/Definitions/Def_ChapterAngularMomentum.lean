-- Prove2me | Definitions.Def_ChapterAngularMomentum
-- name    : ChapterAngularMomentum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:21:45.818884+00:00
-- url     : https://prove2.me/theorems/517e850e-9c3a-4035-9086-10268dbc0d75
-- title:
--   Chapter AngularMomentum
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAngularMomentum.lean`): generated def bundle for ChapterAngularMomentum. See BookProof/ChapterAngularMomentum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAngularMomentum.lean

import Mathlib


/-!
# Note 68, the angular half: the generator of rotations and the eigenvalue `μ`

Source: `book.tex`, §A.5, subsection *"Hankel–Majorana Transform"*, **Note 68**
(`book.tex` line ~5860).  Besides the Laplacian identity (the radial half, proved
in `BookProof.ChapterSphericalBesselODE` and `BookProof.ChapterRadialLaplacian`),
Note 68 states that the inverse spherical transform intertwines the third
component of the angular momentum with multiplication by `μ`:

`(−x¹ i ∂₂ + x² i ∂₁) 𝓗_P⁻¹{ψ}(x⃗) = 𝓗_P⁻¹{R'ψ}(x⃗)`,  `R'ψ(p,l,μ) = μ ψ(p,l,μ)`.

The self-contained mathematical content is that the differential operator
`L₃ = −i(x¹∂₂ − x²∂₁)` — the generator of rotations in the `1`–`2` plane —
has eigenvalue `μ` exactly on the functions that transform with the phase
`e^{iμt}` under those rotations, which is precisely the `e^{iμφ}` factor of the
spherical harmonic `Y_{lμ}`.  The plane of the rotation is identified with `ℂ`,
so that the rotation by the angle `t` is multiplication by `e^{it}` and the
generating vector field at `z` is `i z`.

## Contents

* `fderiv_rotationVector` — the rotation vector field in Cartesian form:
  `Du(z)(i z) = x¹ ∂₂u(z) − x² ∂₁u(z)` (pure `ℝ`-linearity);
* `angularMomentum_eigen` — **the eigenvalue statement**: if `u` is real
  differentiable at `z` and `u(e^{it} z) = e^{iμt} u(z)` for every `t`, then
  `−i (x¹ ∂₂u(z) − x² ∂₁u(z)) = μ u(z)`;
* `circHarm` — the circular harmonic `(z/‖z‖)^μ`, the `e^{iμφ}` factor of
  `Y_{lμ}`; `circHarm_rotate` is its equivariance and
  `circHarm_angularMomentum_eigen` the resulting eigenvalue equation, so the
  hypothesis of `angularMomentum_eigen` is not vacuous;
* `circHarm_abs` — the circular harmonic has modulus one away from the origin.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterAngularMomentum

open Complex





/-! ## The circular harmonic `e^{iμφ} = (z/‖z‖)^μ` -/

/-- The circular harmonic of order `μ`: the `e^{iμφ}` factor of the spherical
harmonic `Y_{lμ}`, written as `(z/‖z‖)^μ` in the plane of the rotation. -/
noncomputable def circHarm (μ : ℕ) (z : ℂ) : ℂ := (z / (‖z‖ : ℂ)) ^ μ









end BookProof.ChapterAngularMomentum


