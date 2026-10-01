-- Prove2me | Definitions.Def_ChapterSphericalBesselODE
-- name    : ChapterSphericalBesselODE
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:10:14.340365+00:00
-- url     : https://prove2.me/theorems/98b994d1-80db-4067-b7e4-b3d3e35f8a00
-- title:
--   Chapter SphericalBesselODE
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSphericalBesselODE.lean`): generated def bundle for ChapterSphericalBesselODE. See BookProof/ChapterSphericalBesselODE.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSphericalBesselODE.lean

import Definitions.Def_ChapterSphericalBessel
import Mathlib


/-!
# Chapter — Hankel–Majorana transform: the spherical Bessel equation for every `l`

Source: `book.tex`, §A.5, subsection *"Hankel–Majorana Transform"* (line ~5805),
Definitions 65–67 and **Note 68**.  The book defines the spherical transform

`𝓗_P{ψ}(p,l,μ) = ∫ r² dr d(cos θ) dφ (2p/√(2π)) jₗ(pr) Y_{lμ}(θ,φ) ψ(r,θ,φ)`

out of the spherical Bessel functions `jₗ` of `BookProof.ChapterSphericalBessel`
(the Rayleigh formula `jₗ(r) = rˡ (−(1/r) d/dr)ˡ (sin r / r)`), and states in
**Note 68** that, "due to the properties of the spherical harmonics and Bessel
functions", the inverse transform intertwines the Laplacian with multiplication
by `p²`:

`−∂⃗² 𝓗_P⁻¹{ψ} = 𝓗_P⁻¹{p² ψ}`.

The analytic heart of that statement — the only part of it that concerns the
Bessel functions themselves — is that `jₗ` solves the **spherical Bessel
equation**, equivalently that `r ↦ jₗ(p r)` is an eigenfunction, with eigenvalue
`p²`, of the radial part of `−∂⃗²` in the sector of angular momentum `l`.
`BookProof.ChapterSphericalBessel` proved this for `l = 0` only.  This module
proves it for **every** `l`, directly from the Rayleigh formula.

## Contents

* `gIter l` — the `l`-th Rayleigh iterate `(−(1/r) d/dr)ˡ (sin r / r)`, so that
  `jₗ(r) = rˡ · gIter l r`;
* `contDiffOn_gIter`, `diffAt_gIter`, `diffAt_deriv_gIter` — every iterate is
  smooth away from the origin (proved by induction, and needed to differentiate
  the iterates at all);
* `deriv_gIter_eq` — the Rayleigh step `gₗ'(r) = −r · gₗ₊₁(r)`;
* `gIter_ode` — the equation satisfied by the iterates:
  `r gₗ'' + (2l+2) gₗ' + r gₗ = 0`, proved by induction on `l`;
* `gIter_pred_eq` — the companion first-order identity
  `gₗ = (2l+3) gₗ₊₁ + r gₗ₊₁'`;
* `sbessel_ode` — **the spherical Bessel equation**
  `r² jₗ'' + 2 r jₗ' + (r² − l(l+1)) jₗ = 0` for every `l`;
* `sbessel_rayleigh_raise` — the Rayleigh raising relation
  `jₗ₊₁(r) = −rˡ · d/dr (jₗ(r)/rˡ)`;
* `sbessel_recurrence` — the three-term recurrence
  `jₗ₋₁(r) + jₗ₊₁(r) = ((2l+1)/r) jₗ(r)`;
* `sbessel_radial_eigen` — **Note 68 in the radial sector**: for `p > 0` the
  function `u(r) = jₗ(p r)` satisfies
  `−(u''(r) + (2/r) u'(r) − (l(l+1)/r²) u(r)) = p² u(r)`,
  i.e. it is an eigenfunction of the radial Laplacian with angular momentum `l`
  and eigenvalue `p²`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis.
-/

namespace BookProof.ChapterSphericalBesselODE

open BookProof.ChapterSphericalBessel

/-- The `l`-th Rayleigh iterate `gₗ = (−(1/r) d/dr)ˡ (sin r / r)`; the spherical
Bessel function is `jₗ(r) = rˡ gₗ(r)`. -/
noncomputable def gIter (l : ℕ) : ℝ → ℝ := rayleighOp^[l] sbesselBase



/-! ## Smoothness of the Rayleigh iterates away from the origin -/









/-! ## The Rayleigh step and the equation satisfied by the iterates -/
















/-! ## The spherical Bessel equation -/









/-! ## The three-term recurrence -/



/-! ## Note 68 in the radial sector -/









end BookProof.ChapterSphericalBesselODE


