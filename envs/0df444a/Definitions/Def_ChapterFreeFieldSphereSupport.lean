-- Prove2me | Definitions.Def_ChapterFreeFieldSphereSupport
-- name    : ChapterFreeFieldSphereSupport
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T03:46:44.987282+00:00
-- url     : https://prove2.me/theorems/b44e5835-d963-4158-bae9-b3bd783530f0
-- title:
--   Chapter FreeFieldSphereSupport
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeFieldSphereSupport.lean`): generated def bundle for ChapterFreeFieldSphereSupport. See BookProof/ChapterFreeFieldSphereSupport.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldSphereSupport.lean

import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldGaussian
import Mathlib

/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the Gaussian-built uniform measure really lives on the unit sphere

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"*, section *"5. Free field parametrization in Bayesian inference and
Statistical Mechanics"* (`book.tex` line ~1706):

> "it is well known since many decades that a uniform (Lebesgue-like) measure of
> an infinite-dimensional sphere can be defined using the Gaussian measure and
> the Fock-space."

`ChapterFreeFieldGaussian` proved the standard Gaussian prior is
rotation-invariant, and `ChapterFreeFieldSphere` defined `sphereGaussian`, the
pushforward of that Gaussian under radial normalization `x ↦ ‖x‖⁻¹ • x`, and
proved it too is rotation-invariant.  This file takes the natural **next step**:
it verifies that the constructed measure is *actually a measure on the sphere* —
`sphereGaussian n` gives full mass `1` to the unit sphere (for `n ≥ 1`).  This is
what makes the book's construction a genuine *uniform measure on the sphere*: the
Gaussian has no atom at the origin, so after normalization all the mass lands on
`{x : ‖x‖ = 1}`.

## Main results

* `normalize_mem_sphere` — for `x ≠ 0`, `normalize x` lies on the unit sphere.
* `stdGaussian_singleton` — for `n ≥ 1`, the standard Gaussian is atomless:
  `stdGaussian n {x} = 0`.
* **headline** `sphereGaussian_sphere_eq_one` — for `n ≥ 1`,
  `sphereGaussian n (Metric.sphere 0 1) = 1`: the Gaussian-built uniform measure
  is concentrated on the unit sphere.

Everything is intended to be `sorry`-free and axiom-clean.
-/
namespace BookProof.ChapterFreeFieldSphereSupport

end BookProof.ChapterFreeFieldSphereSupport


