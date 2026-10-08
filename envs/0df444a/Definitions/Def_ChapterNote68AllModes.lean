-- Prove2me | Definitions.Def_ChapterNote68AllModes
-- name    : ChapterNote68AllModes
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T05:50:51.056916+00:00
-- url     : https://prove2.me/theorems/e5d6bb60-493b-4b0a-9c85-1de9434daf58
-- title:
--   ChapterNote68AllModes
-- statement:
--   ChapterNote68AllModes

import Definitions.Def_ChapterBesselHarmonic
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterSphericalBessel
import Mathlib


/-!
# Note 68 for every angular-momentum mode `(l, μ)`

`BookProof.ChapterBesselHarmonic` proved Note 68 of `book.tex` §A.5 —
`−∂⃗² (jₗ(p r)/rˡ · H) = p² (jₗ(p r)/rˡ · H)` — for an *arbitrary* harmonic
function `H` homogeneous of degree `l`, but only realized it concretely for
`l ≤ 1` (a linear functional).  `BookProof.ChapterSolidHarmonic` now supplies
those `H` for every `l` and every order `μ ≤ l`: the solid harmonics
`rˡ Y_{lμ}(θ, φ)` built from the associated Legendre functions.  Putting the two
together closes the boundary recorded in those modules.

## Contents

* `helmholtz_sbessel_solidHarmonic` — **Note 68 in the mode `(l, μ)`**: on a
  three-dimensional real inner product space with an orthonormal frame
  `(u, v, e)`,
  `−∂⃗² (jₗ(p‖x⃗‖)/‖x⃗‖ˡ · rˡY_{lμ}(x⃗)) = p² · (jₗ(p‖x⃗‖)/‖x⃗‖ˡ · rˡY_{lμ}(x⃗))`,
  and the same for the `Im` (i.e. `sin μφ`) partner;
* `euclidean_frame_*` — the standard frame of `ℝ³` is such a frame, so
* `helmholtz_sbessel_solidHarmonic_euclidean` — the concrete statement on
  `EuclideanSpace ℝ (Fin 3)`;
* `solidHarmonic_spherical_euclidean` — and there the mode is literally
  `rˡ P_l^μ(cos θ) cos(μφ)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterNote68AllModes

open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterSphericalBessel BookProof.ChapterBesselHarmonic
open BookProof.ChapterSolidHarmonic
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]





/-! ## The standard frame of `ℝ³` -/

/-- The `i`-th standard basis vector of `ℝ³`. -/
noncomputable def stdVec (i : Fin 3) : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single i 1











end BookProof.ChapterNote68AllModes


