-- Prove2me | Definitions.Def_ChapterWignerLittleGroupOrbits
-- name    : ChapterWignerLittleGroupOrbits
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:50:31.974458+00:00
-- url     : https://prove2.me/theorems/412037b8-4057-45cc-8e17-d6e9c8aa6a91
-- title:
--   Chapter WignerLittleGroupOrbits
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWignerLittleGroupOrbits.lean`): generated def bundle for ChapterWignerLittleGroupOrbits. See BookProof/ChapterWignerLittleGroupOrbits.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWignerLittleGroupOrbits.lean

import Definitions.Def_ChapterWignerLittleGroup
import Mathlib


/-!
# Wigner's classification: the orbits of `SL(2,ℂ)` on momentum space

`BookProof.ChapterWignerLittleGroup` computes the little groups of the reference momenta and
proves transitivity on the massive future shell and on the future light cone.  Its recorded
boundary was that only the *first* orbit invariant, the Minkowski square `p·p`, is treated
there: "the second invariant, the sign of the energy, is not formalized here".  This file
removes that boundary and completes Wigner's classification of the orbits.

## Results

* `hermOfMom_injective` — a momentum is determined by its Hermitian matrix, and
  `hermOfMom_eq_zero_iff`;
* `hermOfMom_posSemidef` — for a momentum in the closed future cone (`0 ≤ p⁰`,
  `0 ≤ p·p`) the matrix `hermOfMom p` is positive semidefinite.  The proof reduces along
  the boost supplied by the transitivity theorems to the diagonal reference matrices
  `diag(m, m)` and `diag(2, 0)`;
* **`energy_nonneg_of_act`** and **`energy_pos_of_act`** — the sign of the energy is an
  orbit invariant: an `SL(2,ℂ)` transform of a future-pointing momentum with `p·p ≥ 0` is
  future-pointing.  Hence `future_cone_invariant`: the closed future cone, the open future
  cone, the future mass shells and the future light cone are unions of orbits;
* **`orbit_iff_massSq_eq`** — two momenta in the open future cone with `p·p ≥ 0` are in the
  same orbit **iff** they have the same Minkowski square: together with the previous item,
  `p·p` and the sign of `p⁰` are a complete set of invariants for these momenta;
* `littleGroup_zero` — the little group of the zero momentum is all of `SL(2,ℂ)`;
* `littleGroup_spacelike` — the little group of the spacelike reference momentum
  `(0,0,0,1)` is `SU(1,1)`, the stabilizer of the form `diag(1,-1)`, so that the third kind
  of orbit (the tachyonic shells) carries the remaining little group of the classification.

Everything is `sorry`-free and uses only the standard axioms.
-/

open Matrix Complex
open scoped ComplexOrder

namespace BookProof.ChapterWignerLittleGroupOrbits

open BookProof.ChapterWignerLittleGroup

/-! ## The momentum is determined by its matrix -/







/-! ## Positive semidefiniteness in the closed future cone -/





/-! ## Inverting the action -/





/-! ## The sign of the energy is an orbit invariant -/







/-! ## The orbits of the future cone -/



/-! ## The remaining orbits: the origin and the spacelike shells -/



/-- The spacelike reference momentum `(0,0,0,1)`. -/
def spaceMom : Fin 4 → ℝ := ![0, 0, 0, 1]



/-- `SU(1,1)`: the stabilizer in `SL(2,ℂ)` of the indefinite form `diag(1,-1)`. -/
def SU11 : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {A | A.det = 1 ∧ A * !![(1 : ℂ), 0; 0, -1] * Aᴴ = !![(1 : ℂ), 0; 0, -1]}



end BookProof.ChapterWignerLittleGroupOrbits


