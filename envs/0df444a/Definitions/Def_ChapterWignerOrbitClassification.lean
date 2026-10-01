-- Prove2me | Definitions.Def_ChapterWignerOrbitClassification
-- name    : ChapterWignerOrbitClassification
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:17:35.927439+00:00
-- url     : https://prove2.me/theorems/355445ab-80f6-486a-9416-5fcd489fcba1
-- title:
--   Chapter WignerOrbitClassification
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWignerOrbitClassification.lean`): generated def bundle for ChapterWignerOrbitClassification. See BookProof/ChapterWignerOrbitClassification.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWignerOrbitClassification.lean

import Definitions.Def_ChapterWignerLittleGroupOrbits
import Mathlib


/-!
# Wigner's orbit classification, completed: the spacelike shells and the full list

`BookProof.ChapterWignerLittleGroupOrbits` classified the orbits of `SL(2,ℂ)` on momentum
space *inside the closed future cone* (mass shells, future light cone, origin) and computed
the little group of the spacelike reference momentum `(0,0,0,1)`; transitivity on the
spacelike shells was left open.  This file removes that boundary.

## Results

* `exists_boost_spacelike` — **every** momentum `p` with `p·p = -m² < 0` is obtained from
  the spacelike reference momentum `(0,0,0,m)` by an explicit element of `SL(2,ℂ)`.  The
  element is written down in closed form in the three cases `p⁰+p³ > 0`, `p⁰+p³ < 0` and
  `p⁰+p³ = 0`: it is the Gauss (`LDLᴴ`) factorization of the Hermitian matrix `hermOfMom p`,
  whose determinant `-m²` is negative, followed by a real diagonal rescaling and, in the
  last case, by a square root of a phase;
* `sameOrbit_spacelike` — consequently each spacelike shell `{p | p·p = -m²}` is a **single**
  orbit, and `littleGroup_spacelike_conj_SU11` transports the little group `SU(1,1)` of
  `BookProof.ChapterWignerLittleGroupOrbits` to every one of its points;
* `orbit_classification` — the complete list of the orbits: two momenta lie in the same
  orbit iff their Minkowski squares agree and, when that square is nonnegative, they are
  either both zero, or both of positive energy, or both of negative energy.  So the orbits
  are exactly: the spacelike shells (one for each `m > 0`), the two mass shells for each
  `m > 0`, the two halves of the light cone, and the origin.

Everything is `sorry`-free and uses only the standard axioms.
-/

open Matrix Complex

namespace BookProof.ChapterWignerOrbitClassification

open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

/-- The Minkowski square `p·p` of a 4-momentum. -/
def minkSq (p : Fin 4 → ℝ) : ℝ := p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2

/-- Two momenta lie in the same `SL(2,ℂ)` orbit. -/
def SameOrbit (p q : Fin 4 → ℝ) : Prop :=
  ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom p) = hermOfMom q









/-! ## The spacelike reference momentum -/

/-- The spacelike reference momentum `(0,0,0,m)`. -/
def spaceRefMom (m : ℝ) : Fin 4 → ℝ := ![0, 0, 0, m]





/-! ## Transitivity on the spacelike shells

The three cases of the Gauss factorization of `hermOfMom p`. -/













/-! ## The complete list of the orbits -/

/-- The momentum with all components negated. -/
def negMom (p : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => -p i















end BookProof.ChapterWignerOrbitClassification


