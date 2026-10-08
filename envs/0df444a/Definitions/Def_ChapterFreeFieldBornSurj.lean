-- Prove2me | Definitions.Def_ChapterFreeFieldBornSurj
-- name    : ChapterFreeFieldBornSurj
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T15:09:19.512399+00:00
-- url     : https://prove2.me/theorems/0f4e6c64-72e5-4190-8e52-70dda8f0d18d
-- title:
--   Chapter FreeFieldBornSurj
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeFieldBornSurj.lean`): generated def bundle for ChapterFreeFieldBornSurj. See BookProof/ChapterFreeFieldBornSurj.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldBornSurj.lean

import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterA4
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the Born parametrization of the probability simplex is surjective

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the Introduction's statement (`book.tex` ~line 805) that *"the
wave-function is nothing else than one possible parametrization of any
probability distribution; the parametrization is a surjective map from an
hypersphere to the set of all possible probability distributions"*, together
with the free-field construction of §5 (`book.tex` ~line 1706).

Wave 141 (`ChapterFreeFieldBorn`) introduced the coordinate-wise Born map
`x ↦ (x_k)²` and showed it sends the unit sphere *into* the probability simplex
`stdSimplex ℝ (Fin n)`, hence pushes the Gaussian sphere measure forward to a
genuine probability distribution on the simplex.  This file completes the book's
headline claim by proving the map is **surjective**: every probability
distribution `p` on `Fin n` is the Born image of a wave function on the unit
sphere, namely the coordinate-wise square root `x_k = √(p_k)`.

## Main results

* `bornSection` — the canonical section `p ↦ (fun k => √(p_k))` of the Born map.
* `bornMap_bornSection` — `bornMap (bornSection p) = p` for `p` in the simplex.
* `bornSection_mem_sphere` — `bornSection p` lies on the unit sphere.
* **headline** `bornMap_surjOn_stdSimplex` — the Born map restricted to the unit
  sphere surjects onto the probability simplex `stdSimplex ℝ (Fin n)`; this is
  the book's claim that the hypersphere parametrizes *"the set of all possible
  probability distributions"*.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory

namespace BookProof.ChapterFreeFieldBornSurj

variable {n : ℕ}

/-- The canonical **section** of the Born map: a probability distribution `p` is
realized by the wave function whose coordinates are the square roots
`x_k = √(p_k)`. -/
noncomputable def bornSection (p : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.toLp 2) (fun k => Real.sqrt (p k))



/-
The Born map recovers `p` from its square-root section, on the simplex (where
every coordinate is nonnegative, so `(√ p_k)² = p_k`).
-/


/-
The square-root section of a probability distribution lands on the unit sphere:
`‖bornSection p‖² = ∑ (√ p_k)² = ∑ p_k = 1`.
-/


/-
**Headline.** The Born map restricted to the unit sphere is surjective onto the
probability simplex: every probability distribution `p` on `Fin n` is the Born
image `bornMap x` of a wave function `x` on the unit sphere (namely
`x = bornSection p`).  This is the book's claim that the hypersphere
parametrizes "the set of all possible probability distributions".
-/


end BookProof.ChapterFreeFieldBornSurj


