-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignGauge
-- name    : ChapterFreeFieldBornSignGauge
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:36:13.301865+00:00
-- url     : https://prove2.me/theorems/3c9f3823-d84c-4bd9-8714-85d1806ff29f
-- title:
--   Chapter FreeFieldBornSignGauge
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeFieldBornSignGauge.lean`): generated def bundle for ChapterFreeFieldBornSignGauge. See BookProof/ChapterFreeFieldBornSignGauge.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldBornSignGauge.lean

import Definitions.Def_ChapterA4
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the full coordinate-wise *sign gauge group* of the Born parametrization

Source: `book.tex`, Introduction, section *"Wave-function collapse versus Euler's
formula"* (`book.tex` line ~805): *"the wave-function is nothing else than one
possible parametrization of any probability distribution; the parametrization is
a surjective map from an hypersphere to the set of all possible probability
distributions.  **Two wave-functions are always related by a rotation of the
hypersphere** …"* together with the free-field construction of §5 (`book.tex`
~line 1706).

Wave 144 (`ChapterFreeFieldBornGauge`) recorded a single element of the gauge
redundancy of the Born map `x ↦ (x_k)²`: invariance under the antipodal map
`x ↦ -x` (a *global* sign flip).  In fact the real gauge freedom is much larger:
the Born probabilities `(x_k)²` are unchanged by *any coordinate-wise choice of
signs* `x_k ↦ s_k x_k` with `s_k = ±1`.  This diagonal `{±1}ⁿ` reflection group
preserves the unit sphere (each reflection is an isometry) and acts trivially on
the Born image, so it lies inside every Born fiber; the antipodal map of Wave 144
is the special case `s ≡ -1`.

## Main results

* `signFlip` — the coordinate-wise sign flip `x ↦ (fun k => s_k · x_k)`.
* `signFlip_apply` — its defining coordinate formula.
* `signFlip_norm` — for a `±1` sign vector `s`, `‖signFlip s x‖ = ‖x‖`
  (each reflection is an isometry).
* `signFlip_mem_sphere` — the sign flip preserves the unit sphere.
* **headline** `bornMap_signFlip` — for a `±1` sign vector `s`,
  `bornMap (signFlip s x) = bornMap x`: the Born image is invariant under the
  whole diagonal `{±1}ⁿ` sign group.
* `signFlip_neg_one` — the antipodal map of Wave 144 is the special case
  `s ≡ -1`, recovering `bornMap_neg`.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory

namespace BookProof.ChapterFreeFieldBornSignGauge

variable {n : ℕ}

/-- The **coordinate-wise sign flip** by a sign vector `s : Fin n → ℝ`:
`signFlip s x` has coordinates `s_k · x_k`.  When each `s_k = ±1` this is one of
the `2ⁿ` diagonal reflections generating the real gauge group of the Born map. -/
noncomputable def signFlip (s : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun k => s k * x k)

@[simp] theorem signFlip_apply (s : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    signFlip s x k = s k * x k := rfl









end BookProof.ChapterFreeFieldBornSignGauge


