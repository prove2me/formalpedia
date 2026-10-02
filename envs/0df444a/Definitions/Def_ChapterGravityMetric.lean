-- Prove2me | Definitions.Def_ChapterGravityMetric
-- name    : ChapterGravityMetric
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:17:30.993005+00:00
-- url     : https://prove2.me/theorems/69390061-f0ee-4480-be34-fe0ef32b0e56
-- title:
--   Chapter GravityMetric
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGravityMetric.lean`): generated def bundle for ChapterGravityMetric. See BookProof/ChapterGravityMetric.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGravityMetric.lean

import Definitions.Def_ChapterGravityProjector
import Mathlib


/-!
# Chapter — Diffeomorphisms and gravity: the induced spatial metric `h = η + v♭⊗v♭`

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  There, relative to the globally defined **unit
timelike vector** `v` (`vᵘ vᵤ = −1` in the mostly-plus Minkowski metric
`η = diag(−1,1,1,1)`), the author introduces the mixed projector
`χ_a{}^b = δ_a{}^b + v_a v^b` used to split every torsion tensor into its
spatial and temporal parts.  Lowering the free index of `χ` with the metric
produces the associated **`(0,2)` spatial tensor**

`h_{ab} = η_{ab} + v_a v_b`  ( `= η_{ac} χ^c{}_b` ),

the *induced (Riemannian) metric on the spatial hyperplane* `v^⊥`.  This file
records its self-contained linear-algebra properties, continuing the projector
development of `BookProof/ChapterGravityProjector.lean` (whose `metric`, `lower`,
`minkSq`, `spatialProj` are reused).

Formalized here (all under the physical unit-timelike hypothesis
`minkSq v = -1`):

* `spatialMetric v` — the symmetric matrix `h_{ab} = η_{ab} + v_a v_b`;
* `spatialMetric_symm` — `h` is symmetric (`hᵀ = h`);
* `spatialMetric_eq_metric_mul_proj` — the tensor identity `h = η · χ`
  (lowering the free index of the projector `χ`);
* `spatialMetric_mulVec_self` — `h v = 0`: `v` lies in the kernel, so `h`
  degenerates exactly along the time direction;
* `reverse_cauchy_schwarz` — the reverse Cauchy–Schwarz inequality for the
  timelike vector `v`: `⟨x,v⟩_η² ≥ −⟨x,x⟩_η`;
* `spatialMetric_quadForm_nonneg` — **headline**: the quadratic form of `h` is
  nonnegative, `0 ≤ xᵀ h x` for every `x` — i.e. `h` is positive semidefinite,
  a genuine (degenerate) Riemannian metric whose kernel is the time direction;
* `spatialMetric_posSemidef` — the packaged `Matrix.PosSemidef` statement.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterGravityMetric

open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

/-- The induced spatial `(0,2)` metric `h_{ab} = η_{ab} + v_a v_b`, where
`v_a = lower v a` are the lowered components. -/
noncomputable def spatialMetric (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  metric + Matrix.of (fun a b => lower v a * lower v b)

/-
`h` is symmetric.
-/


/-
The tensor identity `h = η · χ`: the spatial metric is the projector `χ`
with its free index lowered by the Minkowski metric.
-/


/-
`h` annihilates the timelike vector `v` (`h v = 0`): the induced metric is
degenerate exactly along the time direction, and is genuinely Riemannian only on
the spatial hyperplane `v^⊥`.
-/


/-
Reverse Cauchy–Schwarz for the unit timelike vector `v`: for every `x`,
`(∑ₐ xᵃ vₐ)² ≥ −(∑ₐ xᵃ xₐ)`, equivalently `⟨x,v⟩_η² ≥ −⟨x,x⟩_η`.  This is the
analytic heart of the positive-semidefiniteness of the induced spatial metric.
-/


/-
**Headline.** The quadratic form of the induced spatial metric is
nonnegative: `0 ≤ xᵀ h x` for all `x`.  Hence `h` is positive semidefinite — a
(degenerate) Riemannian metric, positive definite on the spatial hyperplane
`v^⊥` and vanishing along `v`.
-/


/-
The packaged positive-semidefiniteness of the induced spatial metric.
-/


end BookProof.ChapterGravityMetric


