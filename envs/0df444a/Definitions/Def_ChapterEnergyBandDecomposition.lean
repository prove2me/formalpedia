-- Prove2me | Definitions.Def_ChapterEnergyBandDecomposition
-- name    : ChapterEnergyBandDecomposition
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:49:03.496455+00:00
-- url     : https://prove2.me/theorems/7b16d78a-c536-40b6-8103-c089c1e11a8c
-- title:
--   Chapter EnergyBandDecomposition
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEnergyBandDecomposition.lean`): generated def bundle for ChapterEnergyBandDecomposition. See BookProof/ChapterEnergyBandDecomposition.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEnergyBandDecomposition.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §10 — the
decomposition of a continuous energy spectrum into countably many narrow bands

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"*, §*"10. Ensemble forecasting allows the approximation of a non-linear
infinite-dimensional model by a direct sum of linear models with few variables"*
(line ~2048):

> *"We have to show how to decompose an eventually continuous spectrum of the
> quantum time-evolution into a direct sum of sufficiently small intervals of
> energy, each of these intervals described by few variables.  This is not
> obvious, since any continuous interval, no matter how small, is still
> uncountable."*

This file formalizes the part of that programme which is a theorem: **for every
width `ε > 0` a continuous spectrum splits into *countably many* energy bands of
width `ε`, the bands are mutually orthogonal and exhaust the state space, and on
each band the Hamiltonian — and therefore the time evolution — is within `ε`
(resp. `|t| ε`) of a *scalar*.**  What the manuscript defers to "another article"
is the further statement that each band can be described by *few variables*;
that is not claimed here.

## Model

A Hamiltonian with (possibly continuous) spectrum is realized, as everywhere in
this development, as the multiplication operator by a measurable real "energy"
function `E : X → ℝ` on `L²(X, μ)`, and its unitary group is multiplication by
`exp(−i t E(x))`.  The `k`-th band is `band E ε k = E⁻¹([kε, (k+1)ε))`.

## Deliverables

* `mem_band_iff_floor` — every point lies in exactly one band, the one with
  index `⌊E x / ε⌋`; hence `band_pairwise_disjoint` and `iUnion_band`
  (**countably many bands covering the whole space**);
* `measurableSet_band` — the bands are measurable, so they define orthogonal
  projections on `L²`;
* `lintegral_eq_tsum_band` — **Pythagoras**: the `L²` norm of a state is the sum
  of the norms of its band components, i.e. `L²(X) = ⊕ₖ L²(band k)`;
* `bandPart`, `tsum_bandPart` — the band components of a state reassemble it;
* `energy_sub_scalar_lt` and `norm_mul_energy_sub_scalar_le` — on the `k`-th band
  the Hamiltonian differs from the **scalar** `kε` by less than `ε`;
* `norm_evolution_sub_scalar_le` — on the `k`-th band the time evolution differs
  from the scalar phase `exp(−i t kε)` by at most `|t| ε`;
* `evolution_preserves_band` — the evolution leaves each band invariant.
-/

namespace BookProof.EnergyBandDecomposition

open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

/-- The `k`-th **energy band** of width `ε`: the states whose energy lies in
`[kε, (k+1)ε)`. -/
def band (E : X → ℝ) (ε : ℝ) (k : ℤ) : Set X := E ⁻¹' Set.Ico (k * ε) ((k + 1) * ε)











/-! ## Band components of a state -/

/-- The component of the state `f` in the `k`-th band. -/
noncomputable def bandPart (E : X → ℝ) (ε : ℝ) (k : ℤ) (f : X → ℂ) : X → ℂ :=
  (band E ε k).indicator f









/-! ## The Hamiltonian and its evolution are nearly scalar on each band -/









end BookProof.EnergyBandDecomposition


