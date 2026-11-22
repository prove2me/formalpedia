-- Prove2me | Definitions.Def_Paper_RoundingAveraging
-- name    : Paper_RoundingAveraging
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:52:34.891071+00:00
-- url     : https://prove2.me/theorems/e23e4903-6c9f-4d3c-9d0e-62751b0db6ec
-- title:
--   Rounding Averaging
-- statement:
--   Definitions and structural lemmas for Rounding Averaging, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace Paper.Hypergraph
def levelMeasure : Measure ℝ := volume.restrict (Ioo 0 1)
instance : IsProbabilityMeasure levelMeasure := by
  constructor
  simp [levelMeasure]
def vertexMultiplier (x d : ℕ → ℝ) (v : ℕ) : ℝ → ℝ :=
  (Icc (d v - x v) (d v)).indicator (fun _ => 1 / x v)
def intervalMultiplier (V : Finset ℕ) (hne : V.Nonempty) (x d : ℕ → ℝ) (r : ℝ) : ℝ :=
  V.sup' hne (fun v => vertexMultiplier x d v r)
end Paper.Hypergraph


