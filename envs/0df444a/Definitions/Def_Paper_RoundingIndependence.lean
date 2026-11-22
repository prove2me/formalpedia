-- Prove2me | Definitions.Def_Paper_RoundingIndependence
-- name    : Paper_RoundingIndependence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:53:06.179815+00:00
-- url     : https://prove2.me/theorems/a1da971c-cf7b-4a34-a889-d01549f4a4c9
-- title:
--   Rounding Independence
-- statement:
--   Definitions and structural lemmas for Rounding Independence, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
def trimDemand (x : ℕ → ℝ) (ε : ℝ) (v : ℕ) : ℝ :=
  if ε ≤ x v then min (2 * x v) 1 else 0
end Paper.Hypergraph


