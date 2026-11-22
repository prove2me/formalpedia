-- Prove2me | Definitions.Def_Paper_RoundingDegeneracy
-- name    : Paper_RoundingDegeneracy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:53:03.511485+00:00
-- url     : https://prove2.me/theorems/bb2d41d3-979d-4e23-aa41-a21e00b13bb2
-- title:
--   Rounding Degeneracy
-- statement:
--   Definitions and structural lemmas for Rounding Degeneracy, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean

import Definitions.Def_Paper_RoundingAveraging
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
def degeneracyLevelCover (H : Hypergraph) (rank : ℕ ⊕ ℕ → ℕ) (x d y q : ℕ → ℝ)
    (e : ℕ) (r : ℝ) : ℝ :=
  (∑ v ∈ (H.edge e).filter (fun v => rank (.inr e) < rank (.inl v)),
    2 * y e * vertexMultiplier x d v r) +
  (Set.Icc (q e - 2 * H.degeneracy * y e) (q e + 2 * H.degeneracy * y e)).indicator (fun _ => 1) r
end Paper.Hypergraph


