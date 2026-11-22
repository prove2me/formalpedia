-- Prove2me | Definitions.Def_Paper_RoundingGeometry
-- name    : Paper_RoundingGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:50:28.638734+00:00
-- url     : https://prove2.me/theorems/cb2fdc92-9fe0-407e-857b-41c9dd5468a4
-- title:
--   Rounding Geometry
-- statement:
--   Definitions and structural lemmas for Rounding Geometry, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean

import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
def annulusPotential (a b q d : ℝ) : ℝ := min (b - a - q) (max 0 (d - a))
def FractionalSeparator (H : Hypergraph) (A B : Finset ℕ) (x : ℕ → ℝ) : Prop :=
  H.UnitDemand x ∧ ∀ u ∈ A, ∀ v ∈ B, 1 ≤ H.vertexDistance x u v
end Paper.Hypergraph


