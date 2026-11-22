-- Prove2me | Definitions.Def_Paper_RoundingPaths
-- name    : Paper_RoundingPaths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:50:45.895992+00:00
-- url     : https://prove2.me/theorems/0221a241-dcb9-4fb4-83b4-8e7ba5955ee7
-- title:
--   Rounding Paths
-- statement:
--   Definitions and structural lemmas for Rounding Paths, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
end Paper.Hypergraph


