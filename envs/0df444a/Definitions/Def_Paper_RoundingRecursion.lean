-- Prove2me | Definitions.Def_Paper_RoundingRecursion
-- name    : Paper_RoundingRecursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:52:39.474232+00:00
-- url     : https://prove2.me/theorems/903b26d9-dc6d-45de-adb8-a482e943253a
-- title:
--   Rounding Recursion
-- statement:
--   Definitions and structural lemmas for Rounding Recursion, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingRecursion.lean

import Definitions.Def_Paper_RoundingCutoff
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
end Paper.Hypergraph


