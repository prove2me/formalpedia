-- Prove2me | Definitions.Def_Paper_RoundingComplete
-- name    : Paper_RoundingComplete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:54:08.671589+00:00
-- url     : https://prove2.me/theorems/7d3690c5-4179-4fe0-a32a-d5607c8c29a8
-- title:
--   Rounding Complete
-- statement:
--   Definitions and structural lemmas for Rounding Complete, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingComplete.lean

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
end Paper.Hypergraph


