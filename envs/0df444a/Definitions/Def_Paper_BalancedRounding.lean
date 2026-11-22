-- Prove2me | Definitions.Def_Paper_BalancedRounding
-- name    : Paper_BalancedRounding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:53:18.166414+00:00
-- url     : https://prove2.me/theorems/9f39c11e-8e3c-4d00-9c31-a2a239f6c900
-- title:
--   Balanced Rounding
-- statement:
--   Definitions and structural lemmas for Balanced Rounding, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/BalancedRounding.lean

import Definitions.Def_Paper_RoundingRecursion
import Definitions.Def_Paper_TwoTerminalRounding
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
end Paper.Hypergraph


