-- Prove2me | Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
-- name    : Scott1972_ContinuousLattice_ScottMaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:29:13.25255+00:00
-- url     : https://prove2.me/theorems/9fe311da-6f33-4ed2-980f-210503c15c7e
-- title:
--   Scott Maps
-- statement:
--   Definitions and structural lemmas for Scott Maps, from Lars Warren Ericson (catskillsresearch/scott1972; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Dana Scott's Continuous Lattices (1972): injective T0-spaces, Scott topology, and D_infinity homeomorphism development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
set_option autoImplicit true
namespace Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
def PreservesDirectedSup (f : D → D') : Prop :=
  ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → f (sSup S) = sSup (f '' S)
end Scott1972.ContinuousLattice


