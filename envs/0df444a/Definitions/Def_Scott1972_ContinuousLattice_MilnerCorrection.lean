-- Prove2me | Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
-- name    : Scott1972_ContinuousLattice_MilnerCorrection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:29:23.121427+00:00
-- url     : https://prove2.me/theorems/b6872673-3baf-4c76-a2a8-5d2ea564e905
-- title:
--   Milner Correction
-- statement:
--   Definitions and structural lemmas for Milner Correction, from Lars Warren Ericson (catskillsresearch/scott1972; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Dana Scott's Continuous Lattices (1972): injective T0-spaces, Scott topology, and D_infinity homeomorphism development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/MilnerCorrection.lean

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
set_option autoImplicit true
namespace Scott1972.ContinuousLattice
open Set Topology
variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']
def scottLowerSubbasisSet (y : D) : Set D :=
  { x | ¬ x ≤ y }
def scottPrincipalUpSet (y : D) : Set D :=
  Set.Ici y
def CoarserThanScottTopology (τ : TopologicalSpace D) : Prop :=
  scottTopologicalSpace ≤ τ
end Scott1972.ContinuousLattice


