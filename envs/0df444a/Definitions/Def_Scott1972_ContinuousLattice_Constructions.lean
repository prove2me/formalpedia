-- Prove2me | Definitions.Def_Scott1972_ContinuousLattice_Constructions
-- name    : Scott1972_ContinuousLattice_Constructions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:29:52.014384+00:00
-- url     : https://prove2.me/theorems/069bac34-2e8b-48b9-9a96-ec250bd013f2
-- title:
--   Constructions
-- statement:
--   Definitions and structural lemmas for Constructions, from Lars Warren Ericson (catskillsresearch/scott1972; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Dana Scott's Continuous Lattices (1972): injective T0-spaces, Scott topology, and D_infinity homeomorphism development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
set_option autoImplicit true
namespace Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
section InjectiveExtension
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]
def scottExtend (e : X → Y) (f : X → E) (y : Y) : E :=
  sSup {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))}
end InjectiveExtension
end Scott1972.ContinuousLattice


