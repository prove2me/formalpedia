-- Prove2me | Definitions.Def_Scott1972_ContinuousLattice_Specialization
-- name    : Scott1972_ContinuousLattice_Specialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:28:58.068431+00:00
-- url     : https://prove2.me/theorems/250d61a8-8d18-4aae-bc98-d1b9a014e0e2
-- title:
--   Specialization
-- statement:
--   Definitions and structural lemmas for Specialization, from Lars Warren Ericson (catskillsresearch/scott1972; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Dana Scott's Continuous Lattices (1972): injective T0-spaces, Scott topology, and D_infinity homeomorphism development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean

import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans

set_option autoImplicit true
namespace Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]
def SpecializationLe (x y : X) : Prop :=
  ∀ U, IsOpen U → x ∈ U → y ∈ U
instance specializationPreorder : Preorder X where
  le := SpecializationLe
  le_refl x := fun _ _ hx => hx
  le_trans x y z hxy hyz U hU hxU := hyz U hU (hxy U hU hxU)
@[reducible] noncomputable def scottTopologicalSpace : TopologicalSpace D :=
  Topology.scott D univ
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
def IsMonotoneNet (x : ι → D) : Prop :=
  Monotone x
def ScottConvergesTo (x : ι → D) (y : D) : Prop :=
  ∀ U, ScottOpen U → y ∈ U → ∃ i, ∀ j ≥ i, x j ∈ U
variable {x : ι → D} {L y : D}
end Scott1972.ContinuousLattice


