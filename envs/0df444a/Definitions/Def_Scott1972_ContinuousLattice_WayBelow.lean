-- Prove2me | Definitions.Def_Scott1972_ContinuousLattice_WayBelow
-- name    : Scott1972_ContinuousLattice_WayBelow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:27:47.131284+00:00
-- url     : https://prove2.me/theorems/92e5032b-20fb-5d3e-a992-6ee3dcaf7065
-- title:
--   Way Below
-- statement:
--   Definitions and structural lemmas for Way Below, from Lars Warren Ericson (catskillsresearch/scott1972; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Dana Scott's Continuous Lattices (1972): injective T0-spaces, Scott topology, and D_infinity homeomorphism development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
set_option autoImplicit true
namespace Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
def ScottOpen (U : Set D) : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : SupSet D :=
    (CompleteLattice.toCompleteSemilatticeSup (α := D)).toSupSet
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty
def WayBelow (x y : D) : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : Preorder D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x
@[inherit_doc] scoped infix:50 " ≪ " => WayBelow
def IsContinuousLattice (D : Type u) [CompleteLattice D] : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  ∀ y : D, IsLUB {x | x ≪ y} y
end Scott1972.ContinuousLattice


