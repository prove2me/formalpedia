-- Prove2me | Definitions.Def_Scott1972_ContinuousLattice_Injective
-- name    : Scott1972_ContinuousLattice_Injective
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:27:46.669777+00:00
-- url     : https://prove2.me/theorems/3867a8f3-1385-4240-b499-89e6b8809167
-- title:
--   Injective
-- statement:
--   Definitions and structural lemmas for Injective, from Lars Warren Ericson (catskillsresearch/scott1972; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Dana Scott's Continuous Lattices (1972): injective T0-spaces, Scott topology, and D_infinity homeomorphism development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
set_option autoImplicit true
abbrev Sierpinski := Prop
open Topology TopologicalSpace
universe u v w
def IsInjectiveSpace (D : Type v) [TopologicalSpace D] : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y),
    IsEmbedding e → ∀ f : C(X, D), ∃ g : C(Y, D), ∀ x, g (e x) = f x
structure IsRetractSubspace (D' D : Type u) [TopologicalSpace D'] [TopologicalSpace D] where
  «section'» : C(D', D)
  isEmbedding_section : IsEmbedding section'
  retraction : C(D, D')
  retraction_section : ∀ d, retraction (section' d) = d


