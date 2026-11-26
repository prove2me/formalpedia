-- Prove2me | Definitions.Def_MurtySimon_Defs
-- name    : MurtySimon_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:48:00.1892+00:00
-- url     : https://prove2.me/theorems/e252df89-0568-5bed-8ca9-121115a903f0
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Juan Pablo Traverso Gianini (jtraverso/murty-simon-conjecture; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Murty-Simon conjecture on diameter-2-critical graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MurtySimon
open SimpleGraph
variable {V : Type*}
def IsDiameterTwoCritical (G : SimpleGraph V) : Prop :=
  G.ediam = 2 ∧ ∀ e ∈ G.edgeSet, 2 < (G.deleteEdges {e}).ediam
def IsEdgeMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v ∈ e, v ∉ f
def IsMaximalEdgeMatching [DecidableEq V] (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsEdgeMatching G M ∧ ∀ e ∈ G.edgeSet, e ∉ M → ¬ IsEdgeMatching G (insert e M)
def DiamLeTwo (G : SimpleGraph V) : Prop :=
  ∀ u v, u ≠ v → G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v
def IsCritical (G : SimpleGraph V) : Prop :=
  DiamLeTwo G ∧ ∀ e ∈ G.edgeSet, ¬ DiamLeTwo (G.deleteEdges {e})
end MurtySimon


