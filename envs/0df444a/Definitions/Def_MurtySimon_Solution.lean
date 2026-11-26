-- Prove2me | Definitions.Def_MurtySimon_Solution
-- name    : MurtySimon_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:21:04.666155+00:00
-- url     : https://prove2.me/theorems/9e34fac2-512a-4b53-b8f0-80fc19d27347
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/murty-simon-conjecture; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Murty-Simon conjecture on diameter-2-critical graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean

module
public import Definitions.Def_MurtySimon_Main
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}
def IsDiameterTwoCritical (G : SimpleGraph V) : Prop :=
  G.ediam = 2 ∧ ∀ e ∈ G.edgeSet, 2 < (G.deleteEdges {e}).ediam
def IsEdgeMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v ∈ e, v ∉ f
def IsMaximalEdgeMatching [DecidableEq V] (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsEdgeMatching G M ∧ ∀ e ∈ G.edgeSet, e ∉ M → ¬ IsEdgeMatching G (insert e M)
end MurtySimonConjecture


