-- Prove2me | Definitions.Def_MurtySimon_Components
-- name    : MurtySimon_Components
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:52:19.017915+00:00
-- url     : https://prove2.me/theorems/4f66d0e9-70fa-5502-ae14-e2ca051e901a
-- title:
--   Components
-- statement:
--   Definitions and structural lemmas for Components, from Juan Pablo Traverso Gianini (jtraverso/murty-simon-conjecture; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Murty-Simon conjecture on diameter-2-critical graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean

module
public import Definitions.Def_MurtySimon_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable (G) in
/-- The critical non-edges: the right side of the auxiliary graph. -/
def Rt : Finset (Sym2 V) := univ.filter (IsCrit G)
variable (G) in
/-- The edges of `G` outside `M`: the left side of the auxiliary graph. -/
def Lt (M : Finset (Sym2 V)) : Finset (Sym2 V) := univ.filter fun e => e ∈ G.edgeSet ∧ e ∉ M
variable (G) in
/-- The number of left vertices of a component. -/
def cA (M : Finset (Sym2 V)) (C : (aux G M).ConnectedComponent) : ℕ :=
  #((Lt G M).filter fun e => (aux G M).connectedComponentMk e = C)
variable (G) in
/-- The number of right vertices of a component. -/
def cB (M : Finset (Sym2 V)) (C : (aux G M).ConnectedComponent) : ℕ :=
  #((Rt G).filter fun f => (aux G M).connectedComponentMk f = C)
end
end MurtySimon


