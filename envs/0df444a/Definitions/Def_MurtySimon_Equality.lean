-- Prove2me | Definitions.Def_MurtySimon_Equality
-- name    : MurtySimon_Equality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:59:43.539553+00:00
-- url     : https://prove2.me/theorems/ae93156d-944c-4e30-bf6f-18fa7e451d6a
-- title:
--   Equality
-- statement:
--   Definitions and structural lemmas for Equality, from Juan Pablo Traverso Gianini (jtraverso/murty-simon-conjecture; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Murty-Simon conjecture on diameter-2-critical graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean

module
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_aux_mono

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable (G) in
/-- The component of `𝓘 = aux G ∅` containing a component of `𝓘' = aux G M`. -/
def emb (M : Finset (Sym2 V)) : (aux G M).ConnectedComponent → (aux G ∅).ConnectedComponent :=
  ConnectedComponent.map (Hom.ofLE (aux_mono (empty_subset M)))
abbrev LC0 (C : (aux G ∅).ConnectedComponent) : Finset (Sym2 V) :=
  (Lt G ∅).filter fun e => (aux G ∅).connectedComponentMk e = C
variable (G) in
/-- `G` is an equality case: `|E(G) \ M| = |non-edges|` for every maximal matching `M`. -/
def EqCase : Prop := ∀ M, IsMaximalEdgeMatching G M → #(Lt G M) = #(Rt G) + #(Nc G)
end
end MurtySimon


