-- Prove2me | Definitions.Def_SizeRamsey_Shared
-- name    : SizeRamsey_Shared
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:17:30.49561+00:00
-- url     : https://prove2.me/theorems/d8688177-c4d7-49e2-b9a3-c171a43795b5
-- title:
--   Shared
-- statement:
--   Definitions and structural lemmas for Shared, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Shared.lean

module
public import Definitions.Def_SizeRamsey_Defs
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey.Plan
universe u v
attribute [local instance] Classical.propDecidable
def erase {V : Type u} (G : SimpleGraph V) (D : Finset V) :
    SimpleGraph {v : V // v ∉ D} :=
  G.induce {v | v ∉ D}
def EdgeOnSquare {V : Type u} (G : SimpleGraph V) (a b : V) : Prop :=
  ∃ f : Fin 4 → V, IsC4Map G f ∧ f 0 = a ∧ f 1 = b
def SquareSupported {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b⦄, G.Adj a b → EdgeOnSquare G a b
def Tight {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 * tau4 G = edgeCount G
def Classified {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.cycleGraph 4) ∨
    Nonempty (G ≃g wheel5) ∨
    Nonempty (G ≃g k33MinusEdge) ∨
    Nonempty (G ≃g octahedron)
def SmallerClassified {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    H.Connected → 0 < edgeCount H →
    edgeCount H < edgeCount G → Tight H → Classified H
def PrescribedOptimal {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  ∀ v : V, ∃ S : Finset V,
    v ∈ S ∧ c4Transversal G S ∧ S.card = tau4 G
def compGraph {V : Type u} (G : SimpleGraph V)
    (C : G.ConnectedComponent) : SimpleGraph C.supp :=
  G.induce C.supp
noncomputable instance componentFintype
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    Fintype G.ConnectedComponent :=
  Fintype.ofFinite _
def HitsDeleted {V : Type u} (G : SimpleGraph V)
    (D X : Finset V) : Prop :=
  ∀ f : Fin 4 → V, IsC4Map G f →
    (∃ i, f i ∈ D) → ∃ i, f i ∈ X
noncomputable def liftTransversal {V : Type u}
    (D X : Finset V) (T : Finset {v : V // v ∉ D}) : Finset V :=
  T.image Subtype.val ∪ X
noncomputable def componentVerts {V : Type u} [Fintype V]
    (G : SimpleGraph V) (D : Finset V)
    (C : (erase G D).ConnectedComponent) : Finset V :=
  C.supp.toFinset.image Subtype.val
noncomputable def attachmentEdges {V : Type u} [Fintype V]
    (G : SimpleGraph V) (D : Finset V)
    (C : (erase G D).ConnectedComponent) : Finset (V × V) :=
  ((componentVerts G D C) ×ˢ D).filter
    (fun p => G.Adj p.1 p.2)
end SizeRamsey.Plan


