-- Prove2me | Definitions.Def_SizeRamsey_Defs
-- name    : SizeRamsey_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:17:14.447286+00:00
-- url     : https://prove2.me/theorems/82a9d94e-8af5-4b70-bcac-84bb737e2978
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Defs.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey
def IsC4Map {V : Type*} (G : SimpleGraph V) (f : Fin 4 → V) : Prop :=
  Function.Injective f ∧
    G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧ G.Adj (f 2) (f 3) ∧ G.Adj (f 3) (f 0)
def HasC4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : Fin 4 → V, IsC4Map G f
def HasMatching4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : Fin 8 → V, Function.Injective f ∧
    G.Adj (f 0) (f 1) ∧ G.Adj (f 2) (f 3) ∧ G.Adj (f 4) (f 5) ∧ G.Adj (f 6) (f 7)
def c4Transversal {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ f : Fin 4 → V, IsC4Map G f → ∃ i : Fin 4, f i ∈ S
noncomputable def tau4 {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, c4Transversal G S ∧ S.card = k}
noncomputable def edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card
def ArrowsMatching4C4 {V : Type*} (F : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph V, R ≤ F → HasMatching4 R ∨ HasC4 (F \ R)
def graphOfEdges {n : ℕ} (es : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ es)
def wheel5 : SimpleGraph (Fin 5) :=
  graphOfEdges {(0,1), (1,2), (2,3), (3,0), (4,0), (4,1), (4,2), (4,3)}
def k33MinusEdge : SimpleGraph (Fin 6) :=
  graphOfEdges {(0,4), (0,5), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5)}
def octahedron : SimpleGraph (Fin 6) :=
  graphOfEdges {(0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4), (1,5),
    (2,4), (2,5), (3,4), (3,5)}
def F17 : SimpleGraph (Fin 12) :=
  graphOfEdges {(0,4), (0,5), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5),
    (6,10), (6,11), (7,9), (7,10), (7,11), (8,9), (8,10), (8,11), (5,6)}
noncomputable def connectedSizeRamsey : ℕ :=
  sInf {m : ℕ | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
    F.Connected ∧ edgeCount F = m ∧ ArrowsMatching4C4 F}
end SizeRamsey


