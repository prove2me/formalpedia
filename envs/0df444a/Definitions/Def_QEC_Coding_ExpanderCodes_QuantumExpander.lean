-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
-- name    : QEC_Coding_ExpanderCodes_QuantumExpander
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:20:10.093014+00:00
-- url     : https://prove2.me/theorems/609d0076-cc0e-4fdf-a1bd-8e1ab13be1b6
-- title:
--   Quantum Expander
-- statement:
--   Definitions and structural lemmas for Quantum Expander, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
structure BiregularBipartiteGraph (A B : Type u)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] where
  adjacent : A → B → Bool
  leftDegree : Nat
  rightDegree : Nat
  leftNonempty : Nonempty A
  rightNonempty : Nonempty B
  leftDegree_pos : 0 < leftDegree
  rightDegree_pos : 0 < rightDegree
  left_regular : ∀ a,
    (Finset.univ.filter fun b => adjacent a b = true).card = leftDegree
  right_regular : ∀ b,
    (Finset.univ.filter fun a => adjacent a b = true).card = rightDegree
namespace BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
def incidenceMatrix (G : BiregularBipartiteGraph A B) :
    Matrix B A (ZMod 2) :=
  fun b a => if G.adjacent a b = true then 1 else 0
def leftNeighborhood (G : BiregularBipartiteGraph A B)
    (S : Finset A) : Finset B :=
  Finset.univ.filter fun b => ∃ a ∈ S, G.adjacent a b = true
def swap (G : BiregularBipartiteGraph A B) :
    BiregularBipartiteGraph B A where
  adjacent b a := G.adjacent a b
  leftDegree := G.rightDegree
  rightDegree := G.leftDegree
  leftNonempty := G.rightNonempty
  rightNonempty := G.leftNonempty
  leftDegree_pos := G.rightDegree_pos
  rightDegree_pos := G.leftDegree_pos
  left_regular := G.right_regular
  right_regular := G.left_regular
def LeftExpanding (G : BiregularBipartiteGraph A B)
    (γ δ : Real) : Prop :=
  ∀ S : Finset A,
    (S.card : Real) ≤ γ * Fintype.card A →
      (1 - δ) * G.leftDegree * S.card ≤
        (G.leftNeighborhood S).card
def RightExpanding (G : BiregularBipartiteGraph A B)
    (γ δ : Real) : Prop :=
  G.swap.LeftExpanding γ δ
def LeftRightExpanding (G : BiregularBipartiteGraph A B)
    (γA δA γB δB : Real) : Prop :=
  G.LeftExpanding γA δA ∧ G.RightExpanding γB δB
def leftInducedDegree (G : BiregularBipartiteGraph A B)
    (S : Finset A) (b : B) : Nat :=
  (S.filter fun a => G.adjacent a b = true).card
def hypergraphProductData (G : BiregularBipartiteGraph A B) :
    Data (ZMod 2) B A B A :=
  diagonalData G.incidenceMatrix
def extendedNatToENNReal : WithTop Nat → ENNReal :=
  WithTop.map fun n : Nat => (n : NNReal)
end BiregularBipartiteGraph
end QEC.Coding.QuantumExpander


