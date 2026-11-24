-- Prove2me | Definitions.Def_RequestProject_LeafExtMaster
-- name    : RequestProject_LeafExtMaster
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:15:48.3848+00:00
-- url     : https://prove2.me/theorems/c2c49be5-a19f-4cc3-a32c-a73d4f1aafa9
-- title:
--   Leaf Ext Master
-- statement:
--   Definitions and structural lemmas for Leaf Ext Master, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean

import Definitions.Def_RequestProject_PhiFormula
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
def leafEdge (l : Σ i, Fin (m i)) : Sym2 (K ⊕ Σ i, Fin (m i)) := s(.inl l.1, .inr l)
def extEdges (l0 : Σ i, Fin (m i)) (F : Finset (Sym2 K)) :
    Finset (Sym2 (K ⊕ Σ i, Fin (m i))) :=
  (univ.erase l0).image (leafEdge m) ∪ F.map (Function.Embedding.inl.sym2Map)
def blk (l0 : Σ i, Fin (m i)) (C : Finset K) : Finset (K ⊕ Σ i, Fin (m i)) :=
  C.map Function.Embedding.inl ∪
    (univ.filter fun l : Σ i, Fin (m i) => l.1 ∈ C ∧ l ≠ l0).map Function.Embedding.inr
variable {S m}
end ChromaticReconstruction


