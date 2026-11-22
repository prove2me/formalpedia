-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
-- name    : LeanPool_FormalLearningTheory_Complexity_Littlestone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:18.03947+00:00
-- url     : https://prove2.me/theorems/1531b826-5163-4b80-96c2-f36178cdc61b
-- title:
--   Littlestone
-- statement:
--   Definitions and structural lemmas for Littlestone, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Littlestone.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
inductive MistakeTree (X : Type u) where
  | leaf : MistakeTree X
  | branch : X → MistakeTree X → MistakeTree X → MistakeTree X
def MistakeTree.depth {X : Type u} : MistakeTree X → ℕ
  | .leaf => 0
  | .branch _ l r => 1 + max l.depth r.depth
def MistakeTree.isShattered (X : Type u) (C : ConceptClass X Bool) :
    MistakeTree X → Prop
  | .leaf => True
  | .branch x l r =>
      (∃ c ∈ C, c x = true ∧ MistakeTree.isShattered X C l) ∧
      (∃ c ∈ C, c x = false ∧ MistakeTree.isShattered X C r)
noncomputable def BranchWiseLittlestoneDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (T : MistakeTree X) (_ : T.isShattered X C), (T.depth : WithTop ℕ)
def MistakeTree.fromList {X : Type u} : List X → MistakeTree X
  | [] => .leaf
  | x :: xs => .branch x (fromList xs) (fromList xs)


