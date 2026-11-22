-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
-- name    : LeanPool_FormalLearningTheory_Complexity_Ordinal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:36.176467+00:00
-- url     : https://prove2.me/theorems/102825e0-8306-4ebe-a1d6-45a05121c84c
-- title:
--   Ordinal
-- statement:
--   Definitions and structural lemmas for Ordinal, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Ordinal.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
structure VCLTree (X : Type u) where
  /-- The ordinal value of the combined VC-Littlestone measure -/
  value : Ordinal.{0}
  /-- The concept class this measures -/
  conceptClass : ConceptClass X Bool
noncomputable def OrdinalVCDim (X : Type u) (C : ConceptClass X Bool) : Ordinal :=
  ⨆ (S : Finset X) (_ : Shatters X C S), ((S.card : ℕ) : Ordinal)
noncomputable def OrdinalLittlestoneDim (X : Type u) (C : ConceptClass X Bool) : Ordinal :=
  ⨆ (T : MistakeTree X) (_ : T.isShattered X C), ((T.depth : ℕ) : Ordinal)


