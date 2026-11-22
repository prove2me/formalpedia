-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_DualVC
-- name    : LeanPool_FormalLearningTheory_Complexity_DualVC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:26.10632+00:00
-- url     : https://prove2.me/theorems/e88e2036-08a9-4c00-a71d-80f95dc5c301
-- title:
--   Dual VC
-- statement:
--   Definitions and structural lemmas for Dual VC, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/DualVC.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
universe u
def DualClass (X : Type u) (C : ConceptClass X Bool) : ConceptClass (↥C) Bool :=
  { f | ∃ x : X, ∀ c : ↥C, f c = c.val x }
namespace DualVC
variable {X : Type u} {C : ConceptClass X Bool}
def evalConcept (x : X) : ↥C → Bool := fun c => c.val x
end DualVC


