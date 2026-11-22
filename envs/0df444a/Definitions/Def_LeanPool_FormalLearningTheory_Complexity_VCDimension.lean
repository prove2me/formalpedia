-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
-- name    : LeanPool_FormalLearningTheory_Complexity_VCDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:50.902804+00:00
-- url     : https://prove2.me/theorems/03c9754b-f8d3-41ad-96d5-d0ef0d98ab10
-- title:
--   VCDimension
-- statement:
--   Definitions and structural lemmas for VCDimension, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/VCDimension.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
def Shatters (X : Type u) (C : ConceptClass X Bool) (S : Finset X) : Prop :=
  ∀ f : S → Bool, ∃ c ∈ C, ∀ x : S, c (x : X) = f x
noncomputable def VCDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ)
noncomputable def GrowthFunction (X : Type u)
    (C : ConceptClass X Bool) : ℕ → ℕ :=
  fun m => sSup (Set.range fun (S : { S : Finset X // S.card = m }) =>
    ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard)
noncomputable def StarNumber (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (S : Finset X)
    (_ : ∀ x ∈ S, ∃ c ∈ C, c x = true ∧ ∀ y ∈ S, y ≠ x → c y = false),
    (S.card : WithTop ℕ)


