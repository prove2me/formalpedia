-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
-- name    : LeanPool_FormalLearningTheory_Complexity_GameInfra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:44.802999+00:00
-- url     : https://prove2.me/theorems/d1ff1ef5-dff5-465a-84e1-3e42685e95f5
-- title:
--   Game Infra
-- statement:
--   Definitions and structural lemmas for Game Infra, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
inductive LTree (X : Type) : ℕ → Type where
  | leaf : LTree X 0
  | branch : {n : ℕ} → X → LTree X n → LTree X n → LTree X (n + 1)
def LTree.isShattered {X : Type} {n : ℕ} (C : ConceptClass X Bool) : LTree X n → Prop
  | .leaf => C.Nonempty  -- Path B: was True, now C.Nonempty (Γ₂₁ fix)
  | .branch x l r =>
      (∃ c ∈ C, c x = true) ∧ (∃ c ∈ C, c x = false) ∧
      l.isShattered {c ∈ C | c x = true} ∧
      r.isShattered {c ∈ C | c x = false}
noncomputable def LittlestoneDim (X : Type) (C : ConceptClass X Bool) :
    WithBot (WithTop ℕ) :=
  ⨆ (n : ℕ) (_ : ∃ T : LTree X n, T.isShattered C),
    (↑(↑n : WithTop ℕ) : WithBot (WithTop ℕ))
def versionSpace {X : Type} (C : ConceptClass X Bool) (history : List (X × Bool)) :
    ConceptClass X Bool :=
  {c ∈ C | ∀ p ∈ history, c p.1 = p.2}
noncomputable def SOA (X : Type) (C : ConceptClass X Bool) : OnlineLearner X Bool where
  State := List (X × Bool)
  init := []
  predict := fun history x =>
    let V := versionSpace C history
    if LittlestoneDim X {c ∈ V | c x = true} ≥ LittlestoneDim X {c ∈ V | c x = false}
    then true else false
  update := fun history x y => history ++ [(x, y)]


