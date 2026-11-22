-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Basic
-- name    : LeanPool_DeciSigma1_Full_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:38:15.549142+00:00
-- url     : https://prove2.me/theorems/68df65da-1bfd-4da0-9fb3-3f2d54a101b5
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Basic.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Full
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n k : Nat} {V : Type}
def seed (q : V × V) (m : Bool) (w : List (Fin n)) : Closure.Config n V :=
  (if m then q.2 else q.1, m, w)
def exclusion (q : V × V) (m : Bool) (w : List (Fin n)) : Closure.Config n V :=
  (if m then q.1 else q.2, m, w)
def HasCountermodelIn (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) (q : Fin k → V × V) : Prop :=
  ∃ ρ, (∀ v, C (ρ v)) ∧ SatT c ρ Γ ∧
    ∀ i, ¬ Tree.Le c (ρ (q i).1) (ρ (q i).2)
def DisjEntailsIn (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) (q : Fin k → V × V) : Prop :=
  ∀ ρ, (∀ v, C (ρ v)) → SatT c ρ Γ →
    ∃ i, Tree.Le c (ρ (q i).1) (ρ (q i).2)
end DeciSigma1.Full


