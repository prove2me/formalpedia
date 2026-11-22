-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Constraints_TopFree_Basic
-- name    : LeanPool_DeciSigma1_Constraints_TopFree_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:40:00.80062+00:00
-- url     : https://prove2.me/theorems/d14dd86b-ff33-430f-a698-2fb4007d191b
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/TopFree/Basic.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Mathlib.Data.Fintype.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Constraints.TopFree
open DeciSigma1.Semantics
variable {n : ℕ}
inductive Lit (n : ℕ) (V : Type*) where
  | le (u v : V)
  | fLe (a : Fin n → V) (u : V)
  | leF (u : V) (a : Fin n → V)
  | eqBot (u : V)
  deriving DecidableEq
def Lit.Holds {V : Type*} (ρ : V → PrefixSet n) : Lit n V → Prop
  | .le u v => ρ u ≤ ρ v
  | .fLe a u => PrefixSet.node (ρ ∘ a) ≤ ρ u
  | .leF u a => ρ u ≤ PrefixSet.node (ρ ∘ a)
  | .eqBot u => ρ u = PrefixSet.bot
def Sat {V : Type*} (ρ : V → PrefixSet n) (Γ : List (Lit n V)) : Prop :=
  ∀ l ∈ Γ, l.Holds ρ
end DeciSigma1.Constraints.TopFree


