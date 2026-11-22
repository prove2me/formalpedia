-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
-- name    : LeanPool_DeciSigma1_Entailment_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:40:24.759532+00:00
-- url     : https://prove2.me/theorems/56808949-4fab-47c9-abcf-673fe50686cc
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Basic.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_TopFree_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Entailment
def DisjEntailsIn {n k : ℕ} {V : Type} (C : Semantics.PrefixSet n → Prop)
    (Γ : List (Constraints.TopFree.Lit n V)) (q : Fin k → V × V) : Prop :=
  ∀ ρ : V → Semantics.PrefixSet n, (∀ v, C (ρ v)) → Constraints.TopFree.Sat ρ Γ →
    ∃ i, ρ (q i).1 ≤ ρ (q i).2
end DeciSigma1.Entailment


