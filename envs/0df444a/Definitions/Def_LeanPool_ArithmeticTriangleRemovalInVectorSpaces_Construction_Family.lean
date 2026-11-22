-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Family
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Family
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:33.866068+00:00
-- url     : https://prove2.me/theorems/3b20c96b-9618-4588-b4e5-c45d1e9428b2
-- title:
--   Family
-- statement:
--   Definitions and structural lemmas for Family, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Family.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Behrend
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Hash
public import Mathlib.NumberTheory.Bertrand
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Real
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {n p : ℕ}
def permTriple (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)
  | (a, b, c) => (a ∘ σ, b ∘ σ, c ∘ σ)
variable {a₀ b₀ c₀ : Fin n → ℕ}
end ArithmeticTriangleRemovalInVectorSpaces


