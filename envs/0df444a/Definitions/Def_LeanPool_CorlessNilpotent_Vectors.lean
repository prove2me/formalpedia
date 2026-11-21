-- Prove2me | Definitions.Def_LeanPool_CorlessNilpotent_Vectors
-- name    : LeanPool_CorlessNilpotent_Vectors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:41:41.403027+00:00
-- url     : https://prove2.me/theorems/eb2efc50-a101-4ed7-9c0e-50cdab70f344
-- title:
--   Vectors
-- statement:
--   Definitions and structural lemmas for Vectors, from Marcel Blattner; maintained by LeanPool contributors's pinned Corless's nilpotent Bohemian matrix conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Polynomial
namespace Corless
def foldVector {α : Type*} (u : List α) (a b : α) : List α := u ++ [a, b] ++ u.reverse
inductive CorlessVec : ℕ → List ℂ → Prop
  | base : CorlessVec 0 []
  | step₁ {k : ℕ} {u : List ℂ} :
      CorlessVec k u → CorlessVec (k + 1) (foldVector u 1 Complex.I)
  | step₂ {k : ℕ} {u : List ℂ} :
      CorlessVec k u → CorlessVec (k + 1) (foldVector u Complex.I 1)
noncomputable def sgns (u : List ℂ) : ℕ → ℤ := fun i => entrySign (u.getD i 1)
open Classical in
/-- Corless's vectors with parameter `k`, as a finite set. -/
noncomputable def vecs : ℕ → Finset (List ℂ)
  | 0 => {[]}
  | k + 1 => (vecs k).biUnion fun u =>
      {foldVector u 1 Complex.I, foldVector u Complex.I 1}
end Corless


