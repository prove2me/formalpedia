-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:09:10.729508+00:00
-- url     : https://prove2.me/theorems/87c286a9-7456-445f-98aa-a91584650c8b
-- title:
--   Type Class
-- statement:
--   Definitions and structural lemmas for Type Class, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
public import Mathlib.GroupTheory.Perm.DomMulAct
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Real
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}
@[expose] def typeClass (a : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  univ.image fun σ : Equiv.Perm (Fin n) ↦ a ∘ σ
end ArithmeticTriangleRemovalInVectorSpaces


