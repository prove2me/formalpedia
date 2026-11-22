-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:32.741489+00:00
-- url     : https://prove2.me/theorems/071029fb-1c1d-4651-84e1-7b7a7dcd29cc
-- title:
--   Tensor Power
-- statement:
--   Definitions and structural lemmas for Tensor Power, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/TensorPower.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SliceRank
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Module
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime] {G ι : Type*} [AddCommGroup G] [Module (ZMod p) G] [Fintype ι]
  {x y z : ι → G}
end ArithmeticTriangleRemovalInVectorSpaces


