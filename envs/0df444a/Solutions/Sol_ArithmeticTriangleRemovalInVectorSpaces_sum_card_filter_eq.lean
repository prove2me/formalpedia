-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.sum_card_filter_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:34.295291+00:00
-- url     : https://prove2.me/submissions/2861ac79-bd55-4dca-a933-bd641c4bfb30

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (ha : ∀ r, a r ≤ N) : ∑ k ∈ range (N + 1), #{r | a r = k} = n := by
  rw [← card_eq_sum_card_fiberwise (fun r _ ↦ mem_range.2 (by grind [ha r])), card_univ,
    Fintype.card_fin]
end ArithmeticTriangleRemovalInVectorSpaces
