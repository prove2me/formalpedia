-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.card_vecSumTriples_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:47.670803+00:00
-- url     : https://prove2.me/submissions/e20ebdf2-5970-4d20-808d-dede67a47b69

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Hash

set_option autoImplicit true
@[expose] public section
public section
open Finset Matrix
open ArithmeticTriangleRemovalInVectorSpaces
variable {n p P F : ℕ}
variable {A B C : Finset (Fin n → ℕ)} {V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))}
  {S : Finset (ZMod P)} {θ : (Fin n → ZMod P) × ZMod P × ZMod P}
  {v v' : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} {a b c a' b' c' : Fin n → ℕ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution : #(vecSumTriples p A B C) ≤ #A * #B * #C := by
  grw [vecSumTriples, card_filter_le, card_product, card_product, mul_assoc]
end ArithmeticTriangleRemovalInVectorSpaces
