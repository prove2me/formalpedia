-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mk_mem_vecSumTriples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:19.909658+00:00
-- url     : https://prove2.me/submissions/bd54df17-e97c-409e-adba-a4d0eecb8b2d

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
theorem _root_.solution :
    (a, b, c) ∈ vecSumTriples p A B C ↔ a ∈ A ∧ b ∈ B ∧ c ∈ C ∧ ∀ r, a r + b r + c r = p - 1 := by
  simp [vecSumTriples, and_assoc]
end ArithmeticTriangleRemovalInVectorSpaces
