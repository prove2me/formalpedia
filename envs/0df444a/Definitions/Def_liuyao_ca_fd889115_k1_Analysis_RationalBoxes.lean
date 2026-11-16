-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RationalBoxes
-- name    : liuyao_ca_fd889115_k1_Analysis_RationalBoxes
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:18.566579+00:00
-- url     : https://prove2.me/theorems/768aef59-1f05-4bb7-abfc-c2ab0ea8cc8f
-- title:
--   Computable analysis · RationalBoxes · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RationalBoxes.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-! Rational points and boxes for finite-dimensional quadrature. -/

namespace ComputableAnalysis

/-- A rational point in a fixed finite dimension. -/
abbrev QPoint (dimension : Nat) := Fin dimension → Rat

/-- Closed rational box in a fixed finite dimension. -/
structure RationalBox (dimension : Nat) where
  lower : QPoint dimension
  upper : QPoint dimension
  ordered : ∀ i, lower i ≤ upper i

namespace RationalBox

def Contains {dimension : Nat} (B : RationalBox dimension)
    (x : QPoint dimension) : Prop :=
  ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i

end RationalBox

def origin (dimension : Nat) : QPoint dimension := fun _ => 0

/-- Rational finite sum indexed by `Fin dimension`. -/
def sumRat : (dimension : Nat) → (Fin dimension → Rat) → Rat
  | 0, _ => 0
  | dimension + 1, f =>
      sumRat dimension (fun i => f i.castSucc) + f (Fin.last dimension)

/-- Rational finite product indexed by `Fin dimension`. -/
def productRat : (dimension : Nat) → (Fin dimension → Rat) → Rat
  | 0, _ => 1
  | dimension + 1, f =>
      productRat dimension (fun i => f i.castSucc) * f (Fin.last dimension)

/-- Add a final coordinate to a finite tuple. -/
def appendLast {dimension : Nat} {α : Type} (x : Fin dimension → α)
    (t : α) : Fin (dimension + 1) → α :=
  Fin.lastCases t x

namespace RationalBox

/-- Volume of one cell in the level-`n` dyadic subdivision. -/
def dyadicCellVolume {dimension : Nat} (B : RationalBox dimension)
    (level : Nat) : Rat :=
  productRat dimension fun i =>
    (B.upper i - B.lower i) / ((2 ^ level : Nat) : Rat)

theorem volume_nonneg {dimension : Nat} (B : RationalBox dimension) :
    0 ≤ B.dyadicCellVolume 0 := by
  have nonnegProduct : ∀ n (f : Fin n → Rat),
      (∀ i, 0 ≤ f i) → 0 ≤ productRat n f := by
    intro n
    induction n with
    | zero =>
      intro _ _
      change (0 : Rat) ≤ 1
      decide
    | succ n ih =>
      intro f hf
      exact Rat.mul_nonneg (ih _ (fun i => hf i.castSucc)) (hf (Fin.last n))
  apply nonnegProduct
  intro i
  have h := B.ordered i
  change 0 ≤ (B.upper i - B.lower i) / 1
  grind

end RationalBox

end ComputableAnalysis


