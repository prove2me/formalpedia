-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Hash
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Hash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:47.028171+00:00
-- url     : https://prove2.me/theorems/92079684-f6c3-489c-a0e3-a84b7cb09cba
-- title:
--   Hash
-- statement:
--   Definitions and structural lemmas for Hash, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Hash.lean

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
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Matrix
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {n p P F : ℕ}
def vecSumTriples (p : ℕ) (A B C : Finset (Fin n → ℕ)) :
    Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :=
  (A ×ˢ B ×ˢ C).filter fun (a, b, c) ↦ ∀ r, a r + b r + c r = p - 1
def Shares :
    (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → Prop
  | (a, b, c), (a', b', c') => a = a' ∨ b = b' ∨ c = c'
instance : DecidableRel (Shares (n := n)) :=
  fun (a, b, c) (a', b', c') ↦ inferInstanceAs (Decidable (a = a' ∨ b = b' ∨ c = c'))
def hashedTriples (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)))
    (S : Finset (ZMod P)) :
    (Fin n → ZMod P) × ZMod P × ZMod P → Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))
  | (h, α, β) => V.filter fun (a, _, c) ↦ β + h ⬝ᵥ (fun r ↦ (a r : ZMod P)) ∈ S ∧
      α + h ⬝ᵥ (fun r ↦ (c r : ZMod P)) = β + h ⬝ᵥ (fun r ↦ (a r : ZMod P))
def isolatedTriples (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)))
    (S : Finset (ZMod P)) (θ : (Fin n → ZMod P) × ZMod P × ZMod P) :
    Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :=
  {v ∈ hashedTriples V S θ | ∀ v' ∈ hashedTriples V S θ, Shares v v' → v' = v}
def sharingPairs (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))) :
    Finset (((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) ×
      ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))) :=
  (V ×ˢ V).filter fun (v, v') ↦ v ≠ v' ∧ Shares v v'
variable {A B C : Finset (Fin n → ℕ)} {V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))}
  {S : Finset (ZMod P)} {θ : (Fin n → ZMod P) × ZMod P × ZMod P}
  {v v' : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} {a b c a' b' c' : Fin n → ℕ}
end ArithmeticTriangleRemovalInVectorSpaces


