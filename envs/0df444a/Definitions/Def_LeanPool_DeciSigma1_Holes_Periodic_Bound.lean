-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
-- name    : LeanPool_DeciSigma1_Holes_Periodic_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:44:24.841805+00:00
-- url     : https://prove2.me/theorems/6d8fd176-da8c-43eb-bb15-62bc8b329f30
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
section
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
def shiftFloor (N : ℕ) (P : Piece W ρ.length) : ℤ :=
  -(((P.len - fixedMargin N ρ.length) / statePeriodModulus N ρ.length : ℕ) : ℤ)
def shiftSystem (W : Fin k → List α) (ρ : List α) (N : ℕ) :
    DifferenceSystem {P // P ∈ piecesOf W ρ} where
  edgeWeight P Q := if FollowerEdge P.val Q.val then
    if P.val.len < Q.val.len + comparisonGap N ρ.length ∧ Q.val.len < P.val.len +
        comparisonGap N ρ.length then
      some 0
    else if P.val.len + comparisonGap N ρ.length ≤ Q.val.len then
      some (-(((Q.val.len - P.val.len - comparisonGap N ρ.length) / statePeriodModulus N ρ.length :
          ℕ) : ℤ))
    else none
  else none
def deletionCounts (z : {P // P ∈ piecesOf W ρ} → ℤ) (P : Piece W ρ.length) : ℕ :=
  if h : P ∈ piecesOf W ρ then (-z ⟨P, h⟩).toNat else 0
variable {N : ℕ} {z : {P // P ∈ piecesOf W ρ} → ℤ}
structure OccurrenceSplit (W : Fin k → List α) (ρ : List α) (h t : ℕ) where
  /-- Pieces charged to the bounded initial part of the occurrence split. -/
  head : Piece W ρ.length → Prop
  head_bound : ∀ c : Finset (Piece W ρ.length), c ⊆ piecesOf W ρ →
    (∀ P ∈ c, head P) → (∀ P ∈ c, ∀ Q ∈ c, FollowerEdge P Q) → c.card ≤ h
  tail_bound : ∀ c : Finset (Piece W ρ.length), c ⊆ piecesOf W ρ →
    (∀ P ∈ c, ¬ head P) → c.card ≤ t
end
end DeciSigma1.Holes.Periodic


