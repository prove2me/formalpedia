-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:09:02.857852+00:00
-- url     : https://prove2.me/theorems/e7ea6914-aa07-487b-bf13-336fe22f31a0
-- title:
--   Peeling
-- statement:
--   Definitions and structural lemmas for Peeling, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
@[expose] def IsDecreasingOn (N : ℕ) (π : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ π k) ∧ Antitone π ∧ π (N + 1) = 0
@[expose] def mass (N : ℕ) (π : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), π k
@[expose] def moment (N : ℕ) (π : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), k * π k
@[expose] def DecreasingCompatible (N : ℕ) : Prop :=
  ∀ π₁ π₂ π₃ : ℕ → ℝ, IsDecreasingOn N π₁ → IsDecreasingOn N π₂ → IsDecreasingOn N π₃ →
    mass N π₂ = mass N π₁ → mass N π₃ = mass N π₁ →
    moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁ → Compatible N π₁ π₂ π₃
variable {N : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
noncomputable def peelWeight (N : ℕ) (π₂ π₃ : ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  min (min (π₂ k) (π₃ (N - k))) x
section Peel
variable {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (h₂ : IsDecreasingOn n π₂) (h₃ : IsDecreasingOn n π₃)
include hx h₂ h₃
end Peel
end ArithmeticTriangleRemovalInVectorSpaces


