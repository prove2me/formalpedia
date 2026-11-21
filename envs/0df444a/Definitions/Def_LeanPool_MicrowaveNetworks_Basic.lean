-- Prove2me | Definitions.Def_LeanPool_MicrowaveNetworks_Basic
-- name    : LeanPool_MicrowaveNetworks_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:35:44.637551+00:00
-- url     : https://prove2.me/theorems/aa9483fd-346d-4c5a-8fb2-810242e233dd
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Matteo Nerini and Claude AI; maintained by LeanPool contributors's pinned Microwave network synthesis and power-of-two DFT implementation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace MiLAC
abbrev Network (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
@[expose] def interconnection : Network 1 :=
  1
@[expose] noncomputable def phaseShifter (φ : ℝ) : Network 1 :=
  fun _ _ => Complex.exp (φ * Complex.I)
@[expose] def permutationNetwork {n : ℕ} (σ : Equiv.Perm (Fin n)) : Network n :=
  σ.toPEquiv.toMatrix
@[expose] def series {n : ℕ} (A B : Network n) : Network n :=
  B * A
@[expose] def parallel {n m : ℕ} (A : Network n) (B : Network m) : Network (n + m) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)
@[expose] noncomputable def phaseDiagonal {n : ℕ}
    (φ : Fin n → ℝ) : Network n :=
  Matrix.diagonal (fun i => Complex.exp (φ i * Complex.I))
namespace PhaseShifters
inductive Implementable : {n : ℕ} → Network n → Prop where
  /-- An interconnection is implementable. -/
  | ic : Implementable interconnection
  /-- A phase shifter is implementable. -/
  | ps (φ : ℝ) : Implementable (phaseShifter φ)
  /-- A permutation network is implementable. -/
  | pn {n : ℕ} (σ : Equiv.Perm (Fin n)) : Implementable (permutationNetwork σ)
  /-- The series of two implementable networks is implementable. -/
  | series {n : ℕ} {A B : Network n} :
      Implementable A → Implementable B → Implementable (series A B)
  /-- The parallel of two implementable networks is implementable. -/
  | parallel {n m : ℕ} {A : Network n} {B : Network m} :
      Implementable A → Implementable B → Implementable (parallel A B)
end PhaseShifters
end MiLAC


