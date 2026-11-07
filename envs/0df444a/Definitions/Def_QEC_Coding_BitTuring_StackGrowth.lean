-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_StackGrowth
-- name    : QEC_Coding_BitTuring_StackGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:51:33.827091+00:00
-- url     : https://prove2.me/theorems/4b308215-ff78-4390-942b-199e12edb509
-- title:
--   Stack Growth
-- statement:
--   Definitions and structural lemmas for Stack Growth, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false
namespace QEC.Coding.BitTuring
open Turing
open scoped BigOperators
def pushes {K Λ σ : Type} : TM2.Stmt (fun _ : K => Bool) Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0
def stackSize {K : Type} [Fintype K] (tapes : K → List Bool) : ℕ :=
  ∑ k, (tapes k).length
def programPushes {K Λ σ : Type} [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : ℕ :=
  Finset.univ.sup (fun l => pushes (M l))
end QEC.Coding.BitTuring


