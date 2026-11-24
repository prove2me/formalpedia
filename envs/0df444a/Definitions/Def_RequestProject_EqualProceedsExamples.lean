-- Prove2me | Definitions.Def_RequestProject_EqualProceedsExamples
-- name    : RequestProject_EqualProceedsExamples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:48.164054+00:00
-- url     : https://prove2.me/theorems/35583ba5-5e18-4e42-9532-b11721e5379f
-- title:
--   Equal Proceeds Examples
-- statement:
--   Definitions and structural lemmas for Equal Proceeds Examples, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace EqualProceedsExampleThree
variable (N : ℕ)
def val : Fin (N + 1) → ℝ := fun g => if g = 0 then 0 else 1
def price : Fin (N + 1) → ℝ := fun g => if g = 0 then 1 else 0
def keptFun : Fin (N + 1) → Finset (Fin (N + 1)) := fun j => if j = 0 then ∅ else {j}
def out1 : Outcome (Fin (N + 1)) (N + 1) where
  sold := {0}
  kept := keptFun N
  money := fun j => if j = 0 then 1 else 0
noncomputable def out2 : Outcome (Fin (N + 1)) (N + 1) where
  sold := {0}
  kept := keptFun N
  money := fun _ => 1 / ((N : ℝ) + 1)
end EqualProceedsExampleThree
namespace EqualProceedsExampleFour
variable (N : ℕ)
def price : Fin (N + 2) → ℝ := fun _ => 1
noncomputable def val (L : ℝ) (i : Fin (N + 2)) : Fin (N + 2) → ℝ :=
  fun _ => if i = 0 then 1 / L else L
def outSellAll : Outcome (Fin (N + 2)) (N + 2) where
  sold := Finset.univ
  kept := fun _ => ∅
  money := fun _ => 1
def outKeepAll : Outcome (Fin (N + 2)) (N + 2) where
  sold := ∅
  kept := fun j => {j}
  money := fun _ => 0
end EqualProceedsExampleFour
end FairSelling


