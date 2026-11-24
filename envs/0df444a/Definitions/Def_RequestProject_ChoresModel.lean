-- Prove2me | Definitions.Def_RequestProject_ChoresModel
-- name    : RequestProject_ChoresModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:19.089809+00:00
-- url     : https://prove2.me/theorems/3cf4b0fe-2188-45d0-834c-6243df4dfe13
-- title:
--   Chores Model
-- statement:
--   Definitions and structural lemmas for Chores Model, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
structure Outcome (T : Type*) (n : ℕ) where
  /-- The set of chores that are outsourced. -/
  outsourced : Finset T
  /-- The bundle of chores performed by each agent. -/
  kept : Fin n → Finset T
  /-- The part of the outsourcing bill paid by each agent. -/
  pay : Fin n → ℝ
variable {n : ℕ}
def Outcome.Valid (p : T → ℝ) (o : Outcome T n) : Prop :=
  (∀ j, Disjoint o.outsourced (o.kept j)) ∧
  (∀ j k, j ≠ k → Disjoint (o.kept j) (o.kept k)) ∧
  (o.outsourced ∪ Finset.univ.biUnion o.kept = Finset.univ) ∧
  (∀ j, 0 ≤ o.pay j) ∧
  (∑ t ∈ o.outsourced, p t ≤ ∑ j, o.pay j)
def cost (c : T → ℝ) (o : Outcome T n) (j : Fin n) : ℝ := (∑ t ∈ o.kept j, c t) + o.pay j
def cbar (c p : T → ℝ) (t : T) : ℝ := min (c t) (p t)
def cbarSum (c p : T → ℝ) (A : Finset T) : ℝ := ∑ t ∈ A, cbar c p t
def MMSset (n : ℕ) (c p : T → ℝ) : Set ℝ :=
  {r | ∃ o : Outcome T n, o.Valid p ∧ ∀ j, cost c o j ≤ r}
noncomputable def MMS (n : ℕ) (c p : T → ℝ) : ℝ := sInf (MMSset n c p)
section Basic
variable {c p : T → ℝ}
end Basic
section MMSBasic
variable {c p : T → ℝ}
end MMSBasic
noncomputable def wt (c p : T → ℝ) (mu : ℝ) (t : T) : ℝ :=
  if mu < cbar c p t then p t else cbar c p t
noncomputable def wtSum (c p : T → ℝ) (mu : ℝ) (A : Finset T) : ℝ := ∑ t ∈ A, wt c p mu t
section Weight
variable {c p : T → ℝ} {mu : ℝ}
end Weight
end FairChores


