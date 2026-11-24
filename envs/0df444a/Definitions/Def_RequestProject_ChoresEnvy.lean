-- Prove2me | Definitions.Def_RequestProject_ChoresEnvy
-- name    : RequestProject_ChoresEnvy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:57.788411+00:00
-- url     : https://prove2.me/theorems/435ba58b-ac99-46b0-8ab1-476d71eac845
-- title:
--   Chores Envy
-- statement:
--   Definitions and structural lemmas for Chores Envy, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
def EF (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j, cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j
def SEF1 (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j,
    (0 < o.pay i →
      cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∧
    (o.pay i = 0 →
      (cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∨
      (∃ t ∈ o.kept i,
        (cbarSum (c i) p (o.kept i) + o.pay i) - (cbarSum (c i) p (o.kept j) + o.pay j)
          ≤ p t - cbar (c i) p t))
def SEFX (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j,
    (0 < o.pay i →
      cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∧
    (o.pay i = 0 →
      (cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∨
      (∀ t ∈ o.kept i,
        (cbarSum (c i) p (o.kept i) + o.pay i) - (cbarSum (c i) p (o.kept j) + o.pay j)
          ≤ p t - cbar (c i) p t))
def SEF1lit (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j,
    (0 < o.pay i →
      cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∧
    (o.pay i = 0 → ∃ t ∈ o.kept i,
        cbarSum (c i) p (o.kept i) - cbarSum (c i) p (o.kept j) - o.pay j ≤ p t - c i t)
def SEFXlit (c : Fin n → T → ℝ) (p : T → ℝ) (o : Outcome T n) : Prop :=
  ∀ i j,
    (0 < o.pay i →
      cbarSum (c i) p (o.kept i) + o.pay i ≤ cbarSum (c i) p (o.kept j) + o.pay j) ∧
    (o.pay i = 0 → ∀ t ∈ o.kept i,
        cbarSum (c i) p (o.kept i) - cbarSum (c i) p (o.kept j) - o.pay j ≤ p t - c i t)
section Relations
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
end Relations
section Derivation
variable {ci p : T → ℝ}
end Derivation
namespace LitCounterexample
def cc : Fin 2 → Fin 2 → ℝ := fun _ _ => 5
def pp : Fin 2 → ℝ := fun _ => 1
def oo : Outcome (Fin 2) 2 :=
  { outsourced := ∅
    kept := fun j => {j}
    pay := fun _ => 0 }
end LitCounterexample
end FairChores


