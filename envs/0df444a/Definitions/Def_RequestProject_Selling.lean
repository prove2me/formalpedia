-- Prove2me | Definitions.Def_RequestProject_Selling
-- name    : RequestProject_Selling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:16.337583+00:00
-- url     : https://prove2.me/theorems/a9cbd3e1-4f95-4e66-86dd-b264eabee30f
-- title:
--   Selling
-- statement:
--   Definitions and structural lemmas for Selling, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
structure Outcome (G : Type*) (n : ℕ) where
  /-- The set of goods that are sold. -/
  sold : Finset G
  /-- The bundle of (unsold) goods kept by each agent. -/
  kept : Fin n → Finset G
  /-- The amount of sale proceeds (money) received by each agent. -/
  money : Fin n → ℝ
variable {n : ℕ}
def Outcome.Valid (p : G → ℝ) (o : Outcome G n) : Prop :=
  (∀ j, Disjoint o.sold (o.kept j)) ∧
  (∀ j k, j ≠ k → Disjoint (o.kept j) (o.kept k)) ∧
  (∀ j, 0 ≤ o.money j) ∧
  (∑ j, o.money j ≤ ∑ g ∈ o.sold, p g)
def util (v : G → ℝ) (o : Outcome G n) (j : Fin n) : ℝ :=
  (∑ g ∈ o.kept j, v g) + o.money j
def vbar (v p : G → ℝ) (g : G) : ℝ := max (p g) (v g)
noncomputable def PS (n : ℕ) (v p : G → ℝ) : ℝ := (∑ g, max (p g) (v g)) / n
noncomputable def truncSum (n : ℕ) (v p : G → ℝ) (t : ℝ) : ℝ :=
  (∑ g, max (p g) (min (v g) t)) / n
def MMSset (n : ℕ) (v p : G → ℝ) : Set ℝ :=
  {r | ∃ o : Outcome G n, o.Valid p ∧ ∀ j, r ≤ util v o j}
noncomputable def MMS (n : ℕ) (v p : G → ℝ) : ℝ := sSup (MMSset n v p)
def TPSset (n : ℕ) (v p : G → ℝ) : Set ℝ := {t | t ≤ truncSum n v p t}
noncomputable def TPS (n : ℕ) (v p : G → ℝ) : ℝ := sSup (TPSset n v p)
def vbarSum (vi p : G → ℝ) (A : Finset G) : ℝ := ∑ g ∈ A, vbar vi p g
def EF (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j, vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j
def SEF1 (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 →
      (vbarSum (v i) p (o.kept i) + o.money i ≥ vbarSum (v i) p (o.kept j)) ∨
      (∃ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g))
def SEFX (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 →
      (vbarSum (v i) p (o.kept i) + o.money i ≥ vbarSum (v i) p (o.kept j)) ∨
      (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g))
def SEF1lit (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 → ∃ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i)
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g)
def SEFXlit (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 → ∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i)
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g)
section EnvyRelations
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
end EnvyRelations
end FairSelling


