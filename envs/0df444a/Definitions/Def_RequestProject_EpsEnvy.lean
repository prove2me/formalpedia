-- Prove2me | Definitions.Def_RequestProject_EpsEnvy
-- name    : RequestProject_EpsEnvy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:51.000255+00:00
-- url     : https://prove2.me/theorems/64c05ae3-5919-498a-9680-7603caf58cc9
-- title:
--   Eps Envy
-- statement:
--   Definitions and structural lemmas for Eps Envy, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
def epsSEF1 (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 →
      (vbarSum (v i) p (o.kept i) + o.money i + eps ≥ vbarSum (v i) p (o.kept j)) ∨
      (∃ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g))
def epsSEFX (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 →
      (vbarSum (v i) p (o.kept i) + o.money i + eps ≥ vbarSum (v i) p (o.kept j)) ∨
      (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g))
def epsSEF1lit (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 → ∃ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g)
def epsSEFXlit (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (o.money j = 0 → ∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g)
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
def epsSEFXu (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i + eps
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g + o.money j)
def SEFXu (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + o.money i
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g + o.money j)
def epsSEFXs (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i + eps
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i) + eps
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g + o.money j)
def SEFXs (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i j,
    (0 < o.money j → vbarSum (v i) p (o.kept i) + o.money i
        ≥ vbarSum (v i) p (o.kept j) + o.money j) ∧
    (∀ g ∈ o.kept j,
        vbarSum (v i) p (o.kept i)
          ≥ vbarSum (v i) p (o.kept j \ {g}) + p g + o.money j)
end FairSelling


