-- Prove2me | Definitions.Def_ReusableIntervalContracts
-- name    : ReusableIntervalContracts
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T20:19:54.841081+00:00
-- url     : https://prove2.me/theorems/3322c8d4-a26a-40de-8c3b-5d5bea6548e3
-- title:
--   Reusable contracts for fixed-length execution intervals
-- statement:
--   Each contract specifies a start predicate, an end predicate, and an exact duration. A finite table can use identity and single-step rows, trusted primitives with separately proved semantics, sequential composition, repeated use of an invariant contract, weakening, or a case split. A compositional row may refer only to earlier rows. A table is checked when every row's local obligation holds for every state.
-- source:
--   Adapts the composition and consequence rules of Hoare logic to a finite table for exact iterates. See Hoare, An axiomatic basis for computer programming, Communications of the ACM 12(10), 1969, https://doi.org/10.1145/363235.363259.

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Verification.IntervalContracts

abbrev Row := List ℕ
abbrev Table := List Row

def out (code : Table) (i : ℕ) : Row := code[i]?.getD []

def field (row : Row) (column : ℕ) := row[column]?.getD 0

def kind (row : Row) := field row 0
def span (row : Row) := field row 1
def pre (row : Row) := field row 2
def post (row : Row) := field row 3
def first (row : Row) := field row 4
def second (row : Row) := field row 5

variable {S : Type*}

/-- A summary constrains the endpoints of a fixed-length interval. -/
def Holds (step : S → S) (pred : ℕ → S → Prop) (row : Row) : Prop :=
  ∀ s, pred (pre row) s → pred (post row) (step^[span row] s)

/-- A registered rule may certify an exact interval directly from its
syntax. Its soundness can be proved once over the full state type. -/
structure Model (S : Type*) where
  step : S → S
  pred : ℕ → S → Prop
  primitive : Row → Bool
  primitive_sound : ∀ row, primitive row = true → Holds step pred row

/-- A local obligation. Structural checks are explicit so that a checker
can inspect references and binary durations without unfolding the DAG. -/
def obligationAt (pred : ℕ → S → Prop) (primitive : Row → Bool)
    (possible : Prop) (code : Table) (i : ℕ) (input output : S) : Prop :=
  let row := out code i
  let left := out code (first row)
  let right := out code (second row)
  if kind row = 0 then
    span row = 0 ∧ (pred (pre row) input → pred (post row) input)
  else if kind row = 1 then
    span row = 1 ∧ (possible → pred (pre row) input → pred (post row) output)
  else if kind row = 2 then
    primitive row = true
  else if kind row = 3 then
    first row < i ∧ second row < i ∧ span row = span left + span right ∧
      pre row = pre left ∧ post left = pre right ∧ post right = post row
  else if kind row = 4 then
    first row < i ∧ span row = second row * span left ∧
      pre row = pre left ∧ post left = pre left ∧ post row = pre left
  else if kind row = 5 then
    first row < i ∧ span row = span left ∧
      (pred (pre row) input → pred (pre left) input) ∧
      (pred (post left) input → pred (post row) input)
  else if kind row = 6 then
    first row < i ∧ second row < i ∧ span row = span left ∧ span row = span right ∧
      post left = post row ∧ post right = post row ∧
      (pred (pre row) input → pred (pre left) input ∨ pred (pre right) input)
  else False

def obligation (m : Model S) (code : Table) (i : ℕ) (s : S) : Prop :=
  obligationAt m.pred m.primitive True code i s (m.step s)

def Checked (m : Model S) (code : Table) : Prop :=
  ∀ i < code.length, ∀ s, obligation m code i s

end Verification.IntervalContracts


