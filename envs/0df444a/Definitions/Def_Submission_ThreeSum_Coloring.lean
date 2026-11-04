-- Prove2me | Definitions.Def_Submission_ThreeSum_Coloring
-- name    : Submission_ThreeSum_Coloring
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:01.234582+00:00
-- url     : https://prove2.me/theorems/2e2b6c05-48f9-45bc-8a7b-240f8296aa1b
-- title:
--   Coloring
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.Coloring
variable {α : Type*}
abbrev Parameter (d : ℕ) := (Fin d × Fin d) × ((Bool × Bool) → Fin 3)
def applyColor {d : ℕ} (p : Parameter d) (word : Fin d → Bool) : Fin 3 :=
  p.2 (word p.1.1, word p.1.2)
def indexWidth (n : ℕ) : ℕ := Nat.size (n - 1)
def indexWord {n : ℕ} (i : Fin n) : Fin (indexWidth n) → Bool :=
  fun j => i.val.testBit j.val
def colorIndex {n : ℕ} (p : Parameter (indexWidth n)) (i : Fin n) : Fin 3 :=
  applyColor p (indexWord i)
def family (n : ℕ) : Finset (Fin n → Fin 3) :=
  Finset.univ.image (fun p : Parameter (indexWidth n) => colorIndex p)
def values {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (color : Fin 3) :
    Finset ℤ :=
  (Finset.univ.filter (fun i => c i = color)).image x
def negValues {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) : Finset ℤ :=
  (values x c 2).image (fun z => -z)
def DistinctZeroSum {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x i + x j + x k = 0
def ThreeSetWitness (a b c : Finset ℤ) : Prop :=
  ∃ u ∈ a, ∃ v ∈ b, ∃ w ∈ c, u + v = w
def runReduction {n : ℕ} (x : Fin n → ℤ)
    (solve : Finset ℤ → Finset ℤ → Finset ℤ → Bool) : Bool :=
  decide (∃ p : Parameter (indexWidth n),
    solve (values x (colorIndex p) 0) (values x (colorIndex p) 1)
      (negValues x (colorIndex p)) = true)
end ThreeSum.Coloring


