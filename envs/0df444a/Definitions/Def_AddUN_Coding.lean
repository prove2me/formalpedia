-- Prove2me | Definitions.Def_AddUN_Coding
-- name    : AddUN_Coding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:23:14.739578+00:00
-- url     : https://prove2.me/theorems/414dcb4d-d635-408c-8dba-09df63e84cff
-- title:
--   Coding
-- statement:
--   Definitions and structural lemmas for Coding, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Theorems.Thm_MeasureTheory_Determined_univ

set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter MeasureTheory
namespace AddUN
namespace Coding
def mu (n : ℕ) : ℕ := 4 ^ (n + 1)
def coord (n k j : ℕ) : ℕ := Nat.pair (Nat.pair n k) j
def stage (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).1).1
def low (n : ℕ) : Set ℕ := {i | stage i < n}
def block (n k : ℕ) : Finset ℕ := (Finset.range (mu n + n)).image (coord n k)
def markerBlock (n k : ℕ) : Finset ℕ := (Finset.range (mu n)).image (coord n k)
def pattern (c : ℕ → Bool) (i : ℕ) : Bool :=
  decide (mu (stage i) ≤ (Nat.unpair i).2) && c ((Nat.unpair i).2 - mu (stage i))
def marker (n k : ℕ) : Set (ℕ → Bool) := cylinderOn (markerBlock n k) fun _ ↦ false
def hit (c : ℕ → Bool) (n k : ℕ) : Set (ℕ → Bool) := cylinderOn (block n k) (pattern c)
open Classical in
/-- The decoding map. The bit `i` of `decode f w` is `true` if, for all large `n`, a marker of
`w` at `(n, f n)` is followed by a message whose bit `i` is `true`. -/
noncomputable def decode (f : ℕ → ℕ) (w : ℕ → Bool) (i : ℕ) : Bool :=
  decide (∀ᶠ n in atTop, i < n ∧ w ∈ marker n (f n) → w (coord n (f n) (mu n + i)) = true)
noncomputable def theta (n : ℕ) : ℝ := 4 * (1 / 2) ^ mu n
def bad (K : Set (ℕ → Bool)) (c : ℕ → Bool) (n : ℕ) : Set ℕ :=
  {k | ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ Determined (low n) E ∧
    theta n ≤ cantorMeasure.real (K ∩ E) ∧
    cantorMeasure.real (K ∩ E ∩ hit c n k) <
      (1 / 2) ^ (mu n + n) / 2 * cantorMeasure.real (K ∩ E)}
open Classical in
/-- The events along the branch of `f`, from the stage `n₀` on. At the stage `n₀ + m` the event
is intersected with the hit at `(n₀ + m, f (n₀ + m))` if `f (n₀ + m)` is not in the slalom. If
it is in the slalom, the points with a marker and no hit are removed. -/
noncomputable def branch (K : Set (ℕ → Bool)) (c : ℕ → Bool) (f : ℕ → ℕ) (n₀ : ℕ) :
    ℕ → Set (ℕ → Bool)
  | 0 => univ
  | m + 1 =>
    if f (n₀ + m) ∈ bad K c (n₀ + m) then
      branch K c f n₀ m \ (marker (n₀ + m) (f (n₀ + m)) \ hit c (n₀ + m) (f (n₀ + m)))
    else branch K c f n₀ m ∩ hit c (n₀ + m) (f (n₀ + m))
variable {K : Set (ℕ → Bool)} {c : ℕ → Bool} {f : ℕ → ℕ} {n₀ : ℕ}
end Coding
open Coding
end AddUN


