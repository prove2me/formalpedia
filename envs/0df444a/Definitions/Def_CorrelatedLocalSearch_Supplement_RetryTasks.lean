-- Prove2me | Definitions.Def_CorrelatedLocalSearch_Supplement_RetryTasks
-- name    : CorrelatedLocalSearch_Supplement_RetryTasks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:01:25.992871+00:00
-- url     : https://prove2.me/theorems/b7c0feca-9121-4d7f-b544-ff501d52213a
-- title:
--   Retry tasks, selectors, powered success weights and deadline recursion
-- statement:
--   A finite retry-task instance has a nonempty success set $B_i\subseteq A$ for each unfinished task. A deterministic nonanticipating selector chooses an unfinished task from the observed prefix; the next symbol completes it exactly when it belongs to $B_i$. The model defines the stopping time $\tau$, $W=\sum_a\pi(a)^s$, $w_i=\sum_{a\in B_i}\pi(a)^s$, both powered prefix sums $Z_T$ and $\widetilde Z_T$, and the suffix recursion of Theorem 3.1. It also contains the two-task-type instance of Theorem 3.2 and its fixed orders $\Lambda_A,\Lambda_B$.
--
--   **Formalization Note** The current unfinished set is explicit, so completed tasks cannot be selected by a valid selector.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §3, pp.7–8 (PDF pp.9–10)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_GeneralSource

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- A finite family of retry tasks, each with a nonempty success set. -/
structure RetryModel (A I : Type*) [Fintype A] [Fintype I] where
  success : I -> Finset A
  success_nonempty : ∀ i, (success i).Nonempty

/-- A deterministic selector sees the full consumed prefix and current unfinished set. -/
abbrev RetrySelector (A I : Type*) := List A -> Finset I -> I

/-- A selector never selects a completed task while work remains. -/
def IsValidRetrySelector {A I : Type*} [Fintype I] [DecidableEq I]
    (sel : RetrySelector A I) : Prop :=
  ∀ w U, U.Nonempty -> sel w U ∈ U

noncomputable def retryRunFrom {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (M : RetryModel A I) (sel : RetrySelector A I) :
    List A -> Finset I -> List A -> Finset I
  | _, U, [] => U
  | pre, U, a :: rest =>
      let i := sel pre U
      let U' := if i ∈ U ∧ a ∈ M.success i then U.erase i else U
      retryRunFrom M sel (pre ++ [a]) U' rest

/-- The unfinished tasks after consuming a word. -/
noncomputable def retryState {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (M : RetryModel A I) (sel : RetrySelector A I) (w : List A) : Finset I :=
  retryRunFrom M sel [] Finset.univ w

/-- The attempt count until every task completes, with top for nontermination. -/
noncomputable def retryTau {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (M : RetryModel A I) (sel : RetrySelector A I) (omega : Nat -> A) : ℕ∞ :=
  ⨅ (t : Nat) (_h : retryState M sel (tapePrefix omega t) = ∅), (t : ℕ∞)

def retrySurvivalEvent {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (M : RetryModel A I) (sel : RetrySelector A I) (T : Nat) : Set (Nat -> A) :=
  {omega | (T : ℕ∞) < retryTau M sel omega}

/-- `W = sum_a pi(a)^s`. -/
noncomputable def totalPowerWeight {A : Type*} [Fintype A] (pi : A -> Real) (s : Real) : Real :=
  ∑ a, pi a ^ s

/-- `w_i = sum_{a in B_i} pi(a)^s`. -/
noncomputable def taskPowerWeight {A I : Type*} [Fintype A] [Fintype I]
    (M : RetryModel A I) (pi : A -> Real) (s : Real) (i : I) : Real :=
  ∑ a ∈ M.success i, pi a ^ s

/-- The smallest-powered-success-set priority rule. -/
def AlwaysChoosesSmallest {A I : Type*} [Fintype A] [Fintype I]
    [DecidableEq A] [DecidableEq I] (M : RetryModel A I) (pi : A -> Real) (s : Real)
    (sel : RetrySelector A I) : Prop :=
  ∀ w U, U.Nonempty -> sel w U ∈ U ∧
    ∀ i ∈ U, taskPowerWeight M pi s (sel w U) ≤ taskPowerWeight M pi s i

/-- The powered mass of all live words at one depth. -/
noncomputable def retryPrefixPowerSum {A I : Type*} [Fintype A] [Fintype I]
    [DecidableEq A] [DecidableEq I] (M : RetryModel A I) (sel : RetrySelector A I)
    (pi : A -> Real) (T : Nat) (theta : Real) : Real :=
  ∑ f : Fin T -> A,
    if (retryState M sel (List.ofFn f)).Nonempty
    then wordMass pi (List.ofFn f) ^ theta else 0

/-- The paper's `Z_T(theta)`: the powered mass of length-`T` words for which the `T`-th
attempt is made, including words on which that attempt terminates.  At `T=0` the empty word
has mass one. -/
noncomputable def retryCompletionPrefixPowerSum {A I : Type*} [Fintype A] [Fintype I]
    [DecidableEq A] [DecidableEq I] (M : RetryModel A I) (sel : RetrySelector A I)
    (pi : A -> Real) (T : Nat) (theta : Real) : Real :=
  ∑ f : Fin T -> A,
    let w := List.ofFn f
    if T = 0 ∨ (retryState M sel (w.take (T - 1))).Nonempty
    then wordMass pi w ^ theta else 0

/-- The reference survival probability, written as its finite product-mass sum. -/
noncomputable def retryReferenceTail {A I : Type*} [Fintype A] [Fintype I]
    [DecidableEq A] [DecidableEq I] (M : RetryModel A I) (sel : RetrySelector A I)
    (pi : A -> Real) (T : Nat) : Real :=
  retryPrefixPowerSum M sel pi T 1

/-- The scalar suffix recursion in Theorem 3.1. -/
noncomputable def retryValue (W : Real) (weights : List Real) : Nat -> Nat -> Real
  | 0, j => if j < weights.length then 1 else 0
  | t + 1, j =>
      if h : j < weights.length then
        min 1 ((W - weights[j]) * retryValue W weights t j +
          weights[j] * retryValue W weights t (j + 1))
      else 0

/-- One row of the displayed suffix dynamic program.  The extra final cell is the boundary
`v_t(n+1)=0`; the row can be updated in place from left to right because cell `j` uses only the
old cells `j` and `j+1`. -/
noncomputable def retryValueNextRow (W : Real) (weights row : List Real) : List Real :=
  List.ofFn (fun j : Fin (weights.length + 1) =>
    if h : j.val < weights.length then
      min 1 ((W - weights[j]) * row.getD j.val 0 +
        weights[j] * row.getD (j.val + 1) 0)
    else 0)

/-- The row produced after `T` iterations of the displayed dynamic program. -/
noncomputable def retryValueTable (W : Real) (weights : List Real) : Nat -> List Real
  | 0 => List.replicate weights.length 1 ++ [0]
  | T + 1 => retryValueNextRow W weights (retryValueTable W weights T)

/-- Arithmetic-operation cost of the in-place row implementation (four elementary operations per
state and time step). -/
def retryArithmeticOperations (n T : Nat) : Nat := 4 * n * T

/-- Two rolling rows are unnecessary; one row of suffix values suffices. -/
def retryMemoryCells (n : Nat) : Nat := n + 1

/-- The explicit two-symbol family in Theorem 3.2: `n` zero-tasks and one one-task. -/
def separationRetryModel (n : Nat) : RetryModel Bool (Fin (n + 1)) where
  success i := if i = Fin.last n then {true} else {false}
  success_nonempty i := by
    split <;> simp

/-- `Lambda_A`: all zero-tasks before the one-task. -/
noncomputable def orderASelector (n : Nat) : RetrySelector Bool (Fin (n + 1)) :=
  fun _ U => if h : U.Nonempty then U.min' h else 0

/-- `Lambda_B`: the one-task first, then the zero-tasks. -/
noncomputable def orderBSelector (n : Nat) : RetrySelector Bool (Fin (n + 1)) :=
  fun _ U => if _hlast : Fin.last n ∈ U then Fin.last n
    else if h : U.Nonempty then U.min' h else 0

/-- The reference distribution `P(0)=15/16`, `P(1)=1/16`. -/
noncomputable def separationPi : Bool -> Real
  | false => 15 / 16
  | true => 1 / 16

/-- Main catalog declaration for the retry-task model. -/
abbrev RetryTasks (A I : Type*) [Fintype A] [Fintype I] := RetryModel A I

end CorrelatedLocalSearch.Supplement


