-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Reverse
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Reverse
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:09.716695+00:00
-- url     : https://prove2.me/theorems/064229d3-22aa-485f-a57c-04f63422c4a8
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.Reverse — The input-reversal machine
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Reverse` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A two-state machine without work tapes that outputs the reversal of its input word tidily in
--   `2 * input.length + 2` steps and zero work-tape space.
--
--   In its initial state `false`, `Turing.MultiTapeTM.reverseInput` scans the input from left to right
--   without emitting anything until it reaches the right boundary blank at position `input.length + 1`,
--   where it steps one cell left onto position `input.length` and enters state `true`. In state `true`
--   it walks left across the input, emitting each symbol as it passes, until it reaches the left
--   boundary blank at position `0`, where it steps one cell right back to the initial head position `1`
--   and halts.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.reverseInput`: the two-state zero-work-tape reversal machine.
--   * `Turing.MultiTapeTM.ReverseInput.cfg`: configurations of `reverseInput`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ReverseInput.runFrom_full`: from the initial state at head position `1` with
--     any prior output prefix `out`, `reverseInput` halts at head position `1` with output
--     `out ++ input.reverse` after `2 * input.length + 2` steps.
--   * `Turing.MultiTapeTM.ReverseInput.computesInTimeAndSpace`: `reverseInput` computes `input.reverse`
--     in `2 * input.length + 2` steps and zero space.
--   * `Turing.MultiTapeTM.ReverseInput.computesTidily`: `reverseInput` computes `input.reverse` tidily
--     in `2 * input.length + 2` steps and zero space.
--   * `Turing.MultiTapeTM.computableTidilyInTimeAndSpace_reverse`: any function whose encoding reverses
--     the encoded input is tidily computable in `2 * (encIn a).length + 2` steps and zero space.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Reverse`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/Reverse.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Reverse` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The input-reversal machine

A two-state machine without work tapes that outputs the reversal of its input word tidily in
`2 * input.length + 2` steps and zero work-tape space.

In its initial state `false`, `Turing.MultiTapeTM.reverseInput` scans the input from left to right
without emitting anything until it reaches the right boundary blank at position `input.length + 1`,
where it steps one cell left onto position `input.length` and enters state `true`. In state `true`
it walks left across the input, emitting each symbol as it passes, until it reaches the left
boundary blank at position `0`, where it steps one cell right back to the initial head position `1`
and halts.

## Main definitions

* `Turing.MultiTapeTM.reverseInput`: the two-state zero-work-tape reversal machine.
* `Turing.MultiTapeTM.ReverseInput.cfg`: configurations of `reverseInput`.

## Main results

* `Turing.MultiTapeTM.ReverseInput.runFrom_full`: from the initial state at head position `1` with
  any prior output prefix `out`, `reverseInput` halts at head position `1` with output
  `out ++ input.reverse` after `2 * input.length + 2` steps.
* `Turing.MultiTapeTM.ReverseInput.computesInTimeAndSpace`: `reverseInput` computes `input.reverse`
  in `2 * input.length + 2` steps and zero space.
* `Turing.MultiTapeTM.ReverseInput.computesTidily`: `reverseInput` computes `input.reverse` tidily
  in `2 * input.length + 2` steps and zero space.
* `Turing.MultiTapeTM.computableTidilyInTimeAndSpace_reverse`: any function whose encoding reverses
  the encoded input is tidily computable in `2 * (encIn a).length + 2` steps and zero space.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The input-reversal machine: two states (`Bool`) and no work tapes. State `false` scans right to
the blank after the input and steps left into state `true`; state `true` walks left emitting each
input symbol until the blank before the input, then steps right to position `1` and halts. -/
public def reverseInput (Symbol : Type*) : MultiTapeTM 0 Symbol Bool :=
  ofTr false fun q s _ =>
    match q, s with
    | false, some _ =>
      { inputTape := 1, workTapes := Fin.elim0, output := none, state := some false }
    | false, none =>
      { inputTape := -1, workTapes := Fin.elim0, output := none, state := some true }
    | true, some b =>
      { inputTape := -1, workTapes := Fin.elim0, output := some b, state := some true }
    | true, none =>
      { inputTape := 1, workTapes := Fin.elim0, output := none, state := none }

namespace ReverseInput

variable {tapes : Fin 0 → ℤ → Option Symbol} {heads : Fin 0 → ℤ} {out : List Symbol}

/-- Configuration of `reverseInput` in state `q` with the input head at `pos` and output `out`.
`input` is explicit because it only occurs in the type. -/
public def cfg (input : List Symbol) (q : Option Bool) (pos : Fin (input.length + 2))
    (tapes : Fin 0 → ℤ → Option Symbol) (heads : Fin 0 → ℤ) (out : List Symbol) :
    Cfg 0 Symbol Bool input :=
  ⟨q, pos, tapes, heads, out⟩

/-- Over an input symbol in state `false`, `reverseInput` moves one cell right without output. -/
lemma step_scan {n : ℕ} (hn : n < input.length) :
    (reverseInput Symbol).step (cfg input (some false) ⟨n + 1, by omega⟩ tapes heads out) =
      cfg input (some false) ⟨n + 1 + 1, by omega⟩ tapes heads out := by
  have hsym : (cfg input (some false) ⟨n + 1, by omega⟩ tapes heads out).inputSymbol =
      some input[n] :=
    inputSymbolInner n (by simp only [cfg]; omega) hn
  rw [step_of_state rfl, hsym, reverseInput, tr_ofTr]
  refine Cfg.ext_zero_tapes rfl ?_ (by simp [cfg, Action.apply])
  simp only [cfg, Action.apply]
  exact moveInputPos_pos_of_ne_right _ (by simp only; omega)

/-- After `n ≤ input.length` steps in state `false` from position `1`, the input head is at
`n + 1` and the output is unchanged. -/
lemma runFrom_scan (n : ℕ) (hn : n ≤ input.length) :
    (reverseInput Symbol).runFrom (cfg input (some false) 1 tapes heads out) n =
      cfg input (some false) ⟨n + 1, by omega⟩ tapes heads out := by
  induction n with
  | zero =>
    refine Cfg.ext_zero_tapes rfl ?_ rfl
    exact Fin.ext rfl
  | succ n ih =>
    rw [runFrom_succ, ih (by omega), step_scan (by omega)]

/-- At the right boundary blank in state `false`, `reverseInput` steps left onto `input.length`
and enters state `true`. -/
lemma step_turn :
    (reverseInput Symbol).step
        (cfg input (some false) ⟨input.length + 1, by omega⟩ tapes heads out) =
      cfg input (some true) ⟨input.length, by omega⟩ tapes heads out := by
  have hsym : (cfg input (some false) ⟨input.length + 1, by omega⟩ tapes heads out).inputSymbol =
      none :=
    inputSymbol_eq_none_of_boundary (.inr rfl)
  rw [step_of_state rfl, hsym, reverseInput, tr_ofTr]
  refine Cfg.ext_zero_tapes rfl ?_ (by simp [cfg, Action.apply])
  simp only [cfg, Action.apply]
  exact moveInputPos_neg_of_ne_left _ (by intro h; have := congrArg Fin.val h; simp at this)

/-- Over an input symbol in state `true`, `reverseInput` emits that symbol and moves one cell
left. -/
lemma step_walk {j : ℕ} (hj : j < input.length) (out : List Symbol) :
    (reverseInput Symbol).step (cfg input (some true) ⟨j + 1, by omega⟩ tapes heads out) =
      cfg input (some true) ⟨j, by omega⟩ tapes heads (out ++ [input[j]]) := by
  have hsym : (cfg input (some true) ⟨j + 1, by omega⟩ tapes heads out).inputSymbol =
      some input[j] :=
    inputSymbolInner j (by simp only [cfg]; omega) hj
  rw [step_of_state rfl, hsym, reverseInput, tr_ofTr]
  refine Cfg.ext_zero_tapes rfl ?_ (by simp [cfg, Action.apply])
  simp only [cfg, Action.apply]
  exact moveInputPos_neg_of_ne_left _ (by intro h; have := congrArg Fin.val h; simp at this)

/-- At the left boundary blank in state `true`, `reverseInput` steps right to position `1` and
halts. -/
lemma step_halt (out : List Symbol) :
    (reverseInput Symbol).step (cfg input (some true) ⟨0, by omega⟩ tapes heads out) =
      cfg input none 1 tapes heads out := by
  have hsym : (cfg input (some true) ⟨0, by omega⟩ tapes heads out).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (.inl rfl)
  rw [step_of_state rfl, hsym, reverseInput, tr_ofTr]
  refine Cfg.ext_zero_tapes rfl ?_ (by simp [cfg, Action.apply])
  simp only [cfg, Action.apply]
  exact (moveInputPos_pos_of_ne_right _ (by simp only; omega)).trans (Fin.ext rfl)

/-- From state `true` at position `j ≤ input.length`, `reverseInput` halts at position `1` after
`j + 1` steps, having appended `(input.take j).reverse` to `out`. -/
lemma runFrom_walk (j : ℕ) (hj : j ≤ input.length) (out : List Symbol) :
    (reverseInput Symbol).runFrom (cfg input (some true) ⟨j, by omega⟩ tapes heads out) (j + 1) =
      cfg input none 1 tapes heads (out ++ (input.take j).reverse) := by
  induction j generalizing out with
  | zero =>
    rw [Nat.zero_add, runFrom_one, step_halt out, List.take_zero, List.reverse_nil,
      List.append_nil]
  | succ j ih =>
    have hj' : j < input.length := by omega
    have htake : (input.take (j + 1)).reverse = [input[j]] ++ (input.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.reverse_append,
        List.reverse_singleton]
    have hstep : j + 1 + 1 = 1 + (j + 1) := by omega
    rw [hstep, runFrom_add, runFrom_one, step_walk hj' out, ih (by omega),
      List.append_assoc, htake]

/-- Complete run from the initial state at position `1` with arbitrary prior output prefix `out`:
after `2 * input.length + 2` steps, `reverseInput` halts at position `1` with output
`out ++ input.reverse`. -/
public theorem runFrom_full (input : List Symbol) (tapes : Fin 0 → ℤ → Option Symbol)
    (heads : Fin 0 → ℤ) (out : List Symbol) :
    (reverseInput Symbol).runFrom (cfg input (some (reverseInput Symbol).q₀) 1 tapes heads out)
      (2 * input.length + 2) = cfg input none 1 tapes heads (out ++ input.reverse) := by
  have htime : 2 * input.length + 2 = (input.length + 1) + (input.length + 1) := by omega
  have hscan : (reverseInput Symbol).runFrom
      (cfg input (some (reverseInput Symbol).q₀) 1 tapes heads out) (input.length + 1) =
        cfg input (some true) ⟨input.length, by omega⟩ tapes heads out := by
    change (reverseInput Symbol).runFrom (cfg input (some false) 1 tapes heads out)
      (input.length + 1) = _
    rw [runFrom_succ, runFrom_scan input.length le_rfl, step_turn]
  rw [htime, runFrom_add, hscan, runFrom_walk input.length le_rfl out, List.take_length]

/-- `reverseInput` computes `input.reverse` in `2 * input.length + 2` steps and zero space. -/
public theorem computesInTimeAndSpace (input : List Symbol) :
    (reverseInput Symbol).ComputesInTimeAndSpace input input.reverse (2 * input.length + 2) 0 := by
  have hrun : (reverseInput Symbol).runFrom ((reverseInput Symbol).initCfg input)
      (2 * input.length + 2) = cfg input none 1 (fun _ _ => none) (fun _ => 0) input.reverse := by
    simpa only [MultiTapeNTM.initCfg, Cfg.init, cfg, List.nil_append] using
      runFrom_full input (fun _ _ => none) (fun _ => 0) []
  have hhalt : ((reverseInput Symbol).runFrom ((reverseInput Symbol).initCfg input)
      (2 * input.length + 2)).Halted := by
    rw [hrun]
    rfl
  exact ⟨⟨2 * input.length + 2, hhalt, by rw [hrun]; rfl⟩,
    runsInTime_iff_halted.mpr hhalt, by simp⟩

/-- `reverseInput` computes `input.reverse` tidily in `2 * input.length + 2` steps and zero
work-tape space, preserving any ambient output prefix. -/
public theorem computesTidily (input : List Symbol) :
    (reverseInput Symbol).ComputesTidilyInTimeAndSpace input input.reverse
      (2 * input.length + 2) 0 := by
  rintro inp ws out ⟨rfl, rfl⟩
  refine ⟨fun _ => [], inp.reverse, ⟨rfl, rfl⟩,
    .ofDeterministic (reverseInput Symbol)
      (wordsCfg inp (some (reverseInput Symbol).q₀) (fun _ => []) out)
      (2 * inp.length + 2), rfl, ?_, le_rfl, by simp [MultiTapeNTM.RunPath.space]⟩
  exact (runFrom_full inp _ _ out).trans (Cfg.ext_zero_tapes rfl rfl rfl)

end ReverseInput

/-- Any function whose encoding reverses the encoded input is tidily computable in
`2 * (encIn a).length + 2` steps and zero work-tape space. -/
public theorem computableTidilyInTimeAndSpace_reverse {α β : Type*} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (hf : ∀ a, encOut (f a) = (encIn a).reverse) :
    ComputableTidilyInTimeAndSpace f encIn encOut
      (fun a => 2 * (encIn a).length + 2) (fun _ => 0) :=
  ⟨0, Bool, inferInstance, reverseInput Bool, fun a =>
    hf a ▸ ReverseInput.computesTidily (encIn a)⟩

end Turing.MultiTapeTM


