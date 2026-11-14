-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Id
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Id
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:16.252435+00:00
-- url     : https://prove2.me/theorems/8bf6958f-191b-4bb7-bba7-49ead17e9e2f
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.Id — The copy machine, public
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Id` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The change of Christian Reitwiessner's branch `crei/tidy-universal` to
--   `Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id`: the copy machine and its
--   specification become public, under the names `copyInput` and `CopyInput.computesInTimeAndSpace`,
--   for use by `Turing.MultiTapeTM.tidyCopy`. The pinned machine `copy` is private to its module, so
--   the machine is defined here anew.
--
--   A machine with a single state and no work tapes scans the input from left to right, copying each
--   symbol to the output tape, and halts on the blank at the right end of the input. On input `w` it
--   outputs `w` after `w.length + 1` steps, and having no work tapes it uses zero space.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.copyInput`: the copy machine.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.CopyInput.computesInTimeAndSpace`: it computes the identity in one step per
--     input symbol and zero space.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Id`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/Id.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Id` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The copy machine, public

The change of Christian Reitwiessner's branch `crei/tidy-universal` to
`Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id`: the copy machine and its
specification become public, under the names `copyInput` and `CopyInput.computesInTimeAndSpace`,
for use by `Turing.MultiTapeTM.tidyCopy`. The pinned machine `copy` is private to its module, so
the machine is defined here anew.

A machine with a single state and no work tapes scans the input from left to right, copying each
symbol to the output tape, and halts on the blank at the right end of the input. On input `w` it
outputs `w` after `w.length + 1` steps, and having no work tapes it uses zero space.

## Main definitions

* `Turing.MultiTapeTM.copyInput`: the copy machine.

## Main results

* `Turing.MultiTapeTM.CopyInput.computesInTimeAndSpace`: it computes the identity in one step per
  input symbol and zero space.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The copy machine: a single state and no work tapes. It copies every input symbol to the output
tape while moving right, and halts on reading the blank at the right end of the input. -/
public def copyInput : MultiTapeTM 0 Symbol Unit :=
  ofTr () fun _ s _ =>
    match s with
    | some b => { inputTape := 1, workTapes := Fin.elim0, output := some b, state := some () }
    | none => { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

namespace CopyInput

/-- The configuration of the copy machine in state `q` after copying the first `n` input symbols
to the output: the input head is over cell `n + 1` (capped at the right end marker) and there are
no work tapes. `input` is explicit because it only occurs in the type. -/
def cfg (input : List Symbol) (q : Option Unit) (n : ℕ) : Cfg 0 Symbol Unit input :=
  ⟨q, ⟨min (n + 1) (input.length + 1), by omega⟩, fun _ _ => none, fun _ => 0, input.take n⟩

/-- Over an input symbol, the copy machine emits it and moves right. -/
lemma step_scan {n : ℕ} (hn : n < input.length) :
    copyInput.step (cfg input (some ()) n) = cfg input (some ()) (n + 1) := by
  have hsym : (cfg input (some ()) n).inputSymbol = some input[n] :=
    inputSymbolInner n (by simp [cfg]; omega) hn
  rw [step_of_state rfl, hsym, copyInput, tr_ofTr]
  apply Cfg.ext_zero_tapes (by rfl)
  · simp [cfg, moveInputPos]
    grind
  · simp only [cfg, Action.apply, Option.toList_some]
    grind [List.take_add_one]

/-- On the blank at the right end of the input, the copy machine halts in place. -/
lemma step_halt :
    copyInput.step (cfg input (some ()) input.length) = cfg input none input.length := by
  have hsym : (cfg input (some ()) input.length).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr (by simp [cfg]))
  rw [step_of_state rfl, hsym, copyInput, tr_ofTr]
  apply Cfg.ext_zero_tapes <;> simp [cfg, Action.apply]

/-- After `n ≤ input.length` steps, the copy machine has copied the first `n` input symbols. -/
lemma runFrom_scan (n : ℕ) (hn : n ≤ input.length) :
    copyInput.runFrom (copyInput.initCfg input) n = cfg input (some ()) n := by
  induction n with
  | zero => exact Cfg.ext_zero_tapes rfl rfl rfl
  | succ n ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_scan (by omega)]

/-- The complete run: after `input.length + 1` steps the copy machine has halted with the input
copied to the output. -/
lemma runFrom_full (input : List Symbol) :
    copyInput.runFrom (copyInput.initCfg input) (input.length + 1) =
      cfg input none input.length := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, runFrom_scan _ le_rfl, step_halt]

/-- The copy machine outputs its input unchanged, in `input.length + 1` steps and zero space. -/
public theorem computesInTimeAndSpace (input : List Symbol) :
    ComputesInTimeAndSpace copyInput input input (input.length + 1) 0 := by
  have hhalt := congrArg Cfg.state (runFrom_full input)
  exact ⟨⟨input.length + 1, hhalt, by rw [runFrom_full]; simp [cfg]⟩,
    runsInTime_iff_halted.mpr hhalt, by simp⟩

end CopyInput

end Turing.MultiTapeTM


