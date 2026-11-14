-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_MarkWork
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_MarkWork
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:17.71545+00:00
-- url     : https://prove2.me/theorems/580ca2c7-910d-4fb3-869f-8db865ba5226
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork — A machine that marks the cell left of its head
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `markWork Symbol write` is a machine with one work tape that writes `write` to the cell left of its
--   head and moves the head back, halting after two steps. It neither moves the input head nor emits
--   output. To use it on tape `i` of a machine with more tapes, embed it with
--   `Turing.MultiTapeTM.tapeEmb`.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_MarkWork`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/MarkWork.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# A machine that marks the cell left of its head

`markWork Symbol write` is a machine with one work tape that writes `write` to the cell left of its
head and moves the head back, halting after two steps. It neither moves the input head nor emits
output. To use it on tape `i` of a machine with more tapes, embed it with
`Turing.MultiTapeTM.tapeEmb`.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The states of `markWork`: `start` steps left, `put` writes and steps back. -/
public inductive MarkWorkState : Type
  | start
  | put
  deriving DecidableEq

public instance : Fintype MarkWorkState := ⟨{.start, .put}, fun q => by cases q <;> simp⟩

/-- `markWork Symbol write` steps left, writes `write` (erasing if `write = none`), steps back
right and halts. -/
public def markWork (Symbol : Type*) (write : Option Symbol) :
    MultiTapeTM 1 Symbol MarkWorkState :=
  ofTr .start fun q _ _ =>
    match q with
    | .start => ⟨0, fun _ => (none, -1), none, some .put⟩
    | .put => ⟨0, fun _ => (some write, 1), none, none⟩

/-- Started with its head at `p`, after two steps `markWork Symbol write` has halted with `write`
at cell `p - 1` and its head back at `p`. -/
public theorem runFrom_markWork (write : Option Symbol) (ip : Fin (input.length + 2))
    (tp : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) :
    (markWork Symbol write).runFrom
        ⟨some (markWork Symbol write).q₀, ip, fun _ => tp, fun _ => p, out⟩ 2 =
      ⟨none, ip, fun _ => Function.update tp (p - 1) write, fun _ => p, out⟩ := by
  simp [runFrom, step_of_state, markWork, Action.apply, sub_eq_add_neg]

end Turing.MultiTapeTM


