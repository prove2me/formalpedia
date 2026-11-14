-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Basic
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:51.809787+00:00
-- url     : https://prove2.me/theorems/3b9618cf-e92f-4452-bd05-d45a2191590e
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic — Basic properties of tidy computations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A tidy computation is a computation, it emits at most one symbol per step, and it stays tidy when
--   the machine is given more work tapes.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace`: a tidily
--     computable function is computable, within the same bounds.
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.length_output_le`: a tidy computation emits at
--     most one symbol per step.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.length_le`: the output of a tidily computable
--     function is no longer than its time bound.
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.extendTapes`: a tidy computation stays tidy with
--     more work tapes.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Basic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/Tidy/Basic.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: submitted #1111 @3441fa81
-- `ComputableTidilyInTimeAndSpace.length_le` is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelFacts
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Basic properties of tidy computations

A tidy computation is a computation, it emits at most one symbol per step, and it stays tidy when
the machine is given more work tapes.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace`: a tidily
  computable function is computable, within the same bounds.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.length_output_le`: a tidy computation emits at
  most one symbol per step.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.length_le`: the output of a tidily computable
  function is no longer than its time bound.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.extendTapes`: a tidy computation stays tidy with
  more work tapes.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*} {k : ℕ} {Symbol State : Type*}

variable {tm : MultiTapeTM k Symbol State}

/-- A tidy computation of a function is a computation of it. -/
theorem ComputesFunTidilyInTimeAndSpace.computesFunInTimeAndSpace {encIn : α ↪ List Symbol}
    {encOut : β ↪ List Symbol} {f : α → β} {t s : α → ℕ}
    (h : ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s) :
    tm.ComputesFunInTimeAndSpace encIn encOut f t s :=
  fun a => (h a).computesInTimeAndSpace

/-- The output of a tidily computable function is no longer than its time bound. -/
theorem ComputableTidilyInTimeAndSpace.length_le {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) (a : α) :
    (encOut (f a)).length ≤ t a :=
  let ⟨_, _, _, _, htm⟩ := h
  (htm a).length_output_le

/-- A tidily computable function is computable. -/
theorem ComputableTidilyInTimeAndSpace.computableInTimeAndSpace {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) :
    ComputableInTimeAndSpace f encIn encOut t s :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨k, State, hfinite, tm, htm.computesFunInTimeAndSpace⟩

end Turing.MultiTapeTM


