-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:36.807714+00:00
-- url     : https://prove2.me/theorems/1691e8f6-619e-4b13-b5d8-7499d15c0b60
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs — Tidy computations as runs
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A tidy computation (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`) is the run of exactly the
--   given number of steps from the start with blank work tapes to the halted configuration with blank
--   work tapes that has emitted the output, together with the space bound. This is
--   `Turing.MultiTapeTM.computesTidily_iff` as stated in Christian Reitwiessner's branch
--   `crei/tidy-universal`, from which the vendored modules use it.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.computesTidily_iff_runFrom`: a tidy computation, read on runs.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/Tidy/Defs.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/Tidy/Defs.lean`; `computesTidily_iff` as stated in
-- crei:crei/tidy-universal @7f7c0696, before the run paths of cslib #1117)

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tidy computations as runs

A tidy computation (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`) is the run of exactly the
given number of steps from the start with blank work tapes to the halted configuration with blank
work tapes that has emitted the output, together with the space bound. This is
`Turing.MultiTapeTM.computesTidily_iff` as stated in Christian Reitwiessner's branch
`crei/tidy-universal`, from which the vendored modules use it.

## Main results

* `Turing.MultiTapeTM.computesTidily_iff_runFrom`: a tidy computation, read on runs.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

/-- A tidy computation is a single run between `Turing.wordsCfg` configurations with
blank work tapes, which emits the output, together with the space bound. -/
theorem computesTidily_iff_runFrom {input output : List Symbol} :
    tm.ComputesTidilyInTimeAndSpace input output t s ↔
      tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
          wordsCfg input none (fun _ => []) output ∧
        (MultiTapeNTM.RunPath.ofDeterministic tm (wordsCfg input (some tm.q₀) (fun _ => []) [])
          t).space ≤ s := by
  rw [computesTidily_iff, ← exists_runPath_iff_runFrom rfl]

end Turing.MultiTapeTM


