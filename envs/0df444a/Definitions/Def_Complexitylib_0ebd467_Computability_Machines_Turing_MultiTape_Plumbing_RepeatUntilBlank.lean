-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RepeatUntilBlank
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RepeatUntilBlank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:11.26745+00:00
-- url     : https://prove2.me/theorems/df388b54-1e4a-4c0e-9079-8933341dce08
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank — Confined runs
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The addition of Christian Reitwiessner's branch `crei/tidy-universal` to
--   `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank`: a run between two
--   configurations that keeps every head within a window, which loops built like
--   `Turing.MultiTapeTM.repeatUntilBlank` accumulate round by round. The branch also reproves
--   `Turing.MultiTapeTM.transformsTapes_repeatUntilBlank` through confined runs; that proof is not
--   copied.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.ConfinedRun`: a run of a given length, with every head within `[-r, r]`.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RepeatUntilBlank`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/RepeatUntilBlank.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `ConfinedRun.confined` is stated with the cells visited by a run path since cslib #1122

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RepeatUntilBlank

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Confined runs

The addition of Christian Reitwiessner's branch `crei/tidy-universal` to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank`: a run between two
configurations that keeps every head within a window, which loops built like
`Turing.MultiTapeTM.repeatUntilBlank` accumulate round by round. The branch also reproves
`Turing.MultiTapeTM.transformsTapes_repeatUntilBlank` through confined runs; that proof is not
copied.

## Main definitions

* `Turing.MultiTapeTM.ConfinedRun`: a run of a given length, with every head within `[-r, r]`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `M` runs from `start` to `finish` in `steps` steps, with every head within `[-r, r]`. -/
public structure ConfinedRun (M : MultiTapeTM k Symbol State)
    (start finish : Cfg k Symbol State input) (steps r : ℕ) : Prop where
  reaches : M.runFrom start steps = finish
  confined : ∀ l,
    (MultiTapeNTM.RunPath.ofDeterministic M start steps).visitedByTapeHead l ⊆
      Finset.Icc (-(r : ℤ)) (r : ℤ)

end Turing.MultiTapeTM


