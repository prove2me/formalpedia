-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RewindWork
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RewindWork
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:46.173207+00:00
-- url     : https://prove2.me/theorems/8b7c4f21-5159-4a9c-be24-28986a5c93c6
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork — The space of the work-tape-rewinding machine
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The addition of Christian Reitwiessner's branch `crei/tidy-universal` to
--   `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.space_rewindWork_le`: the rewinding machine visits at most `p + 2` cells.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RewindWork`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/RewindWork.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindWork
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The space of the work-tape-rewinding machine

The addition of Christian Reitwiessner's branch `crei/tidy-universal` to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork`.

## Main results

* `Turing.MultiTapeTM.space_rewindWork_le`: the rewinding machine visits at most `p + 2` cells.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

-- vendored: `spaceUsed_rewindWork_le` in crei:crei/tidy-universal; `spaceUsed` is the space of a
-- run path since cslib #1133 and #1122
/-- The one-tape `rewindWork` machine visits at most `p + 2` cells: its head stays within
`[-1, p]`. -/
public theorem space_rewindWork_le (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (t : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : t = tapeOfList w) {p : ℕ} (hp : p ≤ w.length) (n : ℕ) :
    (MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol write)
        ⟨some (rewindWork Symbol write).q₀, ip, fun _ => t, fun _ => (p : ℤ), out⟩ n).space ≤
      p + 2 := by
  rw [MultiTapeNTM.RunPath.space, Fin.sum_univ_one]
  refine (spaceUsedByTape_le_card _ (S := .Icc (-1) (p : ℤ)) fun m _ => ?_).trans ?_
  · exact Finset.mem_Icc.2 (workTapePos_runFrom_rewindWork write ip t out hw hp m)
  · rw [Int.card_Icc]; omega

end Turing.MultiTapeTM


