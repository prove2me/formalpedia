-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Nondeterministic
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Nondeterministic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:02.262207+00:00
-- url     : https://prove2.me/theorems/92383fcb-e665-40fa-83f5-f636507999be
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Nondeterministic — Output growth along run paths
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Nondeterministic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The additions of cslib PR #1111 to
--   `Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic`: a step emits at most one symbol,
--   so a run path emits at most one symbol per step.
--
--   ### Main results
--
--   * `Turing.MultiTapeNTM.RunPath.length_output_last_le`: a run path emits at most one symbol per
--     step.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Nondeterministic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Nondeterministic.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Nondeterministic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Nondeterministic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Output growth along run paths

The additions of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic`: a step emits at most one symbol,
so a run path emits at most one symbol per step.

## Main results

* `Turing.MultiTapeNTM.RunPath.length_output_last_le`: a run path emits at most one symbol per
  step.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

namespace RunPath

/-- A step emits at most one symbol. -/
lemma length_output_le_of_step {c c' : Cfg k Symbol State input} (h : ntm.Step c c') :
    c'.output.length ≤ c.output.length + 1 := by
  grind [Step, Action.apply_output, Option.length_toList_le]

/-- A run path emits at most one symbol per step. -/
lemma length_output_last_le (p : ntm.RunPath input) :
    p.last.output.length ≤ p.head.output.length + p.time := by
  induction p using RelSeries.inductionOn' with
  | singleton c => simp [time]
  | snoc p c hc ih =>
    have := length_output_le_of_step hc
    simp only [time, RelSeries.last_snoc, RelSeries.head_snoc, RelSeries.snoc_length] at ih ⊢
    lia

end RunPath

end MultiTapeNTM

end Turing


