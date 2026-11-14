-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZeroSpace
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZeroSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:23.039991+00:00
-- url     : https://prove2.me/theorems/b777f2cf-5aab-42d5-9d4c-7a457f3a02c8
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelZeroSpace — The existing zero-workspace rewind and copy machines
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelZeroSpace` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Machine declarations are moved from their original module without changing programs or resource
--   formulas. Higher computability-calculus theorems remain in the original facade.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZeroSpace`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelZeroSpace.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1138 @b1635b2e
-- The section on the identity (`tidyCopy`) is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Mathlib.Data.Finite.Sum
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Id
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelZeroSpace` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # The existing zero-workspace rewind and copy machines

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-! ### Machines without work tapes -/

section NoWorkTapes

variable {State : Type*} {tm : MultiTapeTM 0 Symbol State}

open Sequential in
/-- If a machine without work tapes has a run path from its start to a halted configuration, then
following it with `Turing.MultiTapeTM.rewindInput` computes the output of that configuration
tidily: the rewind returns the input head from its position `p` in `p - 1 + 2` further steps. -/
public theorem computesTidily_seq_rewindInput_of_runPath {q : tm.RunPath input}
    (hh : q.head = wordsCfg input (some tm.q₀) (fun _ => []) []) (hl : q.last.Halted) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input q.last.output
      (q.time + (q.last.inputPos.val - 1 + 2)) 0 := by
  let r := MultiTapeNTM.RunPath.ofDeterministic (rewindInput Symbol)
    (q.last.withState (some (rewindInput Symbol).q₀)) (q.last.inputPos.val - 1 + 2)
  have hr : r.last = wordsCfg input none (fun _ => []) q.last.output :=
    (runFrom_rewindInput q.last.inputPos q.last.workTapes q.last.workTapePos q.last.output).trans
      (Cfg.ext_zero_tapes rfl rfl rfl)
  obtain ⟨p, hph, hpl, hpt, -⟩ := exists_runPath_seq hl rfl (by rw [hr]; rfl)
  exact computesTidily_iff.mpr ⟨p, by rw [hph, hh]; rfl, by simp [hpl, hr, rightCfg], hpt,
    by simp [MultiTapeNTM.RunPath.space]⟩

/-- A machine without work tapes that computes `output` in time `t`, followed by
`Turing.MultiTapeTM.rewindInput`, computes `output` tidily in time `2 * t + 2`: in `t` steps the
input head moves at most `t` cells, so the rewind takes at most `t + 2` steps. -/
public theorem ComputesInTimeAndSpace.computesTidily_seq_rewindInput {output : List Symbol}
    {t s : ℕ} (h : ComputesInTimeAndSpace tm input output t s) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input output (2 * t + 2) 0 := by
  obtain ⟨⟨u, hu_halt, hu_out⟩, htime, -⟩ := h
  -- the computation path of `t` steps ends halted
  let q := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  have hl : q.last.Halted := htime q le_rfl
  -- the machine has halted after both `t` and `u` steps, so the outputs agree
  have hout : q.last.output = output := by
    change (tm.runFrom (tm.initCfg input) t).output = output
    rcases le_total u t with hut | htu
    · rw [runFrom_eq_of_halt _ _ hut hu_halt, hu_out]
    · rw [← runFrom_eq_of_halt _ _ htu hl, hu_out]
  have hpos : q.last.inputPos.val ≤ 1 + t := by
    change ((tm.runFrom (tm.initCfg input) t).inputPos : ℕ) ≤ 1 + t
    simpa [Cfg.init] using inputPos_runFrom_le tm (tm.initCfg input) t
  have h := computesTidily_seq_rewindInput_of_runPath (q := q.toRunPath)
    (q.head_eq.trans (Cfg.init_eq_wordsCfg _ _)) hl
  rw [hout] at h
  exact h.mono (by change t + _ ≤ _; omega) le_rfl

end NoWorkTapes

/-! ### Zero space -/

/-! ### The identity -/

/-- The identity as a tidy machine without work tapes: copy the input to the output, then move the
input head back to the start. -/
public noncomputable def tidyCopy (Symbol : Type*) : MultiTapeTM 0 Symbol (Unit ⊕ RewindState) :=
  copyInput.seq (rewindInput Symbol)

/-- `tidyCopy` computes the identity tidily, in time linear in the length of the word. -/
public theorem computesTidily_tidyCopy (w : List Symbol) :
    (tidyCopy Symbol).ComputesTidilyInTimeAndSpace w w (2 * w.length + 4) 0 :=
  (CopyInput.computesInTimeAndSpace w).computesTidily_seq_rewindInput.mono (by omega) le_rfl

end Turing.MultiTapeTM


