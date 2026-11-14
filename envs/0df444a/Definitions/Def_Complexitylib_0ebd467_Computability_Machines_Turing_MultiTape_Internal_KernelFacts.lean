-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelFacts
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:23.999813+00:00
-- url     : https://prove2.me/theorems/b2e3ed8c-7009-430e-a100-7c8df4816398
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelFacts — Basic semantic facts for tidy machine runs
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelFacts` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Machine declarations are moved from their original module without changing programs or resource
--   formulas. Higher computability-calculus theorems remain in the original facade.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelFacts`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelFacts.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81
-- `ComputableTidilyInTimeAndSpace.length_le` is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelFacts` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Basic semantic facts for tidy machine runs

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

namespace ComputesTidilyInTimeAndSpace

variable {input output : List Symbol}

/-- A tidy computation is a computation in the sense of
`Turing.MultiTapeTM.ComputesInTimeAndSpace`. -/
theorem computesInTimeAndSpace (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t s := by
  obtain ⟨p, hh, hl, ht, hs⟩ := computesTidily_iff.mp h
  have hhead : p.head = tm.initCfg input := hh.trans (Cfg.init_eq_wordsCfg tm.q₀ input).symm
  have hrun : tm.runFrom (tm.initCfg input) p.time = wordsCfg input none (fun _ => []) output :=
    hhead ▸ (runPath_apply_eq_runFrom p (.last _)).symm.trans hl
  have hhalt : (tm.runFrom (tm.initCfg input) p.time).Halted := by rw [hrun]; rfl
  exact ⟨⟨p.time, hhalt, by rw [hrun]; rfl⟩,
    runsInTime_of_halted (runFrom_eq_of_halt tm _ ht hhalt ▸ hhalt),
    runsInSpace_of_runPath hhead (by rw [hl]; rfl) hs⟩

/-- A tidy computation within `t` steps emits at most `t` symbols. -/
theorem length_output_le (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    output.length ≤ t := by
  obtain ⟨p, hh, hl, ht, -⟩ := computesTidily_iff.mp h
  simpa [hh, hl, wordsCfg] using p.length_output_last_le.trans (Nat.add_le_add_left ht _)

/-- A tidy computation stays tidy with more work tapes, at one cell per added tape. -/
theorem extendTapes {k' : ℕ} (h : tm.ComputesTidilyInTimeAndSpace input output t s)
    (e : Fin k ↪ Fin k') :
    (tm.extendTapes e).ComputesTidilyInTimeAndSpace input output t (s + (k' - k)) := by
  refine (TransformsTapes.extendTapes h e).imp (fun _ _ ⟨hin, hws⟩ => ⟨hin, by subst hws; rfl⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨⟨hv, hout⟩, hx⟩ => ⟨funext fun l => ?_, hout⟩) le_rfl le_rfl
  by_cases hl : l ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hl
    exact congrFun hv j
  · rw [hx l hl, hws]

end ComputesTidilyInTimeAndSpace

end Turing.MultiTapeTM


