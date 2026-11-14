-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:39.201189+00:00
-- url     : https://prove2.me/theorems/0377b84e-dce5-47d2-aa78-6e7060f0e5db
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts — Clock, output and workspace facts for plain machines
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These facts are moved unchanged from the former polynomial-time bridge module. They use only
--   machine semantics and carry no higher computability-calculus dependency.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/ResourceFacts.lean

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
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Clock, output and workspace facts for plain machines

These facts are moved unchanged from the former polynomial-time bridge module. They use only
machine semantics and carry no higher computability-calculus dependency.
-/

@[expose] public section
namespace Turing.MultiTapeTM

section Machine

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State}

/-- A computation within `t` steps needs no separate space bound: it visits at most `k t + k`
work-tape cells. -/
theorem ComputesInTimeAndSpace.space_linear {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t (k * t + k) :=
  ⟨h.1, h.2.1, runsInSpace_of_halted (runsInTime_iff_halted.mp h.2.1)
    ((MultiTapeNTM.RunPath.space_le_mul_time_add_one (.ofDeterministic tm _ t)).trans_eq
      (Nat.mul_add_one _ _))⟩

/-- A computation within `t` steps emits at most `t` symbols. -/
theorem ComputesInTimeAndSpace.length_output_le {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) : output.length ≤ t := by
  obtain ⟨⟨u, hu, rfl⟩, ht, -⟩ := h
  have ht := runsInTime_iff_halted.mp ht
  have heq : tm.runFrom (tm.initCfg input) u = tm.runFrom (tm.initCfg input) t := by
    rcases le_total u t with hut | htu
    · exact (runFrom_eq_of_halt tm _ hut hu).symm
    · exact runFrom_eq_of_halt tm _ htu ht
  rw [heq]
  simpa using tm.length_output_runFrom_le (tm.initCfg input) t

/-- **An output computed without bounds is computed within bounds**: the time at which the machine
halts, and the space it has used by then. -/
theorem Computes.exists_computesInTimeAndSpace {input output : List Symbol}
    (h : tm.Computes input output) : ∃ t s, tm.ComputesInTimeAndSpace input output t s :=
  let ⟨u, hu, _⟩ := h
  ⟨u, _, h, runsInTime_of_halted hu, runsInSpace_of_halted hu le_rfl⟩

end Machine

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function computable within time `t` is computable within time `t` and space `c t + c`, for
a constant `c`: the number of work tapes of the machine. -/
theorem ComputableInTimeAndSpace.exists_space_linear {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ∃ c, ComputableInTimeAndSpace f encIn encOut t fun a => c * t a + c :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨k, k, State, hfinite, tm, fun a => (htm a).space_linear⟩

/-- The encoded values of a function computable within time `t` have length at most `t`. -/
theorem ComputableInTimeAndSpace.length_le {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (a : α) : (encOut (f a)).length ≤ t a :=
  let ⟨_, _, _, _, htm⟩ := h
  (htm a).length_output_le

end Turing.MultiTapeTM


