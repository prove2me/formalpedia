-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyZeroSpace
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyZeroSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:45.534685+00:00
-- url     : https://prove2.me/theorems/cc293096-a9d7-4c27-a228-c881e4fe7a10
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace — Tidiness is free at zero space
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A machine that runs in zero space has no work tapes
--   (`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_no_work_tapes`), so the only part of its
--   final configuration that can differ from the start is the input head. Following it with
--   `Turing.MultiTapeTM.rewindInput` moves that head back, which makes the computation tidy in the
--   sense of `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.tidyCopy`: the identity, as a tidy machine without work tapes.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInTimeAndSpace`: a function
--     computable in time `t` and zero space is computable tidily in time `2 * t + 2` and zero space.
--   * `Turing.MultiTapeTM.computableTidilyInTimeAndSpace_id`: the identity is tidily computable in
--     linear time and zero space.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyZeroSpace`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/TidyZeroSpace.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: submitted #1138 @b1635b2e
-- The section on the identity (`tidyCopy`) is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZeroSpace
public import Mathlib.Data.Finite.Sum
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Id
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tidiness is free at zero space

A machine that runs in zero space has no work tapes
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_no_work_tapes`), so the only part of its
final configuration that can differ from the start is the input head. Following it with
`Turing.MultiTapeTM.rewindInput` moves that head back, which makes the computation tidy in the
sense of `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`.

## Main definitions

* `Turing.MultiTapeTM.tidyCopy`: the identity, as a tidy machine without work tapes.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInTimeAndSpace`: a function
  computable in time `t` and zero space is computable tidily in time `2 * t + 2` and zero space.
* `Turing.MultiTapeTM.computableTidilyInTimeAndSpace_id`: the identity is tidily computable in
  linear time and zero space.
-/

namespace Turing.MultiTapeTM

/-- A function computable in time `t` and zero space is computable tidily in time `2 * t + 2` and
zero space: the machine has no work tapes, so it suffices to rewind the input head. -/
public theorem ComputableInTimeAndSpace.computableTidilyInTimeAndSpace {α β : Type*}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {t : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t (fun _ => 0)) :
    ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 2 * t a + 2) (fun _ => 0) := by
  rcases isEmpty_or_nonempty α with _ | _
  · exact ⟨0, Unit, inferInstance, nop 0 Bool, isEmptyElim⟩
  · obtain ⟨State, hfin, tm, htm⟩ := h.exists_no_work_tapes
    exact ⟨0, State ⊕ RewindState, inferInstance, tm.seq (rewindInput Bool),
      fun a => (htm a).computesTidily_seq_rewindInput⟩

/-- The identity is tidily computable in time linear in the length of the input and zero space. -/
public theorem computableTidilyInTimeAndSpace_id {α : Type*} {enc : α ↪ List Bool} :
    ComputableTidilyInTimeAndSpace (id : α → α) enc enc
      (fun a => 2 * (enc a).length + 4) (fun _ => 0) :=
  ⟨0, _, inferInstance, tidyCopy Bool, fun a => computesTidily_tidyCopy (enc a)⟩

end Turing.MultiTapeTM


