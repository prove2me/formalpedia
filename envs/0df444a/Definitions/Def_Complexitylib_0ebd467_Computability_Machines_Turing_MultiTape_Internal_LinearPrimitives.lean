-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:40:08.025649+00:00
-- url     : https://prove2.me/theorems/c6b5feb9-4f53-46e3-86e9-ffb16878f360
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives — Degree-one certificates from finite transducers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The shared streaming machines give linear time and zero workspace. The actual runtime bounds
--   encoded output growth, so these are degree-1/1 certificates. Copy, constant and composition rules
--   come from the existing degree calculus.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/LinearPrimitives.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FrameMachines
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTransducer
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_NormalForm
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeComposition
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Primitives
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Combinators_AlmostConstant
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Combinators_Id
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Degree-one certificates from finite transducers

The shared streaming machines give linear time and zero workspace. The actual runtime bounds
encoded output growth, so these are degree-1/1 certificates. Copy, constant and composition rules
come from the existing degree calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A finite transducer gives a common linear bound from its actual clock and zero workspace. -/
theorem of_transducer {Q : Type} [Finite Q] (τ : Transducer Bool Q) {f : α → β}
    (h : ∀ a, encMid (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableInDegree f encIn encMid 1 1 := by
  apply of_bounds (t := fun a => 2 * (encIn a).length + 3) (s := fun _ => 0)
    ⟨3, fun _ => by simp only [pow_one]; omega⟩ (DegreeBounded.const 0)
  exact ⟨0, _, inferInstance, τ.toTM, fun a => by
    rw [h a]
    exact τ.computesInTimeAndSpace_toTM (encIn a)⟩

/-- Frame the encoded input using the shared streaming machine. -/
theorem of_frame {f : α → β} (h : ∀ a, encMid (f a) = frame (encIn a)) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer Encodings.frameT fun a => (h a).trans (Encodings.frameT_run _).symm

/-- Read the first framed word, including the prescribed behavior on incomplete frames. -/
theorem of_unframe {f : α → β} (h : ∀ a, encMid (f a) = unframe (encIn a)) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Internal.FrameMachines.readFrameT true) fun a =>
    (h a).trans (Internal.FrameMachines.readFrameT_run_true _).symm

/-- Drop the first framed word using the same shared parser. -/
theorem of_dropFrame {f : α → β} (h : ∀ a, encMid (f a) = dropFrame (encIn a)) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Internal.FrameMachines.readFrameT false) fun a =>
    (h a).trans (Internal.FrameMachines.readFrameT_run_false _).symm

end Turing.MultiTapeTM.ComputableInDegree


