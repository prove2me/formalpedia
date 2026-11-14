-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FrameMachines
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FrameMachines
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:21.600678+00:00
-- url     : https://prove2.me/theorems/e7c04b92-84da-4d80-b33f-b6c7a911d8b4
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines — Shared machines for reading framed words
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These original finite-state machines and run laws preserve all-word behavior, including empty
--   and incomplete frames. Their source is moved unchanged from Encodings.Basic.
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FrameMachines`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/FrameMachines.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTransducer

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Shared machines for reading framed words

These original finite-state machines and run laws preserve all-word behavior, including empty
and incomplete frames. Their source is moved unchanged from Encodings.Basic.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.FrameMachines

/-- The states of a transducer reading a framed word: expecting a marker, expecting a symbol, or
past the frame. -/
inductive FrameState
  | marker
  | bit
  | done

instance : Finite FrameState :=
  Finite.of_surjective (fun b : Option Bool => b.elim .done fun b => if b then .marker else .bit)
    fun q => by cases q; exacts [⟨some true, rfl⟩, ⟨some false, rfl⟩, ⟨none, rfl⟩]

/-- Emits the word framed at the start of its input (`keep = true`), or what follows the frame
(`keep = false`). -/
@[simps q₀ step final]
def readFrameT (keep : Bool) : Transducer Bool FrameState where
  q₀ := .marker
  step
    | .marker, true => (.bit, [])
    | .marker, false => (.done, [])
    | .bit, b => (.marker, if keep then [b] else [])
    | .done, b => (.done, if keep then [] else [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> cases keep <;> simp
  length_final_le _ := by simp

lemma readFrameT_run_done (keep : Bool) (v : List Bool) :
    (readFrameT keep).run .done v = if keep then [] else v := by
  induction v <;> cases keep <;> simp_all

lemma readFrameT_run_true : ∀ v, (readFrameT true).run .marker v = unframe v
  | [] | [true] => rfl
  | false :: v => by simp [unframe, readFrameT_run_done]
  | true :: b :: v => by simp [unframe, readFrameT_run_true v]

lemma readFrameT_run_false : ∀ v, (readFrameT false).run .marker v = dropFrame v
  | [] | [true] => rfl
  | false :: v => by simp [dropFrame, readFrameT_run_done]
  | true :: b :: v => by simp [dropFrame, readFrameT_run_false v]

end Turing.MultiTapeTM.Internal.FrameMachines

namespace Turing.MultiTapeTM.Encodings

-- vendored: expose `frameT` and `frameT_run` for `computableInLogSpace_frame`; private upstream.
/-- Frames its input. -/
@[simps q₀ step final]
public def frameT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [true, b])
  final _ := [false]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

public lemma frameT_run (v : List Bool) : frameT.run () v = frame v := by
  induction v <;> simp [*]

end Turing.MultiTapeTM.Encodings


