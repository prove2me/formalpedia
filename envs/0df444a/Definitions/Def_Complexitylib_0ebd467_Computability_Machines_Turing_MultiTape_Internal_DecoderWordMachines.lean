-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderWordMachines
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderWordMachines
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:38.237868+00:00
-- url     : https://prove2.me/theorems/302b0bad-77bc-4b62-9496-d106285fe5c7
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines — Streaming machines for total decoder leaves
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Both transducers are total on malformed as well as encoded words. They use no work tapes and
--   the standard transducer clock includes every input symbol.
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderWordMachines`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/DecoderWordMachines.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Streaming machines for total decoder leaves

Both transducers are total on malformed as well as encoded words. They use no work tapes and
the standard transducer clock includes every input symbol.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.DecoderWords

/-- Replace each input symbol by one unary symbol. -/
def unaryLengthT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [true])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- The emitted unary word records the length of every input word. -/
theorem unaryLengthT_run (w : List Bool) :
    unaryLengthT.run () w = List.replicate w.length true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [true] ++ unaryLengthT.run () w = List.replicate (w.length + 1) true
    rw [ih, List.replicate_succ]
    rfl

/-- Read the first symbol, returning the fixed default on empty input. -/
def headDefaultT (default : Bool) : Transducer Bool Bool where
  q₀ := false
  step seen b := (true, if seen then [] else [b])
  final seen := if seen then [] else [default]
  length_step_le seen _ := by cases seen <;> simp
  length_final_le seen := by cases seen <;> simp

/-- After seeing the first symbol, this transducer emits nothing further. -/
theorem headDefaultT_run_true (default : Bool) (w : List Bool) :
    (headDefaultT default).run true w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [] ++ (headDefaultT default).run true w = []
    simpa using ih

/-- The default applies exactly to empty input, with no resampling or partiality. -/
theorem headDefaultT_run (default : Bool) (w : List Bool) :
    (headDefaultT default).run false w = [w.headD default] := by
  cases w with
  | nil => rfl
  | cons b w =>
    change [b] ++ (headDefaultT default).run true w = [b]
    rw [headDefaultT_run_true, List.append_nil]

end Turing.MultiTapeTM.Internal.DecoderWords

namespace Turing.MultiTapeTM

/-- Drops the `false`s at the start of a word. -/
def dropFalsesT : Transducer Bool Bool where
  q₀ := false
  step
    | false, false => (false, [])
    | _, b => (true, [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

theorem dropFalsesT_run_true (w : List Bool) : dropFalsesT.run true w = w := by
  induction w with
  | nil => rfl
  | cons b w ih => exact congrArg (b :: ·) ih

theorem dropFalsesT_run (w : List Bool) : dropFalsesT.run false w = w.dropWhile (!·) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · exact ih
    · exact congrArg (true :: ·) (dropFalsesT_run_true w)

end Turing.MultiTapeTM


