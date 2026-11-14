-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeUnaryPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeUnaryPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:09.986704+00:00
-- url     : https://prove2.me/theorems/00dd6b57-6693-4595-ab02-206f77667831
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives — Direct unary degree primitives
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Streaming machines implement successor and saturating predecessor with linear cost and output
--   growth. No higher tidy computability calculus is used.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeUnaryPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/DegreeUnaryPrimitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_UnaryMachines
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_WordPredicates
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeComposition
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Primitives

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct unary degree primitives

Streaming machines implement successor and saturating predecessor with linear cost and output
growth. No higher tidy computability calculus is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM
namespace Internal.Unary

/-- Drop the first unary symbol and copy the remaining input. -/
private def predT : Transducer Bool Bool where
  q₀ := false
  step seen b := (true, if seen then [b] else [])
  final _ := []
  length_step_le seen _ := by cases seen <;> simp
  length_final_le _ := by simp

private lemma predT_run_true (w : List Bool) : predT.run true w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [b] ++ predT.run true w = b :: w
    simp [ih]

private lemma predT_run (w : List Bool) : predT.run false w = w.tail := by
  cases w with
  | nil => rfl
  | cons b w =>
    change [] ++ predT.run true w = w
    simp [predT_run_true]

end Internal.Unary
namespace ComputableInDegree
open Internal.Unary

/-- Successor on unary natural numbers, including the empty encoding of zero. -/
theorem unary_succ : ComputableInDegree (· + 1) encUnary encUnary 1 1 := by
  refine ⟨⟨fun n => 2 * (encUnary n).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, unarySuccTransducer.toTM, fun n => ?_⟩,
    ⟨1, fun n => by simp⟩⟩
  have heq : encUnary (n + 1) =
      unarySuccTransducer.run unarySuccTransducer.q₀ (encUnary n) := by
    rw [show unarySuccTransducer.q₀ = true from rfl, (unarySuccRun _).1]
    simp [List.replicate_succ]
  simpa only [heq] using unarySuccTransducer.computesInTimeAndSpace_toTM (encUnary n)

/-- Saturating predecessor on unary natural numbers. -/
theorem unary_pred : ComputableInDegree (· - 1) encUnary encUnary 1 1 := by
  refine ⟨⟨fun n => 2 * (encUnary n).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, predT.toTM, fun n => ?_⟩,
    ⟨1, fun n => by simp; omega⟩⟩
  have heq : encUnary (n - 1) = predT.run predT.q₀ (encUnary n) := by
    rw [show predT.q₀ = false from rfl, predT_run]
    cases n <;> simp [List.replicate_succ]
  simpa only [heq] using predT.computesInTimeAndSpace_toTM (encUnary n)

/-- The unary zero test preserves the original linear cost and output-degree contract. -/
theorem unary_isZero :
    ComputableInDegree (fun n => decide (n = 0)) encUnary encBool 1 1 := by
  have hn : ComputableInDegree (fun n => decide (n ≠ 0)) encUnary encBool 1 0 := by
    refine ⟨⟨fun n => 2 * (encUnary n).length + 3, fun _ => 0,
      ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
      0, _, inferInstance, Internal.WordPredicates.nonemptyT.toTM, fun n => ?_⟩,
      ⟨1, fun n => by simp⟩⟩
    have heq : encBool (decide (n ≠ 0)) = Internal.WordPredicates.nonemptyT.run
        Internal.WordPredicates.nonemptyT.q₀ (encUnary n) := by
      cases n with
      | zero => rfl
      | succ n =>
        change [true] = [true] ++ Internal.WordPredicates.nonemptyT.run true
          (List.replicate n true)
        rw [Internal.WordPredicates.nonemptyT_run_true, List.append_nil]
    simpa only [heq] using
      Internal.WordPredicates.nonemptyT.computesInTimeAndSpace_toTM (encUnary n)
  have hnot := (of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp hn
  have hz : ComputableInDegree (fun n => decide (n = 0)) encUnary encBool 1 0 := by
    convert hnot using 1 <;> simp [Function.comp_def]
  exact ⟨hz.1, hz.2.mono_deg (by decide)⟩

end ComputableInDegree
end Turing.MultiTapeTM


