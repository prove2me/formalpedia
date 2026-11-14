-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_WordPredicates
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_WordPredicates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:48.659194+00:00
-- url     : https://prove2.me/theorems/c2b0243d-2f9f-424d-a2b9-400f36cf2ad0
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.WordPredicates — Shared finite-state word predicates
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.WordPredicates` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The nonempty-word transducer is shared by direct Option and unary Degree certificates. Its
--   machine clocks include the whole runtime input; it uses no work tapes.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_WordPredicates`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/WordPredicates.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.WordPredicates` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Shared finite-state word predicates

The nonempty-word transducer is shared by direct Option and unary Degree certificates. Its
machine clocks include the whole runtime input; it uses no work tapes.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.WordPredicates

/-- Emit a single Boolean indicating whether the input contains a symbol. -/
def nonemptyT : Transducer Bool Bool where
  q₀ := false
  step q _ := (true, if q then [] else [true])
  final q := if q then [] else [false]
  length_step_le q _ := by cases q <;> simp
  length_final_le q := by cases q <;> simp

/-- After the first input symbol, no further output is emitted. -/
lemma nonemptyT_run_true (w : List Bool) : nonemptyT.run true w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [] ++ nonemptyT.run true w = []
    simpa using ih

end Turing.MultiTapeTM.Internal.WordPredicates


