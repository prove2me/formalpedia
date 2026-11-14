-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_UnaryMachines
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_UnaryMachines
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:50.82646+00:00
-- url     : https://prove2.me/theorems/9bf1a61f-7eec-455c-8a8b-da6f720b137a
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.UnaryMachines — Shared unary machine constructors
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.UnaryMachines` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The finite-state successor machine is shared by direct Degree and polynomial-time providers.
--   Extracted unchanged from the direct list provider by worker `/root/review_560`.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_UnaryMachines`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/UnaryMachines.lean

/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.UnaryMachines` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Shared unary machine constructors

The finite-state successor machine is shared by direct Degree and polynomial-time providers.
Extracted unchanged from the direct list provider by worker `/root/review_560`.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.Unary

/-- Prefix a unary symbol, including on empty input. -/
def unarySuccTransducer : Transducer Bool Bool where
  q₀ := true
  step q bit := (false, if q then [true, bit] else [bit])
  final q := if q then [true] else []
  length_step_le q bit := by cases q <;> simp
  length_final_le q := by cases q <;> simp

/-- The successor transducer prefixes once, then copies every remaining symbol. -/
theorem unarySuccRun (word : List Bool) :
    unarySuccTransducer.run true word = true :: word ∧
      unarySuccTransducer.run false word = word := by
  induction word with
  | nil => constructor <;> rfl
  | cons bit word ih =>
    constructor
    · change [true, bit] ++ unarySuccTransducer.run false word = true :: bit :: word
      rw [ih.2]
      rfl
    · change [bit] ++ unarySuccTransducer.run false word = bit :: word
      rw [ih.2]
      rfl

end Turing.MultiTapeTM.Internal.Unary


