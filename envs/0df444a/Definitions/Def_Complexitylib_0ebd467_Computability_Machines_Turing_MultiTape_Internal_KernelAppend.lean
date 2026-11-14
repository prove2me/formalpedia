-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelAppend
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelAppend
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:50.008165+00:00
-- url     : https://prove2.me/theorems/a04f091b-96b0-487c-bbb4-817d5d00bb90
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelAppend — The existing concatenation machine and its run theorem
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelAppend` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Machine declarations are moved from their original module without changing programs or resource
--   formulas. Higher computability-calculus theorems remain in the original facade.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelAppend`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelAppend.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Finite.Sum
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelFacts

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelAppend` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # The existing concatenation machine and its run theorem

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- Run `tm₁` and then `tm₂`, both with their work tapes padded to `max k₁ k₂`. -/
public noncomputable def appendTM (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (tm₂ : MultiTapeTM k₂ Symbol S₂) : MultiTapeTM (max k₁ k₂) Symbol (S₁ ⊕ S₂) :=
  (tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).seq
    (tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))

/-- If `tm₁` computes `y₁` from `x` tidily and `tm₂` computes `y₂` from `x` tidily, then
`appendTM tm₁ tm₂` computes `y₁ ++ y₂` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.append {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x y₁ y₂ : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x y₁ t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace x y₂ t₂ s₂) :
    (appendTM tm₁ tm₂).ComputesTidilyInTimeAndSpace x (y₁ ++ y₂) (t₁ + t₂)
      (s₁ + s₂ + 2 * max k₁ k₂) :=
  (transformsTapes_seq (h₁.extendTapes _) (h₂.extendTapes _)
    fun _ _ _ _ hP hQ => ⟨hP.1, hQ.1⟩).imp (fun _ _ h => h)
    (by rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩; exact ⟨hws, rfl⟩) le_rfl
    (by omega)

end Turing.MultiTapeTM


