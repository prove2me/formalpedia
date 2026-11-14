-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Append
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Append
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:23.464201+00:00
-- url     : https://prove2.me/theorems/e59ca4de-b5ea-469d-8b14-99dc90532531
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append — Concatenating the outputs of tidy computations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A tidy machine leaves its tapes as it found them, so a second tidy machine can run after it on the
--   same input. `appendTM tm₁ tm₂` runs `tm₁` and then `tm₂`; the outputs concatenate.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.appendTM`: the machine that runs two machines one after the other.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.append`: the outputs of two tidy computations
--     on the same input concatenate.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.append`: a function whose encoded value is the
--     concatenation of the encoded values of two tidily computable functions is tidily computable.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Append`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/Append.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelAppend
public import Mathlib.Data.Finite.Sum
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Concatenating the outputs of tidy computations

A tidy machine leaves its tapes as it found them, so a second tidy machine can run after it on the
same input. `appendTM tm₁ tm₂` runs `tm₁` and then `tm₂`; the outputs concatenate.

## Main definitions

* `Turing.MultiTapeTM.appendTM`: the machine that runs two machines one after the other.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.append`: the outputs of two tidy computations
  on the same input concatenate.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.append`: a function whose encoded value is the
  concatenation of the encoded values of two tidily computable functions is tidily computable.
-/

namespace Turing.MultiTapeTM

/-- If `f₁` and `f₂` are tidily computable and the encoded value of `g` is the concatenation of
their encoded values, then `g` is tidily computable within the sum of their bounds, plus a constant
for the space. -/
public theorem ComputableTidilyInTimeAndSpace.append {γ α₁ α₂ β : Type*} {encIn : γ ↪ List Bool}
    {enc₁ : α₁ ↪ List Bool} {enc₂ : α₂ ↪ List Bool} {encOut : β ↪ List Bool} {f₁ : γ → α₁}
    {f₂ : γ → α₂} {g : γ → β} {t₁ s₁ t₂ s₂ : γ → ℕ}
    (h₁ : ComputableTidilyInTimeAndSpace f₁ encIn enc₁ t₁ s₁)
    (h₂ : ComputableTidilyInTimeAndSpace f₂ encIn enc₂ t₂ s₂)
    (hg : ∀ x, encOut (g x) = enc₁ (f₁ x) ++ enc₂ (f₂ x)) :
    ∃ k, ComputableTidilyInTimeAndSpace g encIn encOut (fun x => t₁ x + t₂ x)
      (fun x => s₁ x + s₂ x + k) := by
  obtain ⟨k₁, S₁, _, tm₁, htm₁⟩ := h₁
  obtain ⟨k₂, S₂, _, tm₂, htm₂⟩ := h₂
  exact ⟨2 * max k₁ k₂, _, _, inferInstance, appendTM tm₁ tm₂,
    fun x => hg x ▸ (htm₁ x).append (htm₂ x)⟩

end Turing.MultiTapeTM


