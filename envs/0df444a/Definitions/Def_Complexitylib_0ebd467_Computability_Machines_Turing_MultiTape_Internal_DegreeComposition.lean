-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeComposition
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeComposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:12.903047+00:00
-- url     : https://prove2.me/theorems/69115355-5d71-46bc-8f1a-ec860a33adc4
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition — Direct composition at independent resource and output degrees
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The proof combines machine normal forms, retaining the separate output degree of each input
--   certificate. Adapted from the direct-construction experiment in #869 by
--   worker-claude-tidyspike-c4b0c164.
--
--   ### Main results
--
--   * `ComputableInDegree.comp`: resource degree `max d₁ (e₁ * d₂)` and output degree `e₁ * e₂`.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeComposition`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/DegreeComposition.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_NormalForm
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelComp

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct composition at independent resource and output degrees

The proof combines machine normal forms, retaining the separate output degree of each input
certificate. Adapted from the direct-construction experiment in #869 by
worker-claude-tidyspike-c4b0c164.

## Main results

* `ComputableInDegree.comp`: resource degree `max d₁ (e₁ * d₂)` and output degree `e₁ * e₂`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- **Composition**, through the machine-level composition of tidy machines. The intermediate word
is no longer than the time of the inner machine. -/
theorem comp {f : β → γ} {g : α → β} {d₁ e₁ d₂ e₂ : ℕ}
    (hf : ComputableInDegree f encMid encOut d₂ e₂)
    (hg : ComputableInDegree g encIn encMid d₁ e₁) :
    ComputableInDegree (f ∘ g) encIn encOut (max d₁ (e₁ * d₂)) (e₁ * e₂) := by
  have hl₁ := hg.2
  have hl₂ := hf.2
  obtain ⟨t₁, s₁, ht₁, hs₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.degree hg
  obtain ⟨t₂, s₂, ht₂, hs₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.degree hf
  have hm : DegreeBounded (fun a => (encIn a).length) (fun a => (encMid (g a)).length) d₁ :=
    ht₁.mono fun a => (h₁ a).length_output_le
  have hd₁ : d₁ ≤ max d₁ (e₁ * d₂) := le_max_left _ _
  exact ⟨⟨_, _, ((ht₁.add_max (ht₂.comp hl₁)).add ((hm.smul 4).mono_deg hd₁)).add_const 9,
    ((hs₁.add_max (hs₂.comp hl₁)).add ((hm.smul 5).mono_deg hd₁)).add_const _,
    _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => ((h₁ a).comp (h₂ (g a)) true).computesInTimeAndSpace⟩, hl₂.comp hl₁⟩

end Turing.MultiTapeTM.ComputableInDegree


