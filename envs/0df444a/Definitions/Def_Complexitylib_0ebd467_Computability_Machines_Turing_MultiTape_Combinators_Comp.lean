-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Comp
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Comp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:35.852111+00:00
-- url     : https://prove2.me/theorems/abe53d91-ff02-486f-8b32-0fa8e1a88d10
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp — Composing tidy computations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `tm₂.comp tm₁ mark` runs `tm₁` with its output written to a work tape, then runs `tm₂` reading its
--   input from that tape, and finally clears the tape. If both machines compute tidily, so does the
--   composition. Its time is the sum of the two times plus a term linear in the length of the
--   intermediate word; so is its space, since the intermediate word is kept on a work tape.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.comp`: the composed machine.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.comp`: tidy computations compose.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp`: tidily computable functions compose.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp_linear`: the same, with the overhead a
--     constant multiple of the length of the intermediate word plus one.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp'`: the same, with the length of the
--     intermediate word bounded by the time of the inner function.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.comp`: the same for bounds of the
--     input length, given a bound `l` on the length of the intermediate word.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace_comp`: hence `f ∘ g`
--     is computable in the sense of `Turing.MultiTapeTM.ComputableInTimeAndSpace`.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.computableInTimeAndSpaceOfLength_comp`:
--     the same for bounds of the input length.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Comp`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/Comp.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: submitted #1111 @3441fa81
-- `transformsTapes_clearWork_only` and `ComputableTidilyInTimeAndSpace.comp_linear` are from
-- crei:crei/tidy-universal @7f7c0696 (unsubmitted).

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelComp
public import Mathlib.Data.Finite.Sum
public import Definitions.Def_Cslib_254e30e_Foundations_Data_Fin_Tuple
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ClearWork
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_InputFromTape
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Composing tidy computations

`tm₂.comp tm₁ mark` runs `tm₁` with its output written to a work tape, then runs `tm₂` reading its
input from that tape, and finally clears the tape. If both machines compute tidily, so does the
composition. Its time is the sum of the two times plus a term linear in the length of the
intermediate word; so is its space, since the intermediate word is kept on a work tape.

## Main definitions

* `Turing.MultiTapeTM.comp`: the composed machine.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.comp`: tidy computations compose.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp`: tidily computable functions compose.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp_linear`: the same, with the overhead a
  constant multiple of the length of the intermediate word plus one.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp'`: the same, with the length of the
  intermediate word bounded by the time of the inner function.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.comp`: the same for bounds of the
  input length, given a bound `l` on the length of the intermediate word.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace_comp`: hence `f ∘ g`
  is computable in the sense of `Turing.MultiTapeTM.ComputableInTimeAndSpace`.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.computableInTimeAndSpaceOfLength_comp`:
  the same for bounds of the input length.
-/

namespace Turing.MultiTapeTM

/-- If `g` and `f` are tidily computable, so is `f ∘ g`, in the sum of their times and spaces plus
a term linear in the length of the intermediate word `encMid (g a)`. -/
public theorem ComputableTidilyInTimeAndSpace.comp {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => t₁ a + t₂ (g a) + 4 * (encMid (g a)).length + 9)
      (fun a => s₁ a + s₂ (g a) + 5 * (encMid (g a)).length + c) := by
  obtain ⟨k₁, S₁, _, tm₁, h₁⟩ := hg
  obtain ⟨k₂, S₂, _, tm₂, h₂⟩ := hf
  exact ⟨6 * max k₁ k₂ + 20, _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => (h₁ a).comp (h₂ (g a)) true⟩

-- vendored: crei:crei/tidy-universal states `ComputableTidilyInTimeAndSpace.comp` with these
-- bounds; cslib #1111 states it with explicit constants, which this follows from
/-- If `g` and `f` are tidily computable, so is `f ∘ g`, in the sum of their times and spaces plus
a constant multiple of the length of the intermediate word `encMid (g a)` plus one. -/
public theorem ComputableTidilyInTimeAndSpace.comp_linear {α β γ : Type*} {g : α → β}
    {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => t₁ a + t₂ (g a) + c * ((encMid (g a)).length + 1))
      (fun a => s₁ a + s₂ (g a) + c * ((encMid (g a)).length + 1)) := by
  obtain ⟨c, h⟩ := hf.comp hg
  refine ⟨c + 9, h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · have := Nat.le_mul_of_pos_right c (by omega : 0 < (encMid (g a)).length + 1)
    rw [Nat.add_mul]
    omega

/-- If `g` and `f` are tidily computable, so is `f ∘ g`: the intermediate word is no longer than
the time of `g`. -/
public theorem ComputableTidilyInTimeAndSpace.comp' {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => 5 * t₁ a + t₂ (g a) + 9) (fun a => s₁ a + s₂ (g a) + 5 * t₁ a + c) := by
  obtain ⟨c, h⟩ := hf.comp hg
  obtain ⟨_, _, _, _, h₁⟩ := hg
  refine ⟨c, h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · have := (h₁ a).length_output_le
    omega

/-- If `g` and `f` are tidily computable in time `t₁`, `t₂` and space `s₁`, `s₂` of the length of
their input, for monotone `t₂` and `s₂`, and the output of `g` on inputs of length `n` has length at
most `l n`, then `f ∘ g` is tidily computable with bounds depending on `t₂ (l n)`, `s₂ (l n)` and
`l n`. -/
public theorem ComputableTidilyInTimeAndSpaceOfLength.comp {α β γ : Type*} {g : α → β}
    {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {l t₁ s₁ t₂ s₂ : ℕ → ℕ} (ht : Monotone t₂) (hs : Monotone s₂)
    (hl : ∀ a, (encMid (g a)).length ≤ l (encIn a).length)
    (hf : ComputableTidilyInTimeAndSpaceOfLength f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpaceOfLength g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpaceOfLength (f ∘ g) encIn encOut
      (fun n => t₁ n + t₂ (l n) + 4 * l n + 9) (fun n => s₁ n + s₂ (l n) + 5 * l n + c) := by
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp hf hg
  refine ⟨c, h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · have := hl a
    have := ht (hl a)
    have := hs (hl a)
    beta_reduce
    omega

/-- If `g` and `f` are tidily computable, then `f ∘ g` is computable. -/
public theorem ComputableTidilyInTimeAndSpace.computableInTimeAndSpace_comp {α β γ : Type*}
    {g : α → β} {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => 5 * t₁ a + t₂ (g a) + 9) (fun a => s₁ a + s₂ (g a) + 5 * t₁ a + c) :=
  let ⟨c, h⟩ := hf.comp' hg
  ⟨c, h.computableInTimeAndSpace⟩

/-- If `g` and `f` are tidily computable in time `t₁`, `t₂` and space `s₁`, `s₂` of the length of
their input, for monotone `t₂` and `s₂`, and the output of `g` on inputs of length `n` has length at
most `l n`, then `f ∘ g` is computable. -/
public theorem ComputableTidilyInTimeAndSpaceOfLength.computableInTimeAndSpaceOfLength_comp
    {α β γ : Type*} {g : α → β} {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {l t₁ s₁ t₂ s₂ : ℕ → ℕ} (ht : Monotone t₂) (hs : Monotone s₂)
    (hl : ∀ a, (encMid (g a)).length ≤ l (encIn a).length)
    (hf : ComputableTidilyInTimeAndSpaceOfLength f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpaceOfLength g encIn encMid t₁ s₁) :
    ∃ c, ComputableInTimeAndSpaceOfLength (f ∘ g) encIn encOut
      (fun n => t₁ n + t₂ (l n) + 4 * l n + 9) (fun n => s₁ n + s₂ (l n) + 5 * l n + c) :=
  let ⟨c, h⟩ := comp ht hs hl hf hg
  ⟨c, ComputableTidilyInTimeAndSpace.computableInTimeAndSpace h⟩

end Turing.MultiTapeTM


