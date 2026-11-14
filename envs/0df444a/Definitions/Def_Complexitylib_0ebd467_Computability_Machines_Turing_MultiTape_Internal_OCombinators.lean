-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCombinators
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCombinators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:58.155642+00:00
-- url     : https://prove2.me/theorems/4e5849cb-b969-41fc-b1f8-0acd25987008
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators — Direct charged resource combinators
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Composition with a linear outer computation preserves independent time/workspace budgets:
--   the inner machine's clock bounds the intermediate word for time, and its explicit output charge
--   bounds that same word for workspace. Concatenation and framed pairing retain their output charge.
--   All construction proofs use only plain certificates and machine-level combinators.
--
--   **Contents.** The module is published as a whole: 14 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCombinators`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/OCombinators.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreePrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelAppend
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Combinators_AlmostConstant
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct charged resource combinators

Composition with a linear outer computation preserves independent time/workspace budgets:
the inner machine's clock bounds the intermediate word for time, and its explicit output charge
bounds that same word for workspace. Concatenation and framed pairing retain their output charge.
All construction proofs use only plain certificates and machine-level combinators.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInO

universe u
variable {α β γ δ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {T S : α → ℕ}

/-- The encoded value is within the time bound, since the machine writes it. -/
theorem length_le_time {f : α → β} (h : ComputableInO f encIn encMid T S) :
    ∃ c, ∀ a, (encMid (f a)).length ≤ c * (T a + 1) :=
  let ⟨c, ⟨_, _, _, _, htm⟩, _⟩ := h
  ⟨c, fun a => (htm a).length_output_le⟩

/-- A common linear certificate includes the output bound through its actual clock. -/
theorem of_linear {f : α → β} {e : ℕ} (h : ComputableInDegree f encIn encMid 1 e) :
    ComputableInO f encIn encMid (fun a => (encIn a).length) (fun a => (encIn a).length) :=
  h.inO_one

/-- A linear outer computation preserves both independent bounds of the inner certificate. -/
theorem comp_linear {f : β → γ} {g : α → β}
    (hf : ComputableInO f encMid encOut (fun b => (encMid b).length)
      (fun b => (encMid b).length)) (hg : ComputableInO g encIn encMid T S) :
    ComputableInO (f ∘ g) encIn encOut T S := by
  exact (hf.comp hg).weaken
    (BigOLe.add (.refl _) (show (fun a => (encMid (g a)).length) ≼ T from hg.length_le_time))
    (BigOLe.add (.refl _) (show (fun a => (encMid (g a)).length) ≼ S from hg.length_le))

private theorem sumBound (a b k x y : ℕ) :
    a * (x + 1) + b * (y + 1) + k ≤ (a + b + k) * (x + y + 1) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Concatenate two computed encodings, retaining the sum of both charged bounds. -/
theorem append {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    {T₁ S₁ T₂ S₂ : α → ℕ}
    (h₁ : ComputableInO f₁ encIn encMid T₁ S₁)
    (h₂ : ComputableInO f₂ encIn enc₂ T₂ S₂)
    (hg : ∀ a, encOut (g a) = encMid (f₁ a) ++ enc₂ (f₂ a)) :
    ComputableInO g encIn encOut (fun a => T₁ a + T₂ a) (fun a => S₁ a + S₂ a) := by
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, hm₁⟩, hl₁⟩ := Internal.NormalForm.inO h₁
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, hm₂⟩, hl₂⟩ := Internal.NormalForm.inO h₂
  let K := 2 * max k₁ k₂
  refine ⟨c₁ + c₂ + K, ⟨_, _, inferInstance, appendTM tm₁ tm₂, fun a => ?_⟩, fun a => ?_⟩
  · rw [hg a]
    refine (((hm₁ a).append (hm₂ a)).mono ?_ ?_).computesInTimeAndSpace
    · have := sumBound c₁ c₂ K (T₁ a) (T₂ a)
      beta_reduce
      omega
    · exact sumBound c₁ c₂ K (S₁ a) (S₂ a)
  · rw [hg a, List.length_append]
    have hleft := hl₁ a
    have hright := hl₂ a
    have := sumBound c₁ c₂ K (S₁ a) (S₂ a)
    beta_reduce
    omega

/-- A fixed output is charged within constant workspace, even when its input is unbounded. -/
theorem constZero (b : β) :
    ComputableInO (fun _ : α => b) encIn encMid (fun a => (encIn a).length) (fun _ => 0) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encMid) b
  refine of_bounds hc (c + (encMid b).length) (fun a => ?_) (fun _ => by simp) (fun _ => ?_)
  · exact (Nat.le_add_right _ _).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos (encIn a).length))
  · simp only [zero_add, mul_one]
    omega

/-- A fixed output fits the input-length charged workspace bound. -/
theorem const (b : β) :
    ComputableInO (fun _ : α => b) encIn encMid (fun a => (encIn a).length)
      (fun a => (encIn a).length) :=
  (constZero b).mono_le (fun _ => le_rfl) (fun _ => Nat.zero_le _)

/-- Standard framed pairing, with the sum of the original time and charged workspace bounds. -/
theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁} {g : α → β₂} {T₁ S₁ T₂ S₂ : α → ℕ}
    (hf : ComputableInO f encIn enc₁ T₁ S₁) (hg : ComputableInO g encIn enc₂ T₂ S₂) :
    ComputableInO (fun a => (f a, g a)) encIn (encPair enc₁ enc₂)
      (fun a => T₁ a + T₂ a) (fun a => S₁ a + S₂ a) := by
  have hframe : ComputableInO (fun x : β₁ => x) enc₁ (encFramed enc₁)
      (fun a => (enc₁ a).length) (fun a => (enc₁ a).length) :=
    of_linear (.of_frame fun _ => rfl)
  exact (hframe.comp_linear hf).append hg fun _ => rfl

/-- Copy an encoded value without changing its independent representation. -/
theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableInO f encIn encMid (fun a => (encIn a).length) (fun a => (encIn a).length) :=
  of_linear (.of_eq h)

/-- The first component of a standard framed pair, with linear charged bounds. -/
theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInO Prod.fst (encPair enc₁ enc₂) enc₁
      (fun p => (encPair enc₁ enc₂ p).length) (fun p => (encPair enc₁ enc₂ p).length) :=
  of_linear (.fst enc₁ enc₂)

/-- The second component of a standard framed pair, with linear charged bounds. -/
theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInO Prod.snd (encPair enc₁ enc₂) enc₂
      (fun p => (encPair enc₁ enc₂ p).length) (fun p => (encPair enc₁ enc₂ p).length) :=
  of_linear (.snd enc₁ enc₂)

/-- Project the first computed component without changing either independent budget. -/
theorem fst' {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (h : ComputableInO f encIn (encPair enc₁ enc₂) T S) :
    ComputableInO (fun a => (f a).1) encIn enc₁ T S := (fst enc₁ enc₂).comp_linear h

/-- Project the second computed component without changing either independent budget. -/
theorem snd' {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (h : ComputableInO f encIn (encPair enc₁ enc₂) T S) :
    ComputableInO (fun a => (f a).2) encIn enc₂ T S := (snd enc₁ enc₂).comp_linear h

/-- Reinterpret an encoding along an equivalence, retaining the same machine and budgets. -/
theorem of_equiv {δ : Type*} {f : α → β} (h : ComputableInO f encIn encMid T S) (e : δ ≃ α) :
    ComputableInO (f ∘ e) (encOfEquiv e encIn) encMid (T ∘ e) (S ∘ e) :=
  h.of_encIn_eq e fun _ => rfl

end Turing.MultiTapeTM.ComputableInO


