-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:40:07.275719+00:00
-- url     : https://prove2.me/theorems/8be0a022-63a6-40d9-8d72-f45e344d4349
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives — Asymptotic composition with explicit intermediate storage
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The same realizing machine is normalized within the internal construction proof. Composition
--   first accounts for the stored intermediate word explicitly in `ComputableInBigO`. The charged
--   `ComputableInO` rule then absorbs that word using its separate output-growth bound.
--   The independent time and space functions are retained.
--   Adapted from #869 by worker-claude-tidyspike-c4b0c164.
--
--   ### Main results
--
--   * `ComputableInBigO.comp`: materializing composition with explicit intermediate storage.
--   * `ComputableInO.comp`: absorb intermediate storage using the output-growth bound.
--   * `ComputableInO.ite`: pay for the test and the branch actually taken.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/OPrimitives.lean

/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_NormalForm
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelComp
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ConditionalMachine

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Asymptotic composition with explicit intermediate storage

The same realizing machine is normalized within the internal construction proof. Composition
first accounts for the stored intermediate word explicitly in `ComputableInBigO`. The charged
`ComputableInO` rule then absorbs that word using its separate output-growth bound.
The independent time and space functions are retained.
Adapted from #869 by worker-claude-tidyspike-c4b0c164.

## Main results

* `ComputableInBigO.comp`: materializing composition with explicit intermediate storage.
* `ComputableInO.comp`: absorb intermediate storage using the output-growth bound.
* `ComputableInO.ite`: pay for the test and the branch actually taken.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Materializing composition stores the inner encoded output on a work tape. Its length is
charged explicitly to workspace; no output-growth hypothesis is needed. The copying time is
already bounded by the inner runtime. This is not the recomputing small-space composition rule. -/
theorem ComputableInBigO.comp {f : β → γ} {g : α → β} {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInBigO f encMid encOut T₂ S₂)
    (hg : ComputableInBigO g encIn encMid T₁ S₁) :
    ComputableInBigO (f ∘ g) encIn encOut (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a) + (encMid (g a)).length) := by
  obtain ⟨c₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.bigO hg
  obtain ⟨c₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.bigO hf
  let K := 6 * max k₁ k₂ + 20
  refine ⟨6 * c₁ + c₂ + K, _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => (((h₁ a).comp (h₂ (g a)) true).mono ?_ ?_).computesInTimeAndSpace⟩
  · have hm := (h₁ a).length_output_le
    have := Nat.mul_le_mul_left c₁ (by omega : T₁ a + 1 ≤ T₁ a + T₂ (g a) + 1)
    have := Nat.mul_le_mul_left c₂ (by omega : T₂ (g a) + 1 ≤ T₁ a + T₂ (g a) + 1)
    have e : (6 * c₁ + c₂) * (T₁ a + T₂ (g a) + 1) =
        6 * (c₁ * (T₁ a + T₂ (g a) + 1)) + c₂ * (T₁ a + T₂ (g a) + 1) := by ring
    beta_reduce
    exact Internal.NormalForm.le_mul_succ (A := 6 * c₁ + c₂) (B := K) (by omega)
      le_rfl
  · have h₁ := Nat.mul_le_mul_left c₁
      (by omega : S₁ a + 1 ≤ S₁ a + S₂ (g a) + (encMid (g a)).length + 1)
    have h₂ := Nat.mul_le_mul_left c₂
      (by omega : S₂ (g a) + 1 ≤ S₁ a + S₂ (g a) + (encMid (g a)).length + 1)
    have hK : 5 ≤ K := by dsimp [K]; omega
    have hpad := Nat.mul_le_mul_left K
      (by omega : (encMid (g a)).length + 1 ≤
        S₁ a + S₂ (g a) + (encMid (g a)).length + 1)
    change c₁ * (S₁ a + 1) + c₂ * (S₂ (g a) + 1) +
      5 * (encMid (g a)).length + K ≤ _
    have hlen := Nat.mul_le_mul_right (encMid (g a)).length hK
    nlinarith

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInO

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Composition absorbs the stored intermediate word using the inner output-growth bound,
retaining time `O(T₁ a + T₂ (g a))` and space `O(S₁ a + S₂ (g a))`. -/
theorem comp {f : β → γ} {g : α → β} {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encMid encOut T₂ S₂) (hg : ComputableInO g encIn encMid T₁ S₁) :
    ComputableInO (f ∘ g) encIn encOut (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a)) := by
  have hspace : (fun a => S₁ a + S₂ (g a) + (encMid (g a)).length) ≼
      (fun a => S₁ a + S₂ (g a)) :=
    BigOLe.add (.refl _)
      ((show (fun a => (encMid (g a)).length) ≼ S₁ from hg.length_le).trans_le
        fun _ => Nat.le_add_right _ _)
  exact ((hf.computableInBigO.comp hg.computableInBigO).weaken (.refl _) hspace).with_output_bound
    ((show (fun a => (encOut (f a)).length) ≼ S₂ from hf.length_le).comp g |>.trans_le
      fun _ => Nat.le_add_left _ _)

/-- **Case distinction** within the bounds of the test plus those of the branch taken, through the
explicit-bound case-distinction combinator. -/
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    {Tc Tf Tg Sc Sf Sg : α → ℕ} (hc : ComputableInO c encIn encC Tc Sc)
    (hf : ComputableInO f encIn encMid Tf Sf) (hg : ComputableInO g encIn encMid Tg Sg) :
    ComputableInO (fun x => if c x then f x else g x) encIn encMid
      (fun x => Tc x + if c x then Tf x else Tg x)
      (fun x => Sc x + if c x then Sf x else Sg x) := by
  obtain ⟨c₀, ⟨k₀, Q₀, _, tm₀, h₀⟩, -⟩ := Internal.NormalForm.inO hc
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, l₁⟩ := Internal.NormalForm.inO hf
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, h₂⟩, l₂⟩ := Internal.NormalForm.inO hg
  obtain ⟨k, K, Q, _, tm, h⟩ := Internal.conditional (encOut := encMid)
    (f := f) (g := g)
    (tc := fun a => c₀ * (Tc a + 1)) (sc := fun a => c₀ * (Sc a + 1))
    (tf := fun a => c₁ * (Tf a + 1)) (sf := fun a => c₁ * (Sf a + 1))
    (tg := fun a => c₂ * (Tg a + 1)) (sg := fun a => c₂ * (Sg a + 1))
    h₀ (fun x => h₁ x.1) (fun x => h₂ x.1)
  -- each bound is a sum of two terms, each at most a constant times their sum plus one
  have key (c' d' X Y : ℕ) (u : ℕ) (hu : u ≤ c₀ * (X + 1) + c' * (Y + 1) + d')
      (hc' : c' + d' ≤ c₁ + c₂ + k) : u ≤ (c₀ + c₁ + c₂ + k) * (X + Y + 1) := by
    have := Nat.mul_le_mul_left c₀ (by omega : X + 1 ≤ X + Y + 1)
    have := Nat.mul_le_mul_left c' (by omega : Y + 1 ≤ X + Y + 1)
    have e : (c₀ + c') * (X + Y + 1) = c₀ * (X + Y + 1) + c' * (X + Y + 1) := by ring
    exact Internal.NormalForm.le_mul_succ (A := c₀ + c') (B := d') (by omega) (by omega)
  refine ⟨c₀ + c₁ + c₂ + k, ⟨K, Q, inferInstance, tm,
    fun x => ((h x).mono ?_ ?_).computesInTimeAndSpace⟩, fun x => ?_⟩
  · beta_reduce
    split_ifs
    · exact key c₁ k _ _ _ le_rfl (by omega)
    · exact key c₂ k _ _ _ le_rfl (by omega)
  · beta_reduce
    split_ifs
    · exact key c₁ k _ _ _ le_rfl (by omega)
    · exact key c₂ k _ _ _ le_rfl (by omega)
  · beta_reduce
    split_ifs
    · exact key c₁ 0 _ _ _ (by have := l₁ x; omega) (by omega)
    · exact key c₂ 0 _ _ _ (by have := l₂ x; omega) (by omega)

end Turing.MultiTapeTM.ComputableInO


