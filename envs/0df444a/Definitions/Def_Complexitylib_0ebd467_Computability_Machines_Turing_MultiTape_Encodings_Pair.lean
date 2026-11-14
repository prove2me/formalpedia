-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:33.832202+00:00
-- url     : https://prove2.me/theorems/39ac0c68-b4ea-4867-9900-84cb070fffe2
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair — The framed encoding of pairs
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `encPair enc₁ enc₂` encodes a pair as its framed first component (`Turing.MultiTapeTM.frame`)
--   followed by its second component. It has the capabilities of `Turing.MultiTapeTM.PairEncoding`.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.encFramed`: an encoding with every encoded value framed.
--   * `Turing.MultiTapeTM.encPair`: the framed encoding of pairs.
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Pair.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearCodecPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The framed encoding of pairs

`encPair enc₁ enc₂` encodes a pair as its framed first component (`Turing.MultiTapeTM.frame`)
followed by its second component. It has the capabilities of `Turing.MultiTapeTM.PairEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encFramed`: an encoding with every encoded value framed.
* `Turing.MultiTapeTM.encPair`: the framed encoding of pairs.
-/

namespace Turing.MultiTapeTM

universe u

variable {α β : Type u}

/-- `enc` with every encoded value framed. -/
@[expose] public def encFramed (enc : α ↪ List Bool) : α ↪ List Bool :=
  ⟨fun a => frame (enc a), fun _ _ h => enc.injective (frame_injective h)⟩

/-- Pairs encoded as the framed first component followed by the second component. -/
@[expose] public def encPair (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) :
    α × β ↪ List Bool :=
  ⟨fun p => frame (enc₁ p.1) ++ enc₂ p.2, fun _ _ h =>
    Prod.ext (enc₁.injective (frame_append_inj h).1) (enc₂.injective (frame_append_inj h).2)⟩

@[simp]
public lemma encFramed_apply (enc : α ↪ List Bool) (a : α) : encFramed enc a = frame (enc a) :=
  rfl

variable {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}

@[simp]
public lemma encPair_apply (p : α × β) : encPair enc₁ enc₂ p = frame (enc₁ p.1) ++ enc₂ p.2 :=
  rfl

public lemma length_encPair (p : α × β) :
    (encPair enc₁ enc₂ p).length = 2 * (enc₁ p.1).length + 1 + (enc₂ p.2).length := by
  simp

public lemma length_le_encPair_left (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (enc₁ p.1).length ≤ (encPair enc₁ enc₂ p).length := by
  rw [length_encPair]; omega

public lemma length_le_encPair_right (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (enc₂ p.2).length ≤ (encPair enc₁ enc₂ p).length := by
  rw [length_encPair]; omega

public instance : PairEncoding enc₁ enc₂ (encPair enc₁ enc₂) where
  fst := .of_unframe fun p => by simp
  snd := .of_dropFrame fun p => by simp
  pair := fun {_ encIn f g t s} hf hg => by
    obtain ⟨c₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.bigO
      (show ComputableInBigO f encIn enc₁ t s from
        ⟨1, hf.mono (fun _ => by omega) (fun _ => by omega)⟩)
    obtain ⟨c₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.bigO
      (show ComputableInBigO g encIn enc₂ t s from
        ⟨1, hg.mono (fun _ => by omega) (fun _ => by omega)⟩)
    obtain ⟨c₀, k₀, Q₀, _, tm₀, h₀⟩ := Internal.NormalForm.linear
      (ComputableInDegree.of_frame (f := id)
        (encIn := enc₁) (encMid := encFramed enc₁) fun _ => rfl)
    let overhead := 6 * max k₁ k₀ + 20 + 2 * max (max k₁ k₀ + 2) k₂
    let ct := c₁ + c₂ + (c₀ + 4) * c₁ + c₀ + 9
    let cs := c₁ + c₂ + c₀ + 5 + overhead
    refine ⟨ct + cs, _, _, inferInstance, appendTM (tm₀.comp tm₁ true) tm₂, fun x => ?_⟩
    have h := ((h₁ x).comp (h₀ (f x)) true).append (h₂ x)
    change (appendTM (tm₀.comp tm₁ true) tm₂).ComputesInTimeAndSpace _ _ _ _
    have hl := (h₁ x).length_output_le
    have hp := length_le_encPair_left enc₁ enc₂ (f x, g x)
    have htime : c₀ * ((enc₁ (f x)).length + 1) + 4 * (enc₁ (f x)).length ≤
        (c₀ + 4) * c₁ * (t x + 1) + c₀ := by nlinarith
    have hspace : c₀ * ((enc₁ (f x)).length + 1) + 5 * (enc₁ (f x)).length ≤
        (c₀ + 5) * (encPair enc₁ enc₂ (f x, g x)).length + c₀ := by nlinarith
    have hct : ct * (t x + 1) ≤ (ct + cs) * (t x + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    have hcs : cs * (s x + (encPair enc₁ enc₂ (f x, g x)).length + 1) ≤
        (ct + cs) * (s x + (encPair enc₁ enc₂ (f x, g x)).length + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    have hm := h.mono (t' := ct * (t x + 1))
      (s' := cs * (s x + (encPair enc₁ enc₂ (f x, g x)).length + 1))
      (by dsimp [ct]; nlinarith)
      (by
        have ho := Nat.le_mul_of_pos_right overhead
          (Nat.succ_pos (s x + (encPair enc₁ enc₂ (f x, g x)).length))
        simp only [Nat.succ_eq_add_one] at ho
        dsimp [cs, overhead] at *
        nlinarith)
    exact (hm.mono hct hcs).computesInTimeAndSpace

end Turing.MultiTapeTM


