-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:43.770555+00:00
-- url     : https://prove2.me/theorems/c310ffe7-e593-45b6-acbb-915ea5431162
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime — Tidy computability in polynomial time
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `ComputableTidilyInPolyTime f encIn encOut`: `f` is tidily computable within time and space
--   bounded by a polynomial in the length of the encoded input. The class is closed under composition,
--   case distinctions and pairing, and contains every function tidily computable in linear time and
--   space.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.PolyBounded`: a function bounded by a polynomial in a size.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime`: tidy computability in polynomial time and space.
--   * `Turing.MultiTapeTM.EncodingEquiv`: encodings that convert into each other in polynomial time.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.PolyBounded.exists_le`, `.of_forall_le`: recover and supply explicit
--     polynomial bounds for the size adapter over `Cslib.PolynomiallyBounded`.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp`, `.ite`, `.pair`: closure properties.
--   * `Turing.MultiTapeTM.computableTidilyInPolyTime_succ`: the successor in binary.
--
--   The closure properties are registered with `fun_prop`, so polynomial-time computability of a
--   composite function follows from that of its parts.
--
--   **Contents.** The module is published as a whole: 21 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_PolynomialBound_Closure
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Polynomial
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Foldl
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyNormalForm

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tidy computability in polynomial time

`ComputableTidilyInPolyTime f encIn encOut`: `f` is tidily computable within time and space
bounded by a polynomial in the length of the encoded input. The class is closed under composition,
case distinctions and pairing, and contains every function tidily computable in linear time and
space.

## Main definitions

* `Turing.MultiTapeTM.PolyBounded`: a function bounded by a polynomial in a size.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime`: tidy computability in polynomial time and space.
* `Turing.MultiTapeTM.EncodingEquiv`: encodings that convert into each other in polynomial time.

## Main results

* `Turing.MultiTapeTM.PolyBounded.exists_le`, `.of_forall_le`: recover and supply explicit
  polynomial bounds for the size adapter over `Cslib.PolynomiallyBounded`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp`, `.ite`, `.pair`: closure properties.
* `Turing.MultiTapeTM.computableTidilyInPolyTime_succ`: the successor in binary.

The closure properties are registered with `fun_prop`, so polynomial-time computability of a
composite function follows from that of its parts.
-/

namespace Turing.MultiTapeTM

universe u

/-! ### Polynomial time -/

/-- `f` is tidily computable within time and space bounded by a polynomial in the length of the
encoded input. -/
@[expose] public def ComputableTidilyInPolyTime {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧ PolyBounded (fun a => (encIn a).length) s ∧
    ComputableTidilyInTimeAndSpace f encIn encOut t s

namespace ComputableTidilyInPolyTime

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- The encoded value of a function computable in polynomial time has polynomial length. -/
public theorem polyBounded_length {f : α → β} (h : ComputableTidilyInPolyTime f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) fun a => (encMid (f a)).length :=
  let ⟨_, _, ht, _, hf⟩ := h
  ht.mono hf.length_le

public theorem of_linear {f : α → β} (h : ComputableTidilyInLinearTimeAndSpace f encIn encMid) :
    ComputableTidilyInPolyTime f encIn encMid :=
  let ⟨c, hc⟩ := h
  ⟨_, _, .of_forall_le c 1 (fun _ => by simp), .of_forall_le c 1 (fun _ => by simp), hc⟩

public theorem comp {f : β → γ} {g : α → β} (hf : ComputableTidilyInPolyTime f encMid encOut)
    (hg : ComputableTidilyInPolyTime g encIn encMid) :
    ComputableTidilyInPolyTime (f ∘ g) encIn encOut := by
  have hl := hg.polyBounded_length
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := hg
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := hf
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear h₂ h₁
  have hm := (PolyBounded.const c).mul (hl.add (PolyBounded.const 1))
  exact ⟨_, _, (ht₁.add (ht₂.comp hl)).add hm, (hs₁.add (hs₂.comp hl)).add hm, h⟩

public theorem restrict {f : α → β} (h : ComputableTidilyInPolyTime f encIn encMid)
    (p : α → Prop) :
    ComputableTidilyInPolyTime (f ∘ Subtype.val) ((Function.Embedding.subtype p).trans encIn)
      encMid :=
  let ⟨_, _, ⟨t, ht, ht'⟩, ⟨s, hs, hs'⟩, hf⟩ := h
  ⟨_, _, ⟨t, ht, fun a => ht' a⟩, ⟨s, hs, fun a => hs' a⟩, hf.restrict p⟩

public theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableTidilyInPolyTime c encIn encC)
    (hf : ComputableTidilyInPolyTime (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encMid)
    (hg : ComputableTidilyInPolyTime (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encMid) :
    ComputableTidilyInPolyTime (fun x => if c x then f x else g x) encIn encMid := by
  obtain ⟨tc, sc, htc, hsc, h₀⟩ := hc
  obtain ⟨tf, sf, htf, hsf, h₁⟩ := hf
  obtain ⟨tg, sg, htg, hsg, h₂⟩ := hg
  -- the bounds of the branches, extended to all inputs
  let ext (u : {x // c x = true} → ℕ) (v : {x // c x = false} → ℕ) (x : α) : ℕ :=
    if h : c x = true then u ⟨x, h⟩ else v ⟨x, by simpa using h⟩
  obtain ⟨k, h⟩ := ComputableTidilyInTimeAndSpace.ite h₀ (tf := ext tf tg) (sf := ext sf sg)
    (tg := ext tf tg) (sg := ext sf sg)
    (h₁.mono (fun x => by simp [ext, x.2]) (fun x => by simp [ext, x.2]))
    (h₂.mono (fun x => by simp [ext, x.2]) (fun x => by simp [ext, x.2]))
  have hext {u v}
      (hu : PolyBounded (fun x : {x // c x = true} => (encIn x).length) u)
      (hv : PolyBounded (fun x : {x // c x = false} => (encIn x).length) v) :
      PolyBounded (fun a => (encIn a).length) (ext u v) := by
    obtain ⟨_, hbu, hu⟩ := hu
    obtain ⟨_, hbv, hv⟩ := hv
    refine ⟨_, hbu.add hbv, fun x => ?_⟩
    by_cases hx : c x = true
    · simpa [ext, hx] using Nat.le_add_right_of_le (hu ⟨x, hx⟩)
    · simpa [ext, hx] using Nat.le_add_left_of_le (hv ⟨x, by simpa using hx⟩)
  refine ⟨_, _, (htc.add (hext htf htg)).add (.const k), (hsc.add (hext hsf hsg)).add (.const k),
    h.mono (fun x => ?_) (fun x => ?_)⟩ <;>
  · by_cases hx : c x = true <;> simp [ext, hx]

public theorem const (b : β) : ComputableTidilyInPolyTime (fun _ : α => b) encIn encMid :=
  of_linear (.const b)

public theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableTidilyInPolyTime f encIn encMid :=
  of_linear (.of_eq h)

public theorem append {δ : Type*} {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableTidilyInPolyTime f₁ encIn encMid)
    (h₂ : ComputableTidilyInPolyTime f₂ encIn enc₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableTidilyInPolyTime g encIn encOut := by
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := h₁
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := h₂
  obtain ⟨k, h⟩ := h₁.append h₂ hg
  exact ⟨_, _, ht₁.add ht₂, (hs₁.add hs₂).add (.const k), h⟩

public theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [hP : PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : ComputableTidilyInPolyTime f encIn enc₁)
    (hg : ComputableTidilyInPolyTime g encIn enc₂) :
    ComputableTidilyInPolyTime (fun x => (f x, g x)) encIn enc := by
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := hf
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := hg
  obtain ⟨c, h⟩ := hP.pair_mono h₁.computableInTimeAndSpace h₂.computableInTimeAndSpace
  have ht := (PolyBounded.const c).mul ((ht₁.add ht₂).add (.const 1))
  have hs := (PolyBounded.const c).mul (((hs₁.add hs₂).add ht).add (.const 1))
  have hp : ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t₁ x + t₂ x + 1))
      (fun x => c * (s₁ x + s₂ x + c * (t₁ x + t₂ x + 1) + 1)) :=
    h.mono (fun _ => le_rfl) (fun x => Nat.mul_le_mul_left c (by
      have := h.length_le x
      omega))
  obtain ⟨C, k, Q, hfin, tm, htm⟩ := Internal.NormalForm.bigO
    (show ComputableInBigO (fun x => (f x, g x)) encIn enc
      (fun x => c * (t₁ x + t₂ x + 1))
      (fun x => c * (s₁ x + s₂ x + c * (t₁ x + t₂ x + 1) + 1)) from
      ⟨1, hp.mono (fun _ => by dsimp; omega) (fun _ => by dsimp; omega)⟩)
  exact ⟨_, _, (PolyBounded.const C).mul (ht.add (.const 1)),
    (PolyBounded.const C).mul (hs.add (.const 1)), k, Q, hfin, tm, htm⟩

/-! ### Automation -/

attribute [fun_prop] ComputableTidilyInPolyTime

attribute [fun_prop] const

@[fun_prop]
public theorem id' : ComputableTidilyInPolyTime (fun a : α => a) encIn encIn :=
  of_eq fun _ => rfl

@[fun_prop]
public theorem comp' {f : β → γ} {g : α → β} (hf : ComputableTidilyInPolyTime f encMid encOut)
    (hg : ComputableTidilyInPolyTime g encIn encMid) :
    ComputableTidilyInPolyTime (fun a => f (g a)) encIn encOut :=
  hf.comp hg

@[fun_prop]
public theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {f : α → β₁} {g : α → β₂}
    (hf : ComputableTidilyInPolyTime f encIn enc₁) (hg : ComputableTidilyInPolyTime g encIn enc₂) :
    ComputableTidilyInPolyTime (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) :=
  hf.pair hg

@[fun_prop]
public theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : β₁ × β₂ => p.1) (encPair enc₁ enc₂) enc₁ :=
  of_linear (.of_unframe fun p => by simp)

@[fun_prop]
public theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : β₁ × β₂ => p.2) (encPair enc₁ enc₂) enc₂ :=
  of_linear (.of_dropFrame fun p => by simp)

/-- A case distinction between functions computable in polynomial time on all inputs. -/
@[fun_prop]
public theorem ite' {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableTidilyInPolyTime c encIn encC) (hf : ComputableTidilyInPolyTime f encIn encMid)
    (hg : ComputableTidilyInPolyTime g encIn encMid) :
    ComputableTidilyInPolyTime (fun x => if c x then f x else g x) encIn encMid :=
  hc.ite (hf.restrict _) (hg.restrict _)

end ComputableTidilyInPolyTime

/-! ### Equivalent encodings -/

/-- Encodings that convert into each other in polynomial time. -/
public def EncodingEquiv {α : Type*} (enc₁ enc₂ : α ↪ List Bool) : Prop :=
  ComputableTidilyInPolyTime id enc₁ enc₂ ∧ ComputableTidilyInPolyTime id enc₂ enc₁

namespace EncodingEquiv

variable {α β : Type*} {enc₁ enc₂ enc₃ : α ↪ List Bool}

@[refl]
public theorem refl (enc : α ↪ List Bool) : EncodingEquiv enc enc :=
  ⟨.of_eq fun _ => rfl, .of_eq fun _ => rfl⟩

@[symm]
public theorem symm (h : EncodingEquiv enc₁ enc₂) : EncodingEquiv enc₂ enc₁ := ⟨h.2, h.1⟩

@[trans]
public theorem trans (h₁₂ : EncodingEquiv enc₁ enc₂) (h₂₃ : EncodingEquiv enc₂ enc₃) :
    EncodingEquiv enc₁ enc₃ :=
  ⟨h₂₃.1.comp h₁₂.1, h₁₂.2.comp h₂₃.2⟩

end EncodingEquiv

/-- The successor is tidily computable in polynomial time, in the binary encoding `encNat`, from
the transducer certificate `computableInTimeAndSpace_succ`. -/
@[fun_prop]
public theorem computableTidilyInPolyTime_succ : ComputableTidilyInPolyTime (· + 1) encNat encNat :=
  let ⟨c, h⟩ := computableInTimeAndSpace_succ.exists_computableTidilyInTimeAndSpace
  ⟨_, _, .of_forall_le (c + 6) 1 (fun _ => by simp only [pow_one]; nlinarith),
    .of_forall_le c 0 (fun _ => by simp), h⟩

end Turing.MultiTapeTM


