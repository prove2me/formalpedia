-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:52:39.712893+00:00
-- url     : https://prove2.me/theorems/3e8cc7a6-da27-4366-abb1-6f5ddde9c81a
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO — Tidy computability within given bounds, up to constants
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `ComputableTidilyInO f encIn encOut T S`: `f` is tidily computable within time `O(T a)` and space
--   `O(S a)` on the input `a`, and its encoded value has length `O(S a)`. Unlike
--   `Turing.MultiTapeTM.ComputableTidilyInDegree`, the bounds are any functions of the input, not of the
--   length of its encoding, so that they can be stated in several measures of the input, such as the
--   length of a description, the length of an input and a number of steps.
--
--   The closure properties are exact up to constants: composition adds the bounds of the outer function
--   at the intermediate value, a case distinction adds the bounds of the branch taken, and a left fold
--   adds, for every round, a bound on the round and on the state to the time, but only once to the
--   space. The encoded value counts towards the space since a combinator keeps it on a work tape.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.ComputableTidilyInO`: tidy computability within given bounds.
--   * `Turing.MultiTapeTM.listMax`: the largest value of a function on a list, to bound rounds.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInO.comp`, `.ite`, `.prod`: closure properties.
--   * `Turing.MultiTapeTM.ComputableTidilyInO.foldl`, `.foldlWith`: left folds with a parameter.
--   * `Turing.MultiTapeTM.ComputableTidilyInDegree.inO`: bounds of a given degree.
--
--   **Contents.** The module is published as a whole: 32 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: use core's fold homomorphism law for the captured-parameter identity.
-- vendored: retire superseded tidy list combinators; plain rules live in BigO/Lists.

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_NormalForm
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigOLe
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tidy computability within given bounds, up to constants

`ComputableTidilyInO f encIn encOut T S`: `f` is tidily computable within time `O(T a)` and space
`O(S a)` on the input `a`, and its encoded value has length `O(S a)`. Unlike
`Turing.MultiTapeTM.ComputableTidilyInDegree`, the bounds are any functions of the input, not of the
length of its encoding, so that they can be stated in several measures of the input, such as the
length of a description, the length of an input and a number of steps.

The closure properties are exact up to constants: composition adds the bounds of the outer function
at the intermediate value, a case distinction adds the bounds of the branch taken, and a left fold
adds, for every round, a bound on the round and on the state to the time, but only once to the
space. The encoded value counts towards the space since a combinator keeps it on a work tape.

## Main definitions

* `Turing.MultiTapeTM.ComputableTidilyInO`: tidy computability within given bounds.
* `Turing.MultiTapeTM.listMax`: the largest value of a function on a list, to bound rounds.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInO.comp`, `.ite`, `.prod`: closure properties.
* `Turing.MultiTapeTM.ComputableTidilyInO.foldl`, `.foldlWith`: left folds with a parameter.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.inO`: bounds of a given degree.
-/

namespace Turing.MultiTapeTM

/-- `f` is tidily computable within time `O(T a)` and space `O(S a)` on the input `a`, and its
encoded value has length `O(S a)`. -/
@[expose] public def ComputableTidilyInO {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (T S : α → ℕ) : Prop :=
  ∃ c, ComputableTidilyInTimeAndSpace f encIn encOut (fun a => c * (T a + 1))
    (fun a => c * (S a + 1)) ∧ ∀ a, (encOut (f a)).length ≤ c * (S a + 1)

/-- A function computable within time `O(T)` and space `O(S)` is tidily computable within them. -/
public theorem ComputableInO.tidy {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {T S : α → ℕ} (h : ComputableInO f encIn encOut T S) :
    ComputableTidilyInO f encIn encOut T S :=
  Internal.NormalForm.inO h

/-- A function tidily computable within time `O(T)` and space `O(S)` is computable within them, by
the same machine. -/
public theorem ComputableInO.of_tidy {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {T S : α → ℕ} (h : ComputableTidilyInO f encIn encOut T S) :
    ComputableInO f encIn encOut T S :=
  let ⟨c, hc, hl⟩ := h
  ⟨c, hc.computableInTimeAndSpace, hl⟩

/-- `Turing.MultiTapeTM.ComputableInO.of_tidy` for dot notation on a tidy hypothesis. -/
public theorem ComputableTidilyInO.computableInO {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {T S : α → ℕ}
    (h : ComputableTidilyInO f encIn encOut T S) : ComputableInO f encIn encOut T S :=
  .of_tidy h

/-- The largest value of `f` on the elements of `l`, or `0`. -/
@[expose] public def listMax {α : Type*} (f : α → ℕ) (l : List α) : ℕ := (l.map f).foldr max 0

public lemma le_listMax {α : Type*} {f : α → ℕ} {l : List α} {a : α} (ha : a ∈ l) :
    f a ≤ listMax f l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

public lemma listMax_le {α : Type*} {f : α → ℕ} {l : List α} {b : ℕ} (h : ∀ a ∈ l, f a ≤ b) :
    listMax f l ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    exact max_le (h a (List.mem_cons_self ..)) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

namespace ComputableTidilyInO

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {T T₁ T₂ S S₁ S₂ : α → ℕ}

/-- Bounds within a constant factor. -/
public theorem of_bounds {f : α → β} {t s : α → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encIn encMid t s) (k : ℕ)
    (ht : ∀ a, t a ≤ k * (T a + 1)) (hs : ∀ a, s a ≤ k * (S a + 1))
    (hl : ∀ a, (encMid (f a)).length ≤ k * (S a + 1)) :
    ComputableTidilyInO f encIn encMid T S :=
  ⟨k, hf.mono ht hs, hl⟩

/-- Weakening the bounds, up to a constant factor. -/
public theorem mono {f : α → β} {T' S' : α → ℕ} (h : ComputableTidilyInO f encIn encMid T S)
    (k : ℕ) (hT : ∀ a, T a ≤ k * (T' a + 1)) (hS : ∀ a, S a ≤ k * (S' a + 1)) :
    ComputableTidilyInO f encIn encMid T' S' :=
  let ⟨c, hc, hl⟩ := h
  of_bounds hc (c * (k + 1)) (fun a => by nlinarith [hT a]) (fun a => by nlinarith [hS a])
    (fun a => by nlinarith [hS a, hl a])

/-- Weakening the bounds. -/
public theorem mono_le {f : α → β} {T' S' : α → ℕ} (h : ComputableTidilyInO f encIn encMid T S)
    (hT : ∀ a, T a ≤ T' a) (hS : ∀ a, S a ≤ S' a) : ComputableTidilyInO f encIn encMid T' S' :=
  h.mono 1 (fun a => by have := hT a; omega) fun a => by have := hS a; omega

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `weaken` below, from that revision's `Complexity/BigO`

/-- Weakening the bounds, up to constant factors. -/
public theorem weaken {f : α → β} {T' S' : α → ℕ} (h : ComputableTidilyInO f encIn encMid T S)
    (hT : T ≼ T') (hS : S ≼ S') : ComputableTidilyInO f encIn encMid T' S' :=
  let ⟨k₁, h₁⟩ := hT
  let ⟨k₂, h₂⟩ := hS
  h.mono (k₁ + k₂) (fun a => (h₁ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    fun a => (h₂ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- The encoded values are within the space bound. -/
public theorem length_le {f : α → β} (h : ComputableTidilyInO f encIn encMid T S) :
    ∃ c, ∀ a, (encMid (f a)).length ≤ c * (S a + 1) :=
  let ⟨c, _, hl⟩ := h
  ⟨c, hl⟩

/-- The encoded values are within the time bound. -/
public theorem length_le_time {f : α → β} (h : ComputableTidilyInO f encIn encMid T S) :
    ∃ c, ∀ a, (encMid (f a)).length ≤ c * (T a + 1) :=
  let ⟨c, hc, _⟩ := h
  ⟨c, hc.length_le⟩

public theorem of_linear {f : α → β} (h : ComputableTidilyInLinearTimeAndSpace f encIn encMid) :
    ComputableTidilyInO f encIn encMid (fun a => (encIn a).length) fun a => (encIn a).length :=
  let ⟨c, hc⟩ := h
  ⟨c, hc, hc.length_le⟩

public theorem comp {f : β → γ} {g : α → β} {T₂ S₂ : β → ℕ}
    (hf : ComputableTidilyInO f encMid encOut T₂ S₂)
    (hg : ComputableTidilyInO g encIn encMid T₁ S₁) :
    ComputableTidilyInO (f ∘ g) encIn encOut (fun a => T₁ a + T₂ (g a))
      fun a => S₁ a + S₂ (g a) := by
  obtain ⟨c₁, h₁, l₁⟩ := hg
  obtain ⟨c₂, h₂, l₂⟩ := hf
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨c, h⟩ := h₂.comp_linear h₁
  refine of_bounds h (c₁ + c₂ + c * (c₁ + 1)) (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · have := Nat.mul_le_mul_left c (h₁.length_le a)
    nlinarith [Nat.zero_le (c * c₁ * T₂ (g a)), Nat.zero_le (c * T₂ (g a)), Nat.zero_le (c * T₁ a)]
  · have := Nat.mul_le_mul_left c (l₁ a)
    nlinarith [Nat.zero_le (c * c₁ * S₂ (g a)), Nat.zero_le (c * S₂ (g a)), Nat.zero_le (c * S₁ a)]
  · exact (l₂ (g a)).trans (Nat.mul_le_mul (by omega) (by omega))

public theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    {Tc Tf Tg Sc Sf Sg : α → ℕ} (hc : ComputableTidilyInO c encIn encC Tc Sc)
    (hf : ComputableTidilyInO f encIn encMid Tf Sf)
    (hg : ComputableTidilyInO g encIn encMid Tg Sg) :
    ComputableTidilyInO (fun x => if c x then f x else g x) encIn encMid
      (fun x => Tc x + if c x then Tf x else Tg x) fun x => Sc x + if c x then Sf x else Sg x := by
  obtain ⟨c₀, h₀, -⟩ := hc
  obtain ⟨c₁, h₁, l₁⟩ := hf
  obtain ⟨c₂, h₂, l₂⟩ := hg
  obtain ⟨k, h⟩ := h₀.ite (h₁.restrict _) (h₂.restrict _)
  refine of_bounds h (c₀ + c₁ + c₂ + k) (fun x => ?_) (fun x => ?_) (fun x => ?_) <;>
  · split_ifs <;> nlinarith [l₁ x, l₂ x]

public theorem append {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableTidilyInO f₁ encIn encMid T₁ S₁) (h₂ : ComputableTidilyInO f₂ encIn enc₂ T₂ S₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableTidilyInO g encIn encOut (fun x => T₁ x + T₂ x) fun x => S₁ x + S₂ x := by
  obtain ⟨c₁, h₁, l₁⟩ := h₁
  obtain ⟨c₂, h₂, l₂⟩ := h₂
  obtain ⟨k, h⟩ := h₁.append h₂ hg
  refine of_bounds h (c₁ + c₂ + k) (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · nlinarith
  · nlinarith
  · rw [hg, List.length_append]
    nlinarith [l₁ x, l₂ x]

public theorem pair {α β₁ β₂ : Type} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {T₁ T₂ S₁ S₂ : α → ℕ}
    {enc : β₁ × β₂ ↪ List Bool} [hP : PairEncoding enc₁ enc₂ enc] {f : α → β₁} {g : α → β₂}
    (hf : ComputableTidilyInO f encIn enc₁ T₁ S₁) (hg : ComputableTidilyInO g encIn enc₂ T₂ S₂) :
    ComputableTidilyInO (fun x => (f x, g x)) encIn enc (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x + (enc (f x, g x)).length := by
  obtain ⟨c₁, h₁, -⟩ := hf
  obtain ⟨c₂, h₂, -⟩ := hg
  obtain ⟨c, h⟩ := hP.pair_mono h₁.computableInTimeAndSpace h₂.computableInTimeAndSpace
  have hp : ComputableInBigO (fun x => (f x, g x)) encIn enc
      (fun x => T₁ x + T₂ x) (fun x => S₁ x + S₂ x + (enc (f x, g x)).length) := by
    refine ⟨c * (c₁ + c₂ + 1), h.mono (fun x => ?_) (fun x => ?_)⟩ <;>
      ring_nf <;> omega
  obtain ⟨C, k, Q, hfin, tm, htm⟩ := Internal.NormalForm.bigO hp
  refine ⟨C + 1, ⟨k, Q, hfin, tm, fun x => (htm x).mono
    (Nat.mul_le_mul_right _ (Nat.le_succ C))
    (Nat.mul_le_mul_right _ (Nat.le_succ C))⟩, fun x => ?_⟩
  nlinarith

/-- Pairing with the framed encoding of pairs. -/
public theorem prod {α β₁ β₂ : Type} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {T₁ T₂ S₁ S₂ : α → ℕ} {f : α → β₁}
    {g : α → β₂} (hf : ComputableTidilyInO f encIn enc₁ T₁ S₁)
    (hg : ComputableTidilyInO g encIn enc₂ T₂ S₂) :
    ComputableTidilyInO (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x := by
  obtain ⟨c₁, l₁⟩ := hf.length_le
  obtain ⟨c₂, l₂⟩ := hg.length_le
  refine (hf.pair hg).mono (2 * c₁ + c₂ + 2) (fun x => by nlinarith) fun x => ?_
  have := l₁ x
  have := l₂ x
  rw [length_encPair]
  nlinarith

/-- Bounds polynomial in the length of the encoded input give polynomial time. -/
public theorem computableTidilyInPolyTime {f : α → β} (h : ComputableTidilyInO f encIn encMid T S)
    (hT : PolyBounded (fun a => (encIn a).length) T)
    (hS : PolyBounded (fun a => (encIn a).length) S) :
    ComputableTidilyInPolyTime f encIn encMid :=
  let ⟨c, hc, _⟩ := h
  ⟨_, _, (PolyBounded.const c).mul (hT.add (.const 1)),
    (PolyBounded.const c).mul (hS.add (.const 1)), hc⟩

/-- A function whose encoded values are those of a function computable within the bounds. -/
public theorem of_enc_eq {f : α → β} {g : α → γ} (hf : ComputableTidilyInO f encIn encMid T S)
    (h : ∀ x, encOut (g x) = encMid (f x)) : ComputableTidilyInO g encIn encOut T S :=
  -- vendored: reuse the exact-bound output transport rule.
  let ⟨c, hf, hl⟩ := hf
  ⟨c, hf.of_enc_eq h, fun a => (h a).symm ▸ hl a⟩

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `of_encIn_eq` below, from that revision's `Complexity/BigO`

/-- A function computed on another encoding of its input, with the same words. -/
public theorem of_encIn_eq {α' : Type} {encIn' : α' ↪ List Bool} {f : α → β} (e : α' → α)
    (hf : ComputableTidilyInO f encIn encMid T S) (henc : ∀ a, encIn' a = encIn (e a)) :
    ComputableTidilyInO (fun a => f (e a)) encIn' encMid (fun a => T (e a)) fun a => S (e a) :=
  let ⟨c, ⟨k, S', hS', tm, htm⟩, hl⟩ := hf
  ⟨c, ⟨k, S', hS', tm, fun a => henc a ▸ htm (e a)⟩, fun a => hl (e a)⟩

/-- A function computed within the length of its encoded value, after one computed within `T` and
`S`, is computed within `T` and `S`. -/
public theorem comp_linear {f : β → γ} {g : α → β}
    (hf : ComputableTidilyInO f encMid encOut (fun b => (encMid b).length)
      fun b => (encMid b).length)
    (hg : ComputableTidilyInO g encIn encMid T₁ S₁) :
    ComputableTidilyInO (f ∘ g) encIn encOut T₁ S₁ := by
  obtain ⟨c, hc⟩ := hg.length_le_time
  obtain ⟨d, hd⟩ := hg.length_le
  exact (hf.comp hg).mono (c + d + 1) (fun a => by nlinarith [hc a]) fun a => by nlinarith [hd a]

public theorem const (b : β) : ComputableTidilyInO (fun _ : α => b) encIn encMid
    (fun a => (encIn a).length) fun a => (encIn a).length :=
  of_linear (.const b)

/-- The first projection of the framed encoding of pairs. -/
public theorem fst {β₁ β₂ : Type} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableTidilyInO Prod.fst (encPair enc₁ enc₂) enc₁ (fun p => (encPair enc₁ enc₂ p).length)
      fun p => (encPair enc₁ enc₂ p).length :=
  of_linear (.of_unframe fun p => by simp)

/-- The second projection of the framed encoding of pairs. -/
public theorem snd {β₁ β₂ : Type} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableTidilyInO Prod.snd (encPair enc₁ enc₂) enc₂ (fun p => (encPair enc₁ enc₂ p).length)
      fun p => (encPair enc₁ enc₂ p).length :=
  of_linear (.of_dropFrame fun p => by simp)

/-- The first component of a pair computed within bounds. -/
public theorem fst' {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (h : ComputableTidilyInO f encIn (encPair enc₁ enc₂) T S) :
    ComputableTidilyInO (fun x => (f x).1) encIn enc₁ T S :=
  (fst enc₁ enc₂).comp_linear h

/-- The second component of a pair computed within bounds. -/
public theorem snd' {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (h : ComputableTidilyInO f encIn (encPair enc₁ enc₂) T S) :
    ComputableTidilyInO (fun x => (f x).2) encIn enc₂ T S :=
  (snd enc₁ enc₂).comp_linear h

end ComputableTidilyInO

/-- Bounds of degree `d` in the length of the encoded input. -/
public theorem ComputableTidilyInDegree.inO {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} {d e : ℕ}
    (h : ComputableTidilyInDegree f encIn encOut d e) :
    ComputableTidilyInO f encIn encOut (fun a => ((encIn a).length + 1) ^ d)
      fun a => ((encIn a).length + 1) ^ d :=
  let ⟨⟨_, _, ⟨ct, ht⟩, ⟨cs, hs⟩, hf⟩, _⟩ := h
  .of_bounds hf (ct + cs)
    (fun a => (ht a).trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _)))
    (fun a => (hs a).trans (Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.le_succ _)))
    (fun a => (hf.length_le a).trans
      ((ht a).trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _))))

/-- Linear bounds in the length of the encoded input. -/
public theorem ComputableTidilyInDegree.inO_one {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} {e : ℕ}
    (h : ComputableTidilyInDegree f encIn encOut 1 e) :
    ComputableTidilyInO f encIn encOut (fun a => (encIn a).length) fun a => (encIn a).length :=
  h.inO.mono 1 (fun a => by simp) fun a => by simp

namespace ComputableTidilyInO

/-! ### Left folds -/

section Fold

variable {γ α β π : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encL : List α ↪ List Bool} {encP : π ↪ List Bool}

/-- **Left folds within given bounds.** If every round is within the time `R x` and the space
`Q x`, and every state has length at most `B x`, a fold takes the time of the list and of the
initial state, plus `R x`, `B x` and the length of the encoded list for every round, and the space
of the list and of the initial state, plus `Q x`, `B x` and the length of the encoded list once. -/
public theorem foldl [ListEncoding encA encL] [hS : SizedListEncoding encA encL]
    {list : γ → List α} {init : γ → β} {step : β → α → β} {Tl Ti Sl Si R Q B : γ → ℕ}
    {Ts Ss : β × α → ℕ}
    (hlist : ComputableTidilyInO list encIn encL Tl Sl)
    (hinit : ComputableTidilyInO init encIn encB Ti Si)
    (hstep : ComputableTidilyInO (fun p : β × α => step p.1 p.2) (encPair encB encA) encB Ts Ss)
    (hround : ∀ x i (hi : i < (list x).length),
      Ts (((list x).take i).foldl step (init x), (list x)[i]) ≤ R x)
    (hspace : ∀ x i (hi : i < (list x).length),
      Ss (((list x).take i).foldl step (init x), (list x)[i]) ≤ Q x)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableTidilyInO (fun x => (list x).foldl step (init x)) encIn encB
      (fun x => Tl x + Ti x + ((list x).length + 1) * (R x + B x + (encL (list x)).length))
      fun x => Sl x + Si x + Q x + B x + (encL (list x)).length :=
  (ComputableInO.foldl hlist.computableInO hinit.computableInO hstep.computableInO hround
    hspace hstate).tidy

/-- **Left folds with a parameter, within given bounds.** The step may depend on a parameter
`par x`, which is kept in the state. -/
public theorem foldlWith [ListEncoding encA encL] [hS : SizedListEncoding encA encL]
    {par : γ → π} {list : γ → List α} {init : γ → β} {step : π → β → α → β}
    {Tp Tl Ti Sp Sl Si R Q B : γ → ℕ} {Ts Ss : (π × β) × α → ℕ}
    (hpar : ComputableTidilyInO par encIn encP Tp Sp)
    (hlist : ComputableTidilyInO list encIn encL Tl Sl)
    (hinit : ComputableTidilyInO init encIn encB Ti Si)
    (hstep : ComputableTidilyInO (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB Ts Ss)
    (hround : ∀ x i (hi : i < (list x).length),
      Ts ((par x, ((list x).take i).foldl (step (par x)) (init x)), (list x)[i]) ≤ R x)
    (hspace : ∀ x i (hi : i < (list x).length),
      Ss ((par x, ((list x).take i).foldl (step (par x)) (init x)), (list x)[i]) ≤ Q x)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableTidilyInO (fun x => (list x).foldl (step (par x)) (init x)) encIn encB
      (fun x => Tp x + Tl x + Ti x +
        ((list x).length + 1) * (R x + B x + (encP (par x)).length + (encL (list x)).length))
      fun x => Sp x + Sl x + Si x + Q x + B x + (encP (par x)).length + (encL (list x)).length :=
  (ComputableInO.foldlWith hpar.computableInO hlist.computableInO hinit.computableInO
    hstep.computableInO hround
    hspace hstate).tidy

end Fold

end ComputableTidilyInO

end Turing.MultiTapeTM


