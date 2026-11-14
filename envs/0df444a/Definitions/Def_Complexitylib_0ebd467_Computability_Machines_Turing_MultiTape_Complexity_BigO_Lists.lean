-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Lists
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Lists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:43.373716+00:00
-- url     : https://prove2.me/theorems/fbbb51e9-d929-4a8a-adf9-71236e53b55d
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists — Finding, filtering and mapping with parameters
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   One left fold over `list x` applies a test or function to the parameter
--   `par x` and the current element. The time bound charges each round for the parameter, the list,
--   the accumulator and the largest cost of the test or function on an element.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInO.findWith`: the first element passing a test.
--   * `Turing.MultiTapeTM.ComputableInO.filterWith`: the elements passing a test.
--   * `Turing.MultiTapeTM.ComputableInO.mapWith`: the images of the elements.
--
--   ### References
--
--   Derived from Christian Reitwiessner's original list-combinator construction, using the plain
--   fold rules and independent time and workspace bounds.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Lists`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO/Lists.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Quantitative
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Finding, filtering and mapping with parameters

One left fold over `list x` applies a test or function to the parameter
`par x` and the current element. The time bound charges each round for the parameter, the list,
the accumulator and the largest cost of the test or function on an element.

## Main results

* `Turing.MultiTapeTM.ComputableInO.findWith`: the first element passing a test.
* `Turing.MultiTapeTM.ComputableInO.filterWith`: the elements passing a test.
* `Turing.MultiTapeTM.ComputableInO.mapWith`: the images of the elements.

## References

Derived from Christian Reitwiessner's original list-combinator construction, using the plain
fold rules and independent time and workspace bounds.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

open ComputableTidilyInDegree (findStep foldl_findStep filterStep foldl_filterStep mapStep
  foldl_mapStep length_encList_filter_le)

variable {γ α β π : Type} {encIn : γ ↪ List Bool} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
  {encP : π ↪ List Bool} {par : γ → π} {list : γ → List α} {Tp Tl Sp Sl : γ → ℕ}

/-- The first element of `list x` passing the test `t` with the parameter `par x`. -/
theorem findWith {t : π × α → Bool} {Tt St : π × α → ℕ}
    (ht : ComputableInO t (encPair encP enc) encBool Tt St)
    (hpar : ComputableInO par encIn encP Tp Sp)
    (hlist : ComputableInO list encIn (encList enc) Tl Sl) :
    ComputableInO (fun x => (list x).find? fun a => t (par x, a)) encIn (encOption enc)
      (fun x => (encIn x).length + Tp x + Tl x + ((list x).length + 1) *
        ((encP (par x)).length + (encList enc (list x)).length +
          listMax (fun a => Tt (par x, a)) (list x)))
      fun x => (encIn x).length + Sp x + Sl x + (encP (par x)).length +
        (encList enc (list x)).length + listMax (fun a => St (par x, a)) (list x) := by
  have hq := fst (encPair encP (encOption enc)) enc
  have hel := snd (encPair encP (encOption enc)) enc
  have hisSome := (ComputableInDegree.isSome enc).inO_one.comp_linear hq.snd'
  have h := hisSome.ite hq.snd' ((ht.comp (hq.fst'.prod hel)).ite
    ((ComputableInDegree.optionSome (enc₁ := enc)).inO_one.comp_linear hel) (const none))
  have hstep : ComputableInO (fun q : (π × Option α) × α => findStep t q.1.1 q.1.2 q.2)
      (encPair (encPair encP (encOption enc)) enc) (encOption enc)
      (fun q => (encPair (encPair encP (encOption enc)) enc q).length + Tt (q.1.1, q.2))
      fun q => (encPair (encPair encP (encOption enc)) enc q).length + St (q.1.1, q.2) := by
    refine (h.mono 4 (fun q => ?_) fun q => ?_).of_enc_eq fun ⟨⟨p, acc⟩, a⟩ => ?_
    · split_ifs <;> omega
    · split_ifs <;> omega
    · cases acc <;> simp [findStep]
  have hst (x : γ) (i : ℕ) :
      (encOption enc (((list x).take i).foldl (findStep t (par x)) none)).length ≤
        (encList enc (list x)).length + 1 := by
    rw [foldl_findStep, Option.none_or]
    exact (length_encOption_find?_le enc _ _).trans
      (Nat.add_le_add_right (length_encList_take_le enc _ _) 1)
  have hfold := foldlWith (encL := encList enc) (encB := encOption enc) hpar hlist
    (const none) hstep (R := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length + 5 + listMax (fun a => Tt (par x, a)) (list x))
    (Q := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length + 5 + listMax (fun a => St (par x, a)) (list x))
    (B := fun x => (encList enc (list x)).length + 1)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => Tt (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => St (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i _ => by have := hst x i; omega)
  refine (hfold.mono 16 (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · have h₁ := length_le_length_encList enc (list x)
    have h₂ : (list x).length ≤ (list x).length * (encList enc (list x)).length := by
      rcases Nat.eq_zero_or_pos (list x).length with h | h
      · simp [h]
      · exact Nat.le_mul_of_pos_right _ (by omega)
    ring_nf
    omega
  · omega
  · rw [foldl_findStep, Option.none_or]

/-- The elements of `list x` passing the test `t` with the parameter `par x`. -/
theorem filterWith {t : π × α → Bool} {Tt St : π × α → ℕ}
    (ht : ComputableInO t (encPair encP enc) encBool Tt St)
    (hpar : ComputableInO par encIn encP Tp Sp)
    (hlist : ComputableInO list encIn (encList enc) Tl Sl) :
    ComputableInO (fun x => (list x).filter fun a => t (par x, a)) encIn (encList enc)
      (fun x => (encIn x).length + Tp x + Tl x + ((list x).length + 1) *
        ((encP (par x)).length + (encList enc (list x)).length +
          listMax (fun a => Tt (par x, a)) (list x)))
      fun x => (encIn x).length + Sp x + Sl x + (encP (par x)).length +
        (encList enc (list x)).length + listMax (fun a => St (par x, a)) (list x) := by
  have hq := fst (encPair encP (encList enc)) enc
  have hel := snd (encPair encP (encList enc)) enc
  have h := (ht.comp (hq.fst'.prod hel)).ite
    ((ComputableInDegree.snoc enc).inO_one.comp_linear (hq.snd'.prod hel)) hq.snd'
  have hstep : ComputableInO
      (fun q : (π × List α) × α => filterStep t q.1.1 q.1.2 q.2)
      (encPair (encPair encP (encList enc)) enc) (encList enc)
      (fun q => (encPair (encPair encP (encList enc)) enc q).length + Tt (q.1.1, q.2))
      fun q => (encPair (encPair encP (encList enc)) enc q).length + St (q.1.1, q.2) := by
    refine (h.mono 4 (fun q => ?_) fun q => ?_).of_enc_eq fun ⟨⟨p, acc⟩, a⟩ => ?_
    · split_ifs <;> omega
    · split_ifs <;> omega
    · simp [filterStep]
  have hst (x : γ) (i : ℕ) :
      (encList enc (((list x).take i).foldl (filterStep t (par x)) [])).length ≤
        (encList enc (list x)).length := by
    rw [foldl_filterStep, List.nil_append]
    exact (length_encList_filter_le enc _ _).trans (length_encList_take_le enc _ _)
  have hfold := foldlWith (encL := encList enc) (encB := encList enc) hpar hlist
    (const []) hstep (R := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length + 5 + listMax (fun a => Tt (par x, a)) (list x))
    (Q := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length + 5 + listMax (fun a => St (par x, a)) (list x))
    (B := fun x => (encList enc (list x)).length + 1)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => Tt (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => St (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i _ => by have := hst x i; omega)
  refine (hfold.mono 16 (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · have h₁ := length_le_length_encList enc (list x)
    have h₂ : (list x).length ≤ (list x).length * (encList enc (list x)).length := by
      rcases Nat.eq_zero_or_pos (list x).length with h | h
      · simp [h]
      · exact Nat.le_mul_of_pos_right _ (by omega)
    ring_nf
    omega
  · omega
  · rw [foldl_filterStep, List.nil_append]

/-- Mapping `f` with the parameter `par x` over `list x`. -/
theorem mapWith {f : π × α → β} {Tf Sf : π × α → ℕ}
    (hf : ComputableInO f (encPair encP enc) encB Tf Sf)
    (hpar : ComputableInO par encIn encP Tp Sp)
    (hlist : ComputableInO list encIn (encList enc) Tl Sl) :
    ComputableInO (fun x => (list x).map fun a => f (par x, a)) encIn (encList encB)
      (fun x => (encIn x).length + Tp x + Tl x + ((list x).length + 1) *
        ((encP (par x)).length + (encList enc (list x)).length +
          (encList encB ((list x).map fun a => f (par x, a))).length +
          listMax (fun a => Tf (par x, a)) (list x)))
      fun x => (encIn x).length + Sp x + Sl x + (encP (par x)).length +
        (encList enc (list x)).length +
        (encList encB ((list x).map fun a => f (par x, a))).length +
        listMax (fun a => Sf (par x, a)) (list x) := by
  have hq := fst (encPair encP (encList encB)) enc
  have hel := snd (encPair encP (encList encB)) enc
  have h := (ComputableInDegree.snoc encB).inO_one.comp (hq.snd'.prod (hf.comp (hq.fst'.prod hel)))
  obtain ⟨c, hc⟩ := hf.length_le
  obtain ⟨d, hd⟩ := hf.length_le_time
  have hstep : ComputableInO (fun q : (π × List β) × α => mapStep f q.1.1 q.1.2 q.2)
      (encPair (encPair encP (encList encB)) enc) (encList encB)
      (fun q => (encPair (encPair encP (encList encB)) enc q).length + Tf (q.1.1, q.2))
      fun q => (encPair (encPair encP (encList encB)) enc q).length + Sf (q.1.1, q.2) :=
    h.mono (2 * c + 2 * d + 6) (fun q => by
      have := hd (q.1.1, q.2)
      simp only [length_encPair, Function.comp_apply] at this ⊢
      nlinarith) fun q => by
      have := hc (q.1.1, q.2)
      simp only [length_encPair, Function.comp_apply] at this ⊢
      nlinarith
  have hst (x : γ) (i : ℕ) :
      (encList encB (((list x).take i).foldl (mapStep f (par x)) [])).length ≤
        (encList encB ((list x).map fun a => f (par x, a))).length := by
    rw [foldl_mapStep, List.nil_append, List.map_take]
    exact length_encList_take_le encB _ _
  have hfold := foldlWith (encL := encList enc) (encB := encList encB) hpar hlist
    (const []) hstep (R := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length +
      3 * (encList encB ((list x).map fun a => f (par x, a))).length + 5 +
      listMax (fun a => Tf (par x, a)) (list x))
    (Q := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length +
      3 * (encList encB ((list x).map fun a => f (par x, a))).length + 5 +
      listMax (fun a => Sf (par x, a)) (list x))
    (B := fun x => (encList encB ((list x).map fun a => f (par x, a))).length)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => Tf (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => Sf (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i hi => by have := hst x i; omega)
  refine (hfold.mono 16 (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · have h₁ := length_le_length_encList enc (list x)
    have h₂ : (list x).length ≤ (list x).length * (encList enc (list x)).length := by
      rcases Nat.eq_zero_or_pos (list x).length with h | h
      · simp [h]
      · exact Nat.le_mul_of_pos_right _ (by omega)
    ring_nf
    omega
  · omega
  · rw [foldl_mapStep, List.nil_append]

end Turing.MultiTapeTM.ComputableInO


