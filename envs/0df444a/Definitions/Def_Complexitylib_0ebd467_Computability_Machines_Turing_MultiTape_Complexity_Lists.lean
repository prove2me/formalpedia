-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:51:40.707957+00:00
-- url     : https://prove2.me/theorems/56c24638-fad6-4524-b5df-560a5ab3d7ac
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists — List operations with bounds of given degrees
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Operations on lists encoded by `Turing.MultiTapeTM.encList`, with explicit degrees
--   (`Turing.MultiTapeTM.ComputableTidilyInDegree`): adding an element at either end and concatenation
--   in linear time; finding the first element that passes a test and keeping the elements that pass a
--   test, one degree above the test. The tests may depend on a parameter.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInDegree.cons`, `.snoc`, `.listAppend`.
--   * `Turing.MultiTapeTM.ComputableTidilyInDegree.findWith`: the first element passing a test.
--   * `Turing.MultiTapeTM.ComputableTidilyInDegree.filterWith`: the elements passing a test.
--
--   **Contents.** The module is published as a whole: 26 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Lists.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: derive encoded prefix/filter bounds from Mathlib's `List.Sublist.flatMap`.

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Primitives
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# List operations with bounds of given degrees

Operations on lists encoded by `Turing.MultiTapeTM.encList`, with explicit degrees
(`Turing.MultiTapeTM.ComputableTidilyInDegree`): adding an element at either end and concatenation
in linear time; finding the first element that passes a test and keeping the elements that pass a
test, one degree above the test. The tests may depend on a parameter.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInDegree.cons`, `.snoc`, `.listAppend`.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.findWith`: the first element passing a test.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.filterWith`: the elements passing a test.
-/

namespace Turing.MultiTapeTM

variable {α : Type}

@[simp]
public lemma encList_append (enc : α ↪ List Bool) (l₁ l₂ : List α) :
    encList enc (l₁ ++ l₂) = encList enc l₁ ++ encList enc l₂ := by
  induction l₁ <;> simp [*]

/-- A prefix is no longer than the list. -/
public lemma length_encList_take_le (enc : α ↪ List Bool) (l : List α) (i : ℕ) :
    (encList enc (l.take i)).length ≤ (encList enc l).length :=
  ((List.take_sublist i l).flatMap (frame ∘ enc)).length_le

/-- An element is no longer than the encoded list. -/
public lemma length_le_encList_of_mem (enc : α ↪ List Bool) {l : List α} {a : α} (h : a ∈ l) :
    (enc a).length ≤ (encList enc l).length := by
  induction l <;> grind [encList_cons, length_frame]

-- vendored: universe-polymorphic `α`, as this library's users need (crei's file has `α : Type`).
/-- The number of elements is at most the length of the encoded list. -/
public lemma length_le_length_encList {α : Type*} (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (encList enc l).length := by
  induction l <;> grind [encList_cons, length_frame]

/-- The element found in a list is no longer than the encoded list. -/
public lemma length_encOption_find?_le (enc : α ↪ List Bool) (p : α → Bool) (l : List α) :
    (encOption enc (l.find? p)).length ≤ (encList enc l).length + 1 := by
  rcases h : l.find? p with _ | a
  · simp
  · simpa using length_le_encList_of_mem enc (List.mem_of_find?_eq_some h)

namespace ComputableTidilyInDegree

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- Adding an element in front: the identity on encoded words. -/
public theorem cons (enc : α ↪ List Bool) :
    ComputableTidilyInDegree (fun p : α × List α => p.1 :: p.2) (encPair enc (encList enc))
      (encList enc) 1 1 :=
  of_eq fun _ => rfl

/-- Adding an element at the end. -/
public theorem snoc (enc : α ↪ List Bool) :
    ComputableTidilyInDegree (fun p : List α × α => p.1 ++ [p.2]) (encPair (encList enc) enc)
      (encList enc) 1 1 :=
  ((fst (encList enc) enc).append ((of_linear
    (ComputableTidilyInLinearTimeAndSpace.of_frame (f := id) (encIn := enc)
      (encOut := encFramed enc) fun _ => rfl)).comp (snd (encList enc) enc))
    (enc₂ := encFramed enc) fun _ => by simp).mono

/-- Concatenation. -/
public theorem listAppend (enc : α ↪ List Bool) :
    ComputableTidilyInDegree (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList enc) (encList enc)) (encList enc) 1 1 :=
  ((fst (encList enc) (encList enc)).append (snd (encList enc) (encList enc))
    fun _ => by simp).mono

/-! ### Finding and filtering -/

variable {π : Type} {encP : π ↪ List Bool} {enc : α ↪ List Bool} {dt et dP eP dL : ℕ}

/-- One step of finding the first element passing the test `t`. -/
@[expose] public def findStep (t : π × α → Bool) (p : π) (acc : Option α) (a : α) : Option α :=
  if acc.isSome then acc else if t (p, a) then some a else none

public lemma foldl_findStep (t : π × α → Bool) (p : π) (l : List α) (acc : Option α) :
    l.foldl (findStep t p) acc = acc.or (l.find? fun a => t (p, a)) := by
  induction l generalizing acc <;> cases acc <;> grind [findStep]

/-- The first element of `list x` passing the test `t` with the parameter `par x`, for a list of
linear size. -/
public theorem findWith {t : π × α → Bool} {par : γ → π} {list : γ → List α}
    (ht : ComputableTidilyInDegree t (encPair encP enc) encBool dt et)
    (hpar : ComputableTidilyInDegree par encIn encP dP eP)
    (hlist : ComputableTidilyInDegree list encIn (encList enc) dL 1) :
    ComputableTidilyInDegree (fun x => (list x).find? fun a => t (par x, a)) encIn
      (encOption enc) (max (max dL dP) (1 + max 1 dt * max 1 eP)) 1 := by
  -- the step, as a function of `((p, acc), a)`
  have hq := fst (encPair encP (encOption enc)) enc
  have hel := snd (encPair encP (encOption enc)) enc
  have hisSome := (of_finite (encIn := encBool) (encMid := encBool) (fun b : Bool => !b)).comp
    ((of_linear (ComputableTidilyInLinearTimeAndSpace.of_isEmpty (encIn := encOption enc)
      (f := fun o : Option α => o.isNone) fun o => by cases o <;> simp)).comp hq.snd')
  have h := hisSome.ite (hq.snd'.restrict _) ((ht.comp (hq.fst'.prod hel)).ite
    (((optionSome (enc₁ := enc)).comp hel).restrict _) ((const none).restrict _) |>.restrict _)
  simp only [max_self, Nat.one_mul, Nat.mul_one] at h
  have hstep : ComputableTidilyInDegree (fun q : (π × Option α) × α => findStep t q.1.1 q.1.2 q.2)
      (encPair (encPair encP (encOption enc)) enc) (encOption enc) (max 1 dt) 1 := by
    convert h.mono (d' := max 1 dt) (e' := 1) using 1
    funext ⟨⟨p, acc⟩, a⟩
    simp only [findStep, Function.comp_apply]
    cases acc <;> simp
  have hfold := foldlWith (encL := encList enc) (encB := encOption enc) hpar hlist
    (const none) hstep (B := fun x => (encList enc (list x)).length + 1) (hlist.2.add_const 1)
    (fun x i hi => ?_)
  · convert hfold.mono (d' := max (max dL dP) (1 + max 1 dt * max 1 eP)) (e' := 1)
      (max_le (by have := le_max_right (max dL dP) (1 + max 1 dt * max 1 eP); omega)
        (le_max_of_le_right (Nat.add_le_add_left (Nat.mul_le_mul (by omega) (by omega)) 1))) using 1
    funext x
    rw [foldl_findStep]
    rfl
  · rw [foldl_findStep, Option.none_or]
    rcases h : (List.take i (list x)).find? (fun a => t (par x, a)) with _ | a
    · simp
    · have hmem := List.mem_of_find?_eq_some h
      have := length_le_encList_of_mem enc hmem
      have := length_encList_take_le enc (list x) i
      simp only [encOption_some, List.length_cons]
      omega

/-- One step of keeping the elements that pass the test `t`. -/
@[expose] public def filterStep (t : π × α → Bool) (p : π) (acc : List α) (a : α) : List α :=
  if t (p, a) then acc ++ [a] else acc

public lemma foldl_filterStep (t : π × α → Bool) (p : π) (l acc : List α) :
    l.foldl (filterStep t p) acc = acc ++ l.filter fun a => t (p, a) := by
  induction l generalizing acc <;> grind [filterStep]

public lemma length_encList_filter_le (enc : α ↪ List Bool) (f : α → Bool) (l : List α) :
    (encList enc (l.filter f)).length ≤ (encList enc l).length :=
  (List.filter_sublist.flatMap (frame ∘ enc)).length_le

/-- The elements of `list x` passing the test `t` with the parameter `par x`, for a list of linear
size. -/
public theorem filterWith {t : π × α → Bool} {par : γ → π} {list : γ → List α}
    (ht : ComputableTidilyInDegree t (encPair encP enc) encBool dt et)
    (hpar : ComputableTidilyInDegree par encIn encP dP eP)
    (hlist : ComputableTidilyInDegree list encIn (encList enc) dL 1) :
    ComputableTidilyInDegree (fun x => (list x).filter fun a => t (par x, a)) encIn
      (encList enc) (max (max dL dP) (1 + max 1 dt * max 1 eP)) 1 := by
  have hq := fst (encPair encP (encList enc)) enc
  have hel := snd (encPair encP (encList enc)) enc
  have h := (ht.comp (hq.fst'.prod hel)).ite (((snoc enc).comp (hq.snd'.prod hel)).restrict _)
    (hq.snd'.restrict _)
  simp only [max_self, Nat.one_mul, Nat.mul_one] at h
  have hstep : ComputableTidilyInDegree
      (fun q : (π × List α) × α => filterStep t q.1.1 q.1.2 q.2)
      (encPair (encPair encP (encList enc)) enc) (encList enc) (max 1 dt) 1 := by
    convert h.mono (d' := max 1 dt) (e' := 1) using 1
    funext ⟨⟨p, acc⟩, a⟩
    simp [filterStep]
  have hfold := foldlWith (encL := encList enc) (encB := encList enc) hpar hlist
    (const []) hstep (B := fun x => (encList enc (list x)).length) hlist.2
    (fun x i hi => by
      rw [foldl_filterStep, List.nil_append]
      exact (length_encList_filter_le enc _ _).trans (length_encList_take_le enc _ _))
  convert hfold.mono (d' := max (max dL dP) (1 + max 1 dt * max 1 eP)) (e' := 1)
    (max_le (by have := le_max_right (max dL dP) (1 + max 1 dt * max 1 eP); omega)
      (le_max_of_le_right (Nat.add_le_add_left (Nat.mul_le_mul (by omega) (by omega)) 1))) using 1
  funext x
  rw [foldl_filterStep, List.nil_append]

/-- One step of mapping with the parameter `p`. -/
@[expose] public def mapStep {β : Type} (f : π × α → β) (p : π) (acc : List β) (a : α) :
    List β :=
  acc ++ [f (p, a)]

public lemma foldl_mapStep {β : Type} (f : π × α → β) (p : π) (l : List α) (acc : List β) :
    l.foldl (mapStep f p) acc = acc ++ l.map fun a => f (p, a) := by
  induction l generalizing acc <;> simp [mapStep, *]

/-- Mapping `f` with the parameter `par x` over `list x`, for a parameter and a list of linear
size. -/
public theorem mapWith {β : Type} {encB : β ↪ List Bool} {f : π × α → β} {par : γ → π}
    {list : γ → List α} {df ef : ℕ} (hf : ComputableTidilyInDegree f (encPair encP enc) encB df ef)
    (hpar : ComputableTidilyInDegree par encIn encP dP 1)
    (hlist : ComputableTidilyInDegree list encIn (encList enc) dL 1) :
    ComputableTidilyInDegree (fun x => (list x).map fun a => f (par x, a)) encIn
      (encList encB) (max (max dL dP) (1 + max 1 (max df ef) * (ef + 1))) (ef + 1) := by
  obtain ⟨c, hcd⟩ := hf.2
  -- a bound on the encoded images of the elements
  set S : γ → ℕ := fun x => 2 * (encP (par x)).length + 1 + (encList enc (list x)).length
  have hS : DegreeBounded (fun x => (encIn x).length) S 1 :=
    ((hpar.2.smul 2).add_const 1).add hlist.2
  have himg (x : γ) (a : α) (ha : a ∈ list x) : (encB (f (par x, a))).length ≤ c * (S x + 1) ^ ef :=
    (hcd _).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by
      have := length_le_encList_of_mem enc ha
      simp only [length_encPair, S]
      omega) ef))
  have hq := fst (encPair encP (encList encB)) enc
  have hel := snd (encPair encP (encList encB)) enc
  have hfold := foldlWith (encL := encList enc) (encB := encList encB) hpar hlist
    (const []) (step := mapStep f) ((snoc encB).comp (hq.snd'.prod (hf.comp (hq.fst'.prod hel))))
    (B := fun x => (encList enc (list x)).length * (2 * (c * (S x + 1) ^ ef) + 1))
    (hlist.2.mul (((DegreeBounded.comp (size' := id) (v := fun n => c * (n + 1) ^ ef)
      ⟨c, fun _ => le_rfl⟩ hS).smul 2).add_const 1))
    (fun x i hi => by
      rw [foldl_mapStep, List.nil_append]
      refine (length_encList_le encB _ (b := c * (S x + 1) ^ ef) fun b hb => ?_).trans ?_
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        exact himg x a (List.mem_of_mem_take ha)
      · refine Nat.mul_le_mul_right _ ?_
        have := length_le_length_encList enc (list x)
        simp only [List.length_map, List.length_take]
        omega)
  simp only [max_self, Nat.one_mul, Nat.mul_one] at hfold
  convert hfold.mono (d' := max (max dL dP) (1 + max 1 (max df ef) * (ef + 1))) (e' := ef + 1)
    (max_le (by have := le_max_right (max dL dP) (1 + max 1 (max df ef) * (ef + 1)); omega)
      (le_max_of_le_right (Nat.add_le_add_left (Nat.mul_le_mul (by omega) (by omega)) 1)))
    (by omega) using 1
  funext x
  rw [foldl_mapStep, List.nil_append]

/-! ### Arithmetic on unary numbers and integers -/

/-- Truncated subtraction of unary numbers. -/
public theorem unary_sub :
    ComputableTidilyInDegree (fun p : ℕ × ℕ => p.1 - p.2) (encPair encUnary encUnary)
      encUnary 2 1 := by
  have hrep (a b : ℕ) : (List.replicate b true).foldl (fun n _ => n - 1) a = a - b := by
    induction b generalizing a with
    | zero => rfl
    | succ b ih => rw [List.replicate_succ, List.foldl_cons, ih]; omega
  have hfold := foldl' (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun p : ℕ × ℕ => List.replicate p.2 true) (step := fun n _ => n - 1)
    ((of_eq (f := fun n => List.replicate n true) (encIn := encUnary) (encMid := encBits)
      fun _ => rfl).comp (snd encUnary encUnary))
    (fst encUnary encUnary) (unary_pred.comp (fst encUnary encBool))
    (B := fun p => (encPair encUnary encUnary p).length) .self (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [encPair_apply, encUnary_apply, List.length_append, length_frame,
        List.length_replicate]
      omega)
  convert hfold.mono (d' := 2) (e' := 1) using 1
  funext p
  rw [hrep]

/-- The minimum of unary numbers. -/
public theorem unary_min :
    ComputableTidilyInDegree (fun p : ℕ × ℕ => min p.1 p.2) (encPair encUnary encUnary)
      encUnary 2 1 := by
  convert (unary_sub.comp ((fst encUnary encUnary).prod unary_sub)).mono (d' := 2) (e' := 1)
    using 1
  funext p
  simp only [Function.comp_apply]
  omega

lemma int_head : ComputableTidilyInDegree (fun z : ℤ => ((encInt z).take 1).headD false)
    encInt encBool 1 1 :=
  ((headD (enc₁ := encBool) false).comp
    (of_linear (.of_take_one (f := fun z : ℤ => (encInt z).take 1) (encOut := encBits)
      fun _ => rfl))).mono

lemma int_tailEmpty : ComputableTidilyInDegree (fun z : ℤ => (encInt z).tail.isEmpty)
    encInt encBool 1 1 :=
  ((isEmpty (enc₁ := encBool)).comp
    (of_linear (.of_tail (f := fun z : ℤ => (encInt z).tail) (encOut := encBits)
      fun _ => rfl))).mono

/-- Whether an integer is positive. -/
public theorem int_pos :
    ComputableTidilyInDegree (fun z : ℤ => decide (0 < z)) encInt encBool 1 0 := by
  convert ((of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    (fun t : Bool × Bool => !t.1 && !t.2)).comp (int_head.prod int_tailEmpty)).mono
      (d' := 1) (e' := 0) using 1
  funext z
  rcases z with (_ | n) | n <;> simp

/-- Whether an integer is negative. -/
public theorem int_neg :
    ComputableTidilyInDegree (fun z : ℤ => decide (z < 0)) encInt encBool 1 1 := by
  convert int_head using 1
  funext z
  rcases z with n | n <;> simp

/-- Whether an option holds a value. -/
public theorem isSome (enc : α ↪ List Bool) :
    ComputableTidilyInDegree (fun o : Option α => o.isSome) (encOption enc) encBool 1 0 := by
  convert ((of_finite (encIn := encBool) (encMid := encBool) (fun b : Bool => !b)).comp
    (of_linear (.of_isEmpty (encIn := encOption enc) (f := fun o : Option α => o.isNone)
      fun o => by cases o <;> simp))).mono (d' := 1) (e' := 0) using 1
  funext o
  cases o <;> rfl

/-- A list of `n` copies of an element. -/
public theorem replicate (enc : α ↪ List Bool) :
    ComputableTidilyInDegree (fun p : ℕ × α => List.replicate p.1 p.2) (encPair encUnary enc)
      (encList enc) 3 2 := by
  have h (a : α) (m : List Bool) (acc : List α) :
      m.foldl (fun acc _ => acc ++ [a]) acc = acc ++ List.replicate m.length a := by
    induction m generalizing acc with
    | nil => simp
    | cons b m ih => simp [ih, List.replicate_succ]
  have hq := fst (encPair enc (encList enc)) encBool
  have hfold := foldlWith (encL := encBits) (encB := encList enc) (encP := enc)
    (par := fun p : ℕ × α => p.2) (list := fun p => List.replicate p.1 true)
    (init := fun _ => []) (step := fun a acc _ => acc ++ [a]) (snd encUnary enc)
    ((of_eq (f := fun n => List.replicate n true) (encIn := encUnary) (encMid := encBits)
      fun _ => rfl).comp (fst encUnary enc)) (const [])
    ((snoc enc).comp (hq.snd'.prod hq.fst'))
    (B := fun p => (encPair encUnary enc p).length * (2 * (encPair encUnary enc p).length + 1))
    (DegreeBounded.self.mul ((DegreeBounded.self.smul 2).add_const 1)) (fun p i hi => by
      rw [h]
      refine (length_encList_le enc _ (b := (enc p.2).length) fun b hb => by
        rw [List.eq_of_mem_replicate hb]).trans (Nat.mul_le_mul ?_ ?_)
      · simp only [List.length_replicate, List.length_take, encPair_apply, encUnary_apply,
          List.length_append, length_frame, List.nil_append]
        omega
      · simp only [length_encPair]
        omega)
  convert hfold.mono (d' := 3) (e' := 2) using 1
  funext p
  rw [h]
  simp

end ComputableTidilyInDegree

end Turing.MultiTapeTM


