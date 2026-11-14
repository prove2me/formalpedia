-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:54:26.90145+00:00
-- url     : https://prove2.me/theorems/5bdb7ddd-2f33-43d6-ae88-20c59ad7d185
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List — Polynomial-time list operations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   List operations for the polynomial-time calculus, using Christian Reitwiessner's encodings,
--   degree-bounded operations and fold rules. Indices use `encUnary`: an index returned by `idxOf`
--   is at most the list length, irrespective of the encoding of its elements. In particular, looking
--   up a variable with a large binary label does not require a certificate as long as that label.
--
--   Predicate counts and Boolean scans use only `ListEncoding` and `SizedListEncoding`: reading the
--   list and bounding traversal suffice because the state is a unary counter or a Boolean. Raw bit
--   strings and framed lists are both instances. No output-list construction capability is needed;
--   counting folds a counter directly instead of constructing the matching sublist.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filter`: filtering by a polytime predicate.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons`, `.listAppend`, `.map`, `.flatten`:
--     constructing lists.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons'`, `.listAppend'`: composition rules
--     that let `fun_prop` infer the element encoding from the result.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith`, `.flatMapWith`: constructing lists
--     with a parameter; the input list may itself have polynomial encoded length.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWithInput`, `.flatMapWithInput`,
--     `.filterWithInput`, `.findWithInput`, `.anyWithInput`, `.allWithInput`:
--     automation rules for traversals whose body also uses the original input.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapConst`, `.flatMapConst`, `.allConst`,
--     `.anyConst`: traverse a fixed list without requiring an encoding of its elements.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapFilterConst`: select and map fixed parameters
--     with computed guards and outputs, preserving list order and duplicates.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.mapConst`, `.flatMapConst`, `.mapFilterConst`:
--     plain certificates for fixed-list templates, without encoding the fixed parameters.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith`, `.findWith`: filtering or searching
--     a polynomial-time list with a parameterized test.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length`, `.range`, `.replicate`: unary lengths,
--     ranges and lists of a computed length, charging each repeated value.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.zipIdx`: number list entries with unary indices.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.zip`: pair entries of framed lists.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWith`, `.allWith`: Boolean scans with a
--     parameter, applied explicitly like the fold rules.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.countPWith`, `.anyWithEncoding`,
--     `.allWithEncoding`: direct scans over readable, size-bounded list encodings.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.countPWithInput`, `.countWithInput`: count
--     predicate matches or occurrences of a computed value.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOf`: the first occurrence of an element.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listGetD`: lookup by a unary index.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listGetD_binary`: lookup by a binary index,
--     which is capped at the length of the list.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.getElem?`: optional lookup in computed lists.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listIsEmpty`, `.listIsEmpty'`, `.bitsIsEmpty`,
--     `.head?`: inspect a list without a default element, with inference rules for framed and raw lists.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listReverse`, `.listReverseWithInput`:
--     reverse framed lists, charging the complete encoded size of every intermediate prefix.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOfWithInput`, `.bitsGetDWithInput`:
--     compositional rules for first-occurrence lookup and raw-bit access.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsDropWithInput`, `.bitsTakeWithInput`:
--     runtime bit-string slicing, with computed unary indices.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.takeUnary`, `.listTakeWithInput`,
--     `.listDropWithInput`: slice framed lists at computed unary indices.
--   * `Turing.MultiTapeTM.bits_encList_polyTime`, `.trans_encList_polyTime`: convert between raw
--     binary words and framed lists of encoded bits, also after an arbitrary binary embedding.
--
--   **Contents.** The module is published as a whole: 95 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/List.lean

/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListMap
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListBinaryLookup
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Fold
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DecoderPrimitives

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
import Mathlib.Data.List.GetD

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time list operations

List operations for the polynomial-time calculus, using Christian Reitwiessner's encodings,
degree-bounded operations and fold rules. Indices use `encUnary`: an index returned by `idxOf`
is at most the list length, irrespective of the encoding of its elements. In particular, looking
up a variable with a large binary label does not require a certificate as long as that label.

Predicate counts and Boolean scans use only `ListEncoding` and `SizedListEncoding`: reading the
list and bounding traversal suffice because the state is a unary counter or a Boolean. Raw bit
strings and framed lists are both instances. No output-list construction capability is needed;
counting folds a counter directly instead of constructing the matching sublist.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filter`: filtering by a polytime predicate.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons`, `.listAppend`, `.map`, `.flatten`:
  constructing lists.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons'`, `.listAppend'`: composition rules
  that let `fun_prop` infer the element encoding from the result.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith`, `.flatMapWith`: constructing lists
  with a parameter; the input list may itself have polynomial encoded length.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWithInput`, `.flatMapWithInput`,
  `.filterWithInput`, `.findWithInput`, `.anyWithInput`, `.allWithInput`:
  automation rules for traversals whose body also uses the original input.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapConst`, `.flatMapConst`, `.allConst`,
  `.anyConst`: traverse a fixed list without requiring an encoding of its elements.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapFilterConst`: select and map fixed parameters
  with computed guards and outputs, preserving list order and duplicates.
* `Turing.MultiTapeTM.ComputableInPolyTime.mapConst`, `.flatMapConst`, `.mapFilterConst`:
  plain certificates for fixed-list templates, without encoding the fixed parameters.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith`, `.findWith`: filtering or searching
  a polynomial-time list with a parameterized test.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length`, `.range`, `.replicate`: unary lengths,
  ranges and lists of a computed length, charging each repeated value.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.zipIdx`: number list entries with unary indices.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.zip`: pair entries of framed lists.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWith`, `.allWith`: Boolean scans with a
  parameter, applied explicitly like the fold rules.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.countPWith`, `.anyWithEncoding`,
  `.allWithEncoding`: direct scans over readable, size-bounded list encodings.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.countPWithInput`, `.countWithInput`: count
  predicate matches or occurrences of a computed value.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOf`: the first occurrence of an element.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listGetD`: lookup by a unary index.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listGetD_binary`: lookup by a binary index,
  which is capped at the length of the list.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.getElem?`: optional lookup in computed lists.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listIsEmpty`, `.listIsEmpty'`, `.bitsIsEmpty`,
  `.head?`: inspect a list without a default element, with inference rules for framed and raw lists.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listReverse`, `.listReverseWithInput`:
  reverse framed lists, charging the complete encoded size of every intermediate prefix.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOfWithInput`, `.bitsGetDWithInput`:
  compositional rules for first-occurrence lookup and raw-bit access.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsDropWithInput`, `.bitsTakeWithInput`:
  runtime bit-string slicing, with computed unary indices.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.takeUnary`, `.listTakeWithInput`,
  `.listDropWithInput`: slice framed lists at computed unary indices.
* `Turing.MultiTapeTM.bits_encList_polyTime`, `.trans_encList_polyTime`: convert between raw
  binary words and framed lists of encoded bits, also after an arbitrary binary embedding.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β γ π : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encIn : γ ↪ List Bool} {encP : π ↪ List Bool}

/-- Concatenate raw bit strings, charging for both computed words. -/
@[fun_prop]
theorem bitsAppend {left right : γ → List Bool}
    (hleft : ComputableTidilyInPolyTime left encIn encBits)
    (hright : ComputableTidilyInPolyTime right encIn encBits) :
    ComputableTidilyInPolyTime (fun x => left x ++ right x) encIn encBits :=
  hleft.append hright fun _ => rfl

/-- Prepend a computed bit to a raw bit string. -/
@[fun_prop]
theorem bitsCons {head : γ → Bool} {tail : γ → List Bool}
    (hhead : ComputableTidilyInPolyTime head encIn encBool)
    (htail : ComputableTidilyInPolyTime tail encIn encBits) :
    ComputableTidilyInPolyTime (fun x => head x :: tail x) encIn encBits :=
  hhead.append htail fun _ => rfl

/-- Read the head of any list encoding with a fixed fallback. -/
@[fun_prop]
theorem headD {encL : List α ↪ List Bool} [ListEncoding encA encL] (fallback : α) :
    ComputableTidilyInPolyTime (fun list => list.headD fallback) encL encA :=
  (ComputableTidilyInDegree.headD fallback).computableTidilyInPolyTime

/-- Read a computed framed list's head, inferring the element encoding from the list before
composing with a later field projection. -/
@[fun_prop]
theorem listHeadDWithInput {list : γ → List α} (fallback : α)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun a => (list a).headD fallback) encIn encA :=
  (headD fallback).comp hlist

/-- Drop the head of any list encoding. -/
@[fun_prop]
theorem tail {encL : List α ↪ List Bool} [ListEncoding encA encL] :
    ComputableTidilyInPolyTime (List.tail (α := α)) encL encL :=
  (ComputableTidilyInDegree.tail (enc₁ := encA)).computableTidilyInPolyTime

/-- Test emptiness without decoding a list element or requiring a default value. -/
@[fun_prop]
theorem listIsEmpty {encL : List α ↪ List Bool} [ListEncoding encA encL] :
    ComputableTidilyInPolyTime (List.isEmpty (α := α)) encL encBool :=
  of_linear (Internal.NormalForm.linear (ListEncoding.isEmpty (enc₁ := encA) (enc := encL)))

/-- Test a framed list's emptiness, determining its element encoding for automation. -/
@[fun_prop]
theorem listIsEmpty' (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (List.isEmpty (α := α)) (encList enc) encBool :=
  listIsEmpty (encA := enc)

/-- Test a raw bit string's emptiness using the standard Boolean element encoding. -/
@[fun_prop]
theorem bitsIsEmpty : ComputableTidilyInPolyTime (List.isEmpty (α := Bool)) encBits encBool :=
  listIsEmpty (encA := encBool)

/-- Drop the head of a framed list, determining its element encoding for automation. -/
@[fun_prop]
theorem listTail (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (List.tail (α := α)) (encList enc) (encList enc) :=
  tail (encA := enc)

/-- Drop the first raw bit. The raw encoding fixes the otherwise undetermined element encoding. -/
@[fun_prop]
theorem bitsTail : ComputableTidilyInPolyTime List.tail encBits encBits := tail (encA := encBool)

/-- Reverse a raw bit string using an accumulator that grows by one bit per step. -/
@[fun_prop]
theorem bitsReverse : ComputableTidilyInPolyTime List.reverse encBits encBits := by
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits)
    (step := fun reversed bit => bit :: reversed) (init := fun _ => [])
    (id' (encIn := encBits)) (const [])
    (show ComputableTidilyInPolyTime (fun p : List Bool × Bool => p.2 :: p.1)
      (encPair encBits encBool) encBits by fun_prop)
    (growth := 1) (fun _ _ => by simp)
  simpa using h

/-- Prepending an element to a framed list is polynomial-time. -/
@[fun_prop]
theorem cons (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : α × List α => p.1 :: p.2)
      (encPair enc (encList enc)) (encList enc) :=
  (ComputableTidilyInDegree.cons enc).computableTidilyInPolyTime

/-- Concatenating two framed lists is polynomial-time. -/
@[fun_prop]
theorem listAppend (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList enc) (encList enc)) (encList enc) :=
  (ComputableTidilyInDegree.listAppend enc).computableTidilyInPolyTime

/-- Prepend computed data. The result encoding determines the element encoding before
`fun_prop` searches for the two component certificates. -/
@[fun_prop]
theorem cons' {head : γ → α} {tail : γ → List α}
    (hhead : ComputableTidilyInPolyTime head encIn encA)
    (htail : ComputableTidilyInPolyTime tail encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => head x :: tail x) encIn (encList encA) :=
  (cons encA).comp (hhead.prod htail)

/-- Concatenate computed lists, inferring their shared encoding from the result. -/
@[fun_prop]
theorem listAppend' {left right : γ → List α}
    (hleft : ComputableTidilyInPolyTime left encIn (encList encA))
    (hright : ComputableTidilyInPolyTime right encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => left x ++ right x) encIn (encList encA) :=
  (listAppend encA).comp (hleft.prod hright)

/-- Reverse a framed list; the accumulator is a permutation of a prefix of the input. -/
@[fun_prop]
theorem listReverse (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime List.reverse (encList enc) (encList enc) := by
  have h := foldl' (encA := enc) (encL := encList enc)
    (step := fun reversed value => value :: reversed) (init := fun _ => [])
    (id' (encIn := encList enc)) (const [])
    (show ComputableTidilyInPolyTime (fun p : List α × α => p.2 :: p.1)
      (encPair (encList enc) enc) (encList enc) by fun_prop)
    (B := fun list => (encList enc list).length) .self (fun list i _ => by
      simpa using length_encList_take_le enc list i)
  simpa using h

/-- Reverse a computed framed list, inferring its element encoding from the result. -/
@[fun_prop]
theorem listReverseWithInput {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun a => (list a).reverse) encIn (encList encA) :=
  (listReverse encA).comp hlist

/-- Find the first element passing a polynomial-time test with a fixed parameter.
The list may have any polynomial encoded length. -/
theorem findWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).find? fun a => test (par x, a))
      encIn (encOption encA) := by
  obtain ⟨d, e, htest⟩ := htest.exists_degree
  exact (ComputableTidilyInDegree.findWith htest
    (ComputableTidilyInDegree.fst encP (encList encA))
    (ComputableTidilyInDegree.snd encP (encList encA))).computableTidilyInPolyTime.comp
      (hpar.prod hlist)

/-- Search with a predicate that captures the original input. -/
@[fun_prop]
theorem findWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).find? (test x)) encIn (encOption encA) :=
  findWith htest id' hlist

/-- Keep the elements passing a polynomial-time test with a fixed parameter.
The input list may have any polynomial encoded length. -/
theorem filterWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).filter fun a => test (par x, a))
      encIn (encList encA) := by
  obtain ⟨d, e, htest⟩ := htest.exists_degree
  exact (ComputableTidilyInDegree.filterWith htest
    (ComputableTidilyInDegree.fst encP (encList encA))
    (ComputableTidilyInDegree.snd encP (encList encA))).computableTidilyInPolyTime.comp
      (hpar.prod hlist)

/-- Filter with a predicate that captures the original input. -/
@[fun_prop]
theorem filterWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).filter (test x)) encIn (encList encA) :=
  filterWith htest id' hlist

/-- Filtering a list by a polynomial-time test is polynomial-time. -/
@[fun_prop]
theorem filter {test : α → Bool} (htest : ComputableTidilyInPolyTime test encA encBool) :
    ComputableTidilyInPolyTime (List.filter test) (encList encA) (encList encA) :=
  filterWith (htest.comp (snd encBool encA)) (const true) id'

/-- Map a polynomial-time function with a fixed parameter over a polynomial-time computable list.
The list may have any polynomial encoded length. -/
theorem mapWith {f : π × α → β} {par : γ → π} {list : γ → List α}
    (hf : ComputableTidilyInPolyTime f (encPair encP encA) encB)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).map fun a => f (par x, a))
      encIn (encList encB) := by
  obtain ⟨d, e, hf⟩ := hf.exists_degree
  exact (ComputableTidilyInDegree.mapWith hf
    (ComputableTidilyInDegree.fst encP (encList encA))
    (ComputableTidilyInDegree.snd encP (encList encA))).computableTidilyInPolyTime.comp
      (hpar.prod hlist)

/-- Map a function that also uses the original input. A single joint certificate in the input
and list element makes the cost uniform across all elements. The list certificate is supplied
first so that `fun_prop` can infer its element encoding before checking the body. -/
@[fun_prop]
theorem mapWithInput {f : γ → α → β} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hf : ComputableTidilyInPolyTime (fun p : γ × α => f p.1 p.2)
      (encPair encIn encA) encB) :
    ComputableTidilyInPolyTime (fun x => (list x).map (f x)) encIn (encList encB) :=
  mapWith hf id' hlist

/-- A polynomial-time function can be mapped over a list in polynomial time. -/
@[fun_prop]
theorem map {f : α → β} (hf : ComputableTidilyInPolyTime f encA encB) :
    ComputableTidilyInPolyTime (List.map f) (encList encA) (encList encB) :=
  mapWith (hf.comp (snd encBool encA)) (const true) id'

/-- Read an optional head in any list encoding, without an inhabitant of the element type. -/
@[fun_prop]
theorem head? (enc : α ↪ List Bool) {encL : List α ↪ List Bool} [ListEncoding enc encL] :
    ComputableTidilyInPolyTime (List.head? (α := α)) encL (encOption enc) := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    apply ((listIsEmpty (encA := enc)).cond (const none)
      ((optionSome enc).comp (headD fallback))).of_enc_eq
    intro values
    cases values <;> rfl

/-- Map an input-dependent function over a fixed list. Only its members need certificates;
the list and its elements are not part of the computational input. -/
@[fun_prop]
theorem mapConst {ι : Type*} (l : List ι) {f : γ → ι → β}
    (hf : ∀ i ∈ l, ComputableTidilyInPolyTime (fun x => f x i) encIn encB) :
    ComputableTidilyInPolyTime (fun x => l.map (f x)) encIn (encList encB) := by
  induction l with
  | nil => exact const []
  | cons a l ih =>
    exact (cons encB).comp ((hf a (List.mem_cons_self ..)).prod
      (ih fun b hb => hf b (List.mem_cons_of_mem _ hb)))

private theorem foldl_append (l : List (List α)) (acc : List α) :
    l.foldl (· ++ ·) acc = acc ++ l.flatten := by
  simpa only [List.map_id_fun, id_eq] using
    (List.foldl_append_eq_append (l := l) (f := id) (l' := acc))

private theorem length_encList_flatten_le (enc : α ↪ List Bool) (l : List (List α)) :
    (encList enc l.flatten).length ≤ (encList (encList enc) l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatten_cons, encList_append, List.length_append, encList_cons, length_frame]
    lia

/-- Concatenating a list of lists is polynomial-time. -/
@[fun_prop]
theorem flatten (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime List.flatten (encList (encList enc)) (encList enc) := by
  have h := foldl' (list := id) (step := fun acc a => acc ++ a) id' (const [])
    (ComputableTidilyInDegree.listAppend enc).computableTidilyInPolyTime
    (B := fun l => (encList (encList enc) l).length) .self (fun l i _ => by
      rw [foldl_append, List.nil_append]
      exact (length_encList_flatten_le enc (l.take i)).trans
        (length_encList_take_le (encList enc) l i))
  simpa only [foldl_append, List.nil_append, id_eq] using h

/-- Concatenate polynomial-time lists computed from each element and a fixed parameter. -/
theorem flatMapWith {f : π × α → List β} {par : γ → π} {list : γ → List α}
    (hf : ComputableTidilyInPolyTime f (encPair encP encA) (encList encB))
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).flatMap fun a => f (par x, a))
      encIn (encList encB) := by
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (flatten encB).comp (mapWith hf hpar hlist)

/-- Concatenate lists computed jointly from the original input and each list element.
Like `mapWithInput`, this is a composition rule for `fun_prop`. -/
@[fun_prop]
theorem flatMapWithInput {f : γ → α → List β} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hf : ComputableTidilyInPolyTime (fun p : γ × α => f p.1 p.2)
      (encPair encIn encA) (encList encB)) :
    ComputableTidilyInPolyTime (fun x => (list x).flatMap (f x)) encIn (encList encB) :=
  flatMapWith hf id' hlist

/-- Concatenate input-dependent lists indexed by a fixed list of parameters.
No encoding of the fixed parameters is required. -/
@[fun_prop]
theorem flatMapConst {ι : Type*} (l : List ι) {f : γ → ι → List β}
    (hf : ∀ i ∈ l, ComputableTidilyInPolyTime (fun x => f x i) encIn (encList encB)) :
    ComputableTidilyInPolyTime (fun x => l.flatMap (f x)) encIn (encList encB) := by
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (flatten encB).comp (mapConst l hf)

/-- Filter and map a fixed list using computed guards and outputs. No encoding of the fixed
parameters is required; only members of the list need certificates. -/
@[fun_prop]
theorem mapFilterConst {ι : Type*} (list : List ι) {test : γ → ι → Bool} {f : γ → ι → β}
    (htest : ∀ i ∈ list, ComputableTidilyInPolyTime (fun a => test a i) encIn encBool)
    (hf : ∀ i ∈ list, ComputableTidilyInPolyTime (fun a => f a i) encIn encB) :
    ComputableTidilyInPolyTime (fun a => (list.filter (test a)).map (f a))
      encIn (encList encB) := by
  induction list with
  | nil => exact const []
  | cons a list ih =>
    have htail := ih (fun i hi => htest i (List.mem_cons_of_mem _ hi))
      (fun i hi => hf i (List.mem_cons_of_mem _ hi))
    simpa only [List.filter_cons, List.map_cons, apply_ite] using
      (htest a (List.mem_cons_self ..)).cond ((hf a (List.mem_cons_self ..)).cons' htail) htail

/-- The length of a list, in unary, including raw bit strings. -/
theorem length (enc : α ↪ List Bool) {encL : List α ↪ List Bool} [ListEncoding enc encL]
    [SizedListEncoding enc encL] :
    ComputableTidilyInPolyTime (fun l : List α => l.length) encL encUnary := by
  have h := foldl' (encA := enc) (encL := encL) (list := id)
    (step := fun n _ => n + 1) id' (const 0)
    (ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime.comp (fst encUnary enc))
    (B := fun l => (encL l).length) .self (fun l i _ => by
      simpa [List.foldl_const] using (Nat.min_le_right i l.length).trans
        (SizedListEncoding.length_le (encA := enc) (encL := encL) l))
  simpa [List.foldl_const] using h

/-- Length of a framed list; the element encoding is inferred from the list encoding. -/
@[fun_prop]
theorem length_list (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun l : List α => l.length) (encList enc) encUnary := length enc

/-- Length of a raw bit string. -/
@[fun_prop]
theorem length_bits :
    ComputableTidilyInPolyTime (fun l : List Bool => l.length) encBits encUnary := length encBool

/-- The encoded input length, computed in unary by reading the input word. -/
@[fun_prop]
theorem encoding_length (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun a => (enc a).length) enc encUnary :=
  length_bits.comp (of_eq (encMid := encBits) fun _ => rfl)

/-- Length of a computed raw bit string, fixing the intermediate encoding for proof search.
Registered after `encoding_length` so `fun_prop` first tries this rule on computed words. -/
@[fun_prop]
theorem length_bits_comp {input : α ↪ List Bool} {word : α → List Bool}
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => (word a).length) input encUnary :=
  length_bits.comp hword

/-- Count predicate matches directly over any readable, size-bounded list encoding.
The accumulator is a unary counter; the certificate does not construct a list of matches. -/
theorem countPWith {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encL) :
    ComputableTidilyInPolyTime (fun x => (list x).countP fun a => test (par x, a))
      encIn encUnary := by
  have heq (p : π) (l : List α) (n : ℕ) :
      l.foldl (fun n a => n + (test (p, a)).toNat) n = n + l.countP fun a => test (p, a) := by
    induction l generalizing n with
    | nil => simp
    | cons a l ih =>
      cases h : test (p, a) <;> simp [h, ih, Nat.add_assoc, Nat.add_comm]
  have hstep : ComputableTidilyInPolyTime
      (fun q : (π × ℕ) × α => q.1.2 + (test (q.1.1, q.2)).toNat)
      (encPair (encPair encP encUnary) encA) encUnary := by fun_prop
  have h := foldlWith_of_bounded_growth (encA := encA) (encL := encL) (encB := encUnary)
    (step := fun p n a => n + (test (p, a)).toNat) hpar hlist (const 0) hstep
    (growth := fun _ => 1) (.const 1) (fun x n a _ => by
      simp only [encUnary_apply, List.length_replicate]
      have := Bool.toNat_le (test (par x, a))
      omega)
  simpa only [heq, Nat.zero_add] using h

/-- Count matches of a predicate that captures the original input. The count is in unary. -/
@[fun_prop]
theorem countPWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).countP (test x)) encIn encUnary :=
  countPWith htest id' hlist

/-- Count occurrences of a computed value using lawful Boolean equality. -/
@[fun_prop]
theorem countWithInput [BEq α] [LawfulBEq α] {list : γ → List α} {value : γ → α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hvalue : ComputableTidilyInPolyTime value encIn encA) :
    ComputableTidilyInPolyTime (fun x => (list x).count (value x)) encIn encUnary := by
  simp only [List.count_eq_countP]
  apply countPWithInput hlist
  fun_prop

/-- Enumerate `0, …, n - 1`, with the bound and the elements in unary. -/
@[fun_prop]
theorem range : ComputableTidilyInPolyTime List.range encUnary (encList encUnary) := by
  have hrep (n : ℕ) :
      (List.replicate n true).foldl (fun l _ => l ++ [l.length]) [] = List.range n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ', List.foldl_append, ih, List.range_succ]
  have hstep := (ComputableTidilyInDegree.snoc encUnary).computableTidilyInPolyTime.comp
    ((fst (encList encUnary) encBool).prod
      ((length encUnary).comp (fst (encList encUnary) encBool)))
  have h := foldl' (encA := encBool) (encL := encBits)
    (list := fun n => List.replicate n true) (step := fun l _ => l ++ [l.length])
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl) (const []) hstep
    (B := fun n => (encUnary n).length * (2 * (encUnary n).length + 1))
    (PolyBounded.self.mul (((PolyBounded.const 2).mul .self).add (.const 1)))
    (fun n i _ => by
      rw [List.take_replicate, hrep]
      refine (length_encList_le encUnary _ (b := n) fun a ha => ?_).trans ?_
      · simpa only [encUnary_apply, List.length_replicate] using
          (Nat.le_of_lt (List.mem_range.mp ha)).trans (Nat.min_le_right i n)
      · simp only [List.length_range, encUnary_apply, List.length_replicate]
        exact Nat.mul_le_mul_right _ (Nat.min_le_right i n))
  simpa only [hrep] using h

/-- Repeat a computed value a computed unary number of times, charging every copy and delimiter. -/
@[fun_prop]
theorem replicate {count : γ → ℕ} {value : γ → α}
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hvalue : ComputableTidilyInPolyTime value encIn encA) :
    ComputableTidilyInPolyTime (fun x => List.replicate (count x) (value x))
      encIn (encList encA) := by
  simpa only [Function.comp_def, List.map_const', List.length_range] using
    mapWithInput (f := fun x _ => value x) (range.comp hcount)
      (hvalue.comp (fst encIn encUnary))

/-- Scan any readable, size-bounded list encoding for a predicate match. -/
theorem anyWithEncoding {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encL) :
    ComputableTidilyInPolyTime (fun x => (list x).any fun a => test (par x, a)) encIn encBool := by
  have heq (p : π) (l : List α) (b : Bool) :
      l.foldl (fun b a => b || test (p, a)) b = (b || l.any fun a => test (p, a)) := by
    induction l generalizing b <;> simp [*, Bool.or_assoc]
  have hstep : ComputableTidilyInPolyTime
      (fun q : (π × Bool) × α => q.1.2 || test (q.1.1, q.2))
      (encPair (encPair encP encBool) encA) encBool := by fun_prop
  have h := foldlWith (encA := encA) (encB := encBool)
    (step := fun p b a => b || test (p, a))
    hpar hlist (const false) hstep (B := fun _ => 1) (.const 1)
    (fun _ _ _ => by simp)
  simpa only [heq, Bool.false_or] using h

/-- Test every element of any readable, size-bounded list encoding. -/
theorem allWithEncoding {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encL) :
    ComputableTidilyInPolyTime (fun x => (list x).all fun a => test (par x, a)) encIn encBool := by
  have h := bool_not.comp (anyWithEncoding (bool_not.comp htest) hpar hlist)
  simpa only [Function.comp_def, ← List.all_eq_not_any_not] using h

/-- Test whether any element satisfies a polynomial-time predicate with a fixed parameter. -/
theorem anyWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).any fun a => test (par x, a)) encIn encBool :=
  anyWithEncoding htest hpar hlist

/-- Test whether every element satisfies a polynomial-time predicate with a fixed parameter. -/
theorem allWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).all fun a => test (par x, a)) encIn encBool :=
  allWithEncoding htest hpar hlist

/-- Test whether any list element satisfies a predicate that captures the original input. -/
@[fun_prop]
theorem anyWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).any (test x)) encIn encBool :=
  anyWith htest id' hlist

/-- Test whether every list element satisfies a predicate that captures the original input. -/
@[fun_prop]
theorem allWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).all (test x)) encIn encBool :=
  allWith htest id' hlist

/-- Test every element of a fixed list. Only its members need certificates; the list and its
elements are fixed before the computational input and require no encoding. -/
@[fun_prop]
theorem allConst {ι : Type*} (l : List ι) {test : γ → ι → Bool}
    (htest : ∀ i ∈ l, ComputableTidilyInPolyTime (fun x => test x i) encIn encBool) :
    ComputableTidilyInPolyTime (fun x => l.all (test x)) encIn encBool := by
  induction l with
  | nil => exact const true
  | cons a l ih =>
    exact bool_and.comp ((htest a (List.mem_cons_self ..)).prod
      (ih fun b hb => htest b (List.mem_cons_of_mem _ hb)))

/-- Test whether any element of a fixed list satisfies its input-dependent predicate.
The fixed list needs no element encoding or uniform certificate over all possible elements. -/
@[fun_prop]
theorem anyConst {ι : Type*} (l : List ι) {test : γ → ι → Bool}
    (htest : ∀ i ∈ l, ComputableTidilyInPolyTime (fun x => test x i) encIn encBool) :
    ComputableTidilyInPolyTime (fun x => l.any (test x)) encIn encBool := by
  simpa only [Function.comp_def, List.any_eq_not_all_not] using
    bool_not.comp (allConst l fun i hi => bool_not.comp (htest i hi))

open Internal.ListIndex

/-- The index of the first occurrence, or the list length if absent, computed in unary.
The element itself can use any encoding. -/
@[fun_prop]
theorem idxOf [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List α × α => p.1.idxOf p.2)
      (encPair (encList enc) enc) encUnary := by
  have hsucc : ComputableTidilyInPolyTime (· + 1) encUnary encUnary :=
    ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime
  have hstep : ComputableTidilyInPolyTime
      (fun q : (α × (Bool × ℕ)) × α => idxStep q.1.1 q.1.2 q.2)
      (encPair (encPair enc (encPair encBool encUnary)) enc) (encPair encBool encUnary) := by
    have hq := fst (encPair enc (encPair encBool encUnary)) enc
    have hn := hq.snd'.snd'
    have ha := snd (encPair enc (encPair encBool encUnary)) enc
    exact (bool_or.comp (hq.snd'.fst'.prod ((decide_eq enc).comp (ha.prod hq.fst')))).ite'
      ((const true).prod hn) ((const false).prod (hsucc.comp hn))
  have h := foldlWith_of_bounded_growth (snd (encList enc) enc) (fst (encList enc) enc)
    (const (false, 0)) hstep
    (growth := fun _ => 1) (.const 1) (by
      intro p state value _
      unfold idxStep
      split <;> simp)
  simpa only [Function.comp_def, foldl_idxStep, Bool.false_eq_true, ite_false, Nat.zero_add]
    using (snd encBool encUnary).comp h

/-- Find a computed value's first occurrence in a computed list. -/
@[fun_prop]
theorem idxOfWithInput [DecidableEq α] {list : γ → List α} {value : γ → α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hvalue : ComputableTidilyInPolyTime value encIn encA) :
    ComputableTidilyInPolyTime (fun x => (list x).idxOf (value x)) encIn encUnary :=
  (idxOf encA).comp (hlist.prod hvalue)

/-- Drop a unary number of elements from a sized list encoding, including raw bit strings. -/
theorem dropUnary {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] :
    ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1.drop p.2)
      (encPair encL encUnary) encL := by
  have heq (l : List α) (n : ℕ) :
      (List.replicate n true).foldl (fun acc _ => acc.tail) l = l.drop n := by
    simp [List.foldl_const, List.tail_iterate]
  have h := foldl' (encA := encBool) (encL := encBits)
    (list := fun p : List α × ℕ => List.replicate p.2 true) (step := fun acc _ => acc.tail)
    ((of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl).comp (snd encL encUnary))
    (fst encL encUnary)
    ((of_linear (Internal.NormalForm.linear
      (ListEncoding.tail (enc₁ := encA)))).comp (fst encL encBool))
    (B := fun p => (encPair encL encUnary p).length) .self (fun p i _ => by
      rw [List.take_replicate, heq]
      have := SizedListEncoding.length_drop_le (encA := encA) (encL := encL) p.1 (min i p.2)
      simp only [length_encPair]
      lia)
  simpa only [heq] using h

/-- Drop a computed unary number of elements from a computed framed list. -/
@[fun_prop]
theorem listDropWithInput {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hcount : ComputableTidilyInPolyTime count encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x).drop (count x)) encIn (encList encA) :=
  (dropUnary (encA := encA)).comp (hlist.prod hcount)

/-- Take a unary number of framed-list elements using certified reversal and dropping. -/
@[fun_prop]
theorem takeUnary (enc : α ↪ List Bool) : ComputableTidilyInPolyTime
    (fun p : List α × ℕ => p.1.take p.2) (encPair (encList enc) encUnary) (encList enc) := by
  have h : ComputableTidilyInPolyTime
      (fun p : List α × ℕ => (p.1.reverse.drop (p.1.length - p.2)).reverse)
      (encPair (encList enc) encUnary) (encList enc) := by fun_prop
  simpa only [← List.reverse_take, List.reverse_reverse] using h

/-- Take a computed unary number of elements from a computed framed list. -/
@[fun_prop]
theorem listTakeWithInput {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hcount : ComputableTidilyInPolyTime count encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x).take (count x)) encIn (encList encA) :=
  (takeUnary encA).comp (hlist.prod hcount)

/-- Look up a computed unary index, returning `none` outside a computed list. The list certificate
determines its encoding before proof search checks the corresponding operation and size rules. -/
@[fun_prop]
theorem getElem? {encL : List α ↪ List Bool} {list : γ → List α} {index : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hindex : ComputableTidilyInPolyTime index encIn encUnary)
    [ListEncoding encA encL] [SizedListEncoding encA encL] :
    ComputableTidilyInPolyTime (fun x => (list x)[index x]?) encIn (encOption encA) := by
  simpa only [Function.comp_def, List.head?_drop] using
    (head? encA).comp ((dropUnary (encA := encA)).comp (hlist.prod hindex))

/-- Drop a computed unary number of bits from a computed bit string. -/
@[fun_prop]
theorem bitsDropWithInput {list : γ → List Bool} {count : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hcount : ComputableTidilyInPolyTime count encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x).drop (count x)) encIn encBits :=
  (dropUnary (encA := encBool)).comp (hlist.prod hcount)

/-- Take a unary number of bits. Reversing and dropping reuses the certified list operations. -/
@[fun_prop]
theorem bitsTake : ComputableTidilyInPolyTime
    (fun p : List Bool × ℕ => p.1.take p.2) (encPair encBits encUnary) encBits := by
  have h : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ => (p.1.reverse.drop (p.1.length - p.2)).reverse)
      (encPair encBits encUnary) encBits := by fun_prop
  simpa only [← List.reverse_take, List.reverse_reverse] using h

/-- Take a computed unary number of bits from a computed bit string. -/
@[fun_prop]
theorem bitsTakeWithInput {list : γ → List Bool} {count : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hcount : ComputableTidilyInPolyTime count encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x).take (count x)) encIn encBits :=
  bitsTake.comp (hlist.prod hcount)

/-- List lookup with a fixed default and a unary index, including lookup in raw bit strings. -/
@[fun_prop]
theorem listGetD {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] (d : α) :
    ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1.getD p.2 d)
      (encPair encL encUnary) encA := by
  simpa only [Function.comp_def, List.headD_eq_head?_getD, List.head?_drop,
    List.getD_eq_getElem?_getD] using
    (of_linear (Internal.NormalForm.linear
      (ListEncoding.headD (enc₁ := encA) (enc := encL) d))).comp
      (dropUnary (encA := encA))

/-- Read a bit at a unary index with a fixed fallback. Fixing the raw encoding avoids
guessing a list-encoding instance during compositional proof search. -/
@[fun_prop]
theorem bitsGetD (fallback : Bool) :
    ComputableTidilyInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 fallback)
      (encPair encBits encUnary) encBool := listGetD (encA := encBool) fallback

/-- Read a computed bit string at a computed unary index. -/
@[fun_prop]
theorem bitsGetDWithInput {list : γ → List Bool} {index : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hindex : ComputableTidilyInPolyTime index encIn encUnary) (fallback : Bool) :
    ComputableTidilyInPolyTime (fun x => (list x).getD (index x) fallback) encIn encBool :=
  (bitsGetD fallback).comp (hlist.prod hindex)

/-- Lookup in a computed list at a computed binary index. The index is first capped at the length
of the list, reading its binary digits most significant first and capping every partial value, so
an index far beyond the list costs only its binary length; beyond the list every lookup returns
the default. -/
theorem listGetD_binary {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {l : γ → List α} {i : γ → ℕ} (d : α)
    (hl : ComputableTidilyInPolyTime l encIn encL)
    (hi : ComputableTidilyInPolyTime i encIn encNat) :
    ComputableTidilyInPolyTime (fun x => (l x).getD (i x) d) encIn encA := by
  have hlen : ComputableTidilyInPolyTime (fun x => (l x).length) encIn encUnary :=
    (length encA).comp hl
  have hcap : ComputableTidilyInPolyTime
      (fun x => Cslib.BitString.boundedBinaryValue (l x).length (encNat (i x)).reverse)
      encIn encUnary := by
    apply foldlWith (encA := encBool) (encL := encBits) (encP := encUnary)
      (par := fun x => (l x).length) (list := fun x => (encNat (i x)).reverse)
      (step := fun cap value bit => min cap (2 * value + bit.toNat))
      hlen (bitsReverse.comp hi.encoded) (const 0) (by fun_prop) (B := fun x => (l x).length)
    · simpa only [encUnary_apply, List.length_replicate] using hlen.polyBounded_length
    · intro x j _
      simpa only [encUnary_apply, List.length_replicate, Cslib.BitString.boundedBinaryValue] using
        Cslib.BitString.boundedBinaryValue_le (l x).length ((encNat (i x)).reverse.take j)
  have heq : (fun x => (l x).getD (i x) d) = fun x =>
      (l x).getD (Cslib.BitString.boundedBinaryValue (l x).length (encNat (i x)).reverse) d := by
    funext x
    rw [Cslib.BitString.boundedBinaryValue_eq, encNat_apply,
      Cslib.BitString.binaryValue_reverse_bits]
    rcases le_total (i x) (l x).length with h | h
    · rw [Nat.min_eq_right h]
    · rw [Nat.min_eq_left h, List.getD_eq_default _ _ h, List.getD_eq_default _ _ le_rfl]
  rw [heq]
  exact (listGetD d).comp (hl.prod hcap)

/-- Zip framed lists, charging both inputs and every pair in the output. -/
@[fun_prop]
theorem zip {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List α × List β => p.1.zip p.2)
      (encPair (encList encA) (encList encB)) (encList (encPair encA encB)) := by
  rcases isEmpty_or_nonempty α with h | h
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.1 with
      | nil => rfl
      | cons a _ => exact isEmptyElim a
    rw [heq]
    exact const []
  rcases isEmpty_or_nonempty β with h' | h'
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.2 with
      | nil => simp
      | cons b _ => exact isEmptyElim b
    rw [heq]
    exact const []
  obtain ⟨a⟩ := h
  obtain ⟨b⟩ := h'
  have heq (p : List α × List β) : p.1.zip p.2 =
      (List.range (min p.1.length p.2.length)).map
        (fun i => (p.1.getD i a, p.2.getD i b)) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have hleft : i < p.1.length := (Nat.lt_min.mp (by simpa using hi)).1
    have hright : i < p.2.length := (Nat.lt_min.mp (by simpa using hi)).2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ hleft, List.getD_eq_getElem _ _ hright]
  simp_rw [heq, List.getD_eq_getElem?_getD]
  fun_prop

/-- Number the entries of a framed list with unary indices, charging the list and every index. -/
@[fun_prop]
theorem zipIdx {α : Type} (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun list : List α => list.zipIdx)
      (encList enc) (encList (encPair enc encUnary)) := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    have heq (list : List α) : list.zipIdx =
        (List.range list.length).map (fun i => (list.getD i fallback, i)) := by
      apply List.ext_getElem (by simp)
      intro i hi hi'
      simp only [List.length_zipIdx] at hi
      simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range,
        List.getD_eq_getElem _ _ hi, Nat.zero_add]
    simp_rw [heq, List.getD_eq_getElem?_getD]
    fun_prop

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Test whether any list element satisfies a predicate that captures the original input. -/
@[fun_prop]
theorem anyWithInput {α : Type}
    {γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {test : γ → α → Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun (p : γ × α) => test p.1 p.2)
  (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun (x : γ) => (list x).any (test x)) encIn
  encBool :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWithInput α γ encA encIn test list
      hlist.tidy htest.tidy)

/-- Concatenate raw bit strings, charging for both computed words. -/
@[fun_prop]
theorem bitsAppend {γ : Type}
    {encIn : γ ↪ List Bool}
    {left : γ → List Bool}
    {right : γ → List Bool}
    (hleft : ComputableInPolyTime left encIn encBits)
    (hright : ComputableInPolyTime right encIn encBits) :
    ComputableInPolyTime (fun (x : γ) => left x ++ right x) encIn
  encBits :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsAppend γ encIn left right
      hleft.tidy hright.tidy)

/-- Take a computed unary number of bits from a computed bit string. -/
@[fun_prop]
theorem bitsTakeWithInput {γ : Type}
    {encIn : γ ↪ List Bool}
    {list : γ → List Bool}
    {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun (x : γ) => List.take (count x) (list x))
  encIn encBits :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsTakeWithInput γ encIn list count
      hlist.tidy hcount.tidy)

/-- The encoded input length, computed in unary by reading the input word. -/
@[fun_prop]
theorem encoding_length {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime
  (fun (a : α) => ((enc : α → List Bool) a).length) enc encUnary :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoding_length α enc)

/-- Filter with a predicate that captures the original input. -/
@[fun_prop]
theorem filterWithInput {α : Type}
    {γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {test : γ → α → Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun (p : γ × α) => test p.1 p.2)
  (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun (x : γ) => List.filter (test x) (list x))
  encIn (encList encA) :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWithInput α γ encA encIn test
      list hlist.tidy htest.tidy)

/-- Filtering a list by a polynomial-time test is polynomial-time. -/
@[fun_prop]
theorem filter {α : Type} {encA : α ↪ List Bool} {test : α → Bool}
    (htest : ComputableInPolyTime test encA encBool) :
    ComputableInPolyTime (List.filter test) (encList encA) (encList encA) :=
  filterWithInput id' (htest.comp (snd _ _))

/-- Map an input-dependent function over a fixed list. Only its members need certificates;
the list and its elements are not part of the computational input. -/
@[fun_prop]
theorem mapConst {β γ : Type} {encB : β ↪ List Bool} {encIn : γ ↪ List Bool}
    {ι : Type*} (l : List ι) {f : γ → ι → β}
    (hf : ∀ i ∈ l, ComputableInPolyTime (fun x => f x i) encIn encB) :
    ComputableInPolyTime (fun x => l.map (f x)) encIn (encList encB) := by
  induction l with
  | nil => exact const []
  | cons a l ih =>
    exact cons' (hf a (List.mem_cons_self ..))
      (ih fun b hb => hf b (List.mem_cons_of_mem _ hb))

/-- Concatenate input-dependent lists indexed by a fixed list of parameters.
No encoding of the fixed parameters is required; only members of the list need certificates. -/
@[fun_prop]
theorem flatMapConst {β γ : Type} {encB : β ↪ List Bool} {encIn : γ ↪ List Bool}
    {ι : Type*} (l : List ι) {f : γ → ι → List β}
    (hf : ∀ i ∈ l, ComputableInPolyTime (fun x => f x i) encIn (encList encB)) :
    ComputableInPolyTime (fun x => l.flatMap (f x)) encIn (encList encB) := by
  induction l with
  | nil => exact const []
  | cons a l ih =>
    exact listAppend' (hf a (List.mem_cons_self ..))
      (ih fun b hb => hf b (List.mem_cons_of_mem _ hb))

/-- Filter and map a fixed list using computed guards and outputs, preserving order and
duplicates. No encoding of the fixed parameters is required; only members need certificates. -/
@[fun_prop]
theorem mapFilterConst {β γ : Type} {encB : β ↪ List Bool} {encIn : γ ↪ List Bool}
    {ι : Type*} (list : List ι) {test : γ → ι → Bool} {f : γ → ι → β}
    (htest : ∀ i ∈ list, ComputableInPolyTime (fun a => test a i) encIn encBool)
    (hf : ∀ i ∈ list, ComputableInPolyTime (fun a => f a i) encIn encB) :
    ComputableInPolyTime (fun a => (list.filter (test a)).map (f a))
      encIn (encList encB) := by
  induction list with
  | nil => exact const []
  | cons a list ih =>
    have htail := ih (fun i hi => htest i (List.mem_cons_of_mem _ hi))
      (fun i hi => hf i (List.mem_cons_of_mem _ hi))
    simpa only [List.filter_cons, List.map_cons, apply_ite] using
      (htest a (List.mem_cons_self ..)).ite ((hf a (List.mem_cons_self ..)).cons' htail) htail

/-- Repeat a computed value a computed unary number of times, charging every copy and delimiter. -/
@[fun_prop]
theorem replicate {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {count : γ → ℕ} {value : γ → α}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime (fun x => List.replicate (count x) (value x))
      encIn (encList encA) :=
  .of_tidy (ComputableTidilyInPolyTime.replicate hcount.tidy hvalue.tidy)

/-- Concatenate lists computed jointly from the original input and each list element.
Like `mapWithInput`, this is a composition rule for `fun_prop`. -/
@[fun_prop]
theorem flatMapWithInput {α : Type}
    {β : Type}
    {γ : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {f : γ → α → List β}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hf : ComputableInPolyTime (fun (p : γ × α) => f p.1 p.2)
  (encPair encIn encA) (encList encB)) :
    ComputableInPolyTime (fun (x : γ) => List.flatMap (f x) (list x))
  encIn (encList encB) :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWithInput α β γ encA encB encIn
      f list hlist.tidy hf.tidy)

/-- Read the head of any list encoding with a fixed fallback. -/
@[fun_prop]
theorem headD {α : Type}
    {encA : α ↪ List Bool}
    {encL : List α ↪ List Bool}
    [_inst3 : ListEncoding encA encL]
    (fallback : α) :
    ComputableInPolyTime (fun (list : List α) => list.headD fallback)
  encL encA :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.headD α encA encL _inst3 fallback)

/-- Length of a framed list, for any element encoding, with a unary result. -/
@[fun_prop]
theorem length_list {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun l : List α => l.length) (encList enc) encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.length_list enc)

/-- Length of a raw bit string. -/
@[fun_prop]
theorem length_bits :
    ComputableInPolyTime (fun (l : List Bool) => l.length)
  encBits encUnary :=
  Internal.DecoderWords.unary_degree.computableInPolyTime

/-- Count matches of a predicate that captures the original input. The count is in unary. -/
@[fun_prop]
theorem countPWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).countP (test x)) encIn encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.countPWithInput hlist.tidy htest.tidy)

/-- Read a computed framed list at a computed unary index with a fixed fallback, inferring the
element encoding from the list. -/
@[fun_prop]
theorem listGetDWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} {index : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hindex : ComputableInPolyTime index encIn encUnary) (fallback : α) :
    ComputableInPolyTime (fun x => (list x).getD (index x) fallback) encIn encA :=
  (listGetD fallback).comp (hlist.prod hindex)

/-- Read a computed bit string at a computed unary index. Registered after `listGetDWithInput` so
`fun_prop` tries raw bit-string lookup before framed-list lookup on `Bool`. -/
@[fun_prop]
theorem bitsGetDWithInput {γ : Type} {encIn : γ ↪ List Bool}
    {list : γ → List Bool} {index : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hindex : ComputableInPolyTime index encIn encUnary) (fallback : Bool) :
    ComputableInPolyTime (fun x => (list x).getD (index x) fallback) encIn encBool :=
  (listGetD fallback).comp (hlist.prod hindex)

/-- Drop a computed unary number of bits from a computed raw word. Counts beyond the word
length return the empty word, with no promise on the count or input. -/
@[fun_prop]
theorem bitsDropWithInput {α : Type} {input : α ↪ List Bool}
    {list : α → List Bool} {count : α → ℕ}
    (hlist : ComputableInPolyTime list input encBits)
    (hcount : ComputableInPolyTime count input encUnary) :
    ComputableInPolyTime (fun a => (list a).drop (count a)) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsDropWithInput hlist.tidy hcount.tidy)

/-- Length of a computed raw word, fixing the intermediate encoding for proof search. -/
@[fun_prop]
theorem length_bits_comp {α : Type} {input : α ↪ List Bool} {word : α → List Bool}
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => (word a).length) input encUnary :=
  length_bits.comp hword

/-- Find the first list element passing a test that captures the original input. -/
@[fun_prop]
theorem findWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2) (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).find? (test x)) encIn (encOption encA) :=
  .of_tidy (ComputableTidilyInPolyTime.findWithInput hlist.tidy htest.tidy)

/-- Count the list elements passing a test with a parameter, in unary. -/
theorem countPWith {α γ π : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool} {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP) (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime (fun x => (list x).countP fun a => test (par x, a)) encIn encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.countPWith htest.tidy hpar.tidy hlist.tidy)

/-- Test whether some list element passes a test with a parameter. -/
theorem anyWithEncoding {α γ π : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool} {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP) (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime (fun x => (list x).any fun a => test (par x, a)) encIn encBool :=
  .of_tidy (ComputableTidilyInPolyTime.anyWithEncoding htest.tidy hpar.tidy hlist.tidy)

/-- Test whether every list element passes a test with a parameter. -/
theorem allWithEncoding {α γ π : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool} {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP) (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime (fun x => (list x).all fun a => test (par x, a)) encIn encBool :=
  .of_tidy (ComputableTidilyInPolyTime.allWithEncoding htest.tidy hpar.tidy hlist.tidy)

/-- Zip framed lists, charging both inputs and every pair in the output. -/
@[fun_prop]
theorem zip {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List β => p.1.zip p.2)
      (encPair (encList encA) (encList encB)) (encList (encPair encA encB)) :=
  .of_tidy (ComputableTidilyInPolyTime.zip encA encB)

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM

open ComputableTidilyInPolyTime

private theorem foldl_snoc (word acc : List Bool) :
    word.foldl (fun acc bit => acc ++ [bit]) acc = acc ++ word := by
  induction word generalizing acc with
  | nil => simp
  | cons bit word ih => simp only [List.foldl_cons, ih, List.append_assoc, List.singleton_append]

/-- Framing a fixed Boolean encoding, or parsing its frames and converting each symbol, takes
polynomial time. The encodings of `false` and `true` can be arbitrary fixed words. -/
theorem bits_encList_polyTime (enc : Bool ↪ List Bool) :
    ComputableInPolyTime (fun word => word) encBits (encList enc) ∧
      ComputableInPolyTime (fun word => word) (encList enc) encBits := by
  let C := 2 * max (enc false).length (enc true).length + 1
  have hsymbol (bit : Bool) : (enc bit).length ≤ max (enc false).length (enc true).length := by
    cases bit
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hforward := foldl' (encA := encBool) (encL := encBits) (encB := encList enc)
    (step := fun acc bit => acc ++ [bit]) id' (const [])
    ((ComputableTidilyInDegree.snoc enc).computableTidilyInPolyTime.comp
      ((fst (encList enc) encBool).prod
        ((of_finite (id : Bool → Bool) (encA := encBool) (encB := enc)).comp
          (snd (encList enc) encBool))))
    (B := fun word : List Bool => word.length * C)
    (PolyBounded.self.mul (.const C)) (by
      intro word i hi
      simp only [foldl_snoc, List.nil_append]
      exact (length_encList_le enc _ (fun bit _ => hsymbol bit)).trans
        (Nat.mul_le_mul_right C (by simp only [List.length_take]; omega)))
  have hreverse := foldl' (encA := enc) (encL := encList enc) (encB := encBits)
    (step := fun acc bit => acc ++ [bit]) id' (const [])
    (bitsAppend (fst encBits enc)
      ((of_finite (fun bit : Bool => [bit]) (encA := enc) (encB := encBits)).comp
        (snd encBits enc)))
    (B := fun word : List Bool => (encList enc word).length)
    PolyBounded.self (by
      intro word i hi
      simp only [foldl_snoc, List.nil_append, encBits_apply, List.length_take]
      exact (Nat.min_le_right _ _).trans (length_le_length_encList enc word))
  constructor
  · simpa only [foldl_snoc, List.nil_append, id_eq] using ComputableInPolyTime.of_tidy hforward
  · simpa only [foldl_snoc, List.nil_append, id_eq] using ComputableInPolyTime.of_tidy hreverse

/-- The word conversion preserves an arbitrary caller-supplied encoding. No computable inverse
of `encIn` is assumed: expose its word, convert that word, and reuse the resulting encoding. -/
theorem trans_encList_polyTime {α : Type} (encIn : α ↪ List Bool)
    (enc : Bool ↪ List Bool) :
    ComputableInPolyTime (fun a => a) encIn (encIn.trans (encList enc)) ∧
      ComputableInPolyTime (fun a => a) (encIn.trans (encList enc)) encIn := by
  obtain ⟨hforward, hreverse⟩ := bits_encList_polyTime enc
  constructor
  · exact .of_tidy ((hforward.tidy.comp (encode encIn)).of_enc_eq fun _ => rfl)
  · have hexpose : ComputableTidilyInPolyTime encIn (encIn.trans (encList enc))
        (encList enc) := of_eq fun _ => rfl
    exact .of_tidy ((hreverse.tidy.comp hexpose).of_enc_eq fun _ => rfl)

end Turing.MultiTapeTM


