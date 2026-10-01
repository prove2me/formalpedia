-- Prove2me | Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
-- name    : Yukon_3ca8dea642d23c4bd0e25cee
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:12:05.948974+00:00
-- url     : https://prove2.me/theorems/bb0a9f66-25fb-4d58-b603-450d84b6a692
-- title:
--   YukonModule.VCVio.OracleComp.ProbComp.part0
-- statement:
--   Source module VCVio.OracleComp.ProbComp. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/ProbComp.lean
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/ProbComp.lean
--
--   yukon-proof-operation:d27000dc7e2546d5bd37cd305db4822300a60b777838525406a29eccf817c9a9
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZDI3MDAwZGM3ZTI1NDZkNWJkMzdjZDMwNWRiNDgyMjMwMGE2MGI3Nzc4Mzg1MjU0MDZhMjllY2NmODE3YzlhOSIsImhhc2giOiIwNDE4YTgzMmE3OTE3YjUwYjBhZDU1ZmE0MzU1MTI5NGQyYTM1YjZiNGE1NDcxNWJmNDBlMWEyMzc1YWI2NTQwIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8zY2E4ZGVhNjQyZDIzYzRiZDBlMjVjZWUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Definitions.Def_Yukon_2b5744019605f484379c669d

public import Batteries.Control.OptionT


public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Definitions.Def_Yukon_67bc98b5f0d16609cb699923
public import Definitions.Def_Yukon_0169f95fdb4d5928b3998f5a
public import Definitions.Def_Yukon_c042061a45cc167df49b6d76
public import Definitions.Def_Yukon_ece90b6202ec9f124162dcb0
public import Definitions.Def_Yukon_9f3aba2e8637ece6713a3f01
public import Definitions.Def_Yukon_135b1e0f495a7a36531945f6
public import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
meta import Definitions.Def_Yukon_67bc98b5f0d16609cb699923
meta import Definitions.Def_Yukon_0169f95fdb4d5928b3998f5a
meta import Definitions.Def_Yukon_c042061a45cc167df49b6d76
meta import Definitions.Def_Yukon_ece90b6202ec9f124162dcb0
meta import Definitions.Def_Yukon_2b5744019605f484379c669d
meta import Definitions.Def_Yukon_9f3aba2e8637ece6713a3f01
meta import Definitions.Def_Yukon_135b1e0f495a7a36531945f6
meta import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
set_option backward.isDefEq.respectTransparency.types false
/-!
# Computations with Uniform Selection Oracles

This file defines a type `ProbComp α` for the case of `OracleComp` with access to a
uniform selection oracle, specified by `unifSpec`, as well as common operations for this type.

We define `$[0..n]` as uniform selection starting from zero for any `n : ℕ` (`uniformFin`)
as well as a version `$[n⋯m]` that tries to synthesize an instance of `n < m` (`uniformRange`).
This allows us to avoid needing an `OptionT` wrapper to handle empty ranges.

We also define typeclasses `HasUniformSelect β cont` and `HasUniformSelect! β cont` to allow for
`$ xs` and `$! xs` notation for uniform sampling from a container.
These don't really enforce any semantics, so any new definition will need to prove
lemmas about the behavior of the operation.
TODO: we could introduce a mixin typeclass at least to handle this?

`SampleableType α` on the other hand allows for `$ᵗ α` notation for uniform type sampleing,
and *does* enforce the uniformity of outputs.
Encapsulating the thing you want to select in a `SampleableType` can therefore give more
useful lemmas out of the box, in particular when using subtypes.

TODO: Some lemmas here don't exist at the `PMF`/`SPMF` levels.
-/

@[expose] public section


open OracleComp BigOperators ENNReal

universe u v w

/-- Simplified notation for computations with no oracles besides random inputs.
This specific case can be used with `#eval` to run a random program, see `OracleComp.runIO`.
NOTE: Need to decide if this should be more opaque than `abbrev`, seems like no as of now.. -/
abbrev ProbComp : Type → Type := OracleComp unifSpec

namespace ProbComp

/-- Independently sample `k` values from `samp`, returning them as a `Fin k → α`. -/
def sampleIID {α : Type} (k : ℕ) (samp : ProbComp α) : ProbComp (Fin k → α) :=
  Fin.mOfFn k fun _ => samp

section uniformFin

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) :=
  unifSpec.query n

notation "$[0.." n "]" => uniformFin n

@[grind =]
lemma uniformFin_def (n : ℕ) : $[0..n] = unifSpec.query n := rfl

@[simp]
lemma support_uniformFin (n : ℕ) :
    support (do $[0..n]) = Set.univ := by simp [uniformFin_def]

@[simp]
lemma finSupport_uniformFin (n : ℕ) :
    finSupport (do $[0..n]) = Finset.univ := by
  rw [finSupport_eq_iff_support_eq_coe, support_uniformFin]; simp

@[grind =]
lemma probOutput_uniformFin_eq_div (n : ℕ) (m : Fin (n + 1)) :
    Pr[= m | do $[0..n]] = 1 / (n + 1) := by simp [uniformFin_def]

@[simp, grind =]
lemma probOutput_uniformFin (n : ℕ) (m : Fin (n + 1)) :
    Pr[= m | do $[0..n]] = (n + 1 : ℝ≥0∞)⁻¹ := by simp [uniformFin_def]

@[simp, grind =]
lemma probEvent_uniformFin (n : ℕ) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    Pr[ p | do $[0..n]] = (Fin.countP fun i => p i) / ↑(n + 1) := by
  simp [uniformFin_def, Fin.card_eq_countP_mem]

lemma probFailure_uniformFin (n : ℕ) :
    Pr[⊥ | do $[0..n]] = 0 := by aesop

/-- Nicer induction rule for `ProbComp` that uses monad notation.
Allows inductive definitions on computations by considering the two cases:
* `return x` / `pure x` for any `x`
* `do let u ← $[0..n]; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected theorem inductionOn {α} {C : ProbComp α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (n : ℕ) → (mx : Fin (n + 1) → ProbComp α) → (∀ m, C (mx m)) → C ($[0..n] >>= mx))
    (oa : ProbComp α) : C oa :=
  PFunctor.FreeM.induction pure query_bind oa

end uniformFin

section uniformRange

/-- Select uniformly from a non-empty range. The notation attempts to derive `h` automatically. -/
def uniformRange (n m : ℕ) (h : n < m) :
    ProbComp (Fin (m + 1)) :=
  (fun ⟨x, hx⟩ => ⟨x + n, by omega⟩) <$> $[0..(m - n)]

/- Bounds use the original built-in tactics directly. -/


/-- Select uniformly from a range of numbers. Attempts to use `get-/
notation "$[" n "⋯" m "]" => uniformRange n m (by first | get_elem_tactic | trivial)

lemma uniformRange_def (n m : ℕ) (h : n < m) : $[n⋯m] = uniformRange n m h := rfl

example {m n : ℕ} (h : m < n) : ProbComp ℕ := do
  let x ← $[314⋯31415]; let y ← $[0⋯10] -- Prove by trivial reduction
  let z ← $[m⋯n] -- Use value from hypothesis
  return x + 2 * y

@[simp, grind =]
lemma uniformRange_eq_uniformFin (n : ℕ) (hn : 0 < n) : $[0⋯n] = $[0..n] := rfl

@[simp, grind =]
lemma probOutput_uniformRange (n m : ℕ) (k : Fin (m + 1)) (h : n < m) :
    Pr[= k | uniformRange n m h] = if n ≤ k then (m - n + 1 : ℝ≥0∞)⁻¹ else 0 := by
  simp only [uniformRange, probOutput_map_eq_sum_finSupport_ite, finSupport_uniformFin, Fin.ext_iff,
    probOutput_uniformFin, natCast_sub, Finset.sum_boole', nsmul_eq_mul]
  rw [show ({x | (k : ℕ) = ↑x + n} : Finset (Fin (m - n + 1))).card =
      if n ≤ (k : ℕ) then 1 else 0 from ?_]
  · split <;> simp
  · by_cases hk : n ≤ (k : ℕ)
    · rw [if_pos hk, Finset.card_eq_one]
      exact ⟨⟨k - n, by omega⟩, by ext i; simp [Fin.ext_iff]; omega⟩
    · rw [if_neg hk, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x; simp; omega

@[simp, grind =]
lemma support_uniformRange (n m : ℕ) (h : n < m) :
    support (uniformRange n m h) =
      Set.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  ext k
  rw [mem_support_iff, probOutput_uniformRange, Set.mem_Icc, Fin.ofNat_Icc_iff h]
  simp

@[simp]
lemma finSupport_uniformRange (n m : ℕ) (h : n < m) :
    finSupport (do uniformRange n m h) =
      Finset.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformRange n m h]

@[simp, grind =]
lemma probEvent_uniformRange (n m : ℕ)
    (p : Fin (m + 1) → Prop) [DecidablePred p] (h : n < m) :
    Pr[ p | uniformRange n m h] = Finset.card {x : Fin (m + 1) | n ≤ x ∧ p x} / (m - n + 1) := by
  rw [probEvent_eq_sum_filter_finSupport, finSupport_uniformRange]
  simp_rw [probOutput_uniformRange]
  rw [Finset.sum_ite_of_true fun x hx => by
        rw [Finset.mem_filter, Finset.mem_Icc, Fin.ofNat_Icc_iff h] at hx; lia,
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 3 with x
  simp only [Finset.mem_filter, Finset.mem_Icc, Fin.ofNat_Icc_iff h,
    Finset.mem_univ, true_and]

lemma probFailure_uniformRange (n m : ℕ) (h : n < m) :
    Pr[⊥ | uniformRange n m h] = 0 := by aesop

end uniformRange

section uniformSelect

/-- Typeclass to implement the notation `$ xs` for selecting an object uniformly from a collection.
The container type is given by `cont` with the resulting type given by `β`.
`β` is marked as an `outParam` so that Lean will first pick the output type before synthesizing.
NOTE: This current implementation doesn't impose any "correctness" conditions,
it purely exists to provide the notation, could revisit that in the future. -/
class HasUniformSelect (cont : Type u) (β : outParam Type) where
  uniformSelect : cont → OptionT ProbComp β

/-- Version of `HasUniformSelect` that doesn't allow for failure.
Useful for things like `Vector` that can be shown nonempty at the type level. -/
class HasUniformSelect! (cont : Type u) (β : outParam Type) where
  uniformSelect! : cont → ProbComp β

export HasUniformSelect (uniformSelect)
export HasUniformSelect! (uniformSelect!)

prefix : 75 "$" => uniformSelect
prefix : 75 "$!" => uniformSelect!

variable {cont : Type u} {β : Type}

/-- Given a non-failing uniform selection operation we also have a potentially failing one,
using `OptionT.lift` -/
instance hasUniformSelect_of_hasUniformSelect!
    [h : HasUniformSelect! cont β] : HasUniformSelect cont β where
  uniformSelect cont := OptionT.lift ($! cont)

/-- Compatibility of the `$! xs` operation with `$ xs` given the inferred instance.
TODO: I think we probably want to `simp` in the other direction when possible? -/
@[simp, grind =] lemma liftM_uniformSelect! [HasUniformSelect! cont β]
    (xs : cont) : (liftM ($! xs) : OptionT ProbComp β) = $ xs := by
  simp [OptionT.liftM_def]; rfl

lemma uniformSelect_eq_liftM_uniformSelect! [HasUniformSelect! cont β]
    (xs : cont) : ($ xs : OptionT ProbComp β) = liftM ($! xs) := by grind

end uniformSelect

section uniformSelectList

/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just fail rather than choose a default value.
This means selecting from a vector is often preferable, as we can prove at the type level
that there is an element in the list, avoiding the defualt case of empty lists. -/
instance hasUniformSelectList (α : Type) :
    HasUniformSelect (List α) α where
  uniformSelect
    | [] => failure
    | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length]

variable {α : Type} (xs : List α)

lemma uniformSelectList_def : $ xs = match xs with
  | [] => failure
  | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length] := rfl

@[simp, grind =]
lemma uniformSelectList_nil : $ ([] : List α) = failure := rfl

@[grind =]
lemma uniformSelectList_cons (x : α) (xs : List α) :
    $ (x :: xs) = ((x :: xs)[·]) <$> $[0..xs.length] := rfl

@[simp, grind =]
lemma support_uniformSelectList (xs : List α) :
    support ($ xs) = {x | x ∈ xs} := match xs with
  | [] => by simp
  | x :: xs => by simp [uniformSelectList_cons, Set.ext_iff, Fin.exists_iff,
      - List.mem_cons, List.mem_iff_getElem]

@[simp, grind =]
lemma finSupport_uniformSelectList [DecidableEq α] (xs : List α) :
    finSupport ($ xs) = xs.toFinset := match xs with
  | [] => by simp
  | x :: xs => by
      apply finSupport_eq_of_support_eq_coe
      simp [Set.ext_iff]

@[simp, grind =]
lemma probOutput_uniformSelectList [DecidableEq α] (xs : List α) (x : α) :
    Pr[= x | $ xs] = (xs.count x : ℝ≥0∞) / xs.length := match xs with
  | [] => by simp
  | y :: ys => by
    rw [List.count, ← List.countP_eq_sum_fin_ite]
    simp [uniformSelectList_cons, probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, @eq_comm _ x]

@[simp, grind =] lemma probFailure_uniformSelectList (xs : List α) :
    Pr[⊥ | $ xs] = if xs.isEmpty then 1 else 0 := match xs with
  | [] => by simp
  | y :: ys => by simp [uniformSelectList_cons]

@[simp, grind =] lemma probEvent_uniformSelectList
    (xs : List α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ xs] = (xs.countP p : ℝ≥0∞) / xs.length := match xs with
  | [] => by simp
  | y :: ys => by
    simp only [uniformSelectList_cons, Fin.getElem_fin, liftM_map, probEvent_map,
      OptionT.probEvent_liftM, probEvent_uniformFin, Function.comp_apply,
      Fin.countP_eq_countP_map_finRange, Nat.cast_add, Nat.cast_one, List.length_cons]
    congr 2
    exact List.countP_finRange_getElem (y :: ys) (fun b => decide (p b))

end uniformSelectList

section uniformSelectVector

/-- Select a random element from a vector by indexing into it with a uniform value.
TODO: different types of vectors in mathlib now -/
instance hasUniformSelectVector (α : Type) (n : ℕ) :
    HasUniformSelect! (Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> $[0..n]

variable {α : Type} {n : ℕ} (xs : Vector α (n + 1))

lemma uniformSelectVector_def : $! xs = (xs[·]) <$> $[0..n] := rfl

@[simp, grind =]
lemma support_uniformSelectVector : support ($! xs) = {x | x ∈ xs.toList} := by
  ext x
  simp [uniformSelectVector_def, Vector.mem_iff_getElem, Fin.exists_iff]

@[simp, grind =]
lemma finSupport_uniformSelectVector [DecidableEq α] :
    finSupport ($ xs) = xs.toList.toFinset := by
  rw [uniformSelect_eq_liftM_uniformSelect!, OptionT.finSupport_liftM]
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformSelectVector]

@[simp, grind =]
lemma probOutput_uniformSelectVector [DecidableEq α] (x : α) :
    Pr[= x | $! xs] = xs.count x / (n + 1) := by
  simp [uniformSelectVector_def, probOutput_map_eq_sum_finSupport_ite, div_eq_mul_inv,
    ← Vector.card_eq_count]

@[simp, grind =]
lemma probEvent_uniformSelectVector (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ xs] = xs.toList.countP p / (n + 1) := by
  simp [uniformSelect_eq_liftM_uniformSelect!, uniformSelectVector_def,
    probEvent_eq_sum_fintype_ite, div_eq_mul_inv, ← Vector.card_eq_countP]

end uniformSelectVector

section uniformSelectListVector

instance hasUniformSelectListVector (α : Type) (n : ℕ) :
    HasUniformSelect! (List.Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> $[0..n]

variable {α : Type} {n : ℕ} (xs : List.Vector α (n + 1))

lemma uniformSelectListVector_def : $! xs = (xs[·]) <$> $[0..n] := rfl

@[simp, grind =]
lemma probOutput_uniformSelectListVector [DecidableEq α] (x : α) :
    Pr[= x | $! xs] = xs.toList.count x / (n + 1) := by
  simp [uniformSelectListVector_def, probOutput_map_eq_sum_finSupport_ite, div_eq_mul_inv,
    ← List.Vector.card_eq_count]

@[simp, grind =]
lemma probEvent_uniformSelectListVector (p : α → Prop) [DecidablePred p] :
    Pr[ p | $! xs] = xs.toList.countP p / (n + 1) := by
  simp [uniformSelectListVector_def, probEvent_eq_sum_fintype_ite, div_eq_mul_inv,
    ← List.Vector.card_eq_countP]

end uniformSelectListVector

section uniformSelectFinset

/-- Choose a random element from a finite set, by converting to a list and choosing from that.
This is noncomputable as we don't have a canoncial ordering for the resulting list,
so generally this should be avoided when possible. -/
noncomputable instance hasUniformSelectFinset (α : Type) :
    HasUniformSelect (Finset α) α where
  uniformSelect s := $ s.toList

variable {α : Type} (s : Finset α)

lemma uniformSelectFinset_def : $ s = $ s.toList := rfl

@[simp, grind =]
lemma support_uniformSelectFinset :
    support ($ s) = if s.Nonempty then ↑s else ∅ := by
  aesop (add norm uniformSelectFinset_def)

@[simp, grind =]
lemma finSupport_uniformSelectFinset [DecidableEq α] :
    finSupport ($ s) = if s.Nonempty then s else ∅ := by
  aesop (add norm uniformSelectFinset_def)

@[simp, grind =]
lemma probOutput_uniformSelectFinset [DecidableEq α] (x : α) :
    Pr[= x | $ s] = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  aesop (add norm uniformSelectFinset_def)

@[simp, grind =]
lemma probEvent_uniformSelectFinset (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ s] = {x ∈ s | p x}.card / s.card := by
  simp only [uniformSelectFinset_def, probEvent_uniformSelectList, Finset.length_toList,
    ← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter, Finset.card_def,
    Finset.filter_val]

@[simp, grind =]
lemma probFailure_uniformSelectFinset :
    Pr[⊥ | $ s] = if s.Nonempty then 0 else 1 := by
  aesop (add norm uniformSelectFinset_def)

end uniformSelectFinset

section uniformSelectArray

instance hasUniformSelectArray (α : Type _) : HasUniformSelect (Array α) α where
  uniformSelect xs := if h : xs.size = 0 then failure else do
    let u ← $[0..xs.size-1]
    return xs[u] -- Note the in-index bound here relies on `h`.

variable {α : Type} (xs : Array α)

lemma uniformSelectArray_def :
    ($ xs : OptionT ProbComp α) =
      if h : xs.size = 0 then failure else do
        let u ← $[0..xs.size-1]
        return xs[u] := rfl

@[simp, grind =]
lemma uniformSelectArray_empty : ($ (#[] : Array α) : OptionT ProbComp α) = failure := rfl

@[simp, grind =]
lemma support_uniformSelectArray : support ($ xs) = {x | x ∈ xs} := by
  ext x
  rcases Nat.eq_zero_or_pos xs.size with h | h
  · simp [Array.size_eq_zero_iff.mp h]
  · rw [uniformSelectArray_def, dif_neg h.ne']
    simp [Array.mem_iff_getElem, Fin.exists_iff, eq_comm, Nat.sub_add_cancel h]

@[simp, grind =]
lemma finSupport_uniformSelectArray [DecidableEq α] :
    finSupport ($ xs) = xs.toList.toFinset := by
  simp [finSupport_eq_iff_support_eq_coe, support_uniformSelectArray]

@[simp, grind =]
lemma probFailure_uniformSelectArray : Pr[⊥ | $ xs] = if xs.size = 0 then 1 else 0 := by
  by_cases h : xs.size = 0
  · have hxs : xs = #[] := Array.size_eq_zero_iff.mp h
    subst hxs; simp
  · rw [uniformSelectArray_def, dif_neg h]
    simp [h]

-- TODO: `probOutput_uniformSelectArray` and `probEvent_uniformSelectArray` analogous to the
-- `List` API. These need a careful `Fin (xs.size - 1 + 1) ≃ Fin xs.size` reindexing that
-- the present helpers don't cleanly factor. Bridging through `xs.toList` once a clean
-- `($ xs : OptionT ProbComp α) = $ xs.toList` lemma lands is probably the right path.

end uniformSelectArray

section uniformSelectMultiset

/-- Choose a random element from a multiset, by converting to a list and choosing from that.
This is noncomputable as the underlying list is only canonical up to permutation; for any
fixed `Multiset.toList` representative each element is sampled with weight equal to its
multiplicity. -/
noncomputable instance hasUniformSelectMultiset (α : Type) :
    HasUniformSelect (Multiset α) α where
  uniformSelect s := $ s.toList

variable {α : Type} (s : Multiset α)

lemma uniformSelectMultiset_def : ($ s : OptionT ProbComp α) = $ s.toList := rfl

@[simp, grind =]
lemma support_uniformSelectMultiset :
    support ($ s) = {x | x ∈ s} := by
  ext x; simp [uniformSelectMultiset_def, Multiset.mem_toList]

@[simp, grind =]
lemma finSupport_uniformSelectMultiset [DecidableEq α] :
    finSupport ($ s) = s.toFinset := by
  apply finSupport_eq_of_support_eq_coe
  ext x
  simp [Multiset.mem_toFinset]

@[simp, grind =]
lemma probOutput_uniformSelectMultiset [DecidableEq α] (x : α) :
    Pr[= x | $ s] = (s.count x : ℝ≥0∞) / Multiset.card s := by
  simp [uniformSelectMultiset_def, ← Multiset.coe_count]

@[simp, grind =]
lemma probEvent_uniformSelectMultiset (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ s] = (Multiset.countP p s : ℝ≥0∞) / Multiset.card s := by
  simp [uniformSelectMultiset_def, ← Multiset.coe_countP]

@[simp, grind =]
lemma probFailure_uniformSelectMultiset :
    Pr[⊥ | $ s] = if 0 < Multiset.card s then 0 else 1 := by
  grind [uniformSelectMultiset_def, probFailure_uniformSelectList, Multiset.empty_toList,
    Multiset.card_eq_zero]

end uniformSelectMultiset

end ProbComp

section coinSpec
-- NOTE: This treats `coin` as essentially part of `ProbComp`, but it is more general.
-- In particular we can have a seperate theory of bounded uniform selection using only coins.

@[simp, grind =]
lemma support_coin : support coin = {true, false} := by aesop

@[simp, grind =]
lemma finSupport_coin : finSupport coin = {true, false} := by aesop

@[simp, grind =]
lemma probOutput_coin (b : Bool) : Pr[= b | coin] = 2⁻¹ := by aesop

@[simp, grind =]
lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] :
    Pr[ p | coin] = if p true then
      (if p false then 1 else 2⁻¹) else
      (if p false then 2⁻¹ else 0) := by
  rw [probEvent_eq_sum_fintype_ite, Fintype.sum_bool]
  split_ifs <;> simp_all [ENNReal.inv_two_add_inv_two]

@[simp, grind =]
lemma probFailure_coin : Pr[⊥ | coin] = 0 := by grind

end coinSpec


