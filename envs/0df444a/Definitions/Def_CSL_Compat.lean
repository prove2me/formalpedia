-- Prove2me | Definitions.Def_CSL_Compat
-- name    : CSL_Compat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T11:58:59.112803+00:00
-- url     : https://prove2.me/theorems/6194cb8d-f0d2-4c37-b1d1-fe24f67e47d3
-- title:
--   Coded sorting bridge: CSL Compat
-- statement:
--   Compatibility layer for the upstream port (Lean v4.19 Mathlib → current Mathlib).
--
--   Current Mathlib removed the predicate `List.Sorted r l` (it was a synonym for
--   `List.Pairwise r l`) together with a few lemmas about it. This module restores that
--   synonym and the lemma names used by the port, each proved from the current API.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Mathlib.Data.List.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fin.Basic

/-! Compatibility layer for the upstream port (Lean v4.19 Mathlib → current Mathlib).

Current Mathlib removed the predicate `List.Sorted r l` (it was a synonym for
`List.Pairwise r l`) together with a few lemmas about it. This module restores that
synonym and the lemma names used by the port, each proved from the current API. -/

namespace List

/-- `Sorted r l`: the list `l` is `r`-sorted, i.e. `List.Pairwise r l`
(the former Mathlib definition). -/
abbrev Sorted {α : Type*} (r : α → α → Prop) (l : List α) : Prop := l.Pairwise r

theorem sorted_cons {α : Type*} {r : α → α → Prop} {a : α} {l : List α} :
    Sorted r (a :: l) ↔ (∀ b ∈ l, r a b) ∧ Sorted r l := pairwise_cons

theorem eq_of_perm_of_sorted {α : Type*} {r : α → α → Prop} [Std.Antisymm r]
    {l₁ l₂ : List α} (hp : l₁.Perm l₂) (hs₁ : Sorted r l₁) (hs₂ : Sorted r l₂) : l₁ = l₂ :=
  hp.eq_of_pairwise' hs₁ hs₂

theorem Sorted.merge {α : Type*} {r : α → α → Prop} [DecidableRel r] [Std.Total r] [IsTrans α r]
    {l l' : List α} (h : Sorted r l) (h' : Sorted r l') :
    Sorted r (List.merge l l' (r · ·)) := Pairwise.merge h h'

theorem Sorted.eq_of_mem_iff {α : Type*} {r : α → α → Prop} [Std.Antisymm r] [Std.Irrefl r]
    {l₁ l₂ : List α} (h₁ : Sorted r l₁) (h₂ : Sorted r l₂) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) :
    l₁ = l₂ := Pairwise.eq_of_mem_iff h₁ h₂ h

theorem sorted_insertionSort {α : Type*} (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (l : List α) : Sorted r (insertionSort r l) := pairwise_insertionSort r l

theorem sorted_le_replicate {α : Type*} [Preorder α] (n : ℕ) (a : α) :
    Sorted (· ≤ ·) (replicate n a) := pairwise_replicate.mpr (Or.inr le_rfl)

theorem sorted_mergeSort {α : Type*} {le : α → α → Bool}
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), le a b || le b a) (l : List α) :
    (mergeSort l le).Pairwise (fun a b => le a b) := pairwise_mergeSort trans total l

end List

theorem Monotone.ofFn_sorted {n : ℕ} {α : Type*} [Preorder α] {f : Fin n → α}
    (h : Monotone f) : (List.ofFn f).Sorted (· ≤ ·) :=
  List.pairwise_ofFn.2 (fun _ _ hij => h hij.le)

/-! Renamed lemmas: the old names used by the upstream development. -/

namespace List

theorem chain'_cons {α : Type*} {R : α → α → Prop} {x y : α} {l : List α} :
    Chain' R (x :: y :: l) ↔ R x y ∧ Chain' R (y :: l) := isChain_cons_cons

theorem chain'_iff_get {α : Type*} {R : α → α → Prop} {l : List α} :
    Chain' R l ↔ ∀ (i : ℕ) (h : i < l.length - 1),
      R (l.get ⟨i, by omega⟩) (l.get ⟨i + 1, by omega⟩) := by
  change IsChain R l ↔ _
  rw [isChain_iff_getElem]
  constructor
  · intro h i hi
    exact h i (by omega)
  · intro h i hi
    exact h i (by omega)

theorem chain'_replicate_of_rel {α : Type*} {r : α → α → Prop} (n : ℕ) {a : α} (h : r a a) :
    Chain' r (replicate n a) := isChain_replicate_of_rel n h

theorem length_eq_zero {α : Type*} {l : List α} : l.length = 0 ↔ l = [] := length_eq_zero_iff

theorem finRange_map_get {α : Type*} (l : List α) : (finRange l.length).map l.get = l :=
  map_get_finRange l

theorem map_coe_finRange {n : ℕ} : (finRange n).map (fun i : Fin n => (i : ℕ)) = range n :=
  map_coe_finRange_eq_range

theorem take_append_eq_append_take {α : Type*} {l₁ l₂ : List α} {n : ℕ} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ := take_append

end List

theorem Option.some_bind {α β : Type*} (a : α) (f : α → Option β) : (some a).bind f = f a :=
  Option.bind_some a f

theorem Option.bind_eq_some {α β : Type*} {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := Option.bind_eq_some_iff

def Option.decidable_eq_none {α : Type*} (o : Option α) : Decidable (o = none) :=
  Option.decidableEqNone o

theorem Fin.cast_trans {k m n : ℕ} (h : n = m) (h' : m = k) {i : Fin n} :
    Fin.cast h' (Fin.cast h i) = Fin.cast (h.trans h') i := Fin.cast_cast h h'

theorem Nat.pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} :
    b ^ y < x ↔ y < Nat.clog b x := (Nat.lt_clog_iff_pow_lt hb).symm

theorem Nat.le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} :
    x ≤ b ^ y ↔ Nat.clog b x ≤ y := (Nat.clog_le_iff_le_pow hb).symm

theorem lt_iff_le_not_le {α : Type*} [Preorder α] {a b : α} : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  lt_iff_le_not_ge


