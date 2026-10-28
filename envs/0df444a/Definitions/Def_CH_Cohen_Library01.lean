-- Prove2me | Definitions.Def_CH_Cohen_Library01
-- name    : CH_Cohen_Library01
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T01:46:40.24254+00:00
-- url     : https://prove2.me/theorems/c0ef3af3-7834-4232-a9e7-7d0ffa1a2539
-- title:
--   Boolean-valued set theory: ToMathlib, PSetOrdinal
-- statement:
--   This module provides length-indexed vectors, Boolean-algebra operations, and cardinal interfaces; well-founded preset representations of ordinals and cardinals. These objects form the language and model interfaces used in the forcing and completeness arguments.
--
--   **Formalization Note** The module retains the structural normalization facts needed by these definitions and their constructor proofs. The principal forcing and model-existence assertions are separate theorem nodes.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/ToMathlib.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/PSetOrdinal.lean

import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Card
import Mathlib.Topology.Clopen
import Mathlib.Topology.Constructions
import Mathlib.Data.PFun
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.Cardinal.Pigeonhole
/-
Physical source: Flypitch, Jesse Han and Floris van Doorn (Apache-2.0).
Lean 4 port: Ian Klatzco, with Claude.
Upstream commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815.
Original notices and source statements are retained.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/- Source module: Definitions.Flypitch4.ToMathlib -/
section CohenSource_ToMathlib
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/to_mathlib.lean -/











set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w w'

/-! ## Lean 3 → Lean 4 Port: Renames and Drops

### Renames (for downstream file porters, search counts in src/)

1. `imp_self` → `ba_imp_self` (renamed to avoid collision with Lean 4 core `imp_self`)
   - Call sites: `src/henkin.lean:210`, `src/fol.lean:2097` (2 sites)

2. `le_trans'` → `le_trans_inf` (renamed to avoid collision with mathlib4 `ge_trans` alias and
   Lean 4 core `le_trans'` for lists)
   - Call sites: `src/bfol.lean:706`, `src/bvm.lean:64`, `:2475`, `:2481`,
   `src/bvm_extras.lean:2121`, `:2124` (6 sites)

3. `mk_union_le` → `mk_union_le_impl` (kept as wrapper; mathlib4 has `Cardinal.mk_union_le`)
   - Call site: `src/collapse.lean:570` — when collapse is ported, prefer
   `Cardinal.mk_union_le` over our wrapper

4. `nontrivial.bot_lt_top` → `nontrivial_bot_lt_top` (flattened from sub-namespace dot notation;
   class accessor pattern changes in Lean 4)
   - Call sites: `src/bfol.lean:790`, `src/bvm.lean:1596`, `src/zfc.lean:519`, `:534` (4 sites)

### Drops (declarations removed because they exist in mathlib4)

1. `congr1` and `rexact` tactics (src/to_mathlib.lean:492-510)
   - `congr1` was a custom tactic used in ~10 downstream Lean 3 proof sites
   - In Lean 4, `congr 1` (with a space) is a built-in tactic
   - When porting `fol`, `henkin`, `language_extension`, etc., translate `congr1` (no space) to
   `congr 1` (with space) inline rather than re-implementing

2. `complete_degenerate_boolean_algebra` (src/to_mathlib.lean:756)
   - Replaced by mathlib4's `PUnit.instCompleteBooleanAlgebra` in
   `Mathlib/Order/CompleteBooleanAlgebra.lean`
   - No downstream `src/` file uses this directly
-/

/-!
## function namespace

`Function.Injective.ne_iff` already exists in mathlib4. No redeclaration needed.
-/

/-! ## dvector type and namespace -/

/-- Dependent-length vector: a list of exactly `n` elements of type `α`. -/
inductive DVec (α : Type u) : ℕ → Type u
  | nil  : DVec α 0
  | cons : ∀ {n} (x : α) (xs : DVec α n), DVec α (n + 1)

/-- Finite type with `n` elements, used with `DVec`. -/
inductive DFin : ℕ → Type
  | fz {n} : DFin (n + 1)
  | fs {n} : DFin n → DFin (n + 1)

instance haszeroDFin {n} : Zero (DFin (n + 1)) := ⟨DFin.fz⟩

namespace DVec

variable {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

@[simp] protected theorem zero_eq : ∀ (xs : DVec α 0), xs = DVec.nil
  | DVec.nil => rfl

@[simp] protected def concat : ∀ {n : ℕ}, DVec α n → α → DVec α (n + 1)
  | _, DVec.nil, x' => DVec.cons x' DVec.nil
  | _, DVec.cons x xs, x' => DVec.cons x (DVec.concat xs x')

@[simp] protected def nth : ∀ {n : ℕ}, DVec α n → (m : ℕ) → m < n → α
  | _, DVec.nil, m, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons x _, 0, _ => x
  | _, DVec.cons _ xs, m + 1, h => DVec.nth xs m (Nat.lt_of_succ_lt_succ h)



@[reducible, simp] protected def last {n : ℕ} (xs : DVec α (n + 1)) : α :=
  xs.nth n (Nat.lt_succ_self n)





protected def mem : ∀ {n : ℕ}, α → DVec α n → Prop
  | _, _, DVec.nil => False
  | _, x, DVec.cons x' xs => x = x' ∨ DVec.mem x xs

instance membershipDVec {n : ℕ} : Membership α (DVec α n) :=
  ⟨fun xs a => DVec.mem a xs⟩

protected def pmem : ∀ {n : ℕ}, α → DVec α n → Type
  | _, _, DVec.nil => Empty
  | _, x, DVec.cons x' xs => PSum (x = x') (DVec.pmem x xs)

protected theorem mem_of_pmem : ∀ {n : ℕ} {x : α} {xs : DVec α n}, DVec.pmem x xs → x ∈ xs
  | _, _, DVec.nil, hx => hx.elim
  | _, x, DVec.cons x' xs, hx => by
    -- x ∈ DVec.cons x' xs = DVec.mem x (DVec.cons x' xs) = x = x' ∨ DVec.mem x xs
    show DVec.mem x (DVec.cons x' xs)
    exact hx.casesOn (fun h => Or.inl h) (fun h => Or.inr (DVec.mem_of_pmem h))

@[simp] protected def map (f : α → β) : ∀ {n : ℕ}, DVec α n → DVec β n
  | _, DVec.nil => DVec.nil
  | _, DVec.cons x xs => DVec.cons (f x) (DVec.map f xs)

@[simp] protected def map2 (f : α → β → γ) : ∀ {n : ℕ}, DVec α n → DVec β n → DVec γ n
  | _, DVec.nil, DVec.nil => DVec.nil
  | _, DVec.cons x xs, DVec.cons y ys => DVec.cons (f x y) (DVec.map2 f xs ys)

@[simp] protected theorem map_id : ∀ {n : ℕ} (xs : DVec α n), DVec.map (fun x => x) xs = xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, DVec.map_id xs]

@[simp] protected theorem map_congr_pmem {f g : α → β} :
    ∀ {n : ℕ} {xs : DVec α n}, (∀ x, DVec.pmem x xs → f x = g x) →
      DVec.map f xs = DVec.map g xs
  | _, DVec.nil, _ => rfl
  | _, DVec.cons x xs, h => by
    simp only [DVec.map]
    congr 1
    · exact h x (PSum.inl rfl)
    · exact DVec.map_congr_pmem (fun x' hx' => h x' (PSum.inr hx'))

@[simp] protected theorem map_congr_mem {f g : α → β} {n : ℕ} {xs : DVec α n}
    (h : ∀ x, x ∈ xs → f x = g x) : DVec.map f xs = DVec.map g xs :=
  DVec.map_congr_pmem (fun x hx => h x (DVec.mem_of_pmem hx))

@[simp] protected theorem map_congr {f g : α → β} (h : ∀ x, f x = g x) :
    ∀ {n : ℕ} (xs : DVec α n), DVec.map f xs = DVec.map g xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, h, DVec.map_congr h xs]

@[simp] protected theorem map_map (g : β → γ) (f : α → β) : ∀ {n : ℕ} (xs : DVec α n),
    DVec.map g (DVec.map f xs) = DVec.map (fun x => g (f x)) xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, DVec.map_map g f xs]



@[simp] protected theorem map_concat (f : α → β) : ∀ {n : ℕ} (xs : DVec α n) (x : α),
    DVec.map f (DVec.concat xs x) = DVec.concat (DVec.map f xs) (f x)
  | _, DVec.nil, _ => rfl
  | _, DVec.cons _ xs, x' => by simp [DVec.map, DVec.concat, DVec.map_concat f xs x']

@[simp] protected theorem map_nth (f : α → β) : ∀ {n : ℕ} (xs : DVec α n) (m : ℕ) (h : m < n),
    DVec.nth (DVec.map f xs) m h = f (DVec.nth xs m h)
  | _, DVec.nil, m, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons _ _, 0, _ => rfl
  | _, DVec.cons _ xs, m + 1, h => DVec.map_nth f xs m _

protected theorem concat_nth : ∀ {n : ℕ} (xs : DVec α n) (x : α) (m : ℕ) (h' : m < n + 1)
    (h : m < n), DVec.nth (DVec.concat xs x) m h' = DVec.nth xs m h
  | _, DVec.nil, _, m, _, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons _ _, _, 0, _, _ => rfl
  | _, DVec.cons _ xs, x', m + 1, h', h => by
    simp only [DVec.concat, DVec.nth]
    exact DVec.concat_nth xs x' m _ _

@[simp] protected theorem concat_nth_last : ∀ {n : ℕ} (xs : DVec α n) (x : α) (h : n < n + 1),
    DVec.nth (DVec.concat xs x) n h = x
  | _, DVec.nil, _, _ => rfl
  | _, DVec.cons _ xs, x', h => by simp [DVec.concat, DVec.nth, DVec.concat_nth_last xs x']

@[simp] protected theorem concat_nth_last' : ∀ {n : ℕ} (xs : DVec α n) (x : α) (h : n < n + 1),
    DVec.last (DVec.concat xs x) = x := DVec.concat_nth_last

@[simp] protected def append : ∀ {n m : ℕ}, DVec α n → DVec α m → DVec α (m + n)
  | _, _, DVec.nil, xs => xs
  | _, _, DVec.cons x' xs, xs' => DVec.cons x' (DVec.append xs xs')

@[simp] protected def insert : ∀ {n : ℕ}, α → ℕ → DVec α n → DVec α (n + 1)
  | n, x, 0, xs => DVec.cons x xs
  | 0, x, _, _ => DVec.cons x DVec.nil
  | n + 1, x, k + 1, DVec.cons y ys => DVec.cons y (DVec.insert x k ys)

@[simp] protected theorem insert_at_zero : ∀ {n : ℕ} (x : α) (xs : DVec α n),
    DVec.insert x 0 xs = DVec.cons x xs := by
  intro n; cases n <;> intros <;> rfl

@[simp] protected theorem insert_nth : ∀ {n : ℕ} (x : α) (k : ℕ) (xs : DVec α n) (h : k < n + 1),
    DVec.nth (DVec.insert x k xs) k h = x
  | 0, x, 0, _, _ => rfl
  | 0, x, k + 1, _, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | n + 1, x, 0, _, _ => by simp [DVec.insert, DVec.nth]
  | n + 1, x, k + 1, DVec.cons _ ys, h => by
    simp [DVec.insert, DVec.nth]
    exact DVec.insert_nth x k ys _



/-- The n-th initial segment of a vector, given a proof that n ≤ m. -/
@[simp] protected def trunc : ∀ (n) {m : ℕ}, n ≤ m → DVec α m → DVec α n
  | 0, 0, _, _ => DVec.nil
  | 0, _ + 1, _, _ => DVec.nil
  | n + 1, 0, h, _ => absurd h (Nat.not_succ_le_zero n)
  | n + 1, m + 1, h, DVec.cons x xs =>
    DVec.cons x (DVec.trunc n (Nat.lt_succ_iff.mp (Nat.lt_of_succ_le h)) xs)

@[simp] protected theorem trunc_n_n {n : ℕ} {h : n ≤ n} {v : DVec α n} :
    DVec.trunc n h v = v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [DVec.trunc, ih]

@[simp] protected theorem trunc_0_n {n : ℕ} {h : 0 ≤ n} {v : DVec α n} :
    DVec.trunc 0 h v = DVec.nil := by cases v <;> rfl

@[simp] protected theorem trunc_nth {n m l : ℕ} {h : n ≤ m} {h' : l < n} {v : DVec α m} :
    DVec.nth (DVec.trunc n h v) l h' = DVec.nth v l (Nat.lt_of_lt_of_le h' h) := by
  induction m generalizing n l with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero h
    subst this; exact absurd h' (Nat.not_lt_zero _)
  | succ m ih =>
    cases n with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ n =>
      cases l with
      | zero =>
        cases v with
        | cons _ _ => rfl
      | succ l =>
        cases v with
        | cons _ vs =>
          show DVec.nth (DVec.trunc n _ vs) l _ = DVec.nth vs l _
          apply ih



protected def cast {n m} (p : n = m) (v : DVec α n) : DVec α m := p ▸ v

@[simp] protected theorem cast_irrel {n m} {p p' : n = m} {v : DVec α n} :
    DVec.cast p v = DVec.cast p' v := rfl

@[simp] protected theorem cast_rfl {n m} {p : n = m} {q : m = n} {v : DVec α n} :
    DVec.cast q (DVec.cast p v) = v := by subst p; rfl



@[simp] protected theorem cast_trans {n m o} {p : n = m} {q : m = o} {v : DVec α n} :
    DVec.cast q (DVec.cast p v) = DVec.cast (p.trans q) v := by subst p; subst q; rfl

@[simp] theorem cast_cons {n m} (h : n + 1 = m + 1) (x : α) (v : DVec α n) :
    DVec.cast h (DVec.cons x v) = DVec.cons x (DVec.cast (Nat.succ_injective h) v) := by
  cases h; rfl

@[simp] theorem cast_append_nil : ∀ {n} (v : DVec α n) (h : 0 + n = n),
    DVec.cast h (DVec.append v DVec.nil) = v
  | _, DVec.nil, _ => rfl
  | _, DVec.cons x v, h => by
    simp only [DVec.append, cast_cons]
    congr 1
    exact cast_append_nil v (by omega)

@[simp] protected def remove_mth : ∀ {n : ℕ}, ℕ → DVec α (n + 1) → DVec α n
  | 0, _, _ => DVec.nil
  | n, 0, DVec.cons _ ys => ys
  | n + 1, k + 1, DVec.cons y ys => DVec.cons y (DVec.remove_mth k ys)

@[simp] protected def replace : ∀ {n : ℕ}, α → ℕ → DVec α n → DVec α n
  | _, x, 0, DVec.cons _ ys => DVec.cons x ys
  | 0, _, _, ys => ys
  | n + 1, x, k + 1, DVec.cons y ys => DVec.cons y (DVec.replace x k ys)

protected theorem insert_nth_lt {n k l : ℕ} (x : α) (xs : DVec α n) (h : l < n)
    (h' : l < n + 1) (h2 : l < k) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs l h := by
  induction xs generalizing k l with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons x' xs ih =>
    cases k with
    | zero => exact absurd h2 (Nat.not_lt_zero _)
    | succ k =>
      cases l with
      | zero => rfl
      | succ l =>
        simp [DVec.insert, DVec.nth]
        exact ih (Nat.lt_of_succ_lt_succ h) (Nat.lt_of_succ_lt_succ h')
          (Nat.lt_of_succ_lt_succ h2)

protected theorem insert_nth_gt' {n k l : ℕ} (x : α) (xs : DVec α n)
    (h : l - 1 < n) (h' : l < n + 1) (h2 : k < l) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs (l - 1) h := by
  induction xs generalizing k l with
  | nil =>
    cases k with
    | zero =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l => simp [DVec.insert, DVec.nth]
    | succ k =>
      cases l with
      | zero => exact absurd h (Nat.not_lt_zero _)
      | succ l => exact absurd h' (by omega)
  | cons x' xs ih =>
    cases k with
    | zero =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l => simp [DVec.insert, DVec.nth]
    | succ k =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l =>
        cases l with
        | zero => exact absurd h2 (by omega)
        | succ l =>
          simp [DVec.insert, DVec.nth]
          have := ih (k := k) (l := l + 1) (by omega) (Nat.lt_of_succ_lt_succ h') (by omega)
          simp at this ⊢
          convert this using 2 <;> omega

@[simp] protected theorem insert_nth_gt_simp {n k l : ℕ} (x : α) (xs : DVec α n)
    (h' : l < n + 1) (h2 : k < l) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs (l - 1) (by omega) :=
  DVec.insert_nth_gt' x xs (by omega) h' h2



@[simp] lemma replace_head {n x z} {xs : DVec α n} :
    DVec.replace z 0 (DVec.cons x xs) = DVec.cons z xs := rfl

@[simp] lemma replace_neck {n x y z} {xs : DVec α n} :
    DVec.replace z 1 (DVec.cons x (DVec.cons y xs)) = DVec.cons x (DVec.cons z xs) := rfl

@[simp] def foldr (f : α → β → β) (b : β) : ∀ {n}, DVec α n → β
  | _, DVec.nil => b
  | _, DVec.cons a l => f a (DVec.foldr f b l)

@[simp] def zip : ∀ {n}, DVec α n → DVec β n → DVec (α × β) n
  | _, DVec.nil, DVec.nil => DVec.nil
  | _, DVec.cons x xs, DVec.cons y ys => DVec.cons (x, y) (DVec.zip xs ys)

/-- The finitary infimum -/
def fInf [SemilatticeInf α] [OrderTop α] (xs : DVec α n) : α :=
  DVec.foldr (fun (x b : α) => x ⊓ b) ⊤ xs

@[simp] lemma fInf_nil [SemilatticeInf α] [OrderTop α] : fInf (DVec.nil (α := α)) = ⊤ := rfl

@[simp] lemma fInf_cons [SemilatticeInf α] [OrderTop α] (x : α) (xs : DVec α n) :
    fInf (DVec.cons x xs) = x ⊓ fInf xs := rfl

/-- The finitary supremum -/
def fSup [SemilatticeSup α] [OrderBot α] (xs : DVec α n) : α :=
  DVec.foldr (fun (x b : α) => x ⊔ b) ⊥ xs

@[simp] lemma fSup_nil [SemilatticeSup α] [OrderBot α] : fSup (DVec.nil (α := α)) = ⊥ := rfl

@[simp] lemma fSup_cons [SemilatticeSup α] [OrderBot α] (x : α) (xs : DVec α n) :
    fSup (DVec.cons x xs) = x ⊔ fSup xs := rfl

/-- Pointwise relation on DVec, given a setoid on the element type -/
inductive DVecRel {α : Type u} [Setoid α] : ∀ {n : ℕ}, DVec α n → DVec α n → Prop
  | rnil : DVecRel DVec.nil DVec.nil
  | rcons {x x' : α} {n : ℕ} {xs xs' : DVec α n} (hx : x ≈ x') (hxs : DVecRel xs xs') :
      DVecRel (DVec.cons x xs) (DVec.cons x' xs')

protected theorem rel_refl {α : Type u} [Setoid α] {n} (xs : DVec α n) : DVecRel xs xs := by
  induction xs with
  | nil => exact DVecRel.rnil
  | cons _ _ ih => exact DVecRel.rcons (Setoid.refl _) ih

protected theorem rel_symm {α : Type u} [Setoid α] {n} {xs xs' : DVec α n}
    (h : DVecRel xs xs') : DVecRel xs' xs := by
  induction h with
  | rnil => exact DVecRel.rnil
  | rcons hx _ ih => exact DVecRel.rcons (Setoid.symm hx) ih

protected theorem rel_trans {α : Type u} [Setoid α] {n} {xs₁ xs₂ xs₃ : DVec α n}
    (h₁ : DVecRel xs₁ xs₂) (h₂ : DVecRel xs₂ xs₃) : DVecRel xs₁ xs₃ := by
  induction h₁ with
  | rnil => exact h₂
  | rcons hx _ ih =>
    cases h₂ with
    | rcons hx₂ hxs₂ => exact DVecRel.rcons (Setoid.trans hx hx₂) (ih hxs₂)

instance setoidInst {α : Type u} [Setoid α] {n : ℕ} : Setoid (DVec α n) :=
  ⟨DVecRel, DVec.rel_refl, DVec.rel_symm, DVec.rel_trans⟩

noncomputable def quotient_lift {α : Type u} {β : Sort v} {R : Setoid α} :
    ∀ {n} (f : DVec α n → β)
    (_h : ∀ {xs xs' : DVec α n}, xs ≈ xs' → f xs = f xs')
    (qs : DVec (Quotient R) n), β
  | 0, f, _, DVec.nil => f DVec.nil
  | n + 1, f, h, DVec.cons q qs =>
    Quotient.lift
      (fun x => DVec.quotient_lift
        (fun xs => f (DVec.cons x xs))
        (fun hxs => h (DVecRel.rcons (Setoid.refl x) hxs))
        qs)
      (fun x x' hx => by
        congr 1; apply funext; intro xs
        apply h; exact DVecRel.rcons hx (DVec.rel_refl xs))
      q

theorem quotient_beta {α : Type u} {β : Sort v} {R : Setoid α} :
    ∀ {n} (f : DVec α n → β)
    (h : ∀ {xs xs' : DVec α n}, xs ≈ xs' → f xs = f xs') (xs : DVec α n),
    DVec.quotient_lift f h (DVec.map Quotient.mk'' xs) = f xs
  | 0, f, h, DVec.nil => rfl
  | n + 1, f, h, DVec.cons x xs => by
    simp only [DVec.map, DVec.quotient_lift, Quotient.lift_mk]
    exact quotient_beta
      (fun xs' => f (DVec.cons x xs'))
      (fun hxs => h (DVecRel.rcons (Setoid.refl x) hxs))
      xs

end DVec

/-! ## set namespace -/

namespace Set



@[simp] theorem not_nonempty_iff {α} {s : Set α} : ¬Nonempty s ↔ s = ∅ := by
  rw [Set.nonempty_coe_sort, Set.not_nonempty_iff_eq_empty]



@[simp] theorem subset_biInter_iff {α β} {s : Set α} {t : Set β} {u : α → Set β} :
    t ⊆ ⋂ x ∈ s, u x ↔ ∀ x ∈ s, t ⊆ u x :=
  Set.subset_iInter₂_iff

-- subset_sInter_iff is already in Mathlib as Set.subset_sInter_iff



end Set

/-! ## topological_space section -/

section TopologicalSpace

open TopologicalSpace Set Filter

variable {α : Type u} {β : Type v}
variable [t : TopologicalSpace α] [TopologicalSpace β]











end TopologicalSpace

/-! ## ordinal namespace -/

namespace Ordinal

variable {σ : Type*}





end Ordinal

/-! ## cardinal namespace -/

namespace Cardinal

open scoped Cardinal

-- Note: Cardinal.mk_union_le already exists in mathlib4 (explicit args version).
-- Downstream files use `mk_union_le` with implicit args; that's directly served
-- by the mathlib4 version since Lean can infer the args. No redeclaration needed.
-- The alias below makes it available for direct call without name conflicts:




@[simp] theorem mk_union_countable_of_countable {α} {P Q : Set α}
    (HP : #P ≤ ℵ₀) (HQ : #Q ≤ ℵ₀) : #(P ∪ Q : Set α) ≤ ℵ₀ :=
  (Cardinal.mk_union_le P Q).trans (Cardinal.add_le_aleph0.mpr ⟨HP, HQ⟩)





end Cardinal

/-! ## nat namespace -/

namespace Nat



@[simp] theorem le_of_le_and_ne_succ {x y : ℕ} (H : x ≤ y + 1) (H' : x ≠ y + 1) : x ≤ y :=
  Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H H')

end Nat

/-! ## classical namespace (logic helpers) -/

namespace Classical

noncomputable def psigma_of_exists {α : Type u} {p : α → Prop} (h : ∃ x, p x) : Σ' x, p x :=
  ⟨Classical.choose h, Classical.choose_spec h⟩









end Classical

/-! ## list namespace -/

namespace List

@[simp] protected def toSet {α : Type u} (l : List α) : Set α := {x | x ∈ l}





end List

/-! ## additional nat lemmas -/

namespace Nat



end Nat

/-! ## misc prop lemmas -/





/-! ## additional set lemmas -/

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}





@[simp] theorem mem_image_univ {f : α → β} {x} : f x ∈ f '' Set.univ :=
  ⟨x, Set.mem_univ x, rfl⟩

theorem image_preimage_eq_of_subset_image {f : α → β} {s : Set β} {t : Set α}
    (h : s ⊆ f '' t) : f '' (f ⁻¹' s) = s :=
  Set.Subset.antisymm (Set.image_preimage_subset f s)
    (fun x hx => by obtain ⟨a, ha, rfl⟩ := h hx; exact Set.mem_image_of_mem f hx)



















end Set

/-! ## nonempty namespace -/

namespace Nonempty

variable {α : Sort u} {β : Sort v}



end Nonempty

/-! ## arity' type and namespace -/

/-- The type α → (α → ... (α → β)...) with n α's. -/
def Arity' (α β : Type u) : ℕ → Type u
  | 0 => β
  | n + 1 => α → Arity' α β n

namespace Arity'



@[simp] def of_dvector_map {α β : Type u} : ∀ {l} (f : DVec α l → β), Arity' α β l
  | 0, f => f DVec.nil
  | l + 1, f => fun x => of_dvector_map (fun xs => f (DVec.cons x xs))

@[simp] def arity'_app {α β : Type u} : ∀ {l}, Arity' α β l → DVec α l → β
  | _, b, DVec.nil => b
  | _, f, DVec.cons x xs => arity'_app (f x) xs

@[simp] theorem arity'_app_zero {α β : Type u} (f : Arity' α β 0) (xs : DVec α 0) :
    arity'_app f xs = f := by cases xs; rfl







inductive arity'_respect_setoid {α β : Type u} [R : Setoid α] : ∀ {n}, Arity' α β n → Type u
  | r_zero (b : β) : @arity'_respect_setoid _ _ _ 0 b
  | r_succ (n : ℕ) (f : Arity' α β (n + 1)) (h₁ : ∀ {a a'}, a ≈ a' → f a = f a')
    (h₂ : ∀ a, arity'_respect_setoid (f a)) : arity'_respect_setoid f

instance subsingleton_arity'_respect_setoid {α β : Type u} [R : Setoid α] {n} (f : Arity' α β n) :
    Subsingleton (arity'_respect_setoid f) := by
  constructor
  intro h h'
  induction h with
  | r_zero => cases h'; rfl
  | r_succ n f _ _ ih =>
    cases h' with
    | r_succ => congr; funext x; exact ih x _

def for_all {α : Type u} (P : α → Prop) : Prop := ∀ x, P x

@[simp] def arity'_map2 {α β : Type u} (q : (α → β) → β) (f : β → β → β) :
    ∀ {n}, Arity' α β n → Arity' α β n → β
  | 0, x, y => f x y
  | n + 1, x, y => q (fun z => arity'_map2 q f (x z) (y z))

@[simp] theorem arity'_map2_refl {α : Type} {f : Prop → Prop → Prop} (r : ∀ A, f A A) :
    ∀ {n} (x : Arity' α Prop n), arity'_map2 for_all f x x
  | 0, x => r x
  | n + 1, x => fun y => arity'_map2_refl r (x y)









end Arity'

/-! ## Miscellaneous lemmas -/

@[simp] theorem lt_irrefl' {α} [Preorder α] {Γ : α} (H_lt : Γ < Γ) : False :=
  lt_irrefl _ H_lt

/-! ## Boolean algebra / lattice helpers -/

/-- A nontrivial complete Boolean algebra has ⊥ < ⊤ -/
class NontrivialCompleteBooleanAlgebra (α : Type*) extends CompleteBooleanAlgebra α where
  bot_lt_top : (⊥ : α) < (⊤ : α)

@[simp] theorem nontrivial_bot_lt_top {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : (⊥ : α) < ⊤ :=
  H.bot_lt_top

@[simp] theorem nontrivial_bot_neq_top {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : ¬(⊥ = (⊤ : α)) :=
  ne_of_lt H.bot_lt_top

@[simp] theorem nontrivial_top_neq_bot {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : ¬(⊤ = (⊥ : α)) :=
  fun h => nontrivial_bot_neq_top h.symm

/-- Every NontrivialCompleteBooleanAlgebra is Nontrivial (witnesses: ⊥ ≠ ⊤). -/
instance (priority := 100) NontrivialCompleteBooleanAlgebra.toNontrivial {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : Nontrivial α :=
  ⟨⊥, ⊤, ne_of_lt H.bot_lt_top⟩



-- iSup/iInf distributivity (aliases for Lean 4 mathlib names)




theorem sup_iInf_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    a ⊔ (⨅ (i : ι), s i) = ⨅ (i : ι), a ⊔ s i :=
  sup_iInf_eq a s

theorem iInf_sup_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    (⨅ (i : ι), s i) ⊔ a = ⨅ (i : ι), s i ⊔ a := by
  rw [sup_comm, sup_iInf_eq']; simp_rw [sup_comm]

-- Aliases without `@[simp]`: mathlib4's `inf_idem`/`sup_idem` already carry `@[simp]`,
-- so adding `@[simp]` here would create duplicate rewrite rules.




-- Note: bot_lt_iff_not_le_bot and lt_top_iff_not_top_le already exist in mathlib4









/-- Material implication in a Boolean algebra -/
def imp {α : Type*} [BooleanAlgebra α] (a₁ a₂ : α) : α := a₁ᶜ ⊔ a₂

scoped[Flypitch] infixl:65 " ⟹ " => imp
open scoped Flypitch

@[reducible, simp] def biimp {α : Type*} [BooleanAlgebra α] (a₁ a₂ : α) : α :=
  imp a₁ a₂ ⊓ imp a₂ a₁

scoped[Flypitch] infixl:50 " ⇔ " => biimp









@[simp] theorem imp_le_of_right_le {α : Type*} [BooleanAlgebra α] {a a₁ a₂ : α} {h : a₁ ≤ a₂} :
    imp a a₁ ≤ imp a a₂ := sup_le_sup_left h _

@[simp] theorem imp_le_of_left_le {α : Type*} [BooleanAlgebra α] {a a₁ a₂ : α} {h : a₂ ≤ a₁} :
    imp a₁ a ≤ imp a₂ a := sup_le_sup_right (compl_le_compl h) _

@[simp] theorem imp_le_of_left_right_le {α : Type*} [BooleanAlgebra α] {a₁ a₂ b₁ b₂ : α}
    {h₁ : b₁ ≤ a₁} {h₂ : a₂ ≤ b₂} : imp a₁ a₂ ≤ imp b₁ b₂ :=
  sup_le_sup (compl_le_compl h₁) h₂





@[simp] theorem imp_bot {α : Type*} [BooleanAlgebra α] {a : α} : imp a ⊥ = aᶜ := by simp [imp]

@[simp] theorem top_imp {α : Type*} [BooleanAlgebra α] {a : α} : imp ⊤ a = a := by simp [imp]

@[simp] theorem ba_imp_self {α : Type*} [BooleanAlgebra α] {a : α} : imp a a = ⊤ := by
  simp [imp]
-- Note: Lean 4 already has a `imp_self` in core; use `ba_imp_self` for Boolean algebra version





theorem imp_inf_le {α : Type*} [BooleanAlgebra α] (a b : α) : imp a b ⊓ a ≤ b := by
  unfold imp; rw [inf_sup_right]; simp









@[simp] theorem imp_top_iff_le {α : Type*} [BooleanAlgebra α] {a₁ a₂ : α} :
    imp a₁ a₂ = ⊤ ↔ a₁ ≤ a₂ := by
  rw [imp, sup_comm, ← himp_eq]
  exact himp_eq_top_iff

theorem curry_uncurry {α : Type*} [BooleanAlgebra α] {a b c : α} :
    imp (a ⊓ b) c = imp a (imp b c) := by simp [imp]; ac_rfl

theorem deduction {α : Type*} [BooleanAlgebra α] {a b c : α} :
    a ⊓ b ≤ c ↔ a ≤ imp b c := by
  rw [← imp_top_iff_le, curry_uncurry, imp_top_iff_le]





-- Aliases without `@[simp]`: mathlib4's `iSup_option`/`iInf_option` already carry `@[simp]`.




























@[simp] theorem supr_congr {ι β : Type*} {s₁ s₂ : ι → β} [CompleteLattice β]
    {h : ∀ i : ι, s₁ i = s₂ i} : (⨆ (i : ι), s₁ i) = ⨆ (i : ι), s₂ i :=
  iSup_congr (fun i => h i)











-- Note: le_trans' already exists in Mathlib (as alias for ge_trans)
-- Use le_trans_inf for our version

@[simp] theorem top_le_imp_top {β : Type*} {b : β} [BooleanAlgebra β] : ⊤ ≤ imp b ⊤ := by
  rw [← deduction]; simp

theorem poset_yoneda_iff {β : Type*} [PartialOrder β] {a b : β} :
    a ≤ b ↔ ∀ {Γ : β}, Γ ≤ a → Γ ≤ b :=
  ⟨fun h _ hΓ => le_trans hΓ h, fun H => H le_rfl⟩



theorem poset_yoneda {β : Type*} [PartialOrder β] {a b : β}
    (H : ∀ Γ : β, Γ ≤ a → Γ ≤ b) : a ≤ b := poset_yoneda_iff.mpr (fun {Γ} => H Γ)

theorem poset_yoneda_inv {β : Type*} [PartialOrder β] {a b : β} (Γ : β) (H : a ≤ b) :
    Γ ≤ a → Γ ≤ b := poset_yoneda_iff.mp H





















theorem context_specialize {β : Type*} [CompleteLattice β] {ι : Type*} {s : ι → β}
    {Γ : β} (H : Γ ≤ ⨅ i, s i) (j : ι) : Γ ≤ s j :=
  le_trans H (iInf_le _ _)







theorem context_imp_elim {β : Type*} [CompleteBooleanAlgebra β] {a b Γ : β}
    (H₁ : Γ ≤ imp a b) (H₂ : Γ ≤ a) : Γ ≤ b :=
  le_trans (le_inf H₁ H₂) (imp_inf_le a b)





theorem neg_imp {β : Type*} [BooleanAlgebra β] {a b : β} : (imp a b)ᶜ = a ⊓ bᶜ := by
  simp [imp]







open scoped Cardinal in
def CCC (𝔹 : Type u) [BooleanAlgebra 𝔹] : Prop :=
  ∀ ι : Type u, ∀ 𝓐 : ι → 𝔹, (∀ i, ⊥ < 𝓐 i) →
    (∀ i j, i ≠ j → 𝓐 i ⊓ 𝓐 j ≤ ⊥) → (#ι) ≤ Cardinal.aleph0

noncomputable def Prop_to_bot_top {𝔹 : Type u} [Bot 𝔹] [Top 𝔹] : Prop → 𝔹 :=
  fun p => @ite 𝔹 p (Classical.propDecidable p) ⊤ ⊥

@[simp] theorem Prop_to_bot_top_true {𝔹 : Type u} [Bot 𝔹] [Top 𝔹] {p : Prop} (H : p) :
    Prop_to_bot_top p = (⊤ : 𝔹) := by
  simp only [Prop_to_bot_top, @if_pos _ (Classical.propDecidable p) H]

@[simp] theorem Prop_to_bot_top_false {𝔹 : Type u} [Bot 𝔹] [Top 𝔹] {p : Prop} (H : ¬p) :
    Prop_to_bot_top p = (⊥ : 𝔹) := by
  simp only [Prop_to_bot_top, @if_neg _ (Classical.propDecidable p) H]



/-! ## tactic.interactive section — DEFERRED

  The tactic extensions (bv_intro, bv_cases_at, bv_or_elim_at, specialize_context,
  bv_split, bv_and_intro, bv_imp_elim_at, bv_mp, bv_imp_intro, bv_split_goal,
  bv_or_inr, bv_or_inl, bv_contradiction, tidy_context, bv_exfalso,
  bv_cases_on, bv_exists_intro, bv_specialize_at, bv_to_pi, bv_to_pi') need
  a complete rewrite for Lean 4's macro/elab system.

  These are deferred until downstream files actually need them.
  - Main block: See src/to_mathlib.lean:1252-1684 for the original definitions.
  - Early block also deferred: src/to_mathlib.lean:492-510 contained `congr1` and `rexact`
    tactics. `congr1` is used in roughly 10 downstream Lean 3 proof sites. In Lean 4,
    `congr 1` (with a space) is a built-in tactic, so when porting `fol`, `henkin`,
    `language_extension`, etc., translate `congr1` (no space) to `congr 1` (with space)
    inline rather than re-implementing the tactic.
-/

-- with_h_asms helper definition



end CohenSource_ToMathlib


/- Source module: Definitions.Flypitch4.PSetOrdinal -/
section CohenSource_PSetOrdinal
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/pSet_ordinal.lean (lines 1-500) — Task 6a -/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
## Port notes (src/pSet_ordinal.lean → Flypitch4.PSetOrdinal)

### Key API renames

- `tactic.tidy` → `aesop` / `simp` / hand proofs
- `ordinal.limit_rec_on` → `induction η using Ordinal.limitRecOn`
- `ordinal.is_limit` → `Order.IsSuccLimit`
- `ordinal.lt_succ` / `lt_succ_self` → `Order.lt_succ`
- `ordinal.succ η` → `Order.succ η`
- `pSet` → `PSet`; `pSet.equiv` → `PSet.Equiv`; `pSet.mem.mk` → `PSet.Mem.mk`
- `pSet.succ x = insert x x` → `PSet.succ_ord x`
- `ordinal.mk` (Lean 3) → `Ordinal.toPSet` (mathlib4, aliased as `PSet.ordinalMk`)
- `mem_Union` → `PSet.mem_sUnion`
- `Set` (Lean 3 ZFC quotient) → `ZFSet`
- `Set.regularity` → `ZFSet.regularity`
- `push_neg` → `push Not` (deprecated, warning only)
- `ZFSet.not_mem_empty` → `ZFSet.notMem_empty`
- `⟦x⟧ : ZFSet` → `ZFSet.mk x` (more reliable elaboration)
- `typein` (in PSet namespace) → `Ordinal.typein` (fully qualified)
- `PSet.Type ∅ = PEmpty` (not `ULift Empty` as in Lean 3)
- `ordinal.mk_zero_type` etc: adapted to mathlib4 universe conventions

### Namespace choices for 6b, 6c

All declarations in `namespace PSet`.
`ordinalMk = Ordinal.toPSet`.
`succ_ord = insert x x`.
-/

universe u

noncomputable section

-- ============================================================
-- Ordinal namespace: tiny helper
-- ============================================================

namespace Ordinal



end Ordinal

-- ============================================================
-- PSet namespace
-- Lines 30+ of src/pSet_ordinal.lean
-- ============================================================

namespace PSet

-- `ordinalMk η` = `Ordinal.toPSet η` (the von Neumann ordinal as a pre-set).
abbrev ordinalMk : Ordinal.{u} → PSet.{u} := Ordinal.toPSet

-- `succ_ord x = insert x x` — the pre-set ordinal successor.
-- Named `succ_ord` to avoid collision with `Order.succ`.
@[reducible] def succ_ord (x : PSet) : PSet := insert x x

/-! ### Basic structural lemmas -/



@[simp] lemma mem_mk' {x : PSet} {i} : x.Func i ∈ x := PSet.func_mem x i







@[simp] lemma mem_self {x : PSet.{u}} (H : x ∈ x) : False :=
  PSet.mem_irrefl x H

-- typein of out.r is less than the ordinal itself


/-! ### Key facts about ordinalMk = Ordinal.toPSet -/

-- The type of `ordinalMk η` is `η.ToType`
@[simp] lemma ordinalMk_type {η : Ordinal} : (ordinalMk η).Type = η.ToType :=
  Ordinal.type_toPSet η

-- Membership characterization (the main tool)
lemma mem_ordinalMk_iff {η : Ordinal} {x : PSet} :
    x ∈ ordinalMk η ↔ ∃ a < η, Equiv x (ordinalMk a) :=
  Ordinal.mem_toPSet_iff

-- Elementary membership
lemma mk_mem_mk_of_lt {ξ η : Ordinal} (H_lt : ξ < η) :
    ordinalMk ξ ∈ ordinalMk η :=
  mem_ordinalMk_iff.mpr ⟨ξ, H_lt, PSet.Equiv.refl _⟩

-- The zero case: ordinalMk 0 ≡ ∅ (extensionally equivalent)
-- Note: this is Equiv, not equality, since Ordinal.ToType 0 ≠ PEmpty definitionally
lemma ordinalMk_zero_equiv : PSet.Equiv (ordinalMk (0 : Ordinal.{u})) (∅ : PSet.{u}) := by
  apply PSet.Mem.ext; intro z
  simp [mem_ordinalMk_iff]

-- For convenience in downstream proofs, state the simp lemma for ZFSet
@[simp] lemma ordinalMk_zero_zfset : ZFSet.mk (ordinalMk (0 : Ordinal.{u})) = ∅ := by
  rw [ZFSet.eq_empty]
  intro y hy
  -- y ∈ ZFSet.mk (ordinalMk 0) means ∃ a < 0, y = ZFSet.mk (ordinalMk a)
  induction y using Quotient.inductionOn with
  | h p =>
    -- ⟦p⟧ = ZFSet.mk p (definitional)
    -- hy : ⟦p⟧ ∈ ZFSet.mk (ordinalMk 0)
    rw [show (⟦p⟧ : ZFSet) = ZFSet.mk p from rfl] at hy
    rw [ZFSet.mk_mem_iff] at hy
    rw [mem_ordinalMk_iff] at hy
    obtain ⟨a, ha, _⟩ := hy
    exact absurd ha (not_lt.mpr (bot_le))

-- For 6b/6c: type of ordinalMk 0 is empty.
-- Note: `Ordinal.ToType 0` is the empty type (mathlib provides
-- `isEmpty_toType_zero`) but it is not definitionally `PEmpty`, so we state
-- the result as `IsEmpty` rather than `= PEmpty`.


-- Successor: membership in ordinalMk(succ η) ↔ in ordinalMk η or ≡ ordinalMk η
lemma ordinalMk_succ_mem_iff {η : Ordinal} {x : PSet} :
    x ∈ ordinalMk (Order.succ η) ↔ x ∈ ordinalMk η ∨ Equiv x (ordinalMk η) := by
  rw [mem_ordinalMk_iff, mem_ordinalMk_iff]
  constructor
  · rintro ⟨a, ha, heq⟩
    rw [Order.lt_succ_iff] at ha
    rcases ha.eq_or_lt with rfl | hlt
    · right; exact heq
    · left; exact ⟨a, hlt, heq⟩
  · rintro (⟨a, ha, heq⟩ | heq)
    · exact ⟨a, ha.trans (Order.lt_succ η), heq⟩
    · exact ⟨η, Order.lt_succ η, heq⟩

-- `succ_ord`: the type is Option
@[simp] lemma succ_ord_type {x : PSet} : (succ_ord x).Type = Option (x.Type) := by
  cases x; rfl

@[simp] lemma option_succ_ord_type {x : PSet} :
    Option (succ_ord x).Type = Option (Option (x.Type)) := by simp


def succ_type_cast' {x : PSet} : Option (x.Type) → (succ_ord x).Type := cast succ_ord_type.symm



@[simp] lemma succ_ord_func_none {x : PSet} :
    (succ_ord x).Func (succ_type_cast' none) = x := by cases x; rfl

@[simp] lemma succ_ord_func_some {x : PSet} {i} :
    (succ_ord x).Func (succ_type_cast' (some i)) = x.Func i := by cases x; rfl







-- The type of ordinalMk for a limit ordinal is η.ToType
@[simp] lemma ordinalMk_limit_type {η : Ordinal} (H_limit : Order.IsSuccLimit η) :
    (ordinalMk η).Type = η.ToType :=
  ordinalMk_type

@[simp] lemma mem_mk_limit_of_lt {η : Ordinal} (_H_limit : Order.IsSuccLimit η)
    (ξ : Ordinal) (Hξ : ξ < η) : ordinalMk ξ ∈ ordinalMk η :=
  mk_mem_mk_of_lt Hξ

/-! ### Epsilon well-orders and pre-set ordinals -/

def epsilon_well_orders (x : PSet.{u}) : Prop :=
  (∀ y, y ∈ x → (∀ z, z ∈ x → (Equiv y z ∨ y ∈ z ∨ z ∈ y))) ∧
  (∀ u, u ⊆ x → (¬ (Equiv u (∅ : PSet.{u})) → ∃ y, (y ∈ u ∧ (∀ z', z' ∈ u → ¬ z' ∈ y))))

def is_transitive (x : PSet) : Prop := ∀ y, y ∈ x → y ⊆ x

def Ord (x : PSet) : Prop := epsilon_well_orders x ∧ is_transitive x

@[simp] lemma is_transitive_of_Ord {x} (H : Ord x) : is_transitive x := H.right

@[simp] lemma is_ewo_of_Ord {x} (H : Ord x) : epsilon_well_orders x := H.left

@[simp, refl] lemma equiv_refl' {x : PSet} : PSet.Equiv x x := PSet.Equiv.refl _



lemma equiv_iff_eq {x y : PSet} : Equiv x y ↔ ZFSet.mk x = ZFSet.mk y :=
  ⟨ZFSet.sound, ZFSet.exact⟩

-- PSet membership ↔ ZFSet membership
lemma mem_iff {x y : PSet} : x ∈ y ↔ ZFSet.mk x ∈ ZFSet.mk y := by
  simp [ZFSet.mk_mem_iff]





-- Helpers for insert membership
lemma mem_insert_mem {x y z : PSet} (H : x ∈ insert y z) : Equiv x y ∨ x ∈ z :=
  PSet.mem_insert_iff.mp H

lemma mem_insert_intro {x y z : PSet} (H : Equiv x y ∨ x ∈ z) : x ∈ insert y z :=
  PSet.mem_insert_iff.mpr H

@[simp] lemma mem_succ_ord (x : PSet) : x ∈ succ_ord x :=
  PSet.mem_insert_iff.mpr (Or.inl (PSet.Equiv.refl _))

lemma subset_of_all_mem {x y : PSet} (H : ∀ z, z ∈ y → z ∈ x) : y ⊆ x :=
  PSet.subset_iff.mpr (fun _ hz => H _ hz)

lemma all_mem_of_subset {x y : PSet} (H : y ⊆ x) : ∀ z, z ∈ y → z ∈ x :=
  fun z hz => PSet.mem_of_subset H hz









-- Type of empty PSet is PEmpty (mathlib4: `PSet.empty = ⟨_, PEmpty.elim⟩`)
@[simp] lemma empty_type : PSet.Type (∅ : PSet) = PEmpty := by
  rw [PSet.empty_def]; rfl



lemma not_empty_of_not_equiv_empty {x : PSet.{u}} (H : ¬ Equiv x (∅ : PSet.{u})) :
    ZFSet.mk x ≠ ∅ := by
  intro H'
  apply H
  -- ZFSet.mk x = ∅ = ZFSet.mk ∅, so exact ZFSet.exact H'
  have : ZFSet.mk x = ZFSet.mk (∅ : PSet.{u}) := by
    rw [H']; rfl
  exact ZFSet.exact this



@[simp] lemma Ord_empty : Ord (∅ : PSet.{u}) := by
  refine ⟨⟨fun y hy => absurd hy (PSet.notMem_empty y), ?_⟩,
    fun y hy => absurd hy (PSet.notMem_empty y)⟩
  intro u Hu H₂
  exact absurd (PSet.Mem.ext (fun w => ⟨
    fun hw => absurd (all_mem_of_subset Hu w hw) (PSet.notMem_empty w),
    fun hw => absurd hw (PSet.notMem_empty w)⟩)) H₂

lemma well_founded (u : PSet.{u}) (H_nonempty : ¬ Equiv u (∅ : PSet.{u})) :
    ∃ (y : PSet), y ∈ u ∧ ∀ (z' : PSet), z' ∈ u → z' ∉ y := by
  have Hu_ne : ZFSet.mk u ≠ ∅ := not_empty_of_not_equiv_empty H_nonempty
  obtain ⟨y, H₁, H₂⟩ := ZFSet.regularity (ZFSet.mk u) Hu_ne
  refine ⟨y.out, ?_, ?_⟩
  · have : ZFSet.mk y.out ∈ ZFSet.mk u := by rw [ZFSet.mk_out y]; exact H₁
    exact mem_iff.mpr this
  · intro z' Hz' Hz''
    apply ZFSet.notMem_empty (ZFSet.mk z')
    rw [← H₂]
    exact ZFSet.mem_inter.mpr
      ⟨mem_iff.mp Hz', by rw [← ZFSet.mk_out y]; exact mem_iff.mp Hz''⟩

lemma transitive_succ_ord (x : PSet) (H : is_transitive x) : is_transitive (succ_ord x) := by
  intro y Hy
  rcases mem_insert_mem Hy with heq | hin
  · exact subset_of_all_mem fun z hz =>
      mem_insert_intro (Or.inr ((PSet.Mem.congr_right heq).mp hz))
  · exact subset_of_all_mem fun z hz =>
      mem_insert_intro (Or.inr (all_mem_of_subset (H y hin) z hz))

@[simp] lemma Ord_succ_ord (x : PSet) (H : Ord x) : Ord (succ_ord x) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro y Hy z Hz
    rcases mem_insert_mem Hy with heq1 | hin1 <;>
    rcases mem_insert_mem Hz with heq2 | hin2
    · left; exact PSet.Equiv.trans heq1 heq2.symm
    · right; right; exact (PSet.Mem.congr_right heq1).mpr hin2
    · right; left; exact (PSet.Mem.congr_right heq2).mpr hin1
    · exact H.left.left y hin1 z hin2
  · intro u _Hu H_nonempty; exact well_founded u H_nonempty
  · exact transitive_succ_ord x H.right





lemma equiv_mk_of_mem_mk {η : Ordinal} :
    ∀ x, x ∈ ordinalMk η → ∃ ρ < η, Equiv x (ordinalMk ρ) :=
  fun x hx => mem_ordinalMk_iff.mp hx

lemma Ord_limit : ∀ (o : Ordinal), Order.IsSuccLimit o →
    (∀ (o' : Ordinal), o' < o → Ord (ordinalMk o')) → Ord (ordinalMk o) := by
  intro η _Hη _ih
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x Hx z Hz
    obtain ⟨ξ₁, H₁, H₂⟩ := equiv_mk_of_mem_mk x Hx
    obtain ⟨ξ₂, H₁', H₂'⟩ := equiv_mk_of_mem_mk z Hz
    rcases lt_trichotomy ξ₁ ξ₂ with hlt | rfl | hlt
    · right; left
      rw [PSet.Mem.congr_left H₂, PSet.Mem.congr_right H₂']
      exact mk_mem_mk_of_lt hlt
    · left; exact PSet.Equiv.trans H₂ H₂'.symm
    · right; right
      rw [PSet.Mem.congr_right H₂, PSet.Mem.congr_left H₂']
      exact mk_mem_mk_of_lt hlt
  · intro u _Hu H_nonempty; exact well_founded u H_nonempty
  · intro y Hy
    obtain ⟨ρ, Hρ, Heq⟩ := equiv_mk_of_mem_mk y Hy
    rw [PSet.Subset.congr_left Heq]
    apply subset_of_all_mem; intro z Hz
    obtain ⟨σ, Hσ, Heq'⟩ := equiv_mk_of_mem_mk z Hz
    rw [PSet.Mem.congr_left Heq']
    exact mk_mem_mk_of_lt (Hσ.trans Hρ)

-- Ord is invariant under PSet.Equiv
lemma Ord_equiv {x y : PSet.{u}} (hxy : PSet.Equiv x y) (hx : Ord x) : Ord y := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- trichotomy: a ∈ y, b ∈ y → a and b are trichotomous
    intro a Ha b Hb
    have Ha' : a ∈ x := (PSet.Mem.congr_right hxy.symm).mp Ha
    have Hb' : b ∈ x := (PSet.Mem.congr_right hxy.symm).mp Hb
    exact hx.left.left a Ha' b Hb'
  · -- well-foundedness
    intro u _Hu H_ne; exact well_founded u H_ne
  · -- transitivity: a ∈ y → a ⊆ y
    intro a Ha
    have Ha' : a ∈ x := (PSet.Mem.congr_right hxy.symm).mp Ha
    -- a ⊆ x (from hx.right)
    have hax : a ⊆ x := hx.right a Ha'
    -- a ⊆ y: for w ∈ a, w ∈ x, so w ∈ y
    apply subset_of_all_mem
    intro w Hw
    exact (PSet.Mem.congr_right hxy).mp (all_mem_of_subset hax w Hw)

-- Key: ordinalMk (Order.succ η) ≡ succ_ord (ordinalMk η)
lemma ordinalMk_succ_equiv {η : Ordinal} :
    PSet.Equiv (ordinalMk (Order.succ η)) (succ_ord (ordinalMk η)) := by
  apply PSet.Mem.ext; intro z
  rw [ordinalMk_succ_mem_iff, PSet.mem_insert_iff]
  tauto

@[simp] lemma Ord_mk (η : Ordinal) : Ord (ordinalMk η) := by
  induction η using Ordinal.limitRecOn with
  | zero => exact Ord_equiv ordinalMk_zero_equiv.symm Ord_empty
  | add_one η ih =>
    -- ordinalMk_succ_equiv : Equiv (ordinalMk (succ η)) (succ_ord (ordinalMk η))
    -- Ord_succ_ord _ ih : Ord (succ_ord (ordinalMk η))
    -- Apply Ord_equiv in reverse: Equiv y x → Ord y → Ord x
    exact Ord_equiv ordinalMk_succ_equiv.symm (Ord_succ_ord _ ih)
  | limit η H_limit ih => exact Ord_limit η H_limit ih













-- card_ex: cardinal → PSet via ordinal
def card_ex : Cardinal.{u} → PSet.{u} := fun κ => ordinalMk (Cardinal.ord κ)

-- WARNING: is_func corresponds to bSet.is_function, not bSet.is_func
-- f ⊆ prod x y ∧ ∀z ∈ x, ∃! w, pair z w ∈ f
@[reducible] def is_func (x y f : PSet.{u}) : Prop :=
  ZFSet.IsFunc (ZFSet.mk x) (ZFSet.mk y) (ZFSet.mk f)







-- ============================================================
-- Task 6b additions: lines 512-1000 of src/pSet_ordinal.lean
-- ============================================================

/-! ### Injectivity of ordinalMk (src lines 512-618) -/

/-- Helper: structural equation for `Ordinal.toPSet`. The `eq_def` form. -/
lemma ordinalMk_eq_def (o : Ordinal.{u}) :
    ordinalMk o = ⟨o.ToType, fun a : o.ToType => ordinalMk a.toOrd.val⟩ :=
  Ordinal.toPSet.eq_def o

/-- Injectivity: `ordinalMk η₁ ≡ ordinalMk η₂` → `η₁ = η₂`.
    Port of `eq_of_mk_equiv` (src/pSet_ordinal.lean:604). -/
lemma eq_of_mk_equiv {η₁ η₂ : Ordinal} (H_equiv : Equiv (ordinalMk η₁) (ordinalMk η₂)) :
    η₁ = η₂ := by
  refine le_antisymm ?_ ?_
  · rw [← not_lt]; intro H_lt
    -- H_lt : η₂ < η₁ (from not_lt of η₁ ≤ η₂)
    -- H_mem : ordinalMk η₂ ∈ ordinalMk η₁
    have H_mem := mk_mem_mk_of_lt H_lt
    -- Want: ordinalMk η₁ ∈ ordinalMk η₁
    -- Mem.congr_left H_equiv : ordinalMk η₁ ∈ w ↔ ordinalMk η₂ ∈ w
    -- .mpr H_mem (H_mem : ordinalMk η₂ ∈ ordinalMk η₁) gives ordinalMk η₁ ∈ ordinalMk η₁
    exact PSet.mem_irrefl _ ((PSet.Mem.congr_left H_equiv).mpr H_mem)
  · rw [← not_lt]; intro H_lt
    -- H_lt : η₁ < η₂ (from not_lt of η₂ ≤ η₁)
    have H_mem := mk_mem_mk_of_lt H_lt
    -- Mem.congr_left H_equiv.symm : ordinalMk η₂ ∈ w ↔ ordinalMk η₁ ∈ w
    -- .mpr H_mem (H_mem : ordinalMk η₁ ∈ ordinalMk η₂) gives ordinalMk η₂ ∈ ordinalMk η₂
    exact PSet.mem_irrefl _ ((PSet.Mem.congr_left H_equiv.symm).mpr H_mem)

/-- The func of ordinalMk η at distinct indices gives inequivalent pSets.
    Port of `ordinal.mk_inj` (src/pSet_ordinal.lean:595). -/
lemma ordinalMk_inj (η : Ordinal.{u}) :
    ∀ (i j : (ordinalMk η).Type), i ≠ j →
      ¬ Equiv ((ordinalMk η).Func i) ((ordinalMk η).Func j) := by
  intro i j hij heq
  apply hij
  -- Extract the HEq characterization of `(ordinalMk η).Func`.
  have hfunc : HEq (ordinalMk η).Func
      (fun a : η.ToType => ordinalMk a.toOrd.val) := by
    rw [ordinalMk_eq_def]; rfl
  -- Type equality.
  have htype : (ordinalMk η).Type = η.ToType := ordinalMk_type
  -- Cast i, j to η.ToType.
  let i' : η.ToType := cast htype i
  let j' : η.ToType := cast htype j
  have hi : HEq i i' := (cast_heq htype i).symm
  have hj : HEq j j' := (cast_heq htype j).symm
  -- `congr_heq` produces `Eq` directly when applied to a `Pi` and a `Sigma` of HEq.
  have heqi : (ordinalMk η).Func i = ordinalMk i'.toOrd.val :=
    congr_heq hfunc hi
  have heqj : (ordinalMk η).Func j = ordinalMk j'.toOrd.val :=
    congr_heq hfunc hj
  rw [heqi, heqj] at heq
  -- heq : Equiv (ordinalMk i'.toOrd.val) (ordinalMk j'.toOrd.val)
  have h_ord_eq : i'.toOrd.val = j'.toOrd.val := eq_of_mk_equiv heq
  have h_toOrd : i'.toOrd = j'.toOrd := Subtype.ext h_ord_eq
  have h_inj : i' = j' :=
    Ordinal.ToType.mk.symm.injective h_toOrd
  -- Cast both back.
  have : (cast htype.symm (cast htype i) : (ordinalMk η).Type) =
         cast htype.symm (cast htype j) :=
    congrArg (cast htype.symm) h_inj
  simpa using this



/-! ### Cardinal type size lemmas (src lines 620-666) -/

open Cardinal in
/-- The cardinality of `(ordinalMk (κ.ord)).Type` equals `κ`, for infinite `κ`.
    Port of `mk_type_mk_eq` (src/pSet_ordinal.lean:620). -/
lemma mk_type_mk_eq (κ : Cardinal) (H_inf : ℵ₀ ≤ κ) :
    Cardinal.mk (ordinalMk (Cardinal.ord κ)).Type = κ := by
  simp only [ordinalMk_type]
  exact Cardinal.mk_ord_toType κ

open Cardinal in
@[simp] lemma mk_type_mk_eq' (κ : Cardinal) (H_inf : ℵ₀ < κ) :
    Cardinal.mk (ordinalMk (Cardinal.ord κ)).Type = κ :=
  mk_type_mk_eq _ H_inf.le

open Cardinal in
@[simp] lemma mk_type_mk_eq'' {κ : Cardinal} {H_inf : ℵ₀ ≤ κ} :
    Cardinal.mk (card_ex κ).Type = κ :=
  mk_type_mk_eq κ H_inf

open Cardinal in
@[simp] lemma mk_type_mk_eq''' {κ : Cardinal} {H_inf : ℵ₀ < κ} :
    Cardinal.mk (card_ex κ).Type = κ :=
  mk_type_mk_eq _ H_inf.le

open Cardinal in
@[simp] lemma mk_type_mk_eq'''' {k : Ordinal} :
    Cardinal.mk (ordinalMk (Cardinal.aleph k).ord).Type = Cardinal.aleph k :=
  mk_type_mk_eq _ (Cardinal.aleph0_le_aleph k)

open Cardinal in
@[simp] lemma mk_type_mk_eq''''' {k : Ordinal} :
    Cardinal.mk (card_ex (Cardinal.aleph k)).Type = Cardinal.aleph k := by
  simp [card_ex]





open Cardinal in
@[simp] lemma mk_type_omega_eq :
    Cardinal.mk (ordinalMk (Cardinal.aleph0.ord)).Type = ℵ₀ :=
  mk_type_mk_eq _ le_rfl

open Cardinal in
@[simp] lemma mk_omega_eq_mk_omega :
    Cardinal.mk (PSet.omega).Type = ℵ₀ := by
  simp only [PSet.omega]
  rw [show (⟨ULift ℕ, fun n => PSet.ofNat n.down⟩ : PSet).Type = ULift ℕ from rfl]
  simp [Cardinal.mk_uLift, Cardinal.mk_nat]

/-! ### Ordinal arithmetic helpers (src lines 668-697) -/





open Cardinal in
lemma one_lt_two : (1 : Ordinal) < 2 := _root_.one_lt_two









open Cardinal in
@[simp] lemma omega_lt_aleph_one : ℵ₀ < Cardinal.aleph 1 :=
  Cardinal.aleph0_lt_aleph_one

open Cardinal in
@[simp] lemma aleph_one_lt_aleph_two : Cardinal.aleph 1 < Cardinal.aleph 2 :=
  Cardinal.aleph_lt_aleph.mpr one_lt_two

open Cardinal in
@[simp] lemma omega_lt_aleph_two : ℵ₀ < Cardinal.aleph 2 :=
  omega_lt_aleph_one.trans aleph_one_lt_aleph_two

/-! ### Subset helpers (src lines 698-704) -/



@[simp] lemma subset_self {x : PSet} : x ⊆ x :=
  subset_of_all_mem fun _ h => h

/-! ### ofNat lemmas (src lines 706-768) -/
-- In mathlib4, Lean 3's `of_nat` is `PSet.ofNat`.
-- Lean 3 omega.type = ℕ-indexed; mathlib4 uses ULift ℕ.

lemma ofNat_succ {k : ℕ} : PSet.ofNat (k + 1) = succ_ord (PSet.ofNat k) := by
  simp [PSet.ofNat, succ_ord]











lemma ofNat_mem_of_lt {k₁ k₂ : ℕ} (H_lt : k₁ < k₂) :
    (PSet.ofNat k₁ : PSet.{u}) ∈ (PSet.ofNat k₂ : PSet.{u}) := by
  induction H_lt with
  | refl =>
    rw [ofNat_succ, succ_ord]
    exact PSet.mem_insert_iff.mpr (Or.inl (PSet.Equiv.refl _))
  | step _ ih =>
    rw [ofNat_succ, succ_ord]
    exact PSet.mem_insert_iff.mpr (Or.inr ih)



/-! ### Transitivity and well-orders for omega (src lines 770-800) -/











/-! ### Pair and product for pSets (src lines 945-984) -/

/-- The ordered pair pSet `{{x}, {x, y}}`. -/
def pSet_pair (x y : PSet.{u}) : PSet.{u} := {{x}, {x, y}}

lemma pSet_pair_sound {x y : PSet.{u}} :
    ZFSet.mk (pSet_pair x y) = ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) := rfl









/-! ### Injection predicates (src lines 986-990) -/

@[reducible] def is_inj (f : PSet.{u}) : Prop :=
  ∀ w₁ w₂ v₁ v₂ : PSet.{u},
    pSet_pair w₁ v₁ ∈ f ∧ pSet_pair w₂ v₂ ∈ f ∧ Equiv v₁ v₂ → Equiv w₁ w₂

def is_injective_function (x y f : PSet.{u}) : Prop := is_func x y f ∧ is_inj f

def injects_into (x y : PSet.{u}) : Prop := ∃ f, is_injective_function x y f

/-! ### Subset characterization via ZFSet (src/pSet_ordinal.lean:994-1000) -/



-- ============================================================
-- Task 6c additions: lines 1000-1391 of src/pSet_ordinal.lean
-- ============================================================

/-! ### is_func characterization (src lines 1002-1045) -/









/-! ### powerset_sound (src line 1047) -/



/-! ### set_of_indicator, functions, mem_functions_iff (src lines 1049-1067) -/







/-! ### card_ex_aleph_exists_mem (src line 1071) -/

open Cardinal in
@[simp] lemma card_ex_aleph_exists_mem {n : ℕ} : ∃ z, z ∈ card_ex (Cardinal.aleph n) := by
  refine ⟨card_ex 0, mk_mem_mk_of_lt ?_⟩
  -- ord 0 < ord (aleph n): since aleph 0 = ℵ₀ > 0, ord is strictly monotone
  apply Cardinal.ord_lt_ord.mpr
  induction n with
  | zero => exact Cardinal.aleph_pos 0
  | succ n ih => exact ih.trans (Cardinal.aleph_lt_aleph.mpr (by exact_mod_cast Nat.lt_succ_self n))

/-! ### function.mk and related (src lines 1080-1132) -/

namespace function_mk









end function_mk

/-! ### P_ext predicate (src lines 1144-1161) -/

def P_ext : (PSet → Prop) → Prop := fun χ => ∀ x y, Equiv x y → χ x → χ y

@[simp] lemma P_ext_mem_left {y : PSet} : P_ext (fun x => x ∈ y) :=
  fun _ _ H_eq H_mem => (PSet.Mem.congr_left H_eq).mp H_mem

@[simp] lemma P_ext_mem_right {x : PSet} : P_ext (fun y => x ∈ y) :=
  fun _ _ H_eq H_mem => (PSet.Mem.congr_right H_eq).mp H_mem

@[simp] lemma P_ext_neg {χ : PSet → Prop} (H : P_ext χ) : P_ext (fun z => ¬ χ z) := by
  intro x y H_eq H'
  intro Hy
  exact H' (H y x H_eq.symm Hy)

@[simp] lemma P_ext_injects_into_left {y : PSet.{u}} : P_ext (fun x => injects_into x y) := by
  intro x₁ x₂ H_eq ⟨f, Hf₁, Hf₂⟩
  refine ⟨f, ?_, Hf₂⟩
  unfold is_func at *
  have h : ZFSet.mk x₁ = ZFSet.mk x₂ := equiv_iff_eq.mp H_eq
  rw [← h]
  exact Hf₁

/-! ### mem_sep_iff (src line 1163) -/

-- PSet.sep for P_ext-respecting predicates
-- Note: must use `PSet.sep p x` explicitly (not `{z ∈ x | p z}` which resolves to Set.sep)
lemma mem_sep_iff {p : PSet → Prop} {x w : PSet} (H_congr : P_ext p) :
    w ∈ PSet.sep p x ↔ w ∈ x ∧ p w :=
  PSet.mem_sep (fun a b hab hpa => H_congr a b hab hpa)

/-! ### sep_subset (src line 1134) -/

@[simp] lemma sep_subset {p : PSet → Prop} {x : PSet} (Hp : P_ext p) : PSet.sep p x ⊆ x := by
  apply subset_of_all_mem
  intro w Hw
  exact ((mem_sep_iff Hp).mp Hw).1

/-! ### sep_equiv_iff (src line 1179) -/



/-! ### mem_two (src line 1186) -/



/-! ### pair_mem.congr_right/left (src lines 1194-1215) -/

lemma pSet_pair_mem_congr_right {p q r s : PSet.{u}} (H : Equiv q r) :
    pSet_pair p q ∈ s ↔ pSet_pair p r ∈ s := by
  rw [mem_iff, mem_iff, pSet_pair_sound, pSet_pair_sound]
  constructor
  · intro h; rwa [show ZFSet.pair (ZFSet.mk p) (ZFSet.mk q) = ZFSet.pair (ZFSet.mk p) (ZFSet.mk r) from
      by rw [ZFSet.pair_inj]; exact ⟨rfl, ZFSet.sound H⟩] at h
  · intro h; rwa [show ZFSet.pair (ZFSet.mk p) (ZFSet.mk r) = ZFSet.pair (ZFSet.mk p) (ZFSet.mk q) from
      by rw [ZFSet.pair_inj]; exact ⟨rfl, ZFSet.sound H.symm⟩] at h

lemma pSet_pair_mem_congr_left {p q r s : PSet.{u}} (H : Equiv q r) :
    pSet_pair q p ∈ s ↔ pSet_pair r p ∈ s := by
  rw [mem_iff, mem_iff, pSet_pair_sound, pSet_pair_sound]
  constructor
  · intro h; rwa [show ZFSet.pair (ZFSet.mk q) (ZFSet.mk p) = ZFSet.pair (ZFSet.mk r) (ZFSet.mk p) from
      by rw [ZFSet.pair_inj]; exact ⟨ZFSet.sound H, rfl⟩] at h
  · intro h; rwa [show ZFSet.pair (ZFSet.mk r) (ZFSet.mk p) = ZFSet.pair (ZFSet.mk q) (ZFSet.mk p) from
      by rw [ZFSet.pair_inj]; exact ⟨ZFSet.sound H.symm, rfl⟩] at h

@[simp] lemma P_ext_pair_mem_right {b c : PSet} : P_ext (fun w => pSet_pair b w ∈ c) :=
  fun _ _ H Hx => (pSet_pair_mem_congr_right H).mp Hx

@[simp] lemma P_ext_pair_mem_left {b c : PSet} : P_ext (fun w => pSet_pair w b ∈ c) :=
  fun _ _ H Hx => (pSet_pair_mem_congr_left H).mp Hx

/-! ### section injects_powerset (src lines 1218-1369) -/

section injects_powerset

variable {x : PSet.{u}}

-- Abbreviation for functions x {0,1}


-- Predicate: "z maps to 0 under χ"


-- For each function χ in fx2, the "preimage of 0" subset of x


















-- Auxiliary: sep for predicate "pair z k ∈ w" is P_ext-respecting








end injects_powerset

/-! ### eq_of_is_func_of_eq (src line 1372) -/



/-! ### exists_mem_of_nonzero, exists_mem_of_regular (src lines 1384-1388) -/





end PSet

end -- noncomputable section


end CohenSource_PSetOrdinal


