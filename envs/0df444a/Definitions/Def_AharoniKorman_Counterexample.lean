-- Prove2me | Definitions.Def_AharoniKorman_Counterexample
-- name    : AharoniKorman_Counterexample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:08:41.231313+00:00
-- url     : https://prove2.me/theorems/2ce754a0-ac4f-478b-9e9f-34e54b734c87
-- title:
--   Counterexample
-- statement:
--   Definitions and structural lemmas for Counterexample, from Bhavik Mehta (b-mehta/AharoniKorman; see pinned Apache-2.0 LICENSE and source headers)'s pinned Hollom counterexample disproving the Aharoni-Korman conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
def Hollom : Type := ℕ × ℕ × ℕ
  deriving DecidableEq
def ofHollom : Hollom ≃ ℕ × ℕ × ℕ := Equiv.refl _
def toHollom : ℕ × ℕ × ℕ ≃ Hollom := Equiv.refl _
@[simp] lemma ofHollom_symm_eq : ofHollom.symm = toHollom := rfl
@[simp] lemma toHollom_symm_eq : toHollom.symm = ofHollom := rfl
@[simp] lemma ofHollom_toHollom (x) : ofHollom (toHollom x) = x := rfl
@[simp] lemma toHollom_ofHollom (x) : toHollom (ofHollom x) = x := rfl
namespace Hollom
@[simp] lemma «forall» {p : Hollom → Prop} : (∀ x, p x) ↔ ∀ x, p (toHollom x) := Iff.rfl
@[simp] lemma «exists» {p : Hollom → Prop} : (∃ x, p x) ↔ ∃ x, p (toHollom x) := Iff.rfl
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma induction {p : Hollom → Prop} (h : ∀ x y z, p (h(x, y, z))) : ∀ x, p x := by simpa
instance : Countable Hollom := .of_equiv (ℕ × ℕ × ℕ) toHollom
@[mk_iff]
inductive HollomOrder : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop
  | twice {x y n u v m : ℕ} : m + 2 ≤ n → HollomOrder (x, y, n) (u, v, m)
  | within {x y u v m : ℕ} : x ≤ u → y ≤ v → HollomOrder (x, y, m) (u, v, m)
  | next_min {x y u v m : ℕ} : min x y + 1 ≤ min u v → HollomOrder (x, y, m + 1) (u, v, m)
  | next_add {x y u v m : ℕ} : x + y ≤ 2 * (u + v) → HollomOrder (x, y, m + 1) (u, v, m)
instance : PartialOrder Hollom where
  le x y := HollomOrder (ofHollom x) (ofHollom y)
  le_refl x := .within le_rfl le_rfl
  le_trans
  | _, _, _, .twice _, .twice _ => .twice (by omega)
  | _, _, _, .twice _, .within _ _ => .twice (by omega)
  | _, _, _, .twice _, .next_min _ => .twice (by omega)
  | _, _, _, .twice _, .next_add _ => .twice (by omega)
  | _, _, _, .within _ _, .twice _ => .twice (by omega)
  | _, _, _, .within _ _, .within _ _ => .within (by omega) (by omega)
  | _, _, _, .within _ _, .next_min _ => .next_min (by omega)
  | _, _, _, .within _ _, .next_add _ => .next_add (by omega)
  | _, _, _, .next_min _, .twice _ => .twice (by omega)
  | _, _, _, .next_min _, .within _ _ => .next_min (by omega)
  | _, _, _, .next_min _, .next_min _ => .twice (by omega)
  | _, _, _, .next_min _, .next_add _ => .twice (by omega)
  | _, _, _, .next_add _, .twice _ => .twice (by omega)
  | _, _, _, .next_add _, .within _ _ => .next_add (by omega)
  | _, _, _, .next_add _, .next_min _ => .twice (by omega)
  | _, _, _, .next_add _, .next_add _ => .twice (by omega)
  le_antisymm
  | _, _, .twice _, .twice _ => by omega
  | _, (_, _, _), .twice _, .within _ _ => by omega
  | _, _, .twice _, .next_min _ => by omega
  | _, _, .twice _, .next_add _ => by omega
  | _, _, .within _ _, .twice _ => by omega
  | _, _, .within _ _, .within _ _ => by
      change (_ : ℕ × ℕ × ℕ) = _
      rw [Prod.ext_iff, Prod.ext_iff]
      simp only [and_true]
      omega
  | _, _, .next_min _, .twice _ => by omega
  | _, _, .next_add _, .twice _ => by omega
@[simp] lemma toHollom_le_toHollom_iff_fixed_right {a b c d n : ℕ} :
    h(a, b, n) ≤ h(c, d, n) ↔ a ≤ c ∧ b ≤ d := by
  refine ⟨?_, ?_⟩
  · rintro (_ | _)
    · omega
    · omega
  · rintro ⟨h₁, h₂⟩
    exact .within h₁ h₂
lemma le_of_toHollom_le_toHollom {a b c d e f : ℕ} :
    h(a, b, c) ≤ h(d, e, f) → f ≤ c
  | .twice _ => by omega
  | .within _ _ => by omega
  | .next_add _ => by omega
  | .next_min _ => by omega
def level (n : ℕ) : Set Hollom := {h(x, y, n) | (x : ℕ) (y : ℕ)}
lemma level_eq (n : ℕ) : level n = {x | (ofHollom x).2.2 = n} := by
  simp [Set.ext_iff, level, eq_comm]
@[simp] lemma toHollom_mem_level_iff {n : ℕ} {x} : toHollom x ∈ level n ↔ x.2.2 = n := by
  simp [level_eq]
@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma induction_on_level {n : ℕ} {p : (x : Hollom) → x ∈ level n → Prop}
    (h : ∀ x y, p h(x, y, n) (by simp)) :
    ∀ {x : Hollom}, (h : x ∈ level n) → p x h := by
  simp +contextual only [«forall», toHollom_mem_level_iff, Prod.forall]
  rintro x y _ rfl
  exact h _ _
def embed (n : ℕ) : ℕ × ℕ ↪o Hollom where
  toFun x := h(x.1, x.2, n)
  inj' x := by aesop
  map_rel_iff' := by rintro ⟨a, b⟩ ⟨c, d⟩; change h(a, b, n) ≤ h(c, d, n) ↔ (a, b) ≤ (c, d); simp
lemma embed_apply (n : ℕ) (x y : ℕ) : embed n (x, y) = h(x, y, n) := rfl
lemma level_eq_range (n : ℕ) : level n = Set.range (embed n) := by
  ext x; simp [level, Set.range, Prod.exists, embed_apply]
lemma level_isPWO {n : ℕ} : (level n).IsPWO := by
  rw [level_eq_range, ← Set.image_univ]
  refine Set.IsPWO.image_of_monotone ?_ (embed n).monotone
  rw [← Set.univ_prod_univ]
  exact .prod (.of_linearOrder _) (.of_linearOrder _)
lemma no_infinite_antichain_level {n : ℕ} {A : Set Hollom} (hA : A ⊆ level n)
    (hA' : IsAntichain (· ≤ ·) A) : A.Finite :=
  hA'.finite_of_partiallyWellOrderedOn ((level_isPWO).mono hA)
lemma ordConnected_level {n : ℕ} : (level n).OrdConnected := by
  rw [Set.ordConnected_iff]
  simp only [level_eq, Set.mem_setOf_eq, Set.subset_def, Set.mem_Icc, and_imp, Hollom.forall,
    ofHollom_toHollom, Prod.forall, forall_eq, toHollom_le_toHollom_iff_fixed_right]
  intro a b c d ac bd e f g h1 h2
  exact le_antisymm (le_of_toHollom_le_toHollom h1) (le_of_toHollom_le_toHollom h2)
@[pp_nodot] def line (x : Hollom) : ℕ := (ofHollom x).1 + (ofHollom x).2.1
@[simp] lemma line_toHollom (x : ℕ × ℕ × ℕ) : line (toHollom x) = x.1 + x.2.1 := rfl
lemma no_strictly_decreasing {α : Type*} [Preorder α] [WellFoundedLT α] (f : ℕ → α) {n₀ : ℕ}
    (hf : ∀ n ≥ n₀, f (n + 1) < f n) : False := by
  let g (n : ℕ) : α := f (n₀ + n)
  obtain ⟨_, ⟨k, rfl⟩, hmin⟩ := wellFounded_lt.has_min (Set.range g) (Set.range_nonempty g)
  exact hmin (g (k + 1)) ⟨k + 1, rfl⟩ (by simpa [g, Nat.add_assoc] using hf (n₀ + k) (by omega))
lemma no_strictAnti {α : Type*} [Preorder α] [WellFoundedLT α] (f : ℕ → α)
    (hf : StrictAnti f) : False :=
  no_strictly_decreasing f (n₀ := 0) fun n _ => hf (by simp)
theorem scattered {f : ℚ → Hollom} (hf : StrictMono f) : False := by
  -- Let `g` be the function from `ℚ` to `ℕ` which is the third coordinate of `f`.
  let g (q : ℚ) : ℕ := (ofHollom (f q)).2.2
  have hg (q : ℚ) : f q ∈ level (g q) := by simp [g, level_eq]
  -- We have that `g` is antitone, since `f` is strictly monotone.
  have hg' : Antitone g := by
    rw [antitone_iff_forall_lt]
    intro x y hxy
    have : f x < f y := hf hxy
    simp only [ge_iff_le, g]
    cases hx : f x with | h x₁ x₂ x₃ =>
    cases hy : f y with | h y₁ y₂ y₃ =>
    rw [hx, hy] at this
    exact le_of_toHollom_le_toHollom this.le
  -- But it cannot be injective: otherwise it is strictly antitone, and thus precomposing with
  -- the obvious map `ℕ → ℚ` would give a strictly decreasing sequence in `ℕ`.
  have hg'' : ¬ g.Injective := fun hg'' ↦
    no_strictAnti _ ((hg'.strictAnti_of_injective hg'').comp_strictMono Nat.strictMono_cast)
  -- Take `x ≠ y` with `g x = g y`
  obtain ⟨x, y, hgxy, hxy'⟩ : ∃ x y, g x = g y ∧ x ≠ y := by simpa [Function.Injective] using hg''
  -- and wlog `x < y`
  wlog hxy : x < y generalizing x y
  · simp only [not_lt, g] at hxy
    exact this y x hgxy.symm hxy'.symm (lt_of_le_of_ne' hxy hxy')
  -- Now `f '' [x, y]` is infinite, as it is the image of an infinite set of rationals,
  have h₁ : (f '' Set.Icc x y).Infinite := (Set.Icc_infinite hxy).image hf.injective.injOn
  -- but it is contained in `[f x, f y]` by monotonicity
  have h₂ : f '' Set.Icc x y ⊆ Set.Icc (f x) (f y) := Monotone.image_Icc_subset hf.monotone
  -- and this is finite, as it is a closed interval in `level (g x)`
  have h₃ : (Set.Icc (f x) (f y)).Finite := by
    set n := g y
    obtain ⟨a, ha⟩ : f x ∈ Set.range (embed n) := by rw [← level_eq_range, ← hgxy]; exact hg _
    obtain ⟨b, hb⟩ : f y ∈ Set.range (embed n) := by rw [← level_eq_range]; exact hg _
    rw [← ha, ← hb, ← OrderEmbedding.image_Icc]
    · exact (Set.finite_Icc a b).image (embed n)
    · rw [← level_eq_range]
      exact ordConnected_level
  -- giving a contradiction.
  exact h₁ (h₃.subset h₂)
theorem no_infinite_antichain {A : Set Hollom} (hC : IsAntichain (· ≤ ·) A) : A.Finite := by
  let f (x : Hollom) : ℕ := (ofHollom x).2.2
  have (n : ℕ) : A ∩ f ⁻¹' {n} ⊆ level n := fun x ↦ by induction x with | h x => simp [f]
  -- We show that the antichain can only occupy finitely much of each level
  -- and it can only exist in finitely many levels.
  apply Set.Finite.of_finite_fibers f
  case hfibers =>
    intro x hx
    exact no_infinite_antichain_level (this _) (hC.subset Set.inter_subset_left)
  case himage =>
    rw [← Set.not_infinite]
    intro h
    obtain ⟨n, hn⟩ := h.nonempty
    suffices f '' A ⊆ Set.Iio (n + 2) from h ((Set.finite_Iio _).subset this)
    intro m
    simp only [Set.mem_image, «exists», ofHollom_toHollom, Prod.exists, exists_eq_right,
      Set.mem_Iio, forall_exists_index, f]
    simp only [Set.mem_image, «exists», ofHollom_toHollom, Prod.exists, exists_eq_right, f] at hn
    obtain ⟨a, b, hab⟩ := hn
    intro c d hcd
    by_contra!
    exact hC hcd hab (by simp; omega) (HollomOrder.twice this)
variable {C : Set Hollom}
open Filter
section SpinalMap
variable {α : Type*} [PartialOrder α] {C : Set α}
structure SpinalMap (C : Set α) where
  /-- The underlying function of a spinal map. -/
  toFun : α → α
  mem' : ∀ x, toFun x ∈ C
  eq_self_of_mem' : ∀ x ∈ C, toFun x = x
  fibre_antichain' : ∀ x, IsAntichain (· ≤ ·) (toFun ⁻¹' {x})
instance : FunLike (SpinalMap C) α α where
  coe := SpinalMap.toFun
  coe_injective | ⟨f, _, _, _⟩, ⟨g, _, _, _⟩, h => by simp_all only
namespace SpinalMap
variable (f : SpinalMap C)
variable {x y z : α}
end SpinalMap
end SpinalMap
variable {f : SpinalMap C}
section make_chains
open Finset
def chainBetween (a b c d : ℕ) : Finset (ℕ × ℕ) :=
  if a ≤ c ∧ b ≤ d
    then Ico (a, b) (a, d) ∪ Icc (a, d) (c, d)
    else ∅
end make_chains
def R (n : ℕ) (C : Set Hollom) : Set Hollom := {x ∈ level n | ∀ y ∈ C ∩ level n, x ≤ y ∨ y ≤ x}
variable {n : ℕ}
open Classical in
/--
Given a subset `C` of the Hollom partial order, and an index `n`, find the smallest element of
`C ∩ level (n + 1)`, expressed as `(x₀, y₀, n + 1)`.
This is only the global minimum provided `C` is a chain, which it is in context.
-/
noncomputable def x0y0 (n : ℕ) (C : Set Hollom) : ℕ × ℕ :=
  if h : (C ∩ level (n + 1)).Nonempty
    then wellFounded_lt.min {x | embed (n + 1) x ∈ C} <| by
      rw [level_eq_range] at h
      obtain ⟨_, h, y, rfl⟩ := h
      exact ⟨y, h⟩
    else 0
noncomputable def x0 (n : ℕ) (C : Set Hollom) : ℕ := (x0y0 n C).1
noncomputable def y0 (n : ℕ) (C : Set Hollom) : ℕ := (x0y0 n C).2
open Classical in
/--
Construction of the set `S`, which has the following key properties:
* It is a subset of `R`.
* No element of it can be mapped to an element of `C ∩ level (n + 1)` by `f`.
* There exists an `a` such that `{(x, y, n) | x ≥ a ∧ y ≥ a} ⊆ S`.

If `C ∩ level (n + 1)` is finite, it is all elements of `R` which are comparable to
`C ∩ level (n + 1)`.
Otherwise, say `(x0, y0, n + 1)` is the smallest element of `C ∩ level (n + 1)`, and take all
elements of `R` of the form `(a, b, n)` with `max x0 y0 + 1 ≤ min a b`.
-/
noncomputable def S (n : ℕ) (C : Set Hollom) : Set Hollom :=
  if (C ∩ level (n + 1)).Finite
    then {x ∈ R n C | ∀ y ∈ C ∩ level (n + 1), x ≤ y ∨ y ≤ x}
    else {x ∈ R n C | max (x0 n C) (y0 n C) + 1 ≤ min (ofHollom x).1 (ofHollom x).2.1}
end Hollom
example : PartialOrder Hollom := inferInstance
example : Countable Hollom := inferInstance
example (A : Set Hollom) (hA : IsAntichain (· ≤ ·) A) : A.Finite := Hollom.no_infinite_antichain hA
example {f : ℚ → Hollom} : ¬ StrictMono f := Hollom.scattered


