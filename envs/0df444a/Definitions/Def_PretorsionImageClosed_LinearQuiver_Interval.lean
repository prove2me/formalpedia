-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
-- name    : PretorsionImageClosed_LinearQuiver_Interval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:45.068861+00:00
-- url     : https://prove2.me/theorems/93d341cd-c7cb-4787-87e0-44bbc493afce
-- title:
--   Interval
-- statement:
--   Definitions and structural lemmas for Interval, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
namespace LinearQuiver
universe u
variable (k : Type u) [Field k]
def inclusionOrZero (p q : Submodule k k) : p →ₗ[k] q :=
  by classical exact if h : p ≤ q then Submodule.inclusion h else 0
theorem inclusionOrZero_of_le {p q : Submodule k k} (h : p ≤ q) :
    inclusionOrZero k p q = Submodule.inclusion h := by
  unfold inclusionOrZero
  rw [dif_pos h]
theorem inclusionOrZero_of_not_le {p q : Submodule k k} (h : ¬ p ≤ q) :
    inclusionOrZero k p q = 0 := by
  unfold inclusionOrZero
  rw [dif_neg h]
open Classical in
theorem coe_inclusionOrZero (p q : Submodule k k) (x : p) :
    ((inclusionOrZero k p q x : q) : k) = if p ≤ q then (x : k) else 0 := by
  by_cases h : p ≤ q
  · rw [inclusionOrZero_of_le k h, if_pos h, Submodule.coe_inclusion]
  · rw [inclusionOrZero_of_not_le k h, if_neg h]
    rfl
theorem inclusionOrZero_self (p : Submodule k k) : inclusionOrZero k p p = LinearMap.id := by
  rw [inclusionOrZero_of_le k le_rfl]
  rfl
variable {n : ℕ}
def intervalSpace (a d i : Fin n) : Submodule k k :=
  if a ≤ i ∧ i ≤ d then ⊤ else ⊥
theorem intervalSpace_of_not_mem {a d i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ d)) :
    intervalSpace k a d i = ⊥ := if_neg h
theorem coe_eq_zero_of_not_mem {a d i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ d)) (x : intervalSpace k a d i) :
    (x : k) = 0 := by
  have hle : intervalSpace k a d i ≤ ⊥ := (intervalSpace_of_not_mem k h).le
  exact (Submodule.mem_bot k).1 (hle x.2)
theorem intervalSpace_le_iff {a d i j : Fin n} (hij : i ≤ j) :
    intervalSpace k a d i ≤ intervalSpace k a d j ↔ ((a ≤ i ∧ i ≤ d) → j ≤ d) := by
  unfold intervalSpace
  constructor
  · intro h hi
    by_contra hjd
    rw [if_pos hi, if_neg (fun hj => hjd hj.2)] at h
    have := h (Submodule.mem_top (x := (1 : k)))
    rw [Submodule.mem_bot] at this
    exact one_ne_zero this
  · intro h
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1.trans hij, h h1⟩ h2
    · exact bot_le
    · exact le_rfl
theorem coe_intervalMap {a d i j : Fin n} (hij : i ≤ j) (x : intervalSpace k a d i) :
    ((inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a d j) x : intervalSpace k a d j) : k) =
      if j ≤ d then (x : k) else 0 := by
  rw [coe_inclusionOrZero, intervalSpace_le_iff k hij]
  by_cases hi : a ≤ i ∧ i ≤ d
  · by_cases hjd : j ≤ d
    · rw [if_pos (fun _ => hjd), if_pos hjd]
    · rw [if_neg (fun h => hjd (h hi)), if_neg hjd]
  · rw [coe_eq_zero_of_not_mem k hi x]
    split_ifs <;> rfl
abbrev interval (a d : Fin n) : Statement.LinRep k n where
  obj i := FGModuleCat.of k (intervalSpace k a d i)
  map {i j} f :=
    FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a d j))
  map_id i := by
    apply FGModuleCat.hom_ext
    exact inclusionOrZero_self k _
  map_comp {i j l} f g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((inclusionOrZero k _ _ x : intervalSpace k a d l) : k) =
      ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a d l) : k)
    rw [coe_intervalMap k (leOfHom (f ≫ g)), coe_intervalMap k (leOfHom g),
      coe_intervalMap k (leOfHom f)]
    by_cases hl : l ≤ d
    · rw [if_pos hl, if_pos hl, if_pos ((leOfHom g).trans hl)]
    · rw [if_neg hl, if_neg hl]
theorem intervalSpace_le_of_le_left {a ℓ d : Fin n} (h : a ≤ ℓ) (i : Fin n) :
    intervalSpace k ℓ d i ≤ intervalSpace k a d i := by
  unfold intervalSpace
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h.trans h1.1, h1.2⟩ h2
  · exact bot_le
  · exact le_rfl
theorem coe_inclusionOrZero_left {a ℓ d : Fin n} (h : a ≤ ℓ) (i : Fin n)
    (x : intervalSpace k ℓ d i) :
    ((inclusionOrZero k (intervalSpace k ℓ d i) (intervalSpace k a d i) x : intervalSpace k a d i) : k)
      = (x : k) := by
  rw [coe_inclusionOrZero, if_pos (intervalSpace_le_of_le_left k h i)]
def intervalIncl {a ℓ : Fin n} (d : Fin n) (h : a ≤ ℓ) : interval k ℓ d ⟶ interval k a d where
  app i := FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k ℓ d i) (intervalSpace k a d i))
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k ℓ d i) => ?_
    apply Subtype.ext
    change ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a d j) : k) =
      ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a d j) : k)
    rw [coe_inclusionOrZero_left k h, coe_intervalMap k (leOfHom f), coe_intervalMap k (leOfHom f),
      coe_inclusionOrZero_left k h]
theorem coe_inclusionOrZero_right {a ℓ d : Fin n} (h : ℓ ≤ d) (i : Fin n)
    (x : intervalSpace k a d i) :
    ((inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a ℓ i) x : intervalSpace k a ℓ i) : k)
      = if i ≤ ℓ then (x : k) else 0 := by
  rw [coe_inclusionOrZero]
  by_cases hi : a ≤ i ∧ i ≤ d
  · by_cases hil : i ≤ ℓ
    · rw [if_pos hil, if_pos]
      unfold intervalSpace
      rw [if_pos hi, if_pos ⟨hi.1, hil⟩]
    · rw [if_neg hil, if_neg]
      unfold intervalSpace
      rw [if_pos hi, if_neg (fun h' => hil h'.2)]
      intro hle
      have := hle (Submodule.mem_top (x := (1 : k)))
      rw [Submodule.mem_bot] at this
      exact one_ne_zero this
  · rw [coe_eq_zero_of_not_mem k hi x]
    split_ifs <;> rfl
def intervalProj (a : Fin n) {ℓ d : Fin n} (h : ℓ ≤ d) : interval k a d ⟶ interval k a ℓ where
  app i := FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a ℓ i))
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k a d i) => ?_
    apply Subtype.ext
    change ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a ℓ j) : k) =
      ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a ℓ j) : k)
    rw [coe_inclusionOrZero_right k h, coe_intervalMap k (leOfHom f), coe_intervalMap k (leOfHom f),
      coe_inclusionOrZero_right k h]
    by_cases hjl : j ≤ ℓ
    · rw [if_pos hjl, if_pos hjl, if_pos (hjl.trans h), if_pos ((leOfHom f).trans hjl)]
    · rw [if_neg hjl, if_neg hjl]
end LinearQuiver
end PretorsionImageClosed


