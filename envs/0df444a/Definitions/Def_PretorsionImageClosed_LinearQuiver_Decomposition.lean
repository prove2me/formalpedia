-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
-- name    : PretorsionImageClosed_LinearQuiver_Decomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:20:22.918699+00:00
-- url     : https://prove2.me/theorems/2b9e92cc-9977-4b76-9c1e-d12d269d656d
-- title:
--   Decomposition
-- statement:
--   Definitions and structural lemmas for Decomposition, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean

module
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_isZero_iff_subsingleton
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSpace_of_mem

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
theorem interval_map_apply (c d : Fin n) {i j : Fin n} (f : i ⟶ j) (x : intervalSpace k c d i) :
    ((interval k c d).map f).hom.hom x =
      inclusionOrZero k (intervalSpace k c d i) (intervalSpace k c d j) x := rfl
section Split
variable (X : Statement.LinRep k n) (i₀ : Fin n) (v : X.obj i₀)
def vmap (j : Fin n) : X.obj j :=
  if h : i₀ ≤ j then (X.map (homOfLE h)).hom.hom v else 0
theorem vmap_of_le {j : Fin n} (h : i₀ ≤ j) : vmap X i₀ v j = (X.map (homOfLE h)).hom.hom v := by
  unfold vmap
  rw [dif_pos h]
theorem map_vmap {i j : Fin n} (f : i ⟶ j) (hi : i₀ ≤ i) :
    (X.map f).hom.hom (vmap X i₀ v i) = vmap X i₀ v j := by
  rw [vmap_of_le X i₀ v hi, vmap_of_le X i₀ v (hi.trans (leOfHom f))]
  change ((X.map (homOfLE hi)) ≫ (X.map f)).hom.hom v = _
  rw [← X.map_comp, Subsingleton.elim (homOfLE hi ≫ f) (homOfLE (hi.trans (leOfHom f)))]
variable {X i₀ v} (d : Fin n)
def fromVectorLin (j : Fin n) : intervalSpace k i₀ d j →ₗ[k] X.obj j :=
  (LinearMap.toSpanSingleton k (X.obj j) (vmap X i₀ v j)).comp (intervalSpace k i₀ d j).subtype
theorem fromVectorLin_apply (j : Fin n) (x : intervalSpace k i₀ d j) :
    fromVectorLin (v := v) d j x = (x : k) • vmap X i₀ v j := rfl
def fromVector (hd : ∀ j, d < j → vmap X i₀ v j = 0) : interval k i₀ d ⟶ X where
  app j := ConcreteCategory.ofHom (fromVectorLin (v := v) d j)
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k i₀ d i) => ?_
    change fromVectorLin (v := v) d j (((interval k i₀ d).map f).hom.hom x) =
      (X.map f).hom.hom (fromVectorLin (v := v) d i x)
    rw [fromVectorLin_apply, fromVectorLin_apply, interval_map_apply, map_smul]
    have hc := coe_intervalMap k (a := i₀) (d := d) (leOfHom f) x
    rw [hc]
    by_cases hi : i₀ ≤ i
    · rw [map_vmap X i₀ v f hi]
      by_cases hjd : j ≤ d
      · rw [if_pos hjd]
      · rw [if_neg hjd, hd j (not_le.1 hjd)]
        simp
    · have hx : (x : k) = 0 := coe_eq_zero_of_not_mem k (fun h => hi h.1) x
      rw [hx]
      simp
variable (ℓ : Module.Dual k (X.obj d))
def toIntervalLin (j : Fin n) : X.obj j →ₗ[k] intervalSpace k i₀ d j := by
  classical
  exact if h : i₀ ≤ j ∧ j ≤ d then
    (ℓ.comp (X.map (homOfLE h.2)).hom.hom).codRestrict (intervalSpace k i₀ d j)
      (fun x => by rw [intervalSpace_of_mem k h]; exact Submodule.mem_top)
  else 0
theorem toIntervalLin_apply_of_mem {j : Fin n} (h : i₀ ≤ j ∧ j ≤ d) (x : X.obj j) :
    (toIntervalLin (i₀ := i₀) d ℓ j x : k) = ℓ ((X.map (homOfLE h.2)).hom.hom x) := by
  unfold toIntervalLin
  rw [dif_pos h]
  rfl
theorem toIntervalLin_apply_of_not_mem {j : Fin n} (h : ¬ (i₀ ≤ j ∧ j ≤ d)) (x : X.obj j) :
    (toIntervalLin (i₀ := i₀) d ℓ j x : k) = 0 := by
  unfold toIntervalLin
  rw [dif_neg h]
  rfl
theorem eq_zero_of_lt_first (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) {i : Fin n} (hi : i < i₀)
    (x : X.obj i) : x = 0 := by
  have := (FGModuleCat.isZero_iff_subsingleton _).1 (hfirst i hi)
  exact Subsingleton.elim _ _
def toInterval (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) : X ⟶ interval k i₀ d where
  app j := ConcreteCategory.ofHom (toIntervalLin (i₀ := i₀) d ℓ j)
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    change (toIntervalLin (i₀ := i₀) d ℓ j ((X.map f).hom.hom x) : k) =
      (((interval k i₀ d).map f).hom.hom (toIntervalLin (i₀ := i₀) d ℓ i x) : k)
    rw [interval_map_apply, coe_intervalMap k (leOfHom f)]
    by_cases hjd : j ≤ d
    · rw [if_pos hjd]
      by_cases hj : i₀ ≤ j
      · rw [toIntervalLin_apply_of_mem d ℓ ⟨hj, hjd⟩]
        by_cases hi : i₀ ≤ i
        · rw [toIntervalLin_apply_of_mem d ℓ ⟨hi, (leOfHom f).trans hjd⟩]
          change ℓ ((X.map f ≫ X.map (homOfLE hjd)).hom.hom x) = _
          rw [← X.map_comp, Subsingleton.elim (f ≫ homOfLE hjd) (homOfLE ((leOfHom f).trans hjd))]
        · rw [toIntervalLin_apply_of_not_mem d ℓ (fun h => hi h.1),
            eq_zero_of_lt_first hfirst (not_le.1 hi) x, map_zero, map_zero, map_zero]
      · rw [toIntervalLin_apply_of_not_mem d ℓ (fun h => hj h.1),
          toIntervalLin_apply_of_not_mem d ℓ (fun h => hj (h.1.trans (leOfHom f)))]
    · rw [if_neg hjd, toIntervalLin_apply_of_not_mem d ℓ (fun h => hjd h.2)]
end Split
inductive IntervalSum : Statement.LinRep k n → Prop
  | zero {X : Statement.LinRep k n} (h : IsZero X) : IntervalSum X
  | step {X X' : Statement.LinRep k n} (a d : Fin n) (had : a ≤ d) (h' : IntervalSum X')
      (e : X ≅ interval k a d ⊞ X') : IntervalSum X
end LinearQuiver
end PretorsionImageClosed


