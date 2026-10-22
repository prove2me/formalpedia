-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
-- name    : LPCA_Solutions_LPCA_FinitePiColimit_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:20:28.553989+00:00
-- url     : https://prove2.me/theorems/5db41505-07d8-4265-9c76-ba0071c3a6e6
-- title:
--   Finite products of sequential module-colimit cocones
-- statement:
--   For a commutative ring R and a finite index type I, this bundle constructs the pointwise product of I many natural-number-indexed module diagrams and proves that the product of their specified colimit cocones is a colimit cocone. The finite-sum descent includes I empty and requires no injectivity of transition maps.
--
--   The included constructions and necessary compatibility results are:
--
--   - A finite family of module diagrams, assembled using the actual dependent function modules and the diagonal transition maps.
--   - Finite products of module colimit cocones are colimit cocones. The construction uses finite sums of the column descents, including the empty index family, without assuming that any transition is injective.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FinitePiColimit.lean, selected declarations in lines 16–122; source SHA-256 e4db2b367b916a66e19569a7c7b6b72b543061ddf602dfc1552cf53ede8882bc; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R]
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- A finite family of module diagrams, assembled using the actual dependent
function modules and the diagonal transition maps. -/
noncomputable abbrev finitePiDiagram (D : I → ℕ ⥤ ModuleCat.{u} R) :
    ℕ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (∀ i, (D i).obj n)
  map f := ModuleCat.ofHom (LinearMap.pi fun i =>
    ((D i).map f).hom.comp (LinearMap.proj i))
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    funext i
    exact congrArg (fun f => f (y i)) ((D i).map_id n)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    funext i
    exact congrArg (fun h => h (y i)) ((D i).map_comp f g)

noncomputable def finitePiInclusion (D : I → ℕ ⥤ ModuleCat.{u} R) (i : I) :
    D i ⟶ finitePiDiagram D where
  app n := ModuleCat.ofHom (LinearMap.single R (fun j => (D j).obj n) i)
  naturality n m f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    funext j
    change (Pi.single i ((D i).map f y) : ∀ j, (D j).obj m) j =
      (D j).map f ((Pi.single i y : ∀ j, (D j).obj n) j)
    by_cases h : j = i
    · subst j
      simp
    · simp [Pi.single_apply, h, Ne.symm h]

noncomputable abbrev finitePiCocone {D : I → ℕ ⥤ ModuleCat.{u} R}
    (c : ∀ i, Cocone (D i)) : Cocone (finitePiDiagram D) where
  pt := ModuleCat.of R (∀ i, (c i).pt)
  ι := {
    app n := ModuleCat.ofHom (LinearMap.pi fun i =>
      ((c i).ι.app n).hom.comp (LinearMap.proj i))
    naturality n m f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      funext i
      exact congrArg (fun h => h (y i)) ((c i).w f) }

/-- Finite products of module colimit cocones are colimit cocones. The
construction uses finite sums of the column descents, including the empty
index family, without assuming that any transition is injective. -/
noncomputable def finitePiCoconeIsColimit
    {D : I → ℕ ⥤ ModuleCat.{u} R} (c : ∀ i, Cocone (D i))
    (hc : ∀ i, IsColimit (c i)) : IsColimit (finitePiCocone c) where
  desc s := ModuleCat.ofHom {
    toFun y := ∑ i, (hc i).desc (Cocone.mk s.pt (finitePiInclusion D i ≫ s.ι)) (y i)
    map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
    map_smul' r y := by
      simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum] }
  fac s n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change (∑ i, (hc i).desc (Cocone.mk s.pt (finitePiInclusion D i ≫ s.ι))
      ((c i).ι.app n (y i))) = s.ι.app n y
    trans ∑ i, s.ι.app n (Pi.single i (y i))
    · apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun h => h (y i))
        ((hc i).fac (Cocone.mk s.pt (finitePiInclusion D i ≫ s.ι)) n)
    · rw [← map_sum, LinearMap.sum_single_apply]
  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply LinearMap.pi_ext
    intro i y
    let inc : (c i).pt ⟶ (finitePiCocone c).pt :=
      ModuleCat.ofHom (LinearMap.single R (fun j => (c j).pt) i)
    have he : inc ≫ m = (hc i).desc
        (Cocone.mk s.pt (finitePiInclusion D i ≫ s.ι)) := by
      refine (hc i).uniq (Cocone.mk s.pt (finitePiInclusion D i ≫ s.ι)) (inc ≫ m) ?_
      intro n
      have h := congrArg (fun f => (finitePiInclusion D i).app n ≫ f) (hm n)
      have hi : (c i).ι.app n ≫ inc =
          (finitePiInclusion D i).app n ≫ (finitePiCocone c).ι.app n := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext j
        change (Pi.single i ((c i).ι.app n x) : ∀ j, (c j).pt) j =
          (c j).ι.app n ((Pi.single i x : ∀ j, (D j).obj n) j)
        by_cases h : j = i
        · subst j
          simp
        · simp [Pi.single_apply, h, Ne.symm h]
      rw [← Category.assoc, hi, Category.assoc]
      exact h
    change (inc ≫ m) y = _
    rw [he]
    change (hc i).desc (Cocone.mk s.pt (finitePiInclusion D i ≫ s.ι)) y =
      ∑ j, (hc j).desc (Cocone.mk s.pt (finitePiInclusion D j ≫ s.ι))
        ((Pi.single i y : ∀ j, (c j).pt) j)
    symm
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_apply, hji, Ne.symm hji]
    · simp

end LPCA


