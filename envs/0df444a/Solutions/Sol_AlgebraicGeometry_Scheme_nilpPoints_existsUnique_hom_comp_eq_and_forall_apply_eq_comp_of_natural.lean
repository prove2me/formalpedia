-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b35addc7-2251-51af-bb6b-35acf4bc42b2

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of 𝒪)) (fY : Y ⟶ Spec (.of 𝒪)) [LocallyOfFiniteType fX]
    (τ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B],
      (Scheme.nilpPoints fX).obj B → (Scheme.nilpPoints fY).obj B)
    (hτ : ∀ (B B' : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B] [CommRing B'] [Algebra 𝒪 B'] [IsNoetherianRing B']
      (g : B →ₐ[𝒪] B') (φ : (Scheme.nilpPoints fX).obj B),
      τ B' ((Scheme.nilpPoints fX).map g φ) = (Scheme.nilpPoints fY).map g (τ B φ)) :
    ∃! h : X ⟶ Y, h ≫ fY = fX ∧
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B] (φ : (Scheme.nilpPoints fX).obj B),
        (τ B φ).1 = φ.1 ≫ h := by
  classical

  have noeth : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (S : Subalgebra 𝒪 B), S.FG → IsNoetherianRing ↥S := by
    intro B _ _ S hS
    haveI : Algebra.FiniteType 𝒪 ↥S := ⟨(Subalgebra.fg_top S).mpr hS⟩
    exact Algebra.FiniteType.isNoetherianRing 𝒪 ↥S
  obtain ⟨hfac, hfilt⟩ := AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType 𝒪 fX

  have ex : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (y : (Scheme.nilpPoints fX).obj C),
      ∃ (S : Subalgebra 𝒪 C) (_ : S.FG) (y₀ : (Scheme.nilpPoints fX).obj ↥S),
        (Scheme.nilpPoints fX).map ((S.val).restrictScalars 𝒪) y₀ = y := fun C _ _ y => hfac C y
  choose Sof hSof y0of hyof using ex

  let val : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (S : Subalgebra 𝒪 C) (hS : S.FG) (y₀ : (Scheme.nilpPoints fX).obj ↥S),
      (Spec (.of C) ⟶ Y) := fun C _ _ S hS y₀ =>
    haveI := noeth C S hS
    Spec.map (CommRingCat.ofHom (S.val).toRingHom) ≫ (τ ↥S y₀).1

  have val_incl : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (S T : Subalgebra 𝒪 C) (hS : S.FG) (hT : T.FG) (h : S ≤ T)
      (y₀ : (Scheme.nilpPoints fX).obj ↥S),
      val C S hS y₀ = val C T hT ((Scheme.nilpPoints fX).map ((Subalgebra.inclusion h).restrictScalars 𝒪) y₀) := by
    intro C _ _ S T hS hT h y₀
    haveI := noeth C S hS; haveI := noeth C T hT
    show Spec.map (CommRingCat.ofHom (S.val).toRingHom) ≫ (τ ↥S y₀).1 =
      Spec.map (CommRingCat.ofHom (T.val).toRingHom) ≫ (τ ↥T ((Scheme.nilpPoints fX).map ((Subalgebra.inclusion h).restrictScalars 𝒪) y₀)).1
    rw [hτ, Scheme.nilpPoints_map_val, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have key : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (y : (Scheme.nilpPoints fX).obj C)
      (S : Subalgebra 𝒪 C) (hS : S.FG) (y₀ : (Scheme.nilpPoints fX).obj ↥S),
      (Scheme.nilpPoints fX).map ((S.val).restrictScalars 𝒪) y₀ = y →
      val C (Sof C y) (hSof C y) (y0of C y) = val C S hS y₀ := by
    intro C _ _ y S hS y₀ hy
    obtain ⟨S₃, hS₃, h₁, h₂, heq⟩ := hfilt C (Sof C y) S (hSof C y) hS (y0of C y) y₀ ((hyof C y).trans hy.symm)
    rw [val_incl C (Sof C y) S₃ (hSof C y) hS₃ h₁, val_incl C S S₃ hS hS₃ h₂, heq]

  obtain ⟨u, hu_over, hu_pts, hu_uniq⟩ := AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural (R := 𝒪) fX fY
    (fun C _ _ z hz => val C (Sof C ⟨z, hz⟩) (hSof C ⟨z, hz⟩) (y0of C ⟨z, hz⟩))
    (by
      intro C _ _ z hz
      haveI := noeth C (Sof C ⟨z, hz⟩) (hSof C ⟨z, hz⟩)
      show (Spec.map (CommRingCat.ofHom (Sof C ⟨z, hz⟩).val.toRingHom) ≫ (τ ↥(Sof C ⟨z, hz⟩) (y0of C ⟨z, hz⟩)).1) ≫ fY = _
      rw [Category.assoc, (τ ↥(Sof C ⟨z, hz⟩) (y0of C ⟨z, hz⟩)).2, Scheme.specMap_algHom_comp_specOver])
    (by
      intro C C' _ _ _ _ φ z hz hz'
      beta_reduce

      let S := Sof C ⟨z, hz⟩
      have hS : S.FG := hSof C ⟨z, hz⟩
      let y₀ := y0of C ⟨z, hz⟩
      let S₁ : Subalgebra 𝒪 C' := S.map φ
      have hS₁ : S₁.FG := hS.map φ
      let y₁ : (Scheme.nilpPoints fX).obj ↥S₁ := (Scheme.nilpPoints fX).map ((AlgHom.subalgebraMap S φ).restrictScalars 𝒪) y₀
      have hy₁ : (Scheme.nilpPoints fX).map ((S₁.val).restrictScalars 𝒪) y₁ = ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z, hz'⟩ := by
        apply Subtype.ext
        show Spec.map (CommRingCat.ofHom ((S₁.val).restrictScalars 𝒪).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom ((AlgHom.subalgebraMap S φ).restrictScalars 𝒪).toRingHom) ≫ y₀.1) =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z
        have hz0 : z = Spec.map (CommRingCat.ofHom ((S.val).restrictScalars 𝒪).toRingHom) ≫ y₀.1 :=
          (congrArg Subtype.val (hyof C ⟨z, hz⟩)).symm
        conv_rhs => rw [hz0]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp]
        rfl
      rw [key C' ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z, hz'⟩ S₁ hS₁ y₁ hy₁]
      haveI := noeth C S hS; haveI := noeth C' S₁ hS₁
      show Spec.map (CommRingCat.ofHom (S₁.val).toRingHom) ≫ (τ ↥S₁ y₁).1 =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (Spec.map (CommRingCat.ofHom (S.val).toRingHom) ≫ (τ ↥S y₀).1)
      rw [show τ ↥S₁ y₁ = _ from hτ ↥S ↥S₁ ((AlgHom.subalgebraMap S φ).restrictScalars 𝒪) y₀, Scheme.nilpPoints_map_val,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl)

  refine ⟨u, ⟨hu_over, ?_⟩, ?_⟩
  · intro B _ _ _ φ
    rw [hu_pts B φ.1 φ.2]
    haveI := noeth B (Sof B φ) (hSof B φ)
    show (τ B φ).1 = Spec.map (CommRingCat.ofHom (Sof B φ).val.toRingHom) ≫ (τ ↥(Sof B φ) (y0of B φ)).1
    have e2 := hτ ↥(Sof B φ) B (((Sof B φ).val).restrictScalars 𝒪) (y0of B φ)
    rw [hyof B φ] at e2
    rw [e2, Scheme.nilpPoints_map_val]
    rfl
  · rintro h' ⟨hh'over, hh'⟩
    apply hu_uniq
    intro C _ _ z hz
    haveI := noeth C (Sof C ⟨z, hz⟩) (hSof C ⟨z, hz⟩)
    show z ≫ h' = Spec.map (CommRingCat.ofHom (Sof C ⟨z, hz⟩).val.toRingHom) ≫ (τ ↥(Sof C ⟨z, hz⟩) (y0of C ⟨z, hz⟩)).1
    rw [hh', ← Category.assoc]
    congr 1
    exact (congrArg Subtype.val (hyof C ⟨z, hz⟩)).symm

end S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural (solution)
