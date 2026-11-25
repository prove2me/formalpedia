-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etale_cohomology_restrict_eq_zero_at_finite_stage
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T06:35:34.552149+00:00
-- url     : https://prove2.me/submissions/b05d7759-d37f-46b7-be30-e799704525ea

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestrictionComposition
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_cohomology_restrict_eq_zero_at_affine_stage

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponEtaleFinitePullbackLimit

universe u

variable {I : Type u} [Category.{u} I] {Y W : Scheme.{u}}

/-- Pull a diagram of schemes over a base to a new base. -/
abbrev diagram (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj Y) (j : W ⟶ Y) :=
  Over.lift D t ⋙ Over.pullback j ⋙ Over.forget W

abbrev cone (D : I ⥤ Scheme.{u}) (c : Cone D)
    (t : D ⟶ (Functor.const I).obj Y) (f : c.pt ⟶ Y)
    (hf : ∀ k, c.π.app k ≫ t.app k = f) (j : W ⟶ Y) :
    Cone (diagram D t j) :=
  (Over.pullback j ⋙ Over.forget W).mapCone (Over.liftCone D t c f hf)

/-- The projections from the stages to the new base. -/
def structuralMaps (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj Y) (j : W ⟶ Y) :
    diagram D t j ⟶ (Functor.const I).obj W where
  app k := pullback.snd (t.app k) j
  naturality k l a := by
    change ((Over.lift D t ⋙ Over.pullback j).map a).left ≫ pullback.snd (t.app l) j
      = pullback.snd (t.app k) j ≫ 𝟙 W
    rw [Category.comp_id]
    exact Over.w ((Over.lift D t ⋙ Over.pullback j).map a)

theorem projection_comp (D : I ⥤ Scheme.{u}) (c : Cone D)
    (t : D ⟶ (Functor.const I).obj Y) (f : c.pt ⟶ Y)
    (hf : ∀ k, c.π.app k ≫ t.app k = f) (j : W ⟶ Y) (k : I) :
    (cone D c t f hf j).π.app k ≫ (structuralMaps D t j).app k = pullback.snd f j :=
  Over.w ((Over.pullback j).map ((Over.liftCone D t c f hf).π.app k))

/-- Pullback commutes with the cofiltered limit of schemes over the base. -/
def isLimit_cone [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (t : D ⟶ (Functor.const I).obj Y) (f : c.pt ⟶ Y)
    (hf : ∀ k, c.π.app k ≫ t.app k = f) (j : W ⟶ Y) :
    IsLimit (cone D c t f hf j) := by
  let : IsConnected I := IsCofiltered.isConnected I
  exact isLimitOfPreserves (Over.pullback j ⋙ Over.forget W)
    (Over.isLimitLiftCone D t c f hf hc)

/-- Base change of a finite scheme over an affine scheme is affine. -/
theorem isAffine_stage [IsAffine W] (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj Y) (j : W ⟶ Y)
    (hFinite : ∀ k, IsFinite (t.app k)) (k : I) :
    IsAffine ((diagram D t j).obj k) := by
  let : IsFinite (t.app k) := hFinite k
  exact isAffine_of_isAffineHom (pullback.snd (t.app k) j)

end PhilipponEtaleFinitePullbackLimit

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleCohomologyRestrictionComp (restrict_comp_eq_zero_iff)
open PhilipponEtaleFinitePullbackLimit

namespace PhilipponEtaleFiniteStageReduction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private theorem restrict_pullback_snd_eq_zero_iff {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z)
    (F : Ab Y) (q : ℕ) (x : F.H q) :
    restrict (pullback.snd a b) F q x = 0 ↔ restrict (pullback.fst b a) F q x = 0 := by
  constructor
  · intro h
    rw [← pullbackSymmetry_hom_comp_snd b a]
    exact (restrict_comp_eq_zero_iff _ _ F q x).mpr (h ▸ map_zero _)
  · intro h
    rw [← pullbackSymmetry_hom_comp_fst a b]
    exact (restrict_comp_eq_zero_iff _ _ F q x).mpr (h ▸ map_zero _)

/-- Finite-stage descent on a closed fiber reduces to descent along a
cofiltered diagram of affine schemes over that fiber. -/
theorem exists_stage_of_affine_limit {I : Type u} [Category.{u} I] [IsCofiltered I] (q : ℕ)
    (hAffine : ∀ (E : I ⥤ Scheme.{u}) (d : Cone E), IsLimit d →
      (∀ k, IsAffine (E.obj k)) →
      ∀ {W : Scheme.{u}} (s : E ⟶ (Functor.const I).obj W) (g : d.pt ⟶ W),
      (∀ k, d.π.app k ≫ s.app k = g) → ∀ (F : Ab W) (x : F.H q),
      restrict g F q x = 0 → ∃ k, restrict (s.app k) F q x = 0)
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    {Y W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
    (t : D ⟶ (Functor.const I).obj Y) (f : c.pt ⟶ Y)
    (hf : ∀ k, c.π.app k ≫ t.app k = f) (hFinite : ∀ k, IsFinite (t.app k))
    (F : Ab W) (x : F.H q) (hx : restrict (pullback.fst j f) F q x = 0) :
    ∃ k, restrict (pullback.fst j (t.app k)) F q x = 0 := by
  let : IsAffine W := isAffine_of_isAffineHom j
  have hx' := (restrict_pullback_snd_eq_zero_iff f j F q x).mpr hx
  obtain ⟨k, hk⟩ :=
    hAffine (diagram D t j) (cone D c t f hf j) (isLimit_cone D c hc t f hf j)
      (isAffine_stage D t j hFinite) (structuralMaps D t j) (pullback.snd f j)
      (projection_comp D c t f hf j) F x hx'
  exact ⟨k, (restrict_pullback_snd_eq_zero_iff (t.app k) j F q x).mp hk⟩

end PhilipponEtaleFiniteStageReduction

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    {Y W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
    (t : D ⟶ (Functor.const I).obj Y) (f : c.pt ⟶ Y)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) (hFinite : ∀ i, IsFinite (t.app i))
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) (x : F.H q) :
    PhilipponEtalePrimeTorsionComparison.restrict (pullback.fst j f) F q x = 0 →
      ∃ i, PhilipponEtalePrimeTorsionComparison.restrict (pullback.fst j (t.app i)) F q x = 0 := by
  intro hx
  refine PhilipponEtaleFiniteStageReduction.exists_stage_of_affine_limit q ?_ D c hc j t f hf hFinite F x hx
  intro E d hd hA X s g hg G y hy
  let : ∀ i, IsAffine (E.obj i) := hA
  exact AlgebraicGeometry.Scheme.exists_etale_cohomology_restrict_eq_zero_at_affine_stage E d hd s g hg G q y hy

end

end
