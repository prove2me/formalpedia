-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_noetherian_affineModels_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-22T07:14:35.184565+00:00
-- url     : https://prove2.me/submissions/6db3cc02-ecc3-4163-84be-676e8d3f436f

import Definitions.Def_AlgebraicGeometry_ProperAffineClosedSubschemes
import Definitions.Def_AlgebraicGeometry_ProperAffineFiniteStageModels
import Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd
import Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_proper_finitePresentation_envelope
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponProperFinitePresentationSpread

universe u

private theorem pullback_property {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {X Y S T : Scheme.{u}} {a : X ⟶ Y} {f : X ⟶ S} {g : Y ⟶ T} {b : S ⟶ T}
    (h : IsPullback a f g b) (hf : P f) : P (pullback.snd g b) := by
  rw [← h.isoPullback_hom_snd, P.cancel_left_of_respectsIso] at hf
  exact hf

private abbrev base (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] :=
  Spec.map (CommRingCat.ofHom (algebraMap A R))

private theorem change_stage {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    (T : Subalgebra A R) {X Y : Scheme.{u}}
    {a : X ⟶ Y} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of A)}
    (h : IsPullback a f g (base A R)) :
    ∃ π : X ⟶ pullback g (base A T), IsPullback π f (pullback.snd g (base A T)) (base T R) := by
  have hb : base T R ≫ base A T = base A R := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have he : a ≫ g = (f ≫ base T R) ≫ base A T := by
    rw [Category.assoc, hb]
    exact h.w
  let π := pullback.lift a (f ≫ base T R) he
  refine ⟨π, IsPullback.of_right (h₁₂ := pullback.fst g (base A T)) (v₁₃ := g)
    (h₂₂ := base A T) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)⟩
  change IsPullback (pullback.lift _ _ _ ≫ pullback.fst _ _) f g (base T R ≫ base A T)
  rw [pullback.lift_fst, hb]
  exact h

/-- A proper finitely presented scheme descends to a proper model over a finitely
generated subalgebra, with a prescribed finite set of coefficients included. -/
theorem exists_proper_model {A R : Type u} [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f] (s : Finset R) :
    ∃ (T : Subalgebra A R), T.FG ∧ (↑s : Set R) ⊆ T ∧
      ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of T)) (a : X ⟶ Y),
        IsProper g ∧ IsPullback a f g (base T R) := by
  obtain ⟨B, hB, hSeed, Y₀, g₀, a₀, hfp₀, hqc₀, hqs₀, h₀⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := A) f s
  let _ := hfp₀
  let _ := hqc₀
  let _ := hqs₀
  let : Algebra.FiniteType A B := (Subalgebra.fg_iff_finiteType B).mp hB
  let : IsSeparated (pullback.snd g₀ (base B R)) := pullback_property (P := @IsSeparated) h₀ inferInstance
  obtain ⟨C, hC, _, hSep⟩ :=
    AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd (A := R) g₀ ∅
  let _ := hSep
  let : Algebra.FiniteType B C := (Subalgebra.fg_iff_finiteType C).mp hC
  let : Algebra.FiniteType A C := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  let g₁ := pullback.snd g₀ (base B C)
  obtain ⟨a₁, h₁⟩ := change_stage C h₀
  let : QuasiCompact g₁ := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ hqc₀
  let : LocallyOfFinitePresentation g₁ := MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ hfp₀
  let : IsProper (pullback.snd g₁ (base C R)) := pullback_property (P := @IsProper) h₁ inferInstance
  obtain ⟨D, hD, _, hProper⟩ :=
    AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd (A := R) g₁ ∅
  obtain ⟨a₂, h₂⟩ := change_stage D h₁
  let : Algebra.FiniteType C D := (Subalgebra.fg_iff_finiteType D).mp hD
  let hFin : Algebra.FiniteType A D := Algebra.FiniteType.trans (S := C) inferInstance inferInstance
  refine ⟨D.restrictScalars A, (Subalgebra.fg_iff_finiteType _).mpr hFin, ?_, _, _, a₂, hProper, h₂⟩
  intro r hr
  let x : B := ⟨r, hSeed hr⟩
  let y : C := ⟨r, C.algebraMap_mem x⟩
  exact D.algebraMap_mem y

/-- The affine Noetherian approximation theorem for proper morphisms that are
locally of finite presentation. -/
theorem nonempty_affineModels_of_finitePresentation {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f] :
    Nonempty (PhilipponProperAffineApproximation.AffineModels f) := by
  let : Algebra (ULift.{u} ℤ) R := ULift.algebra' ℤ R
  let : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨T, hT, _, Y, g, a, hProper, hCart⟩ := exists_proper_model (A := ULift.{u} ℤ) f ∅
  let _ := hProper
  exact PhilipponAffineModelsOfFiniteStage.nonempty_of_isPullback hT a hCart

end PhilipponProperFinitePresentationSpread

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] :
    Nonempty (PhilipponProperAffineApproximation.AffineModels f) := by
  obtain ⟨Y, g, a, hg, hfp, ha, hcomp⟩ := AlgebraicGeometry.Scheme.exists_proper_finitePresentation_envelope f
  let _ := hg
  let _ := hfp
  let _ := ha
  obtain ⟨M⟩ := PhilipponProperFinitePresentationSpread.nonempty_affineModels_of_finitePresentation g
  exact ⟨hcomp ▸ M.closedImmersion a⟩

end

end
