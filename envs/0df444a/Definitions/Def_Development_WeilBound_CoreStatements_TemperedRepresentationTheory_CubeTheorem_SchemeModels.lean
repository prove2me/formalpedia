-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:20.008668+00:00
-- url     : https://prove2.me/theorems/86125351-798b-4cee-b85c-826b26da05db
-- title:
--   Scheme Models
-- statement:
--   Definitions and structural lemmas for Scheme Models, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/CubeTheorem/SchemeModels.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace GlobalTheory.SpreadingModels
def IsModel {R R₀ : Type} [CommRing R] [CommRing R₀] (φ : R₀ →+* R) {Y Y₀ : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (π : Y ⟶ Y₀) : Prop :=
  Algebra.FiniteType ℤ R₀ ∧ LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
    IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))
def SchemeModels : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)),
    LocallyOfFinitePresentation f → QuasiCompact f → QuasiSeparated f →
      ∃ (R₀ : Type) (_ : CommRing R₀) (φ : R₀ →+* R) (Y₀ : Scheme.{0}) (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀))
        (π : Y ⟶ Y₀), IsModel φ f f₀ π
def Spreads (P : MorphismProperty Scheme.{0}) : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (φ : R₀ →+* R) (Y Y₀ : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (π : Y ⟶ Y₀),
    IsModel φ f f₀ π → P f →
      ∃ (R₁ : Type) (_ : CommRing R₁) (ψ : R₀ →+* R₁) (φ₁ : R₁ →+* R), φ₁.comp ψ = φ ∧
        Algebra.FiniteType ℤ R₁ ∧ P (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ)))
end GlobalTheory.SpreadingModels


