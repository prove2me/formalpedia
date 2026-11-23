-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_LBSpreads
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_LBSpreads
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:50.012332+00:00
-- url     : https://prove2.me/theorems/e49a28d3-f352-4eae-9ddb-d25f26efd253
-- title:
--   LBSpreads
-- statement:
--   Definitions and structural lemmas for LBSpreads, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/CubeTheorem/LBSpreads.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw
namespace GlobalTheory.SpreadingModels
def PerfAll : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
    ∀ M : LB Y, M.IsLB → Nonempty (Perf f M)
def HasModel {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) : Prop :=
  ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (φ : R₀ →+* R) (Y₀ : Scheme.{0})
    (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (π : Y ⟶ Y₀),
    IsProper f₀ ∧ Flat f₀ ∧ IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ M₀ : LB Y₀, M₀.IsLB ∧ ∃ w : LB.Iso M (M₀.pull π), w.IsGen
def LBSpreads : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (φ : R₀ →+* R) (Y Y₀ : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (π : Y ⟶ Y₀),
    IsModel φ f f₀ π → ∀ M : LB Y, M.IsLB →
      ∃ (R₁ : Type) (_ : CommRing R₁) (ψ : R₀ →+* R₁) (φ₁ : R₁ →+* R)
        (ρ : Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ))),
        φ₁.comp ψ = φ ∧ Algebra.FiniteType ℤ R₁ ∧ ρ ≫ pullback.fst _ _ = π ∧
          ρ ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom φ₁) ∧
          ∃ M₁ : LB (pullback f₀ (Spec.map (CommRingCat.ofHom ψ))), M₁.IsLB ∧
            ∃ w : LB.Iso M (M₁.pull ρ), w.IsGen
end GlobalTheory.SpreadingModels


