-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T19:30:45.094691+00:00
-- url     : https://prove2.me/theorems/a45676de-79f1-4466-9e16-c7395e97dc1d
-- title:
--   Geometrically Connected Of Is Iso Restrict
-- statement:
--   Definitions and structural lemmas for Geometrically Connected Of Is Iso Restrict, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
namespace GlobalTheory
inductive IsSmoothBlowupSeq {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) : ∀ {Y' : Scheme.{0}}, (Y' ⟶ Y) → Prop

  | id : IsSmoothBlowupSeq f B (𝟙 Y)

  | step {Y₁ Y₂ : Scheme.{0}} {s : Y₁ ⟶ Y} (J : Y₁.IdealSheafData) (π : Y₂ ⟶ Y₁) :
      IsSmoothBlowupSeq f B s → Smooth (J.subschemeι ≫ s ≫ f) → (J.support : Set Y₁) ⊆ s ⁻¹' B →
      FinalTheorems.Blowup π J → IsSmoothBlowupSeq f B (π ≫ s)
namespace Principalise
end Principalise
namespace Principalise
end Principalise
namespace Published
def Principalisation : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (Y : Scheme.{0}) (f : Y ⟶ Sp k),
    IsIntegral Y → SmoothOfRelativeDimension d f → IsProjOver f →
    ∀ I : Y.IdealSheafData, I ≠ ⊥ →
      ∃ (Y' : Scheme.{0}) (s : Y' ⟶ Y),
        IsIntegral Y' ∧ SmoothOfRelativeDimension d (s ≫ f) ∧ IsProjOver (s ≫ f) ∧
        IsSmoothBlowupSeq f (I.support : Set Y) s ∧ IsIso (s ∣_ I.support.compl) ∧
        FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support)
end Published
end GlobalTheory


