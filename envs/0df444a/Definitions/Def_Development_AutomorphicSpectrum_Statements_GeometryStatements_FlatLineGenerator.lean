-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Statements_GeometryStatements_FlatLineGenerator
-- name    : Development_AutomorphicSpectrum_Statements_GeometryStatements_FlatLineGenerator
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:02.048031+00:00
-- url     : https://prove2.me/theorems/97d74882-fdc3-4043-986e-1c4e52241436
-- title:
--   Flat Line Generator
-- statement:
--   Definitions and structural lemmas for Flat Line Generator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/GeometryStatements/FlatLineGenerator.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_BdryChart
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LevelSectionsExactKernelLocusOpen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_ClopenCondOnto
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Geometry__GagaSections_c8ce35651d051f04
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl Filter Topology Metric
def FlatLineGenerator : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → ∃ φ : FrameFn Xo c, IsLineFn U τ φ ∧ FlatOnModel Z τ φ ∧ ∀ φ' : FrameFn Xo c, IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w
end GlobalTheory.CompanionTheory.Ar.Flat


