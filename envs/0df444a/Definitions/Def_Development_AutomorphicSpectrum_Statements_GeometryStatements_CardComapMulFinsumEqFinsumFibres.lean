-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Statements_GeometryStatements_CardComapMulFinsumEqFinsumFibres
-- name    : Development_AutomorphicSpectrum_Statements_GeometryStatements_CardComapMulFinsumEqFinsumFibres
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:40.833857+00:00
-- url     : https://prove2.me/theorems/99a067f4-4a6f-502d-9f84-5481c4fe6e73
-- title:
--   Card Comap Mul Finsum Eq Finsum Fibres
-- statement:
--   Definitions and structural lemmas for Card Comap Mul Finsum Eq Finsum Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/GeometryStatements/CardComapMulFinsumEqFinsumFibres.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_BdryChart
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LevelSectionsExactKernelLocusOpen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_ClopenCondOnto
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Geometry__GagaSections_c8ce35651d051f04
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
def FlatLineGeneratorComponent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → (∀ s : c.F →+* ℂ, ∃ t : ℝ, HasInfNorm U τ φ s t ∧ HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t) ∧ ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsFlatGen U τ φ FU i
end GlobalTheory.CompanionTheory.Ar.Flat


