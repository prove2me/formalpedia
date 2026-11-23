-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:18.810897+00:00
-- url     : https://prove2.me/theorems/c94a7000-7fb6-4781-b881-62b29706c961
-- title:
--   Is Nilpotent Of Mem Ker Jet Trunc R
-- statement:
--   Definitions and structural lemmas for Is Nilpotent Of Mem Ker Jet Trunc R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.JetSer
section Val
variable {A : Type} [CommRing A] {X : Scheme.{0}}
def fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom
end Val
section Jet
variable {R : Type} [CommRing R] {κ : Type}
end Jet
end GlobalTheory.JetSer


