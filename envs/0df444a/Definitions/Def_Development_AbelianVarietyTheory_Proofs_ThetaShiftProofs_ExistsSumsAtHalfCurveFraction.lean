-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:32.907621+00:00
-- url     : https://prove2.me/theorems/941f6247-8051-4ba7-bc72-21cba1974190
-- title:
--   Exists Sums At Half Curve Fraction
-- statement:
--   Definitions and structural lemmas for Exists Sums At Half Curve Fraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_evLoc_algebraMap
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.evLoc_algebraMap
attribute [local simp] GlobalTheory.Conv.expandConv_u


set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
namespace GlobalTheory.Conv
section Values
variable {A : Type} [CommRing A] {Z : Scheme.{0}}
end Values
variable {Z : Scheme.{0}}
def halfCurve {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) (w : ℂ) : Sp ℂ ⟶ Z :=
  if hw : T < w.im then spMap (ev T w hw : halfRing T →+* ℂ) ≫ yT
  else spMap (ev T (((T + 1 : ℝ) : ℂ) * Complex.I) (by simp) : halfRing T →+* ℂ) ≫ yT
def laurentToFraction : ℂ⸨X⸩ ≃ₐ[ℂ⟦X⟧] FractionRing ℂ⟦X⟧ :=
  (FractionRing.algEquiv ℂ⟦X⟧ ℂ⸨X⸩).symm
def convToFraction : convLaurent →+* FractionRing ℂ⟦X⟧ :=
  (laurentToFraction : ℂ⸨X⸩ →+* FractionRing ℂ⟦X⟧).comp (algebraMap convLaurent ℂ⸨X⸩)
end GlobalTheory.Conv


