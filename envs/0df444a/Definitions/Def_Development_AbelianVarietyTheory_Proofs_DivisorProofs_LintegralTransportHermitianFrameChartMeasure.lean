-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:43.879422+00:00
-- url     : https://prove2.me/theorems/bd578a90-5cbc-47bd-baae-8062033670bd
-- title:
--   Lintegral Transport Hermitian Frame Chart Measure
-- statement:
--   Definitions and structural lemmas for Lintegral Transport Hermitian Frame Chart Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
open scoped Matrix
namespace GlobalTheory.FlagTransport
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {E' : Type} [Field E'] [NumberField E'] [IsCMField E']
variable (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)
def entEquiv : Ent X ≃ Ent X' := Equiv.prodCongr e (Equiv.refl _)
def idxEquiv : Fin (nd X) ≃ Fin (nd X') :=
  (Fintype.equivFin (Ent X)).symm.trans ((entEquiv X X' e).trans (Fintype.equivFin (Ent X')))
def coordIso : V (nd X) ≃ₗᵢ[ℂ] V (nd X') := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idxEquiv X X' e)
def coordIsoR : V (nd X) ≃ₗᵢ[ℝ] V (nd X') :=
  { (coordIso X X' e).toLinearEquiv.restrictScalars ℝ with norm_map' := (coordIso X X' e).norm_map }
end
end GlobalTheory.FlagTransport


