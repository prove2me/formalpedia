-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:49.030033+00:00
-- url     : https://prove2.me/theorems/b14ae295-34a2-4a32-a792-1b73b97fae7d
-- title:
--   Frame Meas Statement Pf C
-- statement:
--   Definitions and structural lemmas for Frame Meas Statement Pf C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def ufL : (Ix X.Ψ r → ℂ) ≃ₗ[ℂ] Frame X.Ψ r where
  toFun := uf X
  invFun x i := x i.1 i.2.1 i.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
def ufC : (Ix X.Ψ r → ℂ) ≃L[ℂ] Frame X.Ψ r := (ufL X).toContinuousLinearEquiv
theorem haarF : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure := by
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  rw [volume_pi]
  exact Measure.pi.isAddHaarMeasure _
theorem haarIx : (volume : Measure (Ix X.Ψ r → ℂ)).IsAddHaarMeasure := by
  infer_instance
attribute [local instance] haarF haarIx
def fI (C : Set (Frame X.Ψ r)) (q : Frame X.Ψ r × (UpI X.Ψ r → ℂ)) : ℝ≥0∞ :=
  if ∀ τ b, q.2 (dI τ b) ≠ 0 then
    ENNReal.ofReal (Complex.normSq (jacU q.2)) * C.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul q.1 (UF X q.2)) else 0
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM


