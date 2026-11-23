-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfF
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:24.159532+00:00
-- url     : https://prove2.me/theorems/51e3ae16-797d-45e7-99fd-48f10ade6118
-- title:
--   Poin Statement Pf F
-- statement:
--   Definitions and structural lemmas for Poin Statement Pf F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfF.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
theorem signature_add_sub_cancel (X : Data E r) : X.p0 + (r - X.p0) = r := by
  have := X.p0_le
  omega
def eS (X : Data E r) : Fin (r - X.p0) ⊕ Fin X.p0 ≃ Fin r :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (signature_add_sub_cancel X)))
def gM (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := (mat x0 τ)⁻¹ * mat x τ
def Mq (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  ((gM X x0 x τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def i0 (X : Data E r) : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
def rhY (X : Data E r) (x0 y : Frame X.Ψ r) : ℝ :=
  -∑ τ, (Real.log ‖dmin X.Gm y τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 y τ) (i0 X)‖)
def kaY (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (y : Frame X.Ψ r) : ℝ := Real.exp (-bb * rhY X x0 y)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf


