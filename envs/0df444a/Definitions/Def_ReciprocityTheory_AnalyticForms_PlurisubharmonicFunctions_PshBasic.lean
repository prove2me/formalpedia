-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:41.283423+00:00
-- url     : https://prove2.me/theorems/92cc70f1-b5b3-4938-8b6e-852ad41f7bbe
-- title:
--   Psh Basic
-- statement:
--   Definitions and structural lemmas for Psh Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
namespace ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {D : ℕ}
def L0 (w : Fin D → ℂ) : ℂ →L[ℝ] (Fin D → ℂ) := (ContinuousLinearMap.id ℝ ℂ).smulRight w
def Pc (w : Fin D → ℂ) : ((Fin D → ℂ) →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ ℂ (Fin D → ℂ) ℝ).flip (L0 w)
def Gc (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ : ℂ) : ℂ →L[ℝ] ℝ :=
  Pc w (fderiv ℝ φ (z + ζ • w))
def Hc (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (Pc w).comp ((fderiv ℝ (fderiv ℝ φ) (z + ζ • w)).comp (L0 w))
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
end
end ReciprocityTheory.AnForm.A.PshLap
namespace ReciprocityTheory.AnForm.A.PshInh
open MeasureTheory Metric Set Filter Topology Real
noncomputable section
end
end ReciprocityTheory.AnForm.A.PshInh
namespace ReciprocityTheory.AnForm.A
open MeasureTheory Metric Set Filter Topology Real PshInh
end ReciprocityTheory.AnForm.A


