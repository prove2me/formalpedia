-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MeasurePreservingCompEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MeasurePreservingCompEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:35.379663+00:00
-- url     : https://prove2.me/theorems/ecbed6f4-ecd1-4970-9ad5-d936bd467397
-- title:
--   Measure Preserving Comp Equiv
-- statement:
--   Definitions and structural lemmas for Measure Preserving Comp Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MeasurePreservingCompEquiv.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
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
open MeasureTheory
namespace GlobalTheory.UnifDens
variable {ι : Type} [Fintype ι] {p q n : ℕ}
def flatL (h : Fintype.card (ι × Fin p × Fin q) = n) : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (ι × Fin p × Fin q → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq h)).toContinuousLinearEquiv
end GlobalTheory.UnifDens


