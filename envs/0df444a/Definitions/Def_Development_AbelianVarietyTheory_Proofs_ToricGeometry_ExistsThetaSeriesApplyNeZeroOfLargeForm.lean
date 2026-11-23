-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:11.588574+00:00
-- url     : https://prove2.me/theorems/a1359934-6ae6-44cc-a65a-76538e0a6d0b
-- title:
--   Exists Theta Series Apply Ne Zero Of Large Form
-- statement:
--   Definitions and structural lemmas for Exists Theta Series Apply Ne Zero Of Large Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.ThetaLarge
section General
variable {E : Type*} [NormedAddCommGroup E]
def term (L : Submodule ℤ E) (H : E → E → ℂ) (χ : L → ℂ) (z₀ : E) (l : L) (z : E) : ℂ :=
  (χ l)⁻¹ * cexp (Real.pi * H (z + l) z₀ - (Real.pi * H z l + Real.pi / 2 * H l l))
variable {L : Submodule ℤ E} {H : E → E → ℂ} {χ : L → ℂ}
end General
variable {g : ℕ}
end GlobalTheory.ThetaLarge


