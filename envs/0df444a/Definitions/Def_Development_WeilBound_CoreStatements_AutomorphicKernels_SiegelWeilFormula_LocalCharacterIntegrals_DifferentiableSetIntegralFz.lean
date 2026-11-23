-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalCharacterIntegrals_DifferentiableSetIntegralFz
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalCharacterIntegrals_DifferentiableSetIntegralFz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:32.046536+00:00
-- url     : https://prove2.me/theorems/5c7dd839-213b-4f90-b66d-a0c586a07f1d
-- title:
--   Differentiable Set Integral Fz
-- statement:
--   Definitions and structural lemmas for Differentiable Set Integral Fz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalCharacterIntegrals/DifferentiableSetIntegralFz.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.SwLocFin
open MeasureTheory Filter Topology Set
variable {H : Type*} [MeasurableSpace H]
def fz (r : H → ℝ) (u : H → ℂ) (s₀ z : ℂ) (b : H) : ℂ := (r b : ℂ) ^ (-(z - s₀)) * u b
end PositivityTheory.SiegelWeilFormula.SwLocFin


