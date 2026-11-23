-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:58.155837+00:00
-- url     : https://prove2.me/theorems/9d6b177e-eebf-40f2-ba7a-d7f5e3111e83
-- title:
--   Norm Log Deriv Refl Le
-- statement:
--   Definitions and structural lemmas for Norm Log Deriv Refl Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean

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
namespace PI.EF.Loc
open Complex Metric Set Filter Topology ComplexConjugate
def refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ := ((R : ℂ) ^ 2 - conj (ρ - s₀) * (z - s₀)) / R
end PI.EF.Loc


