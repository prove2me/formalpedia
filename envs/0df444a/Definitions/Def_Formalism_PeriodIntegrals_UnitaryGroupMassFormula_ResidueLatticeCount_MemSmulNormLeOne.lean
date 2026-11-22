-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_MemSmulNormLeOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_MemSmulNormLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:13.736151+00:00
-- url     : https://prove2.me/theorems/753235be-f825-4535-ae69-22f343808621
-- title:
--   Mem Smul Norm Le One
-- statement:
--   Definitions and structural lemmas for Mem Smul Norm Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/MemSmulNormLeOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped ENNReal Classical Pointwise
noncomputable section
namespace PI.Residue
variable (K : Type) [Field K] [NumberField K]
def cHalf : ℝ := (1 / 2 : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ K)
end PI.Residue


