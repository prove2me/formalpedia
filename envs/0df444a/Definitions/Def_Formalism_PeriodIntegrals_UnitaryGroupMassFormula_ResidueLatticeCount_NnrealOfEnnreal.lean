-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NnrealOfEnnreal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NnrealOfEnnreal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:49.709724+00:00
-- url     : https://prove2.me/theorems/1455e660-2f94-4d88-a1e1-9abb4ae72448
-- title:
--   Nnreal Of Ennreal
-- statement:
--   Definitions and structural lemmas for Nnreal Of Ennreal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NnrealOfEnnreal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.Residue
open NumberField
open scoped ENNReal NNReal
noncomputable def wt (s : ℝ) : ℕ →* ℝ≥0∞ where
  toFun n := (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞)
  map_one' := by simp
  map_mul' a b := by
    rw [Nat.cast_mul, NNReal.mul_rpow, ENNReal.coe_mul]
end PI.Residue


