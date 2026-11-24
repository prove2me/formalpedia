-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_HighestWeightExists
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_HighestWeightExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:34.321746+00:00
-- url     : https://prove2.me/theorems/b1d7571d-067f-412a-8673-5b4a17572595
-- title:
--   Highest Weight Exists
-- statement:
--   Definitions and structural lemmas for Highest Weight Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/HighestWeightExists.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
namespace PI.FockOneDegW.HwC
def tw {p q : ℕ} : Ix p q → ℚ
  | .inl i => -((i : ℕ) : ℚ)
  | .inr j => -((j : ℕ) : ℚ)
def fw {p q : ℕ} (ν : Ix p q → ℚ) : ℚ := ∑ c, tw c * ν c
end PI.FockOneDegW.HwC
namespace PI.FockOneDegW
open HwC
end PI.FockOneDegW


