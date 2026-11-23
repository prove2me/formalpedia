-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensityProductAddTwoSuccSucc
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensityProductAddTwoSuccSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:19:55.480177+00:00
-- url     : https://prove2.me/theorems/5389c660-da08-4c9c-837a-2e8af1d47f52
-- title:
--   Density Product Add Two Succ Succ
-- statement:
--   Definitions and structural lemmas for Density Product Add Two Succ Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensExactInertOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace DensInertW
def arF (q i : ℕ) : ℝ := 1 - (-1 : ℝ) ^ i * ((q : ℝ) ^ i)⁻¹
end DensInertW


