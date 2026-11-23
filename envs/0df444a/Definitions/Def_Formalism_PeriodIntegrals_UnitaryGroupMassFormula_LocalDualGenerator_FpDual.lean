-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:44.643683+00:00
-- url     : https://prove2.me/theorems/26509aaa-424f-4254-8eda-e473b1b67134
-- title:
--   Fp Dual
-- statement:
--   Definitions and structural lemmas for Fp Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/FpDual.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel
namespace PI.LocDualGen.FpD
open PI.LocDualGen.W
section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
def P (x : K) : Prop := ∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * (b : K))‖ ≤ 1
end
end PI.LocDualGen.FpD


