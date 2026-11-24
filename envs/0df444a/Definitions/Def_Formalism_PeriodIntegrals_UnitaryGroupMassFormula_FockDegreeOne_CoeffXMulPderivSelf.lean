-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:15.400062+00:00
-- url     : https://prove2.me/theorems/25c71e84-9e15-4d01-a84d-a087c1be2bef
-- title:
--   Coeff XMul Pderiv Self
-- statement:
--   Definitions and structural lemmas for Coeff XMul Pderiv Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/CoeffXMulPderivSelf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
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
def sgnL {p q r s : ℕ} (l : Ln p q r s) : ℚ := if linePos l = true then 1 else -1
def wtv {p q r s : ℕ} (β : Ln p q r s →₀ ℕ) (c : Ix p q) : ℚ :=
  ∑ d : Ix r s, sgnL ((c, d) : Ln p q r s) * (β (c, d) : ℚ) + kShift r s c
def IsWt {p q r s : ℕ} (ν : Ix p q → ℚ) (P : Pol p q r s) : Prop :=
  ∀ β ∈ P.support, ∀ c, wtv β c = ν c
end PI.FockOneDegW.HwC


