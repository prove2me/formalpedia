-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:39.84+00:00
-- url     : https://prove2.me/theorems/7f81ff3e-0935-49bf-93b7-1725c3c8d4de
-- title:
--   Min Deg
-- statement:
--   Definitions and structural lemmas for Min Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MinDeg.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
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
namespace PI.FJMF
def HwHarmDeg2 : Prop := ∀ p q r s : ℕ, ∀ (μ : Ix r s → ℚ) (e : ℕ) (v : Pol p q r s),
  v ∈ homog (Ix p q × Ix r s) e → IsHW (fockAct2 p q r s) μ v →
    (∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) v = 0) →
    (e : ℚ) = degW (cPair p q) μ
section Grade
variable {σ : Type*}
end Grade
section Ops
variable {p q r s : ℕ}
end Ops
end PI.FJMF


