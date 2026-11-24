-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:28.559588+00:00
-- url     : https://prove2.me/theorems/cd8bed38-6d8d-4dce-936f-5f7596289c32
-- title:
--   Exist HW
-- statement:
--   Definitions and structural lemmas for Exist HW, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
namespace PI.FJMX
variable {p q r s : ℕ}
def der1 (a b : Ix p q) : Derivation ℂ (Pol p q r s) (Pol p q r s) :=
  ∑ c : Ix r s, if linePos (a, c) = true then (X (a, c) : Pol p q r s) • pderiv (b, c)
    else -((X (b, c) : Pol p q r s) • pderiv (a, c))
def der2 (c d : Ix r s) : Derivation ℂ (Pol p q r s) (Pol p q r s) :=
  ∑ a : Ix p q, if linePos (a, c) = true then (X (a, c) : Pol p q r s) • pderiv (a, d)
    else -((X (a, d) : Pol p q r s) • pderiv (a, c))
section Kill
variable {m k : ℕ}
end Kill
end PI.FJMX


