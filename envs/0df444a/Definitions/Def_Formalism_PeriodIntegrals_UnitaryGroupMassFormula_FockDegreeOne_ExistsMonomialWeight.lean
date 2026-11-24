-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:32.311811+00:00
-- url     : https://prove2.me/theorems/441d707b-32ad-4182-a2eb-bfa7fe2605ca
-- title:
--   Exists Monomial Weight
-- statement:
--   Definitions and structural lemmas for Exists Monomial Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
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
namespace PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
def gg (v : Pol p q r s) (a : Ix p q) (c d : Ix r s) : Pol p q r s :=
  if (¬ sameBlock c d) ∧ linePos ((a, d) : Ln p q r s) = true then
    pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) v) else 0
def SS (v : Pol p q r s) (a b : Ix p q) : ℂ :=
  ∑ c : Ix r s, ∑ d : Ix r s, fockInner (gg v a c d) (gg v b c d)
end PI.FockOneDegW.Core


