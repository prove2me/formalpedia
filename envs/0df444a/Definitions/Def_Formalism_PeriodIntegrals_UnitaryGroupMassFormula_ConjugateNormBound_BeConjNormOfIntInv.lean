-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_BeConjNormOfIntInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_BeConjNormOfIntInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:25.06238+00:00
-- url     : https://prove2.me/theorems/73e69929-a5b0-4906-9a06-51d8e8c43e7a
-- title:
--   Be Conj Norm Of Int Inv
-- statement:
--   Definitions and structural lemmas for Be Conj Norm Of Int Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/BeConjNormOfIntInv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BeConjNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.BeConjNormW
open PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
variable {p : ℕ} [Fact p.Prime]
end PI.BeConjNormW


