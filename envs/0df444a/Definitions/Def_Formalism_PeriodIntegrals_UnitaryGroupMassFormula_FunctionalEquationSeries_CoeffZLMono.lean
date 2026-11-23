-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FunctionalEquationSeries_CoeffZLMono
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FunctionalEquationSeries_CoeffZLMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:00.219058+00:00
-- url     : https://prove2.me/theorems/938873c2-f683-417b-aac5-45b4adaa5206
-- title:
--   Coeff ZLMono
-- statement:
--   Definitions and structural lemmas for Coeff ZLMono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FunctionalEquationSeries/CoeffZLMono.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FunctionalEquationSeries_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace PI.FunEqAllProof
open PI.FunEqAll
section
variable (l d : ℕ) [Fact l.Prime]
def mono (s : ZMod d) (e : ℕ) : ZMod d × Unit →₀ ℕ :=
  Finsupp.single (s - 2 * (e : ZMod d), ()) ((l ^ 2) ^ e)
end
end PI.FunEqAllProof


