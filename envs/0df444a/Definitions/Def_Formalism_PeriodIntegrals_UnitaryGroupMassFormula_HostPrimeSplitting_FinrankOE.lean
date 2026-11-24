-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:46.894837+00:00
-- url     : https://prove2.me/theorems/f1c8b309-e4f7-4d33-92e2-aa76e2b2dc96
-- title:
--   Finrank OE
-- statement:
--   Definitions and structural lemmas for Finrank OE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HostPrimeSplitting/FinrankOE.lean

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open scoped Pointwise
namespace PI.UnitaryGroupMassFormula.HostPrimeFacts
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
abbrev cj : H.E ≃ₐ[ℚ] H.E := H.conj
end PI.UnitaryGroupMassFormula.HostPrimeFacts


