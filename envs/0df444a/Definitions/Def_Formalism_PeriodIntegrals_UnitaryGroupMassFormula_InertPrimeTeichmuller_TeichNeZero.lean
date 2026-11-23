-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_TeichNeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_TeichNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:37.776336+00:00
-- url     : https://prove2.me/theorems/107387b0-322d-47c8-9482-03d898eeb23d
-- title:
--   Teich Ne Zero
-- statement:
--   Definitions and structural lemmas for Teich Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/TeichNeZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
namespace PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
variable (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b)
include hq
end PI.OkpW


