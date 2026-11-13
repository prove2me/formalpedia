-- Prove2me | Definitions.Def_OAIQ334E024
-- name    : OAIQ334E024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T13:01:35.856699+00:00
-- url     : https://prove2.me/theorems/c6ce11a6-13d0-4915-acd0-7e2a8d1fb8ac
-- title:
--   Definitions bundle OAIQ334E024 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.targetEnvTablet`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean).
--
--   **Imports.** It imports the bundles `OAIQ334E011` and `OAIQ334E019` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.AtomicTriangular.FiniteCertificate.tailTargetEnvelope_bound_eu`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E019

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def targetEnvTablet : Fin 15 → RI := ![targetEnvt36,targetEnvt37,targetEnvt39,targetEnvt40,targetEnvt43,targetEnvt45,targetEnvt48,targetEnvt49,targetEnvt52,targetEnvt55,targetEnvt57,targetEnvt25,targetEnvt27,targetEnvt28,targetEnvt31]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


