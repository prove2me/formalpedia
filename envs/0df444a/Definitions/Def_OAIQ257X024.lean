-- Prove2me | Definitions.Def_OAIQ257X024
-- name    : OAIQ257X024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T04:11:20.29192+00:00
-- url     : https://prove2.me/theorems/8b855a79-84fe-478c-8e95-8dbec9fc260c
-- title:
--   Definitions bundle OAIQ257X024 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.targetEnvTablet`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean).
--
--   **Imports.** It imports the bundles `OAIQ257X011` and `OAIQ257X019` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.AtomicTriangular.Construction.actualFiniteError_norm_x` and `OAI.AtomicTriangular.Construction.actualTail_norm_x`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X019

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_TargetInterval
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


