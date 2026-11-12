-- Prove2me | Definitions.Def_OAIQ257X002
-- name    : OAIQ257X002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:30:26.091862+00:00
-- url     : https://prove2.me/theorems/e386d24a-c490-4e79-93ee-063eebeaea26
-- title:
--   Definitions bundle OAIQ257X002 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.AtomicTriangular.Construction.Ckernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ257X006`; the statements `OAI.AtomicTriangular.Construction.Ckernel_bound_x` and `OAI.AtomicTriangular.Construction.Ckernel_summable_x`; the proofs of `OAI.AtomicTriangular.Construction.Ckernel_bound_x` and `OAI.AtomicTriangular.Construction.Ckernel_summable_x`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
def Ckernel (p : TailNode × Fin 2) (i : Fin 20) : ℝ :=
  jet H h p.1.val.val p.2 (finiteColumn ⟨i.val+2,by omega⟩)
end AtomicTriangular.Construction
end

end OAI
end


