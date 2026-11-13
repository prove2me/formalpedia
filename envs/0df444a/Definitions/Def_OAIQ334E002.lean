-- Prove2me | Definitions.Def_OAIQ334E002
-- name    : OAIQ334E002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T11:39:23.023194+00:00
-- url     : https://prove2.me/theorems/c53cc6d7-2dd2-4ca3-8557-c30dd70570d5
-- title:
--   Definitions bundle OAIQ334E002 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.AtomicTriangular.Construction.Ckernel`, `OAI.AtomicTriangular.Construction.jet`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Basic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Basic.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean).
--
--   **Imports.** It imports the bundle `OAIQ334E000` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ334E006`; the statements `OAI.AtomicTriangular.Construction.Ckernel_bound_eu`, `OAI.AtomicTriangular.Construction.Ckernel_summable_eu`, `OAI.AtomicTriangular.Construction.tail_atom_column_bounds_eu` and `OAI.AtomicTriangular.Construction.tail_finite_column_bound_eu`; the proofs of `OAI.AtomicTriangular.Construction.Ckernel_bound_eu`, `OAI.AtomicTriangular.Construction.Ckernel_summable_eu`, `OAI.AtomicTriangular.Construction.tail_atom_column_bounds_eu` and `OAI.AtomicTriangular.Construction.tail_finite_column_bound_eu`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ334E000

section
-- module Solutions.OAIQ334_EU.Triangular_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex Polynomial

namespace AtomicTriangular.Construction

def jet (k v : ℝ) (n : ℤ) (d : Fin 2) (S : Fin 31 → ℂ) : ℝ :=
  (∑ j : Fin 31, jetMultiplier k v n d (frequency j)*S j).re

end AtomicTriangular.Construction

end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_BlockOperators
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


