-- Prove2me | Definitions.Def_OAIQ5Hy000
-- name    : OAIQ5Hy000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T01:40:53.87934+00:00
-- url     : https://prove2.me/theorems/98dc9abf-0994-4d94-be2b-6a0a8185cf1d
-- title:
--   Definitions bundle OAIQ5Hy000 of the split of OpenAI, Backward intertwiners and a transitive commutant
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Hyperinvariant.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Backward intertwiners and a transitive commutant*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.Hyperinvariant.MainClaim`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Hyperinvariant_Specification`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Hyperinvariant/Specification.lean).
--
--   **Imports.** It imports the published bundle `Def_HyperinvariantSubspaces`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ5Hy002`; the statements `OAI_FiniteFactor_sourceOmittedError_estimate`, `OAI_FiniteFactor_sourceSampling_coordinate_pair_error` and `OAI_FiniteFactor_sourceSampling_mass_limit_event`; the proofs of `OAI_FiniteFactor_sourceOmittedError_estimate`, `OAI_FiniteFactor_sourceSampling_coordinate_pair_error` and `OAI.Hyperinvariant.main_theorem`.
-- source:
--   OpenAI, Backward intertwiners and a transitive commutant, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_HyperinvariantSubspaces

section
-- module Solutions.OAIQ5_Hy.Hyperinvariant_Specification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Hyperinvariant
open Filter
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Nonzero, norm-quasinilpotent, and with no nontrivial closed hyperinvariant subspace. -/
def MainClaim : Prop :=
  ∃ T : H →L[ℂ] H, T ≠ 0 ∧
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
    TransitiveCommutant T

end Hyperinvariant

end OAI
end


