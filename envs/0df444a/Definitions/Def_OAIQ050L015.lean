-- Prove2me | Definitions.Def_OAIQ050L015
-- name    : OAIQ050L015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:09:56.557288+00:00
-- url     : https://prove2.me/theorems/3aad5f8f-79cc-4bb3-9456-d21e957e8775
-- title:
--   Definitions bundle OAIQ050L015 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.Laughlin.Spin.relativeHighest`, `OAI.Laughlin.Spin.relativeHighestNorm`, `OAI.Laughlin.normalizedPairState`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_Pair_NormalizedLadder`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/NormalizedLadder.lean), [`Laughlin_Spin_RelativeHighest`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/RelativeHighest.lean).
--
--   **Imports.** It imports the bundles `OAIQ050L006`, `OAIQ050L008` and `OAIQ050L009` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_Laughlin_Spin_pairTensorLower_weight`, `OAI.Laughlin.Spin.pairTensorLower_weight_s50`, `OAI_Laughlin_Spin_relativeHighestNorm_tendsto`, `OAI.Laughlin.Spin.relativeHighestNorm_tendsto_s50`, `OAI_Laughlin_Spin_relativeHighest_tendsto`, `OAI.Laughlin.Spin.relativeHighest_tendsto_s50`, `OAI_Laughlin_normalizedPairState_lowering` and `OAI.Laughlin.normalizedPairState_lowering_s50`; the proofs of `OAI_Laughlin_Rotation_physicalPairInclusion_SU2`, `OAI.Laughlin.Rotation.physicalPairInclusion_SU2_s50`, `OAI_Laughlin_Spin_pairCoefficient_tensor_lowering`, `OAI.Laughlin.Spin.pairCoefficient_tensor_lowering_s50`, `OAI_Laughlin_Spin_pairCoefficient_tensor_raising`, `OAI.Laughlin.Spin.pairCoefficient_tensor_raising_s50`, `OAI_Laughlin_Spin_pairInclusion_raising`, `OAI.Laughlin.Spin.pairInclusion_raising_s50`, `OAI_Laughlin_Spin_pairTensorLower_weight`, `OAI.Laughlin.Spin.pairTensorLower_weight_s50`, `OAI_Laughlin_Spin_relativeHighestNorm_tendsto`, `OAI.Laughlin.Spin.relativeHighestNorm_tendsto_s50`, `OAI_Laughlin_Spin_relativeHighest_tendsto`, `OAI.Laughlin.Spin.relativeHighest_tendsto_s50`, `OAI_Laughlin_Spin_source_highest_coupling_tendsto`, `OAI.Laughlin.Spin.source_highest_coupling_tendsto_s50`, `OAI_Laughlin_Spin_tripleInclusion_transpose_raising`, `OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50`, `OAI_Laughlin_normalizedPairState_lowering` and `OAI.Laughlin.normalizedPairState_lowering_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L008
import Definitions.Def_OAIQ050L009

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_NormalizedLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

noncomputable def normalizedPairState (Q p i j : ℕ) : ℝ :=
  rawPairState Q p i j / pairNormalization Q p

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_RelativeHighest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def relativeHighest (A B z p : ℕ) : ℝ :=
  highestRaw A B z p / highestRaw A B z 0

noncomputable def relativeHighestNorm (A B z : ℕ) : ℝ :=
  Real.sqrt (∑ p ∈ Finset.range (z+1), (relativeHighest A B z p)^2)

end Laughlin.Spin

end OAI
end


