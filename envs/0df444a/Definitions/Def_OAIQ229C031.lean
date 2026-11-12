-- Prove2me | Definitions.Def_OAIQ229C031
-- name    : OAIQ229C031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T12:11:51.650524+00:00
-- url     : https://prove2.me/theorems/90df5565-402d-421d-b232-0f914cbfe4c2
-- title:
--   Definitions bundle OAIQ229C031 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.NuclearUltrapower.SOS.residual`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `NuclearUltrapower_SOSSemantics`.
--
--   **Imports.** It imports the bundle `OAIQ229C027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C032` and `OAIQ229C033`; the statements `OAI.NuclearUltrapower.SOS.residual_augmentation_ca`, `OAI.NuclearUltrapower.SOS.residual_eval_ca` and `OAI.NuclearUltrapower.SOS.residual_l1_ca`; the proofs of `OAI_NuclearUltrapower_SOS_delta_good`, `OAI.NuclearUltrapower.SOS.residual_augmentation_ca`, `OAI.NuclearUltrapower.SOS.residual_eval_ca`, `OAI.NuclearUltrapower.SOS.residual_l1_ca`, `OAI.NuclearUltrapower.SOS.row_length_bound_ca`, `OAI.NuclearUltrapower.SOS.row_lengths_ca` and `OAI.NuclearUltrapower.SOS.row_normalizations_ca`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ229C027

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {A : Type*} [AddCommGroup A]

def residual : Poly Mat3 := [residualBucket 0, residualBucket 1, residualBucket 2, residualBucket 3, residualBucket 4, residualBucket 5, residualBucket 6, residualBucket 7, residualBucket 8, residualBucket 9, residualBucket 10, residualBucket 11, residualBucket 12, residualBucket 13, residualBucket 14, residualBucket 15, residualBucket 16, residualBucket 17, residualBucket 18, residualBucket 19, residualBucket 20, residualBucket 21, residualBucket 22, residualBucket 23, residualBucket 24, residualBucket 25, residualBucket 26, residualBucket 27, residualBucket 28, residualBucket 29, residualBucket 30, residualBucket 31, residualBucket 32, residualBucket 33, residualBucket 34, residualBucket 35, residualBucket 36, residualBucket 37, residualBucket 38, residualBucket 39, residualBucket 40, residualBucket 41, residualBucket 42, residualBucket 43, residualBucket 44, residualBucket 45, residualBucket 46, residualBucket 47, residualBucket 48, residualBucket 49, residualBucket 50, residualBucket 51, residualBucket 52, residualBucket 53, residualBucket 54, residualBucket 55, residualBucket 56, residualBucket 57, residualBucket 58, residualBucket 59, residualBucket 60, residualBucket 61, residualBucket 62, residualBucket 63, residualBucket 64, residualBucket 65, residualBucket 66, residualBucket 67, residualBucket 68, residualBucket 69, residualBucket 70, residualBucket 71, residualBucket 72, residualBucket 73, residualBucket 74, residualBucket 75, residualBucket 76, residualBucket 77, residualBucket 78, residualBucket 79, residualBucket 80, residualBucket 81, residualBucket 82, residualBucket 83, residualBucket 84, residualBucket 85, residualBucket 86, residualBucket 87, residualBucket 88, residualBucket 89, residualBucket 90, residualBucket 91, residualBucket 92, residualBucket 93, residualBucket 94, residualBucket 95, residualBucket 96, residualBucket 97, residualBucket 98, residualBucket 99, residualBucket 100, residualBucket 101, residualBucket 102, residualBucket 103, residualBucket 104, residualBucket 105, residualBucket 106, residualBucket 107, residualBucket 108, residualBucket 109, residualBucket 110, residualBucket 111, residualBucket 112, residualBucket 113, residualBucket 114, residualBucket 115, residualBucket 116, residualBucket 117, residualBucket 118, residualBucket 119, residualBucket 120, residualBucket 121, residualBucket 122, residualBucket 123, residualBucket 124, residualBucket 125, residualBucket 126, residualBucket 127].flatten

end NuclearUltrapower.SOS
end

end OAI
end


