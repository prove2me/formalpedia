-- Prove2me | Definitions.Def_OAIQ250T109
-- name    : OAIQ250T109
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:13:10.286338+00:00
-- url     : https://prove2.me/theorems/eac478ec-97d1-4592-b92e-0523bbe9a90b
-- title:
--   Definitions bundle OAIQ250T109 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 176 declarations of OpenAI's Lean: 176 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs01.lean), [`Triangular_Signs_Signs02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs02.lean), [`Triangular_Signs_Signs03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs03.lean), [`Triangular_Signs_Signs04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs04.lean), [`Triangular_Signs_Signs05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs05.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T059` and `OAIQ250T091` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T143`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T059
import Definitions.Def_OAIQ250T091

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs0_1_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 0 r = bs0_1_0_0 r := by
  revert r
  decide +kernel
lemma bs0_1_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 1 r = bs0_1_0_1 r := by
  revert r
  decide +kernel
lemma bs0_1_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 2 r = bs0_1_0_2 r := by
  revert r
  decide +kernel
lemma bs0_1_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 3 r = bs0_1_0_3 r := by
  revert r
  decide +kernel
lemma bs0_1_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 4 r = bs0_1_0_4 r := by
  revert r
  decide +kernel
lemma bs0_1_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 5 r = bs0_1_0_5 r := by
  revert r
  decide +kernel
lemma bs0_1_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 6 r = bs0_1_0_6 r := by
  revert r
  decide +kernel
lemma bs0_1_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 7 r = bs0_1_0_7 r := by
  revert r
  decide +kernel
lemma bs0_1_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 8 r = bs0_1_0_8 r := by
  revert r
  decide +kernel
lemma bs0_1_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 9 r = bs0_1_0_9 r := by
  revert r
  decide +kernel
lemma bs0_1_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 10 r = bs0_1_0_10 r := by
  revert r
  decide +kernel
lemma bs0_1_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 11 r = bs0_1_0_11 r := by
  revert r
  decide +kernel
lemma bs0_1_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 12 r = bs0_1_0_12 r := by
  revert r
  decide +kernel
lemma bs0_1_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 13 r = bs0_1_0_13 r := by
  revert r
  decide +kernel
lemma bs0_1_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 14 r = bs0_1_0_14 r := by
  revert r
  decide +kernel
lemma bs0_1_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 15 r = bs0_1_0_15 r := by
  revert r
  decide +kernel
lemma bs0_1_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 16 r = bs0_1_0_16 r := by
  revert r
  decide +kernel
lemma bs0_1_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 17 r = bs0_1_0_17 r := by
  revert r
  decide +kernel
lemma bs0_1_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 18 r = bs0_1_0_18 r := by
  revert r
  decide +kernel
lemma bs0_1_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 19 r = bs0_1_0_19 r := by
  revert r
  decide +kernel
lemma bs0_1_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_0) 20 r = bs0_1_0_20 r := by
  revert r
  decide +kernel
lemma bs0_1_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 0 r = bs0_1_1_0 r := by
  revert r
  decide +kernel
lemma bs0_1_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 1 r = bs0_1_1_1 r := by
  revert r
  decide +kernel
lemma bs0_1_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 2 r = bs0_1_1_2 r := by
  revert r
  decide +kernel
lemma bs0_1_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 3 r = bs0_1_1_3 r := by
  revert r
  decide +kernel
lemma bs0_1_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 4 r = bs0_1_1_4 r := by
  revert r
  decide +kernel
lemma bs0_1_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 5 r = bs0_1_1_5 r := by
  revert r
  decide +kernel
lemma bs0_1_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 6 r = bs0_1_1_6 r := by
  revert r
  decide +kernel
lemma bs0_1_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 7 r = bs0_1_1_7 r := by
  revert r
  decide +kernel
lemma bs0_1_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 8 r = bs0_1_1_8 r := by
  revert r
  decide +kernel
lemma bs0_1_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 9 r = bs0_1_1_9 r := by
  revert r
  decide +kernel
lemma bs0_1_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 10 r = bs0_1_1_10 r := by
  revert r
  decide +kernel
lemma bs0_1_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 11 r = bs0_1_1_11 r := by
  revert r
  decide +kernel
lemma bs0_1_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 12 r = bs0_1_1_12 r := by
  revert r
  decide +kernel
lemma bs0_1_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 13 r = bs0_1_1_13 r := by
  revert r
  decide +kernel
lemma bs0_1_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 14 r = bs0_1_1_14 r := by
  revert r
  decide +kernel
lemma bs0_1_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 15 r = bs0_1_1_15 r := by
  revert r
  decide +kernel
lemma bs0_1_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 16 r = bs0_1_1_16 r := by
  revert r
  decide +kernel
lemma bs0_1_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 17 r = bs0_1_1_17 r := by
  revert r
  decide +kernel
lemma bs0_1_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 18 r = bs0_1_1_18 r := by
  revert r
  decide +kernel
lemma bs0_1_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 19 r = bs0_1_1_19 r := by
  revert r
  decide +kernel
lemma bs0_1_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 1 tr0_1_1) 20 r = bs0_1_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs0_2_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 0 r = bs0_2_0_0 r := by
  revert r
  decide +kernel
lemma bs0_2_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 1 r = bs0_2_0_1 r := by
  revert r
  decide +kernel
lemma bs0_2_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 2 r = bs0_2_0_2 r := by
  revert r
  decide +kernel
lemma bs0_2_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 3 r = bs0_2_0_3 r := by
  revert r
  decide +kernel
lemma bs0_2_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 4 r = bs0_2_0_4 r := by
  revert r
  decide +kernel
lemma bs0_2_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 5 r = bs0_2_0_5 r := by
  revert r
  decide +kernel
lemma bs0_2_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 6 r = bs0_2_0_6 r := by
  revert r
  decide +kernel
lemma bs0_2_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 7 r = bs0_2_0_7 r := by
  revert r
  decide +kernel
lemma bs0_2_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 8 r = bs0_2_0_8 r := by
  revert r
  decide +kernel
lemma bs0_2_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 9 r = bs0_2_0_9 r := by
  revert r
  decide +kernel
lemma bs0_2_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 10 r = bs0_2_0_10 r := by
  revert r
  decide +kernel
lemma bs0_2_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 11 r = bs0_2_0_11 r := by
  revert r
  decide +kernel
lemma bs0_2_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 12 r = bs0_2_0_12 r := by
  revert r
  decide +kernel
lemma bs0_2_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 13 r = bs0_2_0_13 r := by
  revert r
  decide +kernel
lemma bs0_2_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 14 r = bs0_2_0_14 r := by
  revert r
  decide +kernel
lemma bs0_2_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 15 r = bs0_2_0_15 r := by
  revert r
  decide +kernel
lemma bs0_2_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 16 r = bs0_2_0_16 r := by
  revert r
  decide +kernel
lemma bs0_2_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 17 r = bs0_2_0_17 r := by
  revert r
  decide +kernel
lemma bs0_2_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 18 r = bs0_2_0_18 r := by
  revert r
  decide +kernel
lemma bs0_2_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 19 r = bs0_2_0_19 r := by
  revert r
  decide +kernel
lemma bs0_2_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_0) 20 r = bs0_2_0_20 r := by
  revert r
  decide +kernel
lemma bs0_2_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 0 r = bs0_2_1_0 r := by
  revert r
  decide +kernel
lemma bs0_2_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 1 r = bs0_2_1_1 r := by
  revert r
  decide +kernel
lemma bs0_2_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 2 r = bs0_2_1_2 r := by
  revert r
  decide +kernel
lemma bs0_2_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 3 r = bs0_2_1_3 r := by
  revert r
  decide +kernel
lemma bs0_2_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 4 r = bs0_2_1_4 r := by
  revert r
  decide +kernel
lemma bs0_2_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 5 r = bs0_2_1_5 r := by
  revert r
  decide +kernel
lemma bs0_2_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 6 r = bs0_2_1_6 r := by
  revert r
  decide +kernel
lemma bs0_2_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 7 r = bs0_2_1_7 r := by
  revert r
  decide +kernel
lemma bs0_2_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 8 r = bs0_2_1_8 r := by
  revert r
  decide +kernel
lemma bs0_2_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 9 r = bs0_2_1_9 r := by
  revert r
  decide +kernel
lemma bs0_2_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 10 r = bs0_2_1_10 r := by
  revert r
  decide +kernel
lemma bs0_2_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 11 r = bs0_2_1_11 r := by
  revert r
  decide +kernel
lemma bs0_2_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 12 r = bs0_2_1_12 r := by
  revert r
  decide +kernel
lemma bs0_2_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 13 r = bs0_2_1_13 r := by
  revert r
  decide +kernel
lemma bs0_2_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 14 r = bs0_2_1_14 r := by
  revert r
  decide +kernel
lemma bs0_2_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 15 r = bs0_2_1_15 r := by
  revert r
  decide +kernel
lemma bs0_2_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 16 r = bs0_2_1_16 r := by
  revert r
  decide +kernel
lemma bs0_2_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 17 r = bs0_2_1_17 r := by
  revert r
  decide +kernel
lemma bs0_2_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 18 r = bs0_2_1_18 r := by
  revert r
  decide +kernel
lemma bs0_2_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 19 r = bs0_2_1_19 r := by
  revert r
  decide +kernel
lemma bs0_2_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 2 tr0_2_1) 20 r = bs0_2_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs0_3_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 0 r = bs0_3_0_0 r := by
  revert r
  decide +kernel
lemma bs0_3_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 1 r = bs0_3_0_1 r := by
  revert r
  decide +kernel
lemma bs0_3_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 2 r = bs0_3_0_2 r := by
  revert r
  decide +kernel
lemma bs0_3_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 3 r = bs0_3_0_3 r := by
  revert r
  decide +kernel
lemma bs0_3_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 4 r = bs0_3_0_4 r := by
  revert r
  decide +kernel
lemma bs0_3_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 5 r = bs0_3_0_5 r := by
  revert r
  decide +kernel
lemma bs0_3_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 6 r = bs0_3_0_6 r := by
  revert r
  decide +kernel
lemma bs0_3_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 7 r = bs0_3_0_7 r := by
  revert r
  decide +kernel
lemma bs0_3_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 8 r = bs0_3_0_8 r := by
  revert r
  decide +kernel
lemma bs0_3_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 9 r = bs0_3_0_9 r := by
  revert r
  decide +kernel
lemma bs0_3_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 10 r = bs0_3_0_10 r := by
  revert r
  decide +kernel
lemma bs0_3_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 11 r = bs0_3_0_11 r := by
  revert r
  decide +kernel
lemma bs0_3_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 12 r = bs0_3_0_12 r := by
  revert r
  decide +kernel
lemma bs0_3_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 13 r = bs0_3_0_13 r := by
  revert r
  decide +kernel
lemma bs0_3_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 14 r = bs0_3_0_14 r := by
  revert r
  decide +kernel
lemma bs0_3_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 15 r = bs0_3_0_15 r := by
  revert r
  decide +kernel
lemma bs0_3_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 16 r = bs0_3_0_16 r := by
  revert r
  decide +kernel
lemma bs0_3_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 17 r = bs0_3_0_17 r := by
  revert r
  decide +kernel
lemma bs0_3_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 18 r = bs0_3_0_18 r := by
  revert r
  decide +kernel
lemma bs0_3_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 19 r = bs0_3_0_19 r := by
  revert r
  decide +kernel
lemma bs0_3_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_0) 20 r = bs0_3_0_20 r := by
  revert r
  decide +kernel
lemma bs0_3_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 0 r = bs0_3_1_0 r := by
  revert r
  decide +kernel
lemma bs0_3_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 1 r = bs0_3_1_1 r := by
  revert r
  decide +kernel
lemma bs0_3_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 2 r = bs0_3_1_2 r := by
  revert r
  decide +kernel
lemma bs0_3_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 3 r = bs0_3_1_3 r := by
  revert r
  decide +kernel
lemma bs0_3_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 4 r = bs0_3_1_4 r := by
  revert r
  decide +kernel
lemma bs0_3_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 5 r = bs0_3_1_5 r := by
  revert r
  decide +kernel
lemma bs0_3_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 6 r = bs0_3_1_6 r := by
  revert r
  decide +kernel
lemma bs0_3_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 7 r = bs0_3_1_7 r := by
  revert r
  decide +kernel
lemma bs0_3_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 8 r = bs0_3_1_8 r := by
  revert r
  decide +kernel
lemma bs0_3_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 9 r = bs0_3_1_9 r := by
  revert r
  decide +kernel
lemma bs0_3_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 10 r = bs0_3_1_10 r := by
  revert r
  decide +kernel
lemma bs0_3_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 11 r = bs0_3_1_11 r := by
  revert r
  decide +kernel
lemma bs0_3_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 12 r = bs0_3_1_12 r := by
  revert r
  decide +kernel
lemma bs0_3_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 13 r = bs0_3_1_13 r := by
  revert r
  decide +kernel
lemma bs0_3_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 14 r = bs0_3_1_14 r := by
  revert r
  decide +kernel
lemma bs0_3_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 15 r = bs0_3_1_15 r := by
  revert r
  decide +kernel
lemma bs0_3_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 16 r = bs0_3_1_16 r := by
  revert r
  decide +kernel
lemma bs0_3_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 17 r = bs0_3_1_17 r := by
  revert r
  decide +kernel
lemma bs0_3_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 18 r = bs0_3_1_18 r := by
  revert r
  decide +kernel
lemma bs0_3_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 19 r = bs0_3_1_19 r := by
  revert r
  decide +kernel
lemma bs0_3_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 3 tr0_3_1) 20 r = bs0_3_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs0_4_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 0 r = bs0_4_0_0 r := by
  revert r
  decide +kernel
lemma bs0_4_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 1 r = bs0_4_0_1 r := by
  revert r
  decide +kernel
lemma bs0_4_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 2 r = bs0_4_0_2 r := by
  revert r
  decide +kernel
lemma bs0_4_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 3 r = bs0_4_0_3 r := by
  revert r
  decide +kernel
lemma bs0_4_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 4 r = bs0_4_0_4 r := by
  revert r
  decide +kernel
lemma bs0_4_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 5 r = bs0_4_0_5 r := by
  revert r
  decide +kernel
lemma bs0_4_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 6 r = bs0_4_0_6 r := by
  revert r
  decide +kernel
lemma bs0_4_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 7 r = bs0_4_0_7 r := by
  revert r
  decide +kernel
lemma bs0_4_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 8 r = bs0_4_0_8 r := by
  revert r
  decide +kernel
lemma bs0_4_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 9 r = bs0_4_0_9 r := by
  revert r
  decide +kernel
lemma bs0_4_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 10 r = bs0_4_0_10 r := by
  revert r
  decide +kernel
lemma bs0_4_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 11 r = bs0_4_0_11 r := by
  revert r
  decide +kernel
lemma bs0_4_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 12 r = bs0_4_0_12 r := by
  revert r
  decide +kernel
lemma bs0_4_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 13 r = bs0_4_0_13 r := by
  revert r
  decide +kernel
lemma bs0_4_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 14 r = bs0_4_0_14 r := by
  revert r
  decide +kernel
lemma bs0_4_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 15 r = bs0_4_0_15 r := by
  revert r
  decide +kernel
lemma bs0_4_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 16 r = bs0_4_0_16 r := by
  revert r
  decide +kernel
lemma bs0_4_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 17 r = bs0_4_0_17 r := by
  revert r
  decide +kernel
lemma bs0_4_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 18 r = bs0_4_0_18 r := by
  revert r
  decide +kernel
lemma bs0_4_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 19 r = bs0_4_0_19 r := by
  revert r
  decide +kernel
lemma bs0_4_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_0) 20 r = bs0_4_0_20 r := by
  revert r
  decide +kernel
lemma bs0_4_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 0 r = bs0_4_1_0 r := by
  revert r
  decide +kernel
lemma bs0_4_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 1 r = bs0_4_1_1 r := by
  revert r
  decide +kernel
lemma bs0_4_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 2 r = bs0_4_1_2 r := by
  revert r
  decide +kernel
lemma bs0_4_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 3 r = bs0_4_1_3 r := by
  revert r
  decide +kernel
lemma bs0_4_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 4 r = bs0_4_1_4 r := by
  revert r
  decide +kernel
lemma bs0_4_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 5 r = bs0_4_1_5 r := by
  revert r
  decide +kernel
lemma bs0_4_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 6 r = bs0_4_1_6 r := by
  revert r
  decide +kernel
lemma bs0_4_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 7 r = bs0_4_1_7 r := by
  revert r
  decide +kernel
lemma bs0_4_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 8 r = bs0_4_1_8 r := by
  revert r
  decide +kernel
lemma bs0_4_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 9 r = bs0_4_1_9 r := by
  revert r
  decide +kernel
lemma bs0_4_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 10 r = bs0_4_1_10 r := by
  revert r
  decide +kernel
lemma bs0_4_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 11 r = bs0_4_1_11 r := by
  revert r
  decide +kernel
lemma bs0_4_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 12 r = bs0_4_1_12 r := by
  revert r
  decide +kernel
lemma bs0_4_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 13 r = bs0_4_1_13 r := by
  revert r
  decide +kernel
lemma bs0_4_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 14 r = bs0_4_1_14 r := by
  revert r
  decide +kernel
lemma bs0_4_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 15 r = bs0_4_1_15 r := by
  revert r
  decide +kernel
lemma bs0_4_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 16 r = bs0_4_1_16 r := by
  revert r
  decide +kernel
lemma bs0_4_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 17 r = bs0_4_1_17 r := by
  revert r
  decide +kernel
lemma bs0_4_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 18 r = bs0_4_1_18 r := by
  revert r
  decide +kernel
lemma bs0_4_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 19 r = bs0_4_1_19 r := by
  revert r
  decide +kernel
lemma bs0_4_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 4 tr0_4_1) 20 r = bs0_4_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs0_5_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 5 tr0_5_0) 0 r = bs0_5_0_0 r := by
  revert r
  decide +kernel
lemma bs0_5_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 5 tr0_5_0) 10 r = bs0_5_0_10 r := by
  revert r
  decide +kernel
lemma bs0_5_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 5 tr0_5_0) 11 r = bs0_5_0_11 r := by
  revert r
  decide +kernel
lemma bs0_5_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 5 tr0_5_0) 12 r = bs0_5_0_12 r := by
  revert r
  decide +kernel
lemma bs0_5_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 5 tr0_5_0) 13 r = bs0_5_0_13 r := by
  revert r
  decide +kernel
lemma bs0_5_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 5 tr0_5_0) 14 r = bs0_5_0_14 r := by
  revert r
  decide +kernel
lemma bs0_5_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 5 tr0_5_0) 15 r = bs0_5_0_15 r := by
  revert r
  decide +kernel
lemma bs0_5_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 5 tr0_5_0) 16 r = bs0_5_0_16 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


