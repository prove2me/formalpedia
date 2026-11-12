-- Prove2me | Definitions.Def_OAIQ250T111
-- name    : OAIQ250T111
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:19:42.054249+00:00
-- url     : https://prove2.me/theorems/a7327666-e03b-458b-b7c1-5b95cc69606d
-- title:
--   Definitions bundle OAIQ250T111 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 173 declarations of OpenAI's Lean: 173 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs12.lean), [`Triangular_Signs_Signs13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs13.lean), [`Triangular_Signs_Signs14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs14.lean), [`Triangular_Signs_Signs15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs15.lean), [`Triangular_Signs_Signs16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs16.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T061`, `OAIQ250T082` and `OAIQ250T091` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T144`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T061
import Definitions.Def_OAIQ250T082
import Definitions.Def_OAIQ250T091

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_2_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 2 tr1_2_1) 5 r = bs1_2_1_5 r := by
  revert r
  decide +kernel
lemma bs1_2_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 2 tr1_2_1) 6 r = bs1_2_1_6 r := by
  revert r
  decide +kernel
lemma bs1_2_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 2 tr1_2_1) 7 r = bs1_2_1_7 r := by
  revert r
  decide +kernel
lemma bs1_2_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 2 tr1_2_1) 8 r = bs1_2_1_8 r := by
  revert r
  decide +kernel
lemma bs1_2_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 2 tr1_2_1) 9 r = bs1_2_1_9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_3_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 0 r = bs1_3_0_0 r := by
  revert r
  decide +kernel
lemma bs1_3_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 1 r = bs1_3_0_1 r := by
  revert r
  decide +kernel
lemma bs1_3_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 2 r = bs1_3_0_2 r := by
  revert r
  decide +kernel
lemma bs1_3_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 3 r = bs1_3_0_3 r := by
  revert r
  decide +kernel
lemma bs1_3_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 4 r = bs1_3_0_4 r := by
  revert r
  decide +kernel
lemma bs1_3_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 5 r = bs1_3_0_5 r := by
  revert r
  decide +kernel
lemma bs1_3_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 6 r = bs1_3_0_6 r := by
  revert r
  decide +kernel
lemma bs1_3_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 7 r = bs1_3_0_7 r := by
  revert r
  decide +kernel
lemma bs1_3_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 8 r = bs1_3_0_8 r := by
  revert r
  decide +kernel
lemma bs1_3_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 9 r = bs1_3_0_9 r := by
  revert r
  decide +kernel
lemma bs1_3_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 10 r = bs1_3_0_10 r := by
  revert r
  decide +kernel
lemma bs1_3_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 11 r = bs1_3_0_11 r := by
  revert r
  decide +kernel
lemma bs1_3_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 12 r = bs1_3_0_12 r := by
  revert r
  decide +kernel
lemma bs1_3_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 13 r = bs1_3_0_13 r := by
  revert r
  decide +kernel
lemma bs1_3_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 14 r = bs1_3_0_14 r := by
  revert r
  decide +kernel
lemma bs1_3_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 15 r = bs1_3_0_15 r := by
  revert r
  decide +kernel
lemma bs1_3_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 16 r = bs1_3_0_16 r := by
  revert r
  decide +kernel
lemma bs1_3_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 17 r = bs1_3_0_17 r := by
  revert r
  decide +kernel
lemma bs1_3_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 18 r = bs1_3_0_18 r := by
  revert r
  decide +kernel
lemma bs1_3_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 19 r = bs1_3_0_19 r := by
  revert r
  decide +kernel
lemma bs1_3_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_0) 20 r = bs1_3_0_20 r := by
  revert r
  decide +kernel
lemma bs1_3_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 0 r = bs1_3_1_0 r := by
  revert r
  decide +kernel
lemma bs1_3_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 1 r = bs1_3_1_1 r := by
  revert r
  decide +kernel
lemma bs1_3_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 2 r = bs1_3_1_2 r := by
  revert r
  decide +kernel
lemma bs1_3_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 3 r = bs1_3_1_3 r := by
  revert r
  decide +kernel
lemma bs1_3_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 4 r = bs1_3_1_4 r := by
  revert r
  decide +kernel
lemma bs1_3_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 5 r = bs1_3_1_5 r := by
  revert r
  decide +kernel
lemma bs1_3_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 6 r = bs1_3_1_6 r := by
  revert r
  decide +kernel
lemma bs1_3_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 7 r = bs1_3_1_7 r := by
  revert r
  decide +kernel
lemma bs1_3_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 8 r = bs1_3_1_8 r := by
  revert r
  decide +kernel
lemma bs1_3_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 9 r = bs1_3_1_9 r := by
  revert r
  decide +kernel
lemma bs1_3_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 10 r = bs1_3_1_10 r := by
  revert r
  decide +kernel
lemma bs1_3_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 11 r = bs1_3_1_11 r := by
  revert r
  decide +kernel
lemma bs1_3_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 12 r = bs1_3_1_12 r := by
  revert r
  decide +kernel
lemma bs1_3_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 13 r = bs1_3_1_13 r := by
  revert r
  decide +kernel
lemma bs1_3_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 14 r = bs1_3_1_14 r := by
  revert r
  decide +kernel
lemma bs1_3_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 15 r = bs1_3_1_15 r := by
  revert r
  decide +kernel
lemma bs1_3_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 16 r = bs1_3_1_16 r := by
  revert r
  decide +kernel
lemma bs1_3_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 17 r = bs1_3_1_17 r := by
  revert r
  decide +kernel
lemma bs1_3_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 18 r = bs1_3_1_18 r := by
  revert r
  decide +kernel
lemma bs1_3_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 19 r = bs1_3_1_19 r := by
  revert r
  decide +kernel
lemma bs1_3_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 3 tr1_3_1) 20 r = bs1_3_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_4_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 0 r = bs1_4_0_0 r := by
  revert r
  decide +kernel
lemma bs1_4_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 1 r = bs1_4_0_1 r := by
  revert r
  decide +kernel
lemma bs1_4_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 2 r = bs1_4_0_2 r := by
  revert r
  decide +kernel
lemma bs1_4_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 3 r = bs1_4_0_3 r := by
  revert r
  decide +kernel
lemma bs1_4_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 4 r = bs1_4_0_4 r := by
  revert r
  decide +kernel
lemma bs1_4_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 5 r = bs1_4_0_5 r := by
  revert r
  decide +kernel
lemma bs1_4_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 6 r = bs1_4_0_6 r := by
  revert r
  decide +kernel
lemma bs1_4_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 7 r = bs1_4_0_7 r := by
  revert r
  decide +kernel
lemma bs1_4_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 8 r = bs1_4_0_8 r := by
  revert r
  decide +kernel
lemma bs1_4_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 9 r = bs1_4_0_9 r := by
  revert r
  decide +kernel
lemma bs1_4_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 10 r = bs1_4_0_10 r := by
  revert r
  decide +kernel
lemma bs1_4_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 11 r = bs1_4_0_11 r := by
  revert r
  decide +kernel
lemma bs1_4_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 12 r = bs1_4_0_12 r := by
  revert r
  decide +kernel
lemma bs1_4_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 13 r = bs1_4_0_13 r := by
  revert r
  decide +kernel
lemma bs1_4_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 14 r = bs1_4_0_14 r := by
  revert r
  decide +kernel
lemma bs1_4_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 15 r = bs1_4_0_15 r := by
  revert r
  decide +kernel
lemma bs1_4_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 16 r = bs1_4_0_16 r := by
  revert r
  decide +kernel
lemma bs1_4_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 17 r = bs1_4_0_17 r := by
  revert r
  decide +kernel
lemma bs1_4_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 18 r = bs1_4_0_18 r := by
  revert r
  decide +kernel
lemma bs1_4_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 19 r = bs1_4_0_19 r := by
  revert r
  decide +kernel
lemma bs1_4_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_0) 20 r = bs1_4_0_20 r := by
  revert r
  decide +kernel
lemma bs1_4_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 0 r = bs1_4_1_0 r := by
  revert r
  decide +kernel
lemma bs1_4_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 1 r = bs1_4_1_1 r := by
  revert r
  decide +kernel
lemma bs1_4_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 2 r = bs1_4_1_2 r := by
  revert r
  decide +kernel
lemma bs1_4_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 3 r = bs1_4_1_3 r := by
  revert r
  decide +kernel
lemma bs1_4_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 4 r = bs1_4_1_4 r := by
  revert r
  decide +kernel
lemma bs1_4_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 5 r = bs1_4_1_5 r := by
  revert r
  decide +kernel
lemma bs1_4_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 6 r = bs1_4_1_6 r := by
  revert r
  decide +kernel
lemma bs1_4_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 7 r = bs1_4_1_7 r := by
  revert r
  decide +kernel
lemma bs1_4_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 8 r = bs1_4_1_8 r := by
  revert r
  decide +kernel
lemma bs1_4_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 9 r = bs1_4_1_9 r := by
  revert r
  decide +kernel
lemma bs1_4_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 10 r = bs1_4_1_10 r := by
  revert r
  decide +kernel
lemma bs1_4_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 11 r = bs1_4_1_11 r := by
  revert r
  decide +kernel
lemma bs1_4_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 12 r = bs1_4_1_12 r := by
  revert r
  decide +kernel
lemma bs1_4_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 13 r = bs1_4_1_13 r := by
  revert r
  decide +kernel
lemma bs1_4_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 14 r = bs1_4_1_14 r := by
  revert r
  decide +kernel
lemma bs1_4_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 15 r = bs1_4_1_15 r := by
  revert r
  decide +kernel
lemma bs1_4_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 16 r = bs1_4_1_16 r := by
  revert r
  decide +kernel
lemma bs1_4_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 17 r = bs1_4_1_17 r := by
  revert r
  decide +kernel
lemma bs1_4_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 18 r = bs1_4_1_18 r := by
  revert r
  decide +kernel
lemma bs1_4_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 19 r = bs1_4_1_19 r := by
  revert r
  decide +kernel
lemma bs1_4_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 4 tr1_4_1) 20 r = bs1_4_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_5_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 0 r = bs1_5_0_0 r := by
  revert r
  decide +kernel
lemma bs1_5_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 1 r = bs1_5_0_1 r := by
  revert r
  decide +kernel
lemma bs1_5_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 2 r = bs1_5_0_2 r := by
  revert r
  decide +kernel
lemma bs1_5_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 3 r = bs1_5_0_3 r := by
  revert r
  decide +kernel
lemma bs1_5_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 4 r = bs1_5_0_4 r := by
  revert r
  decide +kernel
lemma bs1_5_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 5 r = bs1_5_0_5 r := by
  revert r
  decide +kernel
lemma bs1_5_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 6 r = bs1_5_0_6 r := by
  revert r
  decide +kernel
lemma bs1_5_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 7 r = bs1_5_0_7 r := by
  revert r
  decide +kernel
lemma bs1_5_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 8 r = bs1_5_0_8 r := by
  revert r
  decide +kernel
lemma bs1_5_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 9 r = bs1_5_0_9 r := by
  revert r
  decide +kernel
lemma bs1_5_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 10 r = bs1_5_0_10 r := by
  revert r
  decide +kernel
lemma bs1_5_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 11 r = bs1_5_0_11 r := by
  revert r
  decide +kernel
lemma bs1_5_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 12 r = bs1_5_0_12 r := by
  revert r
  decide +kernel
lemma bs1_5_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 13 r = bs1_5_0_13 r := by
  revert r
  decide +kernel
lemma bs1_5_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 14 r = bs1_5_0_14 r := by
  revert r
  decide +kernel
lemma bs1_5_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 15 r = bs1_5_0_15 r := by
  revert r
  decide +kernel
lemma bs1_5_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 16 r = bs1_5_0_16 r := by
  revert r
  decide +kernel
lemma bs1_5_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 17 r = bs1_5_0_17 r := by
  revert r
  decide +kernel
lemma bs1_5_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 18 r = bs1_5_0_18 r := by
  revert r
  decide +kernel
lemma bs1_5_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 19 r = bs1_5_0_19 r := by
  revert r
  decide +kernel
lemma bs1_5_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_0) 20 r = bs1_5_0_20 r := by
  revert r
  decide +kernel
lemma bs1_5_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 0 r = bs1_5_1_0 r := by
  revert r
  decide +kernel
lemma bs1_5_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 1 r = bs1_5_1_1 r := by
  revert r
  decide +kernel
lemma bs1_5_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 2 r = bs1_5_1_2 r := by
  revert r
  decide +kernel
lemma bs1_5_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 3 r = bs1_5_1_3 r := by
  revert r
  decide +kernel
lemma bs1_5_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 4 r = bs1_5_1_4 r := by
  revert r
  decide +kernel
lemma bs1_5_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 5 r = bs1_5_1_5 r := by
  revert r
  decide +kernel
lemma bs1_5_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 6 r = bs1_5_1_6 r := by
  revert r
  decide +kernel
lemma bs1_5_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 7 r = bs1_5_1_7 r := by
  revert r
  decide +kernel
lemma bs1_5_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 8 r = bs1_5_1_8 r := by
  revert r
  decide +kernel
lemma bs1_5_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 9 r = bs1_5_1_9 r := by
  revert r
  decide +kernel
lemma bs1_5_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 10 r = bs1_5_1_10 r := by
  revert r
  decide +kernel
lemma bs1_5_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 11 r = bs1_5_1_11 r := by
  revert r
  decide +kernel
lemma bs1_5_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 12 r = bs1_5_1_12 r := by
  revert r
  decide +kernel
lemma bs1_5_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 13 r = bs1_5_1_13 r := by
  revert r
  decide +kernel
lemma bs1_5_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 14 r = bs1_5_1_14 r := by
  revert r
  decide +kernel
lemma bs1_5_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 15 r = bs1_5_1_15 r := by
  revert r
  decide +kernel
lemma bs1_5_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 16 r = bs1_5_1_16 r := by
  revert r
  decide +kernel
lemma bs1_5_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 17 r = bs1_5_1_17 r := by
  revert r
  decide +kernel
lemma bs1_5_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 18 r = bs1_5_1_18 r := by
  revert r
  decide +kernel
lemma bs1_5_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 19 r = bs1_5_1_19 r := by
  revert r
  decide +kernel
lemma bs1_5_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) 20 r = bs1_5_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_6_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 0 r = bs1_6_0_0 r := by
  revert r
  decide +kernel
lemma bs1_6_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 1 r = bs1_6_0_1 r := by
  revert r
  decide +kernel
lemma bs1_6_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 2 r = bs1_6_0_2 r := by
  revert r
  decide +kernel
lemma bs1_6_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 3 r = bs1_6_0_3 r := by
  revert r
  decide +kernel
lemma bs1_6_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 4 r = bs1_6_0_4 r := by
  revert r
  decide +kernel
lemma bs1_6_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 5 r = bs1_6_0_5 r := by
  revert r
  decide +kernel
lemma bs1_6_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 6 r = bs1_6_0_6 r := by
  revert r
  decide +kernel
lemma bs1_6_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 7 r = bs1_6_0_7 r := by
  revert r
  decide +kernel
lemma bs1_6_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 8 r = bs1_6_0_8 r := by
  revert r
  decide +kernel
lemma bs1_6_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 9 r = bs1_6_0_9 r := by
  revert r
  decide +kernel
lemma bs1_6_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 10 r = bs1_6_0_10 r := by
  revert r
  decide +kernel
lemma bs1_6_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 11 r = bs1_6_0_11 r := by
  revert r
  decide +kernel
lemma bs1_6_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 12 r = bs1_6_0_12 r := by
  revert r
  decide +kernel
lemma bs1_6_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 13 r = bs1_6_0_13 r := by
  revert r
  decide +kernel
lemma bs1_6_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 14 r = bs1_6_0_14 r := by
  revert r
  decide +kernel
lemma bs1_6_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 15 r = bs1_6_0_15 r := by
  revert r
  decide +kernel
lemma bs1_6_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 16 r = bs1_6_0_16 r := by
  revert r
  decide +kernel
lemma bs1_6_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 17 r = bs1_6_0_17 r := by
  revert r
  decide +kernel
lemma bs1_6_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 18 r = bs1_6_0_18 r := by
  revert r
  decide +kernel
lemma bs1_6_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 19 r = bs1_6_0_19 r := by
  revert r
  decide +kernel
lemma bs1_6_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_0) 20 r = bs1_6_0_20 r := by
  revert r
  decide +kernel
lemma bs1_6_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 0 r = bs1_6_1_0 r := by
  revert r
  decide +kernel
lemma bs1_6_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 1 r = bs1_6_1_1 r := by
  revert r
  decide +kernel
lemma bs1_6_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 2 r = bs1_6_1_2 r := by
  revert r
  decide +kernel
lemma bs1_6_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 3 r = bs1_6_1_3 r := by
  revert r
  decide +kernel
lemma bs1_6_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 4 r = bs1_6_1_4 r := by
  revert r
  decide +kernel
lemma bs1_6_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 5 r = bs1_6_1_5 r := by
  revert r
  decide +kernel
lemma bs1_6_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 6 r = bs1_6_1_6 r := by
  revert r
  decide +kernel
lemma bs1_6_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 7 r = bs1_6_1_7 r := by
  revert r
  decide +kernel
lemma bs1_6_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 8 r = bs1_6_1_8 r := by
  revert r
  decide +kernel
lemma bs1_6_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 9 r = bs1_6_1_9 r := by
  revert r
  decide +kernel
lemma bs1_6_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 10 r = bs1_6_1_10 r := by
  revert r
  decide +kernel
lemma bs1_6_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 11 r = bs1_6_1_11 r := by
  revert r
  decide +kernel
lemma bs1_6_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 12 r = bs1_6_1_12 r := by
  revert r
  decide +kernel
lemma bs1_6_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 13 r = bs1_6_1_13 r := by
  revert r
  decide +kernel
lemma bs1_6_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 14 r = bs1_6_1_14 r := by
  revert r
  decide +kernel
lemma bs1_6_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 15 r = bs1_6_1_15 r := by
  revert r
  decide +kernel
lemma bs1_6_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 16 r = bs1_6_1_16 r := by
  revert r
  decide +kernel
lemma bs1_6_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 17 r = bs1_6_1_17 r := by
  revert r
  decide +kernel
lemma bs1_6_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 18 r = bs1_6_1_18 r := by
  revert r
  decide +kernel
lemma bs1_6_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 19 r = bs1_6_1_19 r := by
  revert r
  decide +kernel
lemma bs1_6_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 6 tr1_6_1) 20 r = bs1_6_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


