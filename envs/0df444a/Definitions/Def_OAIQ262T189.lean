-- Prove2me | Definitions.Def_OAIQ262T189
-- name    : OAIQ262T189
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:36:12.828203+00:00
-- url     : https://prove2.me/theorems/8394b858-d399-49ac-aabf-c2f4d63d76ec
-- title:
--   Definitions bundle OAIQ262T189 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 88 declarations of OpenAI's Lean: 88 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Signs06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs06.lean), [`Triangular_Signs_Signs10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs10.lean), [`Triangular_Signs_Signs11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs11.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T054`, `OAIQ262T057`, `OAIQ262T058`, `OAIQ262T102`, `OAIQ262T105` and `OAIQ262T147` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T263` and `OAIQ262T264`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T054
import Definitions.Def_OAIQ262T057
import Definitions.Def_OAIQ262T058
import Definitions.Def_OAIQ262T102
import Definitions.Def_OAIQ262T105
import Definitions.Def_OAIQ262T147

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs0_6_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 1 r = bs0_6_1_1 r := by
  revert r
  decide +kernel
lemma bs0_6_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 2 r = bs0_6_1_2 r := by
  revert r
  decide +kernel
lemma bs0_6_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 3 r = bs0_6_1_3 r := by
  revert r
  decide +kernel
lemma bs0_6_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 4 r = bs0_6_1_4 r := by
  revert r
  decide +kernel
lemma bs0_6_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 5 r = bs0_6_1_5 r := by
  revert r
  decide +kernel
lemma bs0_6_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 6 r = bs0_6_1_6 r := by
  revert r
  decide +kernel
lemma bs0_6_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 7 r = bs0_6_1_7 r := by
  revert r
  decide +kernel
lemma bs0_6_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 8 r = bs0_6_1_8 r := by
  revert r
  decide +kernel
lemma bs0_6_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 9 r = bs0_6_1_9 r := by
  revert r
  decide +kernel
lemma bs0_6_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 17 r = bs0_6_1_17 r := by
  revert r
  decide +kernel
lemma bs0_6_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 18 r = bs0_6_1_18 r := by
  revert r
  decide +kernel
lemma bs0_6_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 19 r = bs0_6_1_19 r := by
  revert r
  decide +kernel
lemma bs0_6_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 0 6 tr0_6_1) 20 r = bs0_6_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_0_0_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 0 r = bs1_0_0_0 r := by
  revert r
  decide +kernel
lemma bs1_0_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 1 r = bs1_0_0_1 r := by
  revert r
  decide +kernel
lemma bs1_0_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 2 r = bs1_0_0_2 r := by
  revert r
  decide +kernel
lemma bs1_0_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 3 r = bs1_0_0_3 r := by
  revert r
  decide +kernel
lemma bs1_0_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 4 r = bs1_0_0_4 r := by
  revert r
  decide +kernel
lemma bs1_0_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 5 r = bs1_0_0_5 r := by
  revert r
  decide +kernel
lemma bs1_0_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 6 r = bs1_0_0_6 r := by
  revert r
  decide +kernel
lemma bs1_0_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 7 r = bs1_0_0_7 r := by
  revert r
  decide +kernel
lemma bs1_0_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 8 r = bs1_0_0_8 r := by
  revert r
  decide +kernel
lemma bs1_0_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 9 r = bs1_0_0_9 r := by
  revert r
  decide +kernel
lemma bs1_0_0_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 10 r = bs1_0_0_10 r := by
  revert r
  decide +kernel
lemma bs1_0_0_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 11 r = bs1_0_0_11 r := by
  revert r
  decide +kernel
lemma bs1_0_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 12 r = bs1_0_0_12 r := by
  revert r
  decide +kernel
lemma bs1_0_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 13 r = bs1_0_0_13 r := by
  revert r
  decide +kernel
lemma bs1_0_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 14 r = bs1_0_0_14 r := by
  revert r
  decide +kernel
lemma bs1_0_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 15 r = bs1_0_0_15 r := by
  revert r
  decide +kernel
lemma bs1_0_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 16 r = bs1_0_0_16 r := by
  revert r
  decide +kernel
lemma bs1_0_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 17 r = bs1_0_0_17 r := by
  revert r
  decide +kernel
lemma bs1_0_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 18 r = bs1_0_0_18 r := by
  revert r
  decide +kernel
lemma bs1_0_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 19 r = bs1_0_0_19 r := by
  revert r
  decide +kernel
lemma bs1_0_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_0) 20 r = bs1_0_0_20 r := by
  revert r
  decide +kernel
lemma bs1_0_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 0 r = bs1_0_1_0 r := by
  revert r
  decide +kernel
lemma bs1_0_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 1 r = bs1_0_1_1 r := by
  revert r
  decide +kernel
lemma bs1_0_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 2 r = bs1_0_1_2 r := by
  revert r
  decide +kernel
lemma bs1_0_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 3 r = bs1_0_1_3 r := by
  revert r
  decide +kernel
lemma bs1_0_1_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 4 r = bs1_0_1_4 r := by
  revert r
  decide +kernel
lemma bs1_0_1_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 5 r = bs1_0_1_5 r := by
  revert r
  decide +kernel
lemma bs1_0_1_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 6 r = bs1_0_1_6 r := by
  revert r
  decide +kernel
lemma bs1_0_1_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 7 r = bs1_0_1_7 r := by
  revert r
  decide +kernel
lemma bs1_0_1_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 8 r = bs1_0_1_8 r := by
  revert r
  decide +kernel
lemma bs1_0_1_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 9 r = bs1_0_1_9 r := by
  revert r
  decide +kernel
lemma bs1_0_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 10 r = bs1_0_1_10 r := by
  revert r
  decide +kernel
lemma bs1_0_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 11 r = bs1_0_1_11 r := by
  revert r
  decide +kernel
lemma bs1_0_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 12 r = bs1_0_1_12 r := by
  revert r
  decide +kernel
lemma bs1_0_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 13 r = bs1_0_1_13 r := by
  revert r
  decide +kernel
lemma bs1_0_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 14 r = bs1_0_1_14 r := by
  revert r
  decide +kernel
lemma bs1_0_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 15 r = bs1_0_1_15 r := by
  revert r
  decide +kernel
lemma bs1_0_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 16 r = bs1_0_1_16 r := by
  revert r
  decide +kernel
lemma bs1_0_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 17 r = bs1_0_1_17 r := by
  revert r
  decide +kernel
lemma bs1_0_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 18 r = bs1_0_1_18 r := by
  revert r
  decide +kernel
lemma bs1_0_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 19 r = bs1_0_1_19 r := by
  revert r
  decide +kernel
lemma bs1_0_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 0 tr1_0_1) 20 r = bs1_0_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_1_0_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 1 r = bs1_1_0_1 r := by
  revert r
  decide +kernel
lemma bs1_1_0_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 2 r = bs1_1_0_2 r := by
  revert r
  decide +kernel
lemma bs1_1_0_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 3 r = bs1_1_0_3 r := by
  revert r
  decide +kernel
lemma bs1_1_0_4_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 4 r = bs1_1_0_4 r := by
  revert r
  decide +kernel
lemma bs1_1_0_5_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 5 r = bs1_1_0_5 r := by
  revert r
  decide +kernel
lemma bs1_1_0_6_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 6 r = bs1_1_0_6 r := by
  revert r
  decide +kernel
lemma bs1_1_0_7_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 7 r = bs1_1_0_7 r := by
  revert r
  decide +kernel
lemma bs1_1_0_8_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 8 r = bs1_1_0_8 r := by
  revert r
  decide +kernel
lemma bs1_1_0_9_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 9 r = bs1_1_0_9 r := by
  revert r
  decide +kernel
lemma bs1_1_0_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 12 r = bs1_1_0_12 r := by
  revert r
  decide +kernel
lemma bs1_1_0_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 13 r = bs1_1_0_13 r := by
  revert r
  decide +kernel
lemma bs1_1_0_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 14 r = bs1_1_0_14 r := by
  revert r
  decide +kernel
lemma bs1_1_0_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 15 r = bs1_1_0_15 r := by
  revert r
  decide +kernel
lemma bs1_1_0_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 16 r = bs1_1_0_16 r := by
  revert r
  decide +kernel
lemma bs1_1_0_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 17 r = bs1_1_0_17 r := by
  revert r
  decide +kernel
lemma bs1_1_0_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 18 r = bs1_1_0_18 r := by
  revert r
  decide +kernel
lemma bs1_1_0_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 19 r = bs1_1_0_19 r := by
  revert r
  decide +kernel
lemma bs1_1_0_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_0) 20 r = bs1_1_0_20 r := by
  revert r
  decide +kernel
lemma bs1_1_1_0_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 0 r = bs1_1_1_0 r := by
  revert r
  decide +kernel
lemma bs1_1_1_1_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 1 r = bs1_1_1_1 r := by
  revert r
  decide +kernel
lemma bs1_1_1_2_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 2 r = bs1_1_1_2 r := by
  revert r
  decide +kernel
lemma bs1_1_1_3_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 3 r = bs1_1_1_3 r := by
  revert r
  decide +kernel
lemma bs1_1_1_10_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 10 r = bs1_1_1_10 r := by
  revert r
  decide +kernel
lemma bs1_1_1_11_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 11 r = bs1_1_1_11 r := by
  revert r
  decide +kernel
lemma bs1_1_1_12_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 12 r = bs1_1_1_12 r := by
  revert r
  decide +kernel
lemma bs1_1_1_13_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 13 r = bs1_1_1_13 r := by
  revert r
  decide +kernel
lemma bs1_1_1_14_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 14 r = bs1_1_1_14 r := by
  revert r
  decide +kernel
lemma bs1_1_1_15_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 15 r = bs1_1_1_15 r := by
  revert r
  decide +kernel
lemma bs1_1_1_16_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 16 r = bs1_1_1_16 r := by
  revert r
  decide +kernel
lemma bs1_1_1_17_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 17 r = bs1_1_1_17 r := by
  revert r
  decide +kernel
lemma bs1_1_1_18_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 18 r = bs1_1_1_18 r := by
  revert r
  decide +kernel
lemma bs1_1_1_19_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 19 r = bs1_1_1_19 r := by
  revert r
  decide +kernel
lemma bs1_1_1_20_calc (r : Fin 8) : bernsteinRowsBox 20 (ordinarySignRowBox 1 1 tr1_1_1) 20 r = bs1_1_1_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


