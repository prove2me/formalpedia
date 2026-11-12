-- Prove2me | Definitions.Def_OAIQ262T258
-- name    : OAIQ262T258
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T21:00:23.531378+00:00
-- url     : https://prove2.me/theorems/12b8325b-c939-43a7-9e6a-fe6cfb304a75
-- title:
--   Definitions bundle OAIQ262T258 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorExp11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp11.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundle `OAIQ262T194` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T259`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T194

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_1_4_mem (j : Fin 31) : (taylorExp1_1_4 j).Mem (exp (taylorPhase 1 1 (frequency j)*((4:ℤ):ℂ))) := by
  rw [← taylorExp1_1_4_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase1_1_mem j) (CI.mem_point 4)) (by
    revert j
    decide +kernel)
lemma taylorExp1_1_7_mem (j : Fin 31) : (taylorExp1_1_7 j).Mem (exp (taylorPhase 1 1 (frequency j)*((7:ℤ):ℂ))) := by
  rw [← taylorExp1_1_7_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase1_1_mem j) (CI.mem_point 7)) (by
    revert j
    decide +kernel)
lemma taylorExp1_1_9_mem (j : Fin 31) : (taylorExp1_1_9 j).Mem (exp (taylorPhase 1 1 (frequency j)*((9:ℤ):ℂ))) := by
  rw [← taylorExp1_1_9_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase1_1_mem j) (CI.mem_point 9)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end


