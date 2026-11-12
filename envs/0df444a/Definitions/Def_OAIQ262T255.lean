-- Prove2me | Definitions.Def_OAIQ262T255
-- name    : OAIQ262T255
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T21:05:56.265183+00:00
-- url     : https://prove2.me/theorems/18eaeacb-4b43-4688-909d-bfdd3ec72915
-- title:
--   Definitions bundle OAIQ262T255 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean), [`Triangular_Taylor_TaylorExp01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp01.lean), [`Triangular_Taylor_TaylorExp10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp10.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T193` and `OAIQ262T194` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T259`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T193
import Definitions.Def_OAIQ262T194

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_9_mem (j : Fin 31) : (taylorExp0_0_9 j).Mem (exp (taylorPhase 0 0 (frequency j)*((9:ℤ):ℂ))) := by
  rw [← taylorExp0_0_9_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem j) (CI.mem_point 9)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_1_1_mem (j : Fin 31) : (taylorExp0_1_1 j).Mem (exp (taylorPhase 0 1 (frequency j)*((1:ℤ):ℂ))) := by
  rw [← taylorExp0_1_1_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_1_mem j) (CI.mem_point 1)) (by
    revert j
    decide +kernel)
lemma taylorExp0_1_3_mem (j : Fin 31) : (taylorExp0_1_3 j).Mem (exp (taylorPhase 0 1 (frequency j)*((3:ℤ):ℂ))) := by
  rw [← taylorExp0_1_3_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_1_mem j) (CI.mem_point 3)) (by
    revert j
    decide +kernel)
lemma taylorExp0_1_4_mem (j : Fin 31) : (taylorExp0_1_4 j).Mem (exp (taylorPhase 0 1 (frequency j)*((4:ℤ):ℂ))) := by
  rw [← taylorExp0_1_4_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_1_mem j) (CI.mem_point 4)) (by
    revert j
    decide +kernel)
lemma taylorExp0_1_12_mem (j : Fin 31) : (taylorExp0_1_12 j).Mem (exp (taylorPhase 0 1 (frequency j)*((12:ℤ):ℂ))) := by
  rw [← taylorExp0_1_12_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_1_mem j) (CI.mem_point 12)) (by
    revert j
    decide +kernel)
lemma taylorExp0_1_13_mem (j : Fin 31) : (taylorExp0_1_13 j).Mem (exp (taylorPhase 0 1 (frequency j)*((13:ℤ):ℂ))) := by
  rw [← taylorExp0_1_13_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_1_mem j) (CI.mem_point 13)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_0_9_mem (j : Fin 31) : (taylorExp1_0_9 j).Mem (exp (taylorPhase 1 0 (frequency j)*((9:ℤ):ℂ))) := by
  rw [← taylorExp1_0_9_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase1_0_mem j) (CI.mem_point 9)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end


