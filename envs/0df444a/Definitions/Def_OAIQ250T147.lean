-- Prove2me | Definitions.Def_OAIQ250T147
-- name    : OAIQ250T147
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:43:47.230418+00:00
-- url     : https://prove2.me/theorems/131ab8b9-a82a-4b28-b8c4-785103cead9b
-- title:
--   Definitions bundle OAIQ250T147 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean).
--
--   **Imports.** It imports the bundle `OAIQ250T009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T101`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T009

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma waveExp1_1_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 1)).exp = waveExp1_1 j := by
  revert j
  decide +kernel
lemma waveExp1_13_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 13)).exp = waveExp1_13 j := by
  revert j
  decide +kernel
lemma waveExp1_16_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 16)).exp = waveExp1_16 j := by
  revert j
  decide +kernel
lemma waveExp1_19_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 19)).exp = waveExp1_19 j := by
  revert j
  decide +kernel
lemma waveExp1_21_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 21)).exp = waveExp1_21 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


