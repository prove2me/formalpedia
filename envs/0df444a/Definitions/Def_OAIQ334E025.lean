-- Prove2me | Definitions.Def_OAIQ334E025
-- name    : OAIQ334E025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T12:16:48.369458+00:00
-- url     : https://prove2.me/theorems/96c2407d-f482-452e-b500-fb359bb2eadc
-- title:
--   Definitions bundle OAIQ334E025 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave.lean).
--
--   **Imports.** It imports the bundle `OAIQ334E020` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_eu`; the proofs of `OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_6_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_6_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_6_mem_eu` and `OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_eu`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ334E020

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

def taylorWaveBox (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) : CI :=
  (((taylorAmplitudeBox q br j).mul (taylorExpTable q br n j)).mul
    ((taylorPhaseTable q br j).pow (l.val+2))).divNat (l.val+2).factorial

end AtomicTriangular.FiniteCertificate
end

end OAI
end


