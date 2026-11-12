-- Prove2me | Definitions.Def_OAIQ262T155
-- name    : OAIQ262T155
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:56:14.462956+00:00
-- url     : https://prove2.me/theorems/ce869411-324e-403b-9968-8cfdf144b691
-- title:
--   Definitions bundle OAIQ262T155 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.spectrumBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Taylor_TaylorSpectrum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T137`, `OAIQ262T140` and `OAIQ262T142` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T193`, `OAIQ262T194`, `OAIQ262T195` and `OAIQ262T196`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T137
import Definitions.Def_OAIQ262T140
import Definitions.Def_OAIQ262T142

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma waveExp0_1_mem (j : Fin 31) : (waveExp0_1 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((1:ℤ):ℂ))) := by
  rw [← waveExp0_1_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 1)) (by
    revert j
    decide +kernel)
lemma waveExp0_3_mem (j : Fin 31) : (waveExp0_3 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((3:ℤ):ℂ))) := by
  rw [← waveExp0_3_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 3)) (by
    revert j
    decide +kernel)
lemma waveExp0_4_mem (j : Fin 31) : (waveExp0_4 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((4:ℤ):ℂ))) := by
  rw [← waveExp0_4_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 4)) (by
    revert j
    decide +kernel)
lemma waveExp0_7_mem (j : Fin 31) : (waveExp0_7 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((7:ℤ):ℂ))) := by
  rw [← waveExp0_7_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 7)) (by
    revert j
    decide +kernel)
lemma waveExp0_9_mem (j : Fin 31) : (waveExp0_9 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((9:ℤ):ℂ))) := by
  rw [← waveExp0_9_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 9)) (by
    revert j
    decide +kernel)
lemma waveExp0_21_mem (j : Fin 31) : (waveExp0_21 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((21:ℤ):ℂ))) := by
  rw [← waveExp0_21_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 21)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveJetsData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma jetTable0_3_calc (j : Fin 31) : jetMultiplierBox 0 3 j = jetTable0_3 j := by
  revert j
  decide +kernel
lemma jetTable0_4_calc (j : Fin 31) : jetMultiplierBox 0 4 j = jetTable0_4 j := by
  revert j
  decide +kernel
lemma jetTable0_5_calc (j : Fin 31) : jetMultiplierBox 0 5 j = jetTable0_5 j := by
  revert j
  decide +kernel
lemma jetTable0_6_calc (j : Fin 31) : jetMultiplierBox 0 6 j = jetTable0_6 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

def spectrumBox (side q : Fin 2) (j : Fin 31) (r : Fin 8) : CI :=
  if q.val=0 then (coeffBox15 j).mul (CI.ofReal (ATable side 22 r))
  else CI.sum (fun col : Fin 22 => (columnTable ⟨col.val,by omega⟩ j).mul (CI.ofReal (ATable side ⟨col.val,by omega⟩ r)))
end AtomicTriangular.FiniteCertificate
end

end OAI
end


