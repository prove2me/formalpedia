-- Prove2me | Definitions.Def_OAIQ262T089
-- name    : OAIQ262T089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:51:00.501019+00:00
-- url     : https://prove2.me/theorems/4d1ba934-f392-45c0-bdef-f6eca9d34945
-- title:
--   Definitions bundle OAIQ262T089 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 4 definitions and 21 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.A1Table`, `OAI.AtomicTriangular.FiniteCertificate.targetEnvBox`, `OAI.AtomicTriangular.FiniteCertificate.waveExpTable`, `OAI.AtomicTriangular.Interval.matrixColBound`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_MatrixInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/MatrixInterval.lean), [`Triangular_Certificate_ParamA`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamA.lean), [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Envelope_EnvelopePsiB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_EnvelopeWaves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeWaves.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T007`, `OAIQ262T008`, `OAIQ262T010`, `OAIQ262T011` and `OAIQ262T012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139`, `OAIQ262T140`, `OAIQ262T142` and `OAIQ262T143`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T007
import Definitions.Def_OAIQ262T008
import Definitions.Def_OAIQ262T010
import Definitions.Def_OAIQ262T011
import Definitions.Def_OAIQ262T012

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_MatrixInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

def matrixColBound (a : m → n → RI) (j : n) : ℤ := ∑ i, ((a i j).abs).hi
end AtomicTriangular.Interval
end

end OAI
end

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
def waveExpTable : Fin 2 → Fin 10 → Fin 31 → CI :=
  ![![waveExp0_1,waveExp0_3,waveExp0_4,waveExp0_7,waveExp0_9,waveExp0_12,waveExp0_13,waveExp0_16,waveExp0_19,waveExp0_21],
  ![waveExp1_1,waveExp1_3,waveExp1_4,waveExp1_7,waveExp1_9,waveExp1_12,waveExp1_13,waveExp1_16,waveExp1_19,waveExp1_21]]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamA
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def A1Table : Fin 23 → Fin 8 → RI := ![A1TableRow0,A1TableRow1,A1TableRow2,A1TableRow3,A1TableRow4,A1TableRow5,A1TableRow6,A1TableRow7,A1TableRow8,A1TableRow9,A1TableRow10,A1TableRow11,A1TableRow12,A1TableRow13,A1TableRow14,A1TableRow15,A1TableRow16,A1TableRow17,A1TableRow18,A1TableRow19,A1TableRow20,A1TableRow21,A1TableRow22]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma phaseNorm00_check (j : Fin 31) : 0≤(phaseNorm00 j).lo ∧ (phaseNorm00 j).lo*(phaseNorm00 j).lo ≤ scale*max 0 (envelopePhase00 j).normSq.lo ∧ scale*(envelopePhase00 j).normSq.hi ≤ (phaseNorm00 j).hi*(phaseNorm00 j).hi ∧ 0≤(phaseNorm00 j).hi := by
  revert j
  decide +kernel
lemma phaseNorm01_check (j : Fin 31) : 0≤(phaseNorm01 j).lo ∧ (phaseNorm01 j).lo*(phaseNorm01 j).lo ≤ scale*max 0 (envelopePhase01 j).normSq.lo ∧ scale*(envelopePhase01 j).normSq.hi ≤ (phaseNorm01 j).hi*(phaseNorm01 j).hi ∧ 0≤(phaseNorm01 j).hi := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpB1_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 1))).exp.re=envelopeExpB1 j := by
  revert j
  decide +kernel
lemma envelopeExpB1_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 1))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpB3_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 3))).exp.re=envelopeExpB3 j := by
  revert j
  decide +kernel
lemma envelopeExpB3_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 3))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpB4_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 4))).exp.re=envelopeExpB4 j := by
  revert j
  decide +kernel
lemma envelopeExpB4_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 4))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpB7_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 7))).exp.re=envelopeExpB7 j := by
  revert j
  decide +kernel
lemma envelopeExpB7_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 7))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpB12_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 12))).exp.re=envelopeExpB12 j := by
  revert j
  decide +kernel
lemma envelopeExpB12_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 12))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpB13_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 13))).exp.re=envelopeExpB13 j := by
  revert j
  decide +kernel
lemma envelopeExpB13_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 13))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpB16_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 16))).exp.re=envelopeExpB16 j := by
  revert j
  decide +kernel
lemma envelopeExpB16_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 16))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpB19_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 19))).exp.re=envelopeExpB19 j := by
  revert j
  decide +kernel
lemma envelopeExpB19_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 19))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpB21_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 21))).exp.re=envelopeExpB21 j := by
  revert j
  decide +kernel
lemma envelopeExpB21_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 21))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma periodDenD_pos (j : Fin 31) : 0<((RI.point 1).sub (periodExpD j)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def targetEnvBox (q : Fin 2) (qb db eb : RI) : RI :=
  ((QBox1.mul qb.invPos).mul (((RI.point 1).add targetZBox).add
    (targetZBox.mul ((targetRateBox q).sub db).abs))).mul eb
end AtomicTriangular.FiniteCertificate
end

end OAI
end


