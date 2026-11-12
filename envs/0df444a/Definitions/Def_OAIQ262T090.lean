-- Prove2me | Definitions.Def_OAIQ262T090
-- name    : OAIQ262T090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:50:55.885942+00:00
-- url     : https://prove2.me/theorems/15600c4e-001c-4500-bddd-b2e5b640423a
-- title:
--   Definitions bundle OAIQ262T090 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 3 definitions and 16 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.DTable`, `OAI.AtomicTriangular.FiniteCertificate.QTable`, `OAI.AtomicTriangular.FiniteCertificate.jetTable`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Envelope_EnvelopeNorms`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorms.lean), [`Triangular_Envelope_EnvelopePsiB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T007`, `OAIQ262T008`, `OAIQ262T009` and `OAIQ262T010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139` and `OAIQ262T140`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T007
import Definitions.Def_OAIQ262T008
import Definitions.Def_OAIQ262T009
import Definitions.Def_OAIQ262T010

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
def QTable : Fin 10 → RI := ![QBox1,QBox3,QBox4,QBox7,QBox9,QBox12,QBox13,QBox16,QBox19,QBox21]
def DTable : Fin 10 → RI := ![DBox1,DBox3,DBox4,DBox7,DBox9,DBox12,DBox13,DBox16,DBox19,DBox21]

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
def jetTable : Fin 2 → Fin 20 → Fin 31 → CI :=
  ![![jetTable0_0,jetTable0_1,jetTable0_2,jetTable0_3,jetTable0_4,jetTable0_5,jetTable0_6,jetTable0_7,jetTable0_8,jetTable0_9,jetTable0_10,jetTable0_11,jetTable0_12,jetTable0_13,jetTable0_14,jetTable0_15,jetTable0_16,jetTable0_17,jetTable0_18,jetTable0_19],
  ![jetTable1_0,jetTable1_1,jetTable1_2,jetTable1_3,jetTable1_4,jetTable1_5,jetTable1_6,jetTable1_7,jetTable1_8,jetTable1_9,jetTable1_10,jetTable1_11,jetTable1_12,jetTable1_13,jetTable1_14,jetTable1_15,jetTable1_16,jetTable1_17,jetTable1_18,jetTable1_19]]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullWTable_calc (i : Fin 15) (d : Fin 2) : fullTailWBox columnNorm22 i d=fullWTable i d := by
  revert i d
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
lemma envelopeExpB9_calc (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 9))).exp.re=envelopeExpB9 j := by
  revert j
  decide +kernel
lemma envelopeExpB9_pre (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 9))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpD36_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 36))).exp.re=envelopeExpD36 j := by
  revert j
  decide +kernel
lemma envelopeExpD36_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 36))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD37_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 37))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD25_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 25))).exp.re=envelopeExpD25 j := by
  revert j
  decide +kernel
lemma envelopeExpD25_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 25))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD27_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 27))).exp.re=envelopeExpD27 j := by
  revert j
  decide +kernel
lemma envelopeExpD27_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 27))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD28_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 28))).exp.re=envelopeExpD28 j := by
  revert j
  decide +kernel
lemma envelopeExpD28_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 28))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD31_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 31))).exp.re=envelopeExpD31 j := by
  revert j
  decide +kernel
lemma envelopeExpD31_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 31))).normSq.hi ≤ scale*1024^2 := by
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
lemma periodExpD_calc (j : Fin 31) : (CI.ofReal ((envelopePhase00 j).re.mul (RI.point 36))).exp.re=periodExpD j := by
  revert j
  decide +kernel
lemma periodExpD_pre (j : Fin 31) : (CI.ofReal ((envelopePhase00 j).re.mul (RI.point 36))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


