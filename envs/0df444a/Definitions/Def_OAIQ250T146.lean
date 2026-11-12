-- Prove2me | Definitions.Def_OAIQ250T146
-- name    : OAIQ250T146
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:59:40.951505+00:00
-- url     : https://prove2.me/theorems/98be7a39-f549-4c36-b75e-242eb0287646
-- title:
--   Definitions bundle OAIQ250T146 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 2 definitions and 18 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.RBox`, `OAI.AtomicTriangular.FiniteCertificate.jetMatrixTable`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_JetMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Envelope_EnvelopePsiC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T004`, `OAIQ250T005`, `OAIQ250T006`, `OAIQ250T007` and `OAIQ250T008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T048`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T004
import Definitions.Def_OAIQ250T005
import Definitions.Def_OAIQ250T006
import Definitions.Def_OAIQ250T007
import Definitions.Def_OAIQ250T008

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
lemma QTable_mem (a : Fin 10) : (QTable a).Mem (Q (finiteNode a)) := by
  fin_cases a
  · exact QBox1_mem
  · exact QBox3_mem
  · exact QBox4_mem
  · exact QBox7_mem
  · exact QBox9_mem
  · exact QBox12_mem
  · exact QBox13_mem
  · exact QBox16_mem
  · exact QBox19_mem
  · exact QBox21_mem
lemma QTable_pos (n : Fin 10) : 0 < (QTable n).lo := by
  revert n
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def jetMatrixTable : Fin 20 → Fin 23 → RI := ![fullJetRow0,fullJetRow1,fullJetRow2,fullJetRow3,fullJetRow4,fullJetRow5,fullJetRow6,fullJetRow7,fullJetRow8,fullJetRow9,fullJetRow10,fullJetRow11,fullJetRow12,fullJetRow13,fullJetRow14,fullJetRow15,fullJetRow16,fullJetRow17,fullJetRow18,fullJetRow19]
def RBox (i j : Fin 20) : RI := jetMatrixTable i ⟨j.val+2,by omega⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpC48_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 48))).exp.re=envelopeExpC48 j := by
  revert j
  decide +kernel
lemma envelopeExpC48_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 48))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC49_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 49))).exp.re=envelopeExpC49 j := by
  revert j
  decide +kernel
lemma envelopeExpC49_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 49))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC52_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 52))).exp.re=envelopeExpC52 j := by
  revert j
  decide +kernel
lemma envelopeExpC52_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 52))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC55_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 55))).exp.re=envelopeExpC55 j := by
  revert j
  decide +kernel
lemma envelopeExpC55_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 55))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC57_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 57))).exp.re=envelopeExpC57 j := by
  revert j
  decide +kernel
lemma envelopeExpC57_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 57))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpD48_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 48))).exp.re=envelopeExpD48 j := by
  revert j
  decide +kernel
lemma envelopeExpD49_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 49))).exp.re=envelopeExpD49 j := by
  revert j
  decide +kernel
lemma envelopeExpD49_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 49))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD52_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 52))).exp.re=envelopeExpD52 j := by
  revert j
  decide +kernel
lemma envelopeExpD52_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 52))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma Dkernel_summable (q : TailNode × Fin 2) : Summable (fun p => |Dkernel p q|) :=
  (tail_tail_column_bounds 0 0 q.1.val.val q.2).1
end AtomicTriangular.Construction
end

end OAI
end


