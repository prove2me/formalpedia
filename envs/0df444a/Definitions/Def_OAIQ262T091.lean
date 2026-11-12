-- Prove2me | Definitions.Def_OAIQ262T091
-- name    : OAIQ262T091
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:53:35.073751+00:00
-- url     : https://prove2.me/theorems/429a54fb-c03b-47ae-b591-fd4672c73825
-- title:
--   Definitions bundle OAIQ262T091 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 6 definitions and 18 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.Lplus`, `OAI.AtomicTriangular.FiniteCertificate.RBox`, `OAI.AtomicTriangular.FiniteCertificate.jetMatrixTable`, `OAI.AtomicTriangular.FiniteCertificate.minusApproxBox`, `OAI.AtomicTriangular.FiniteCertificate.plusBlockBox`, `OAI.AtomicTriangular.FiniteCertificate.plusResidualBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_JetMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean), [`Triangular_Certificate_MatrixInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/MatrixInterval.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T008` and `OAIQ262T009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T139`, `OAIQ262T140`, `OAIQ262T141` and `OAIQ262T142`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T008
import Definitions.Def_OAIQ262T009

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_JetMatrix
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

lemma RI.mem_singleton (z : ℤ) : (RI.singleton z).Mem ((z:ℝ)/(scale:ℝ)) := by
  have hs : (scale:ℝ) ≠ 0 := scale_pos.ne'
  have hh : (scale:ℝ)*((z:ℝ)/(scale:ℝ)) = (z:ℝ) := by field_simp
  constructor <;> dsimp only [RI.Mem,RI.singleton] <;> rw [hh]
end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
def minusApproxBox (i j : Fin 20) : RI := RI.singleton (minusApproxNum i j)

def plusBlockBox (i j : Fin 20) : RI := (matrixOne i j).add (RBox i j)
lemma plusApproxBox_mem (i j : Fin 20) : (plusApproxBox i j).Mem (plusApprox i j) := RI.mem_singleton _
def plusResidualBox (i j : Fin 20) : RI :=
  (matrixMul plusApproxBox plusBlockBox i j).sub (matrixOne i j)
lemma plusResidualRow0_calc (j : Fin 20) : plusResidualBox 0 j = plusResidualRow0 j := by
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
lemma envelopeExpD37_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 37))).exp.re=envelopeExpD37 j := by
  revert j
  decide +kernel
lemma envelopeExpD39_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 39))).exp.re=envelopeExpD39 j := by
  revert j
  decide +kernel
lemma envelopeExpD39_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 39))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD40_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 40))).exp.re=envelopeExpD40 j := by
  revert j
  decide +kernel
lemma envelopeExpD40_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 40))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD43_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 43))).exp.re=envelopeExpD43 j := by
  revert j
  decide +kernel
lemma envelopeExpD43_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 43))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD45_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 45))).exp.re=envelopeExpD45 j := by
  revert j
  decide +kernel
lemma envelopeExpD45_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 45))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD48_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 48))).exp.re=envelopeExpD48 j := by
  revert j
  decide +kernel
lemma envelopeExpD48_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 48))).normSq.hi ≤ scale*1024^2 := by
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
def Lplus : FiniteCoefficients →L[ℝ] FiniteCoefficients := l1Matrix (1-R)⁻¹
end AtomicTriangular.Construction
end

end OAI
end


