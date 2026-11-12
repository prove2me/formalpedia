-- Prove2me | Definitions.Def_OAIQ250T048
-- name    : OAIQ250T048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:04:20.194844+00:00
-- url     : https://prove2.me/theorems/75d9059b-8b2b-428c-9985-e32a979cb307
-- title:
--   Definitions bundle OAIQ250T048 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 5 definitions and 24 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.minusApproxBox`, `OAI.AtomicTriangular.FiniteCertificate.minusBlockBox`, `OAI.AtomicTriangular.FiniteCertificate.plusBlockBox`, `OAI.AtomicTriangular.FiniteCertificate.plusResidualBox`, `OAI.AtomicTriangular.Interval.matrixColBound`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_MatrixInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/MatrixInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Construction_L1Matrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/L1Matrix.lean), [`Triangular_Construction_RepetitionBound`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/RepetitionBound.lean), [`Triangular_Envelope_EnvelopeBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeBoxes.lean), [`Triangular_Envelope_EnvelopeNorms`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorms.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_EnvelopeWaves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeWaves.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T003`, `OAIQ250T009` and `OAIQ250T146` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T083`, `OAIQ250T084`, `OAIQ250T085` and `OAIQ250T151`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T009
import Definitions.Def_OAIQ250T146

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
lemma phaseHTable0_calc (j : Fin 31) : wavePhaseBox 0 1 j = phaseHTable0 j := by
  revert j
  decide +kernel
lemma phaseHTable1_calc (j : Fin 31) : wavePhaseBox 1 1 j = phaseHTable1 j := by
  revert j
  decide +kernel
lemma waveExp0_21_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 21)).exp = waveExp0_21 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_MatrixInterval
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

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

def matrixColBound (a : m → n → RI) (j : n) : ℤ := ∑ i, ((a i j).abs).hi
end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
def minusBlockBox (i j : Fin 20) : RI := (matrixOne i j).sub (RBox i j)
def minusApproxBox (i j : Fin 20) : RI := RI.singleton (minusApproxNum i j)

def plusBlockBox (i j : Fin 20) : RI := (matrixOne i j).add (RBox i j)
lemma plusApproxBox_mem (i j : Fin 20) : (plusApproxBox i j).Mem (plusApprox i j) := RI.mem_singleton _
def plusResidualBox (i j : Fin 20) : RI :=
  (matrixMul plusApproxBox plusBlockBox i j).sub (matrixOne i j)
lemma plusResidualRow0_calc (j : Fin 20) : plusResidualBox 0 j = plusResidualRow0 j := by
  revert j
  decide +kernel
lemma plusResidualRow10_calc (j : Fin 20) : plusResidualBox 10 j = plusResidualRow10 j := by
  revert j
  decide +kernel
lemma plusResidualRow11_calc (j : Fin 20) : plusResidualBox 11 j = plusResidualRow11 j := by
  revert j
  decide +kernel
lemma plusResidualRow12_calc (j : Fin 20) : plusResidualBox 12 j = plusResidualRow12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_L1Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.MatrixBounds
open L1Kernel
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Nonempty m] [Nonempty n] [Nonempty p]
omit [Nonempty m] in
lemma l1Matrix_norm (A : Matrix m n ℝ) : ‖l1Matrix A‖ ≤ matNorm A :=
  operator_norm _ _ _ (matNorm_nonneg A) _
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullTailWBox_mem (pn : Fin 31 → RI) (hp : ∀ l, (pn l).Mem ‖fourierCoeff l‖)
    (i : Fin 15) (d : Fin 2) : (fullTailWBox pn i d).Mem (fullTailW i d) := by
  unfold fullTailWBox fullTailW
  split_ifs with hd
  · apply RI.mem_mul (by norm_num at *; simpa using RI.mem_divNat (RI.mem_pow piBox_mem 2) (by norm_num : 0<(18^2:ℕ)))
    apply RI.mem_sum
    intro l
    split_ifs
    · apply RI.mem_mul _ (hp l)
      apply RI.mem_sub
      · simpa using RI.mem_point ((frequencyDistance l:ℤ)-i.val)
      · simpa using RI.mem_divNat ri1_mem (by norm_num : 0<(2:ℕ))
    · exact ri0_mem
  · apply RI.mem_mul (by simpa using RI.mem_divNat piBox_mem (by norm_num : 0<(18:ℕ)))
    apply RI.mem_sum
    intro l
    split_ifs
    · exact hp l
    · exact ri0_mem

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorms
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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaNorm0_check (j : Fin 31) : 0≤(lambdaNorm0 j).lo ∧ (lambdaNorm0 j).lo*(lambdaNorm0 j).lo ≤ scale*max 0 (lambdaTable 0 j).normSq.lo ∧ scale*(lambdaTable 0 j).normSq.hi ≤ (lambdaNorm0 j).hi*(lambdaNorm0 j).hi ∧ 0≤(lambdaNorm0 j).hi := by
  revert j
  decide +kernel
lemma envelopePhase00_calc (j : Fin 31) : wavePhaseBox 0 0 j=envelopePhase00 j := by
  revert j
  decide +kernel
lemma envelopePhase01_calc (j : Fin 31) : wavePhaseBox 0 1 j=envelopePhase01 j := by
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
lemma envelopeExpD55_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 55))).exp.re=envelopeExpD55 j := by
  revert j
  decide +kernel
lemma envelopeExpD55_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 55))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpD57_calc (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 57))).exp.re=envelopeExpD57 j := by
  revert j
  decide +kernel
lemma envelopeExpD57_pre (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 57))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSums
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
lemma periodDenD_pos (j : Fin 31) : 0<((RI.point 1).sub (periodExpD j)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_RepetitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma repetitionExpData_calc : repetitionExpInput.exp.re=repetitionExpData := by decide +kernel
lemma repetitionExpData_mem : repetitionExpData.Mem repetitionRatio := by
  rw [← repetitionExpData_calc]
  apply ri_exp_mem
  exact RI.mem_mul (RI.mem_mul (by simpa using RI.mem_point (-36)) piBox_mem)
    (by simpa [Construction.eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5))
  decide +kernel
lemma repetitionNormBox_calc :
    (((RI.point 1).add (piBox.mul ((RI.point 1).divNat 5))).mul repetitionExpData).mul
      (((RI.point 1).sub repetitionExpData).invPos)=repetitionNormBox := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


