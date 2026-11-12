-- Prove2me | Definitions.Def_OAIQ262T140
-- name    : OAIQ262T140
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:22:54.231431+00:00
-- url     : https://prove2.me/theorems/cc6e0586-8ec4-4ca6-bed2-86cc9b01c53f
-- title:
--   Definitions bundle OAIQ262T140 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 3 definitions and 16 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.minusBlockBox`, `OAI.AtomicTriangular.FiniteCertificate.targetCoefficientBox`, `OAI.AtomicTriangular.FiniteCertificate.taylorPhaseBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_MatrixInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/MatrixInterval.lean), [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean), [`Triangular_Taylor_TaylorPhase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorPhase.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T086`, `OAIQ262T089`, `OAIQ262T090` and `OAIQ262T091` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T151`, `OAIQ262T153`, `OAIQ262T154`, `OAIQ262T155`, `OAIQ262T156`, `OAIQ262T157` and `OAIQ262T158`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T089
import Definitions.Def_OAIQ262T090
import Definitions.Def_OAIQ262T091

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
lemma phaseHTable0_calc (j : Fin 31) : wavePhaseBox 0 1 j = phaseHTable0 j := by
  revert j
  decide +kernel
lemma phaseHTable0_mem (j : Fin 31) : (phaseHTable0 j).Mem (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)) := by
  rw [← phaseHTable0_calc]
  exact wavePhaseBox_mem 0 1 j

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

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
lemma matrixNorm_bound [Nonempty n] {a : m → n → RI} {A : Matrix m n ℝ} {b : ℤ}
    (ha : ∀ i j, (a i j).Mem (A i j)) (hb : ∀ j, matrixColBound a j ≤ b) :
    matNorm A ≤ (b:ℝ)/(scale:ℝ) := by
  apply matNorm_le
  intro j
  have hh := (RI.mem_sum (fun i => RI.mem_abs (ha i j))).2
  apply (le_div_iff₀ scale_pos).mpr
  change colNorm A j * (scale:ℝ) ≤ (b:ℝ)
  rw [mul_comm]
  apply hh.trans
  exact_mod_cast hb j

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
def minusBlockBox (i j : Fin 20) : RI := (matrixOne i j).sub (RBox i j)
lemma plusResidualRow10_calc (j : Fin 20) : plusResidualBox 10 j = plusResidualRow10 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def targetCoefficientBox (n : Fin 10) : RI := (QBox1.mul (QTable n).invPos).mul (targetExpTable n).re

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
lemma psiD36_calc (j : Fin 31) : psiBox 0 0 36 j QBox0 DBox0 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD36 j)=psiD36 j := by
  revert j
  decide +kernel
lemma psiD37_calc (j : Fin 31) : psiBox 0 0 37 j QBox1 DBox1 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD37 j)=psiD37 j := by
  revert j
  decide +kernel
lemma psiD39_calc (j : Fin 31) : psiBox 0 0 39 j QBox3 DBox3 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD39 j)=psiD39 j := by
  revert j
  decide +kernel
lemma psiD40_calc (j : Fin 31) : psiBox 0 0 40 j QBox4 DBox4 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD40 j)=psiD40 j := by
  revert j
  decide +kernel
lemma psiD43_calc (j : Fin 31) : psiBox 0 0 43 j QBox7 DBox7 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD43 j)=psiD43 j := by
  revert j
  decide +kernel
lemma psiD45_calc (j : Fin 31) : psiBox 0 0 45 j QBox9 DBox9 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD45 j)=psiD45 j := by
  revert j
  decide +kernel
lemma psiD48_calc (j : Fin 31) : psiBox 0 0 48 j QBox12 DBox12 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD48 j)=psiD48 j := by
  revert j
  decide +kernel
lemma psiD49_calc (j : Fin 31) : psiBox 0 0 49 j QBox13 DBox13 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD49 j)=psiD49 j := by
  revert j
  decide +kernel
lemma psiD52_calc (j : Fin 31) : psiBox 0 0 52 j QBox16 DBox16 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD52 j)=psiD52 j := by
  revert j
  decide +kernel
lemma psiD55_calc (j : Fin 31) : psiBox 0 0 55 j QBox19 DBox19 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD55 j)=psiD55 j := by
  revert j
  decide +kernel
lemma psiD57_calc (j : Fin 31) : psiBox 0 0 57 j QBox21 DBox21 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD57 j)=psiD57 j := by
  revert j
  decide +kernel
lemma psiD31_calc (j : Fin 31) : psiBox 0 0 31 j QBox31 DBox31 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD31 j)=psiD31 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def taylorPhaseBox (q branch : Fin 2) (j : Fin 31) : CI :=
  if branch.val=0 then ((CI.imag.mul (CI.ofReal piBox)).mul (CI.ofReal (realFrequencyBox j))).sub
    (CI.ofReal (piBox.mul ((dampingBox q).sub (dampingBox 0))))
  else wavePhaseBox q 0 j

end AtomicTriangular.FiniteCertificate
end

end OAI
end


