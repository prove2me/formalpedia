-- Prove2me | Definitions.Def_OAIQ262T092
-- name    : OAIQ262T092
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:35.846243+00:00
-- url     : https://prove2.me/theorems/41a998ec-a03d-4d0b-88b1-236627d670ab
-- title:
--   Definitions bundle OAIQ262T092 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 3 definitions and 17 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.tailFixedColumn`, `OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox`, `OAI.AtomicTriangular.FiniteCertificate.plusInverseBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_Inverse`, `Triangular_Certificate_ParamA`, `Triangular_Certificate_ParamInterval`, `Triangular_Certificate_ParamU`, `Triangular_Certificate_PolytopeInterval`, `Triangular_Certificate_WaveExpData`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_DirectCoordinates`, `Triangular_Construction_FiniteInterpolation`, `Triangular_Construction_FiniteTargetBridge`, `Triangular_Construction_L1Matrix`, `Triangular_Envelope_EnvelopePsiD`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T007`, `OAIQ262T008`, `OAIQ262T009`, `OAIQ262T010`, `OAIQ262T011` and `OAIQ262T012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T139`, `OAIQ262T142`, `OAIQ262T143`, `OAIQ262T146`, `OAIQ262T148` and `OAIQ262T149`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T007
import Definitions.Def_OAIQ262T008
import Definitions.Def_OAIQ262T009
import Definitions.Def_OAIQ262T010
import Definitions.Def_OAIQ262T011
import Definitions.Def_OAIQ262T012

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma fourier_node_cancel (n : Node) : waveDerivative 0 n.val = 0 := by
  rw [waveDerivative_zero, P_node]

end AtomicTriangular.Construction

end
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
lemma waveExp0_1_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 1)).exp = waveExp0_1 j := by
  revert j
  decide +kernel
lemma waveExp0_12_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 12)).exp = waveExp0_12 j := by
  revert j
  decide +kernel
lemma waveExp0_13_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 13)).exp = waveExp0_13 j := by
  revert j
  decide +kernel
lemma waveExp0_16_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 16)).exp = waveExp0_16 j := by
  revert j
  decide +kernel
lemma waveExp0_19_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 19)).exp = waveExp0_19 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
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
def plusInverseBox (i j : Fin 20) : RI := (plusApproxBox i j).widen 10000000000000000000000000000000000000

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
lemma targetExp12_calc : (CI.ofReal (etaPiBox.mul (RI.point 12))).exp = targetExp12 := by decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def UminusCachedBox (i : Fin 20) (j : Fin 8) : RI := matrixMul plusInverseBox rhsMinusTable i j
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
lemma A1TableRow0_calc (j : Fin 8) : A1CachedBox 0 j = A1TableRow0 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_L1Matrix
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
def tailFixedColumn (c : Fin 23) : TailCoefficients :=
  column (fun p (_ : Unit) => jet (if c.val=22 then h else H) h p.1.val.val p.2 (finiteColumn c))
    (fun _ => by
      by_cases hc : c.val=22
      · have hh := (tail_atom_column_bounds 0 0 (finiteColumn c)).1
        simpa [hc,damping] using hh
      · have hh := (tail_atom_column_bounds 1 0 (finiteColumn c)).1
        simpa [hc,damping] using hh) ()
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ZBox_mem : ZBox.Mem Z := RI.mem_divNat (RI.mem_point 391) (by norm_num)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_DirectCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma Q_node_ne (n : Node) : Q n.val≠0 :=
  (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n.val n.property.2).1).ne'
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteTargetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Matrix
namespace AtomicTriangular.Construction
lemma Yf_residual (z : ℝ) (i : Fin 20) :
    (Yf *ᵥ actualParameter z) i+finiteResidual z i=
      gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ := by
  rw [Yf_actual]
  change (if i.val<8 then _ else 0)+(if i.val<8 then 0 else _)=_
  split_ifs <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma Roperator_apply (u : FiniteCoefficients) (i : Fin 20) :
    Roperator u i=∑ j : Fin 20,R i j*u j := by
  unfold Roperator
  erw [operator_apply,tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _
end AtomicTriangular.Construction
end

end OAI
end


