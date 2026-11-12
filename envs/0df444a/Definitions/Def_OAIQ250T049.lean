-- Prove2me | Definitions.Def_OAIQ250T049
-- name    : OAIQ250T049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:08:33.991626+00:00
-- url     : https://prove2.me/theorems/686063ea-b89e-4729-999f-f0dd41f480ac
-- title:
--   Definitions bundle OAIQ250T049 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 5 definitions and 13 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.Lplus`, `OAI.AtomicTriangular.FiniteCertificate.A1Table`, `OAI.AtomicTriangular.FiniteCertificate.A2Table`, `OAI.AtomicTriangular.FiniteCertificate.minusResidualTable`, `OAI.AtomicTriangular.FiniteCertificate.targetCoefficientBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_ParamA`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamA.lean), [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_PolytopeInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/PolytopeInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Construction_FiniteInterpolation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FiniteInterpolation.lean), [`Triangular_Construction_NodeJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/NodeJets.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T003`, `OAIQ250T004`, `OAIQ250T005`, `OAIQ250T006`, `OAIQ250T007`, `OAIQ250T008`, `OAIQ250T009` and `OAIQ250T010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T083`, `OAIQ250T084`, `OAIQ250T085`, `OAIQ250T086`, `OAIQ250T087`, `OAIQ250T098` and `OAIQ250T151`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T004
import Definitions.Def_OAIQ250T005
import Definitions.Def_OAIQ250T006
import Definitions.Def_OAIQ250T007
import Definitions.Def_OAIQ250T008
import Definitions.Def_OAIQ250T009
import Definitions.Def_OAIQ250T010

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction

theorem hasDerivAt_P_node (n : Node) : HasDerivAt P 0 (n.val : ℂ) := by
  have hh := (differentiable_rootProduct (n.val : ℂ)).hasDerivAt.pow 2
  have he : (rootProduct ^ 2) = P := funext fun s => (P_eq_square s).symm
  simpa [he, rootProduct_node] using hh

theorem deriv_P_node (n : Node) : deriv P n.val = 0 := (hasDerivAt_P_node n).deriv

theorem dBasis_node (n : Node) : dBasis n n.val = 0 := by
  simp [dBasis, dslope_same, deriv_P_node]

theorem dBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    dBasis n s = P s / (s-n.val) := by
  simp [dBasis, dslope_of_ne _ hs, slope_def_field, P_node]

theorem cBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    cBasis n s = P s / (s-n.val)^2 := by
  rw [cBasis, dslope_of_ne _ hs, slope_def_field, dBasis_node,
    sub_zero, dBasis_eq n hs, div_div, pow_two]

open Polynomial

end AtomicTriangular.Construction

end

end OAI
end

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
lemma waveExp0_3_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 3)).exp = waveExp0_3 j := by
  revert j
  decide +kernel
lemma waveExp0_4_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 4)).exp = waveExp0_4 j := by
  revert j
  decide +kernel
lemma waveExp0_7_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 7)).exp = waveExp0_7 j := by
  revert j
  decide +kernel
lemma waveExp0_9_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 9)).exp = waveExp0_9 j := by
  revert j
  decide +kernel
lemma waveExp1_12_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 12)).exp = waveExp1_12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
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
def minusResidualTable : Fin 20 → Fin 20 → RI := ![minusResidualRow0,minusResidualRow1,minusResidualRow2,minusResidualRow3,minusResidualRow4,minusResidualRow5,minusResidualRow6,minusResidualRow7,minusResidualRow8,minusResidualRow9,minusResidualRow10,minusResidualRow11,minusResidualRow12,minusResidualRow13,minusResidualRow14,minusResidualRow15,minusResidualRow16,minusResidualRow17,minusResidualRow18,minusResidualRow19]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamInterval
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamA
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
def A2Table : Fin 23 → Fin 8 → RI := ![A2TableRow0,A2TableRow1,A2TableRow2,A2TableRow3,A2TableRow4,A2TableRow5,A2TableRow6,A2TableRow7,A2TableRow8,A2TableRow9,A2TableRow10,A2TableRow11,A2TableRow12,A2TableRow13,A2TableRow14,A2TableRow15,A2TableRow16,A2TableRow17,A2TableRow18,A2TableRow19,A2TableRow20,A2TableRow21,A2TableRow22]
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
def Lplus : FiniteCoefficients →L[ℝ] FiniteCoefficients := l1Matrix (1-R)⁻¹
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_PolytopeInterval
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_NodeJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction

lemma P_cBasis (n : Node) : P = fun s => (s-(n.val:ℂ))^2*cBasis n s := by
  funext s
  by_cases hs : s = (n.val:ℂ)
  · simp [hs,P_node]
  · rw [cBasis_eq n hs]
    field_simp

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteInterpolation
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


