-- Prove2me | Definitions.Def_OAIQ257X010
-- name    : OAIQ257X010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:53:19.147293+00:00
-- url     : https://prove2.me/theorems/d75c863d-2fba-45d0-99e7-a226eb773629
-- title:
--   Definitions bundle OAIQ257X010 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.minusResidualTable`, `OAI.AtomicTriangular.FiniteCertificate.plusApproxBox`, `OAI.AtomicTriangular.FiniteCertificate.plusResidualBox`, `OAI.AtomicTriangular.FiniteCertificate.plusResidualTable`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean).
--
--   **Imports.** It imports the bundles `OAIQ257X008` and `OAIQ257X009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ257X011`; the statements `OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.plusResidualBox_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.plusResidualTable_mem_x`; the proofs of `OAI.AtomicTriangular.Construction.actualFiniteError_equations_x`, `OAI.AtomicTriangular.Construction.actualTail_full_equations_x`, `OAI.AtomicTriangular.Construction.finiteSolution_equations_x`, `OAI.AtomicTriangular.FiniteCertificate.minusInverse_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.plusResidualBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.plusResidualTable_mem_x` and `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ257X008
import Definitions.Def_OAIQ257X009

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
def plusApproxBox (i j : Fin 20) : RI := RI.singleton (plusApproxNum i j)
def plusResidualBox (i j : Fin 20) : RI :=
  (matrixMul plusApproxBox plusBlockBox i j).sub (matrixOne i j)
def plusResidualTable : Fin 20 → Fin 20 → RI := ![plusResidualRow0,plusResidualRow1,plusResidualRow2,plusResidualRow3,plusResidualRow4,plusResidualRow5,plusResidualRow6,plusResidualRow7,plusResidualRow8,plusResidualRow9,plusResidualRow10,plusResidualRow11,plusResidualRow12,plusResidualRow13,plusResidualRow14,plusResidualRow15,plusResidualRow16,plusResidualRow17,plusResidualRow18,plusResidualRow19]

end AtomicTriangular.FiniteCertificate
end

end OAI
end


