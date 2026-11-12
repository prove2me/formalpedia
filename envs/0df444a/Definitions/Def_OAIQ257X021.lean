-- Prove2me | Definitions.Def_OAIQ257X021
-- name    : OAIQ257X021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T04:07:15.963069+00:00
-- url     : https://prove2.me/theorems/52b058c1-a1c1-4c96-b7f1-59528e591703
-- title:
--   Definitions bundle OAIQ257X021 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs1_5_0`, `OAI.AtomicTriangular.FiniteCertificate.curvatureBox`, `OAI.AtomicTriangular.FiniteCertificate.remainderBox`, `OAI.AtomicTriangular.FiniteCertificate.remainderExpInput`, `OAI.AtomicTriangular.FiniteCertificate.rowAbsNumerator`, `OAI.AtomicTriangular.FiniteCertificate.rowLowerBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_ParamNormBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamNormBase.lean), [`Triangular_Certificate_PolytopeInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/PolytopeInterval.lean), [`Triangular_Construction_CurvatureBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureBoxes.lean), [`Triangular_Signs_RemainderBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderBoxes.lean), [`Triangular_Signs_Signs15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs15.lean).
--
--   **Imports.** It imports the bundles `OAIQ257X011` and `OAIQ257X020` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.AtomicTriangular.FiniteCertificate.curvatureBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_3_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_4_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData6_10_calc_x` and `OAI.AtomicTriangular.FiniteCertificate.remainderData6_11_calc_x`; the proofs of `OAI.AtomicTriangular.Construction.exceptional_rational_comparison_x`, `OAI.AtomicTriangular.Construction.finiteApprox_norm_x`, `OAI.AtomicTriangular.Construction.finiteTaylor_error_x`, `OAI.AtomicTriangular.Construction.near_negative_polynomial_x`, `OAI.AtomicTriangular.Construction.near_positive_polynomial_x`, `OAI.AtomicTriangular.Construction.tailCurvatureCap_sum_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData10_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData10_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData10_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData10_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_3_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_4_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_2_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_2_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_3_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_3_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_5_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_5_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_6_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_6_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_0_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_0_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_1_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_1_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_3_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_1_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns4_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns5_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns5_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns6_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns6_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst0_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_00_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_00_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_00_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_00_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData6_10_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData6_11_calc_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable2_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable3_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable4_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable5_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable6_x` and `OAI.AtomicTriangular.FiniteCertificate.remainder_table_x`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X020

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

def rowLowerBox (a : Fin 8 → RI) : RI :=
  (((((a 1).add (ZBox.mul ((RI.point 0).imin (a 0)))).add
  (DeltaStarBox.mul ((RI.point 0).imin (a 2).neg))).add
  (WstarBox.mul ((RI.point 0).imin ((a 3).add (ZBox.mul (a 2)))))).add
  (UstarBox.mul ((RI.point 0).imin ((a 5).imin ((a 5).add (ZBox.mul (a 4))))))).add
  (PstarBox.mul (((RI.point 0).imin (a 6)).add ((RI.point 0).imin (a 7))))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamNormBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def rowAbsNumerator (a : Fin 8 → RI) : ℤ :=
  max (-(rowLowerBox a).lo) (-(rowLowerBox (fun i => (a i).neg)).lo)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def curvatureBox (q br : Fin 2) (i : Fin 5) (j : Fin 31) : RI :=
  ((taylorPhaseTable q br j).normSq.mul (amplitudeNormBox q br j)).mul
    (curvatureExpInput q br i j).exp.re
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderExpInput (q br : Fin 2) (n : Fin 7) (j : Fin 31) : CI :=
  CI.ofReal ((taylorPhaseTable q br j).re.mul (RI.point (nearNode n)))
def remainderBox (q br : Fin 2) (n : Fin 7) (j : Fin 31) (dnorm : RI) : RI :=
  (((((taylorPhaseTable q br j).normSq.mul (amplitudeNormBox q br j)).mul
    (remainderExpInput q br n j).exp.re).mul (((nearRadiusBox n).mul dnorm).pow 21)).divNat (23).factorial).mul
    ((RI.point 1).sub (((nearRadiusBox n).mul dnorm).divNat 24)).invPos
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_5_0 : Fin 21 → Fin 8 → RI := ![bs1_5_0_0,bs1_5_0_1,bs1_5_0_2,bs1_5_0_3,bs1_5_0_4,bs1_5_0_5,bs1_5_0_6,bs1_5_0_7,bs1_5_0_8,bs1_5_0_9,bs1_5_0_10,bs1_5_0_11,bs1_5_0_12,bs1_5_0_13,bs1_5_0_14,bs1_5_0_15,bs1_5_0_16,bs1_5_0_17,bs1_5_0_18,bs1_5_0_19,bs1_5_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


