-- Prove2me | Definitions.Def_OAIQ250T050
-- name    : OAIQ250T050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:11:32.381427+00:00
-- url     : https://prove2.me/theorems/0cbffd1e-b36c-49a6-ab4b-6651138b7bae
-- title:
--   Definitions bundle OAIQ250T050 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 92 declarations of OpenAI's Lean: 7 definitions and 85 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.dVariationBox`, `OAI.AtomicTriangular.FiniteCertificate.ex1b`, `OAI.AtomicTriangular.FiniteCertificate.rowAbsNumerator`, `OAI.AtomicTriangular.FiniteCertificate.rowLowerBox`, `OAI.AtomicTriangular.FiniteCertificate.targetEnvBox`, `OAI.AtomicTriangular.FiniteCertificate.targetExpInput`, `OAI.AtomicTriangular.FiniteCertificate.taylorPhaseBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_ParamActual`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamActual.lean), [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_ParamNormBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamNormBase.lean), [`Triangular_Certificate_PolytopeInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/PolytopeInterval.lean), [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Construction_CurvatureSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureSums.lean), [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Taylor_CurvatureData10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData10.lean), [`Triangular_Taylor_CurvatureData11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData11.lean), [`Triangular_Taylor_TaylorPhase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorPhase.lean), [`Triangular_Taylor_VariationBound`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/VariationBound.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T015`, `OAIQ250T016`, `OAIQ250T017`, `OAIQ250T018`, `OAIQ250T019`, `OAIQ250T020`, `OAIQ250T022`, `OAIQ250T023`, `OAIQ250T024` and `OAIQ250T149` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T084`, `OAIQ250T085`, `OAIQ250T086` and `OAIQ250T151`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T015
import Definitions.Def_OAIQ250T016
import Definitions.Def_OAIQ250T017
import Definitions.Def_OAIQ250T018
import Definitions.Def_OAIQ250T019
import Definitions.Def_OAIQ250T020
import Definitions.Def_OAIQ250T022
import Definitions.Def_OAIQ250T023
import Definitions.Def_OAIQ250T024
import Definitions.Def_OAIQ250T149

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

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

lemma RI.mem_min {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.imin b).Mem (min x y) := by
  constructor
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.1 hy.1
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.2 hy.2

end
end AtomicTriangular.Interval

end
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma parameterExpBox2_calc :
    (CI.ofReal ((RI.point (-2)).mul ZBox.invPos)).exp.re = parameterExpBox2 := by decide +kernel
lemma parameterExpBox3_calc :
    (CI.ofReal ((RI.point (-3)).mul ZBox.invPos)).exp.re = parameterExpBox3 := by decide +kernel
lemma parameterExpBox6_calc :
    (CI.ofReal ((RI.point (-6)).mul ZBox.invPos)).exp.re = parameterExpBox6 := by decide +kernel
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
lemma etaPiBox_mem : etaPiBox.Mem (Real.pi*eta) := by
  apply RI.mem_mul piBox_mem
  simpa [eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<(5:ℕ))
lemma targetExp1_calc : (CI.ofReal (etaPiBox.mul (RI.point 1))).exp = targetExp1 := by decide +kernel
lemma targetExp1_mem : targetExp1.Mem (Complex.exp ((Real.pi*eta*(1:ℤ):ℝ):ℂ)) := by
  rw [← targetExp1_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 1))
  · decide +kernel
lemma targetExp3_calc : (CI.ofReal (etaPiBox.mul (RI.point 3))).exp = targetExp3 := by decide +kernel
lemma targetExp3_mem : targetExp3.Mem (Complex.exp ((Real.pi*eta*(3:ℤ):ℝ):ℂ)) := by
  rw [← targetExp3_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 3))
  · decide +kernel
lemma targetExp4_calc : (CI.ofReal (etaPiBox.mul (RI.point 4))).exp = targetExp4 := by decide +kernel
lemma targetExp4_mem : targetExp4.Mem (Complex.exp ((Real.pi*eta*(4:ℤ):ℝ):ℂ)) := by
  rw [← targetExp4_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 4))
  · decide +kernel
lemma targetExp7_calc : (CI.ofReal (etaPiBox.mul (RI.point 7))).exp = targetExp7 := by decide +kernel
lemma targetExp7_mem : targetExp7.Mem (Complex.exp ((Real.pi*eta*(7:ℤ):ℝ):ℂ)) := by
  rw [← targetExp7_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 7))
  · decide +kernel
lemma targetExp9_calc : (CI.ofReal (etaPiBox.mul (RI.point 9))).exp = targetExp9 := by decide +kernel
lemma targetExp9_mem : targetExp9.Mem (Complex.exp ((Real.pi*eta*(9:ℤ):ℝ):ℂ)) := by
  rw [← targetExp9_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 9))
  · decide +kernel
lemma targetExp12_calc : (CI.ofReal (etaPiBox.mul (RI.point 12))).exp = targetExp12 := by decide +kernel
lemma targetExp12_mem : targetExp12.Mem (Complex.exp ((Real.pi*eta*(12:ℤ):ℝ):ℂ)) := by
  rw [← targetExp12_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 12))
  · decide +kernel
lemma targetExp13_calc : (CI.ofReal (etaPiBox.mul (RI.point 13))).exp = targetExp13 := by decide +kernel
lemma targetExp13_mem : targetExp13.Mem (Complex.exp ((Real.pi*eta*(13:ℤ):ℝ):ℂ)) := by
  rw [← targetExp13_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 13))
  · decide +kernel
lemma targetExp16_calc : (CI.ofReal (etaPiBox.mul (RI.point 16))).exp = targetExp16 := by decide +kernel
lemma targetExp16_mem : targetExp16.Mem (Complex.exp ((Real.pi*eta*(16:ℤ):ℝ):ℂ)) := by
  rw [← targetExp16_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 16))
  · decide +kernel
lemma targetExp19_calc : (CI.ofReal (etaPiBox.mul (RI.point 19))).exp = targetExp19 := by decide +kernel
lemma targetExp19_mem : targetExp19.Mem (Complex.exp ((Real.pi*eta*(19:ℤ):ℝ):ℂ)) := by
  rw [← targetExp19_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 19))
  · decide +kernel
lemma targetExp21_calc : (CI.ofReal (etaPiBox.mul (RI.point 21))).exp = targetExp21 := by decide +kernel
lemma targetExp21_mem : targetExp21.Mem (Complex.exp ((Real.pi*eta*(21:ℤ):ℝ):ℂ)) := by
  rw [← targetExp21_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 21))
  · decide +kernel
lemma targetExpTable_mem (n : Fin 10) : (targetExpTable n).Mem (Complex.exp ((Real.pi*eta*(finiteNode n):ℝ):ℂ)) := by
  fin_cases n
  · exact targetExp1_mem
  · exact targetExp3_mem
  · exact targetExp4_mem
  · exact targetExp7_mem
  · exact targetExp9_mem
  · exact targetExp12_mem
  · exact targetExp13_mem
  · exact targetExp16_mem
  · exact targetExp19_mem
  · exact targetExp21_mem

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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma targetRateBox_mem (q : Fin 2) : (targetRateBox q).Mem (Real.pi*(damping q-h)) := by
  fin_cases q
  · simpa [targetRateBox,damping] using ri0_mem
  · convert RI.mem_mul piBox_mem (RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5)) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [targetRateBox,damping,H,h])
def targetExpInput (q : Fin 2) (n : ℤ) : RI :=
  ((targetRateBox q).mul (RI.point n)).add ((RI.point (1-n)).mul targetZBox.invPos)
def targetEnvBox (q : Fin 2) (qb db eb : RI) : RI :=
  ((QBox1.mul qb.invPos).mul (((RI.point 1).add targetZBox).add
    (targetZBox.mul ((targetRateBox q).sub db).abs))).mul eb
lemma targetExpf9_calc : (CI.ofReal (targetExpInput 1 9)).exp.re=targetExpf9 := by decide +kernel
lemma targetEnvf9_calc : targetEnvBox 1 QBox9 DBox9 targetExpf9=targetEnvf9 := by decide +kernel
lemma targetExpf12_calc : (CI.ofReal (targetExpInput 1 12)).exp.re=targetExpf12 := by decide +kernel
lemma targetEnvf12_calc : targetEnvBox 1 QBox12 DBox12 targetExpf12=targetEnvf12 := by decide +kernel
lemma targetExpf13_calc : (CI.ofReal (targetExpInput 1 13)).exp.re=targetExpf13 := by decide +kernel
lemma targetEnvf13_calc : targetEnvBox 1 QBox13 DBox13 targetExpf13=targetEnvf13 := by decide +kernel
lemma targetExpf16_calc : (CI.ofReal (targetExpInput 1 16)).exp.re=targetExpf16 := by decide +kernel
lemma targetEnvf16_calc : targetEnvBox 1 QBox16 DBox16 targetExpf16=targetEnvf16 := by decide +kernel
lemma targetExpf19_calc : (CI.ofReal (targetExpInput 1 19)).exp.re=targetExpf19 := by decide +kernel
lemma targetEnvf19_calc : targetEnvBox 1 QBox19 DBox19 targetExpf19=targetEnvf19 := by decide +kernel
lemma targetExpf21_calc : (CI.ofReal (targetExpInput 1 21)).exp.re=targetExpf21 := by decide +kernel
lemma targetEnvf21_calc : targetEnvBox 1 QBox21 DBox21 targetExpf21=targetEnvf21 := by decide +kernel
lemma targetExpt36_calc : (CI.ofReal (targetExpInput 0 36)).exp.re=targetExpt36 := by decide +kernel
lemma targetEnvt36_calc : targetEnvBox 0 QBox0 DBox0 targetExpt36=targetEnvt36 := by decide +kernel
lemma targetExpt37_calc : (CI.ofReal (targetExpInput 0 37)).exp.re=targetExpt37 := by decide +kernel
lemma targetEnvt37_calc : targetEnvBox 0 QBox1 DBox1 targetExpt37=targetEnvt37 := by decide +kernel
lemma targetExpt39_calc : (CI.ofReal (targetExpInput 0 39)).exp.re=targetExpt39 := by decide +kernel
lemma targetEnvt39_calc : targetEnvBox 0 QBox3 DBox3 targetExpt39=targetEnvt39 := by decide +kernel
lemma targetExpt40_calc : (CI.ofReal (targetExpInput 0 40)).exp.re=targetExpt40 := by decide +kernel
lemma targetEnvt40_calc : targetEnvBox 0 QBox4 DBox4 targetExpt40=targetEnvt40 := by decide +kernel
lemma targetExpt43_calc : (CI.ofReal (targetExpInput 0 43)).exp.re=targetExpt43 := by decide +kernel
lemma targetEnvt43_calc : targetEnvBox 0 QBox7 DBox7 targetExpt43=targetEnvt43 := by decide +kernel
lemma targetExpt45_calc : (CI.ofReal (targetExpInput 0 45)).exp.re=targetExpt45 := by decide +kernel
lemma targetEnvt45_calc : targetEnvBox 0 QBox9 DBox9 targetExpt45=targetEnvt45 := by decide +kernel
lemma targetExpt48_calc : (CI.ofReal (targetExpInput 0 48)).exp.re=targetExpt48 := by decide +kernel
lemma targetEnvt48_calc : targetEnvBox 0 QBox12 DBox12 targetExpt48=targetEnvt48 := by decide +kernel
lemma targetExpt49_calc : (CI.ofReal (targetExpInput 0 49)).exp.re=targetExpt49 := by decide +kernel
lemma targetEnvt49_calc : targetEnvBox 0 QBox13 DBox13 targetExpt49=targetEnvt49 := by decide +kernel
lemma targetExpt52_calc : (CI.ofReal (targetExpInput 0 52)).exp.re=targetExpt52 := by decide +kernel
lemma targetEnvt52_calc : targetEnvBox 0 QBox16 DBox16 targetExpt52=targetEnvt52 := by decide +kernel
lemma targetExpt55_calc : (CI.ofReal (targetExpInput 0 55)).exp.re=targetExpt55 := by decide +kernel
lemma targetEnvt55_calc : targetEnvBox 0 QBox19 DBox19 targetExpt55=targetEnvt55 := by decide +kernel
lemma targetExpt57_calc : (CI.ofReal (targetExpInput 0 57)).exp.re=targetExpt57 := by decide +kernel
lemma targetEnvt57_calc : targetEnvBox 0 QBox21 DBox21 targetExpt57=targetEnvt57 := by decide +kernel
lemma targetExpt25_calc : (CI.ofReal (targetExpInput 0 25)).exp.re=targetExpt25 := by decide +kernel
lemma targetEnvt25_calc : targetEnvBox 0 QBox25 DBox25 targetExpt25=targetEnvt25 := by decide +kernel
lemma targetExpt27_calc : (CI.ofReal (targetExpInput 0 27)).exp.re=targetExpt27 := by decide +kernel
lemma targetEnvt27_calc : targetEnvBox 0 QBox27 DBox27 targetExpt27=targetEnvt27 := by decide +kernel
lemma targetExpt28_calc : (CI.ofReal (targetExpInput 0 28)).exp.re=targetExpt28 := by decide +kernel
lemma targetEnvt28_calc : targetEnvBox 0 QBox28 DBox28 targetExpt28=targetEnvt28 := by decide +kernel
lemma targetExpt31_calc : (CI.ofReal (targetExpInput 0 31)).exp.re=targetExpt31 := by decide +kernel
lemma targetEnvt31_calc : targetEnvBox 0 QBox31 DBox31 targetExpt31=targetEnvt31 := by decide +kernel
lemma targetRatioBox_calc : (CI.ofReal ((RI.point (-36)).mul targetZBox.invPos)).exp.re=targetRatioBox := by decide +kernel
lemma tailTargetBox_calc : (RI.sum targetEnvTablet).mul (((RI.point 1).sub targetRatioBox).invPos)=tailTargetBox := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorPhase
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
lemma taylorPhase0_0_calc (j : Fin 31) : taylorPhaseBox 0 0 j = taylorPhase0_0 j := by
  revert j
  decide +kernel
lemma taylorPhase0_1_calc (j : Fin 31) : taylorPhaseBox 0 1 j = taylorPhase0_1 j := by
  revert j
  decide +kernel
lemma taylorPhase1_0_calc (j : Fin 31) : taylorPhaseBox 1 0 j = taylorPhase1_0 j := by
  revert j
  decide +kernel
lemma taylorPhase1_1_calc (j : Fin 31) : taylorPhaseBox 1 1 j = taylorPhase1_1 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData10_4_calc (j : Fin 31) : curvatureBox 1 0 4 j=curvatureData10_4 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData11_0_calc (j : Fin 31) : curvatureBox 1 1 0 j=curvatureData11_0 j := by
  revert j
  decide +kernel
lemma curvatureData11_1_calc (j : Fin 31) : curvatureBox 1 1 1 j=curvatureData11_1 j := by
  revert j
  decide +kernel
lemma curvatureData11_2_calc (j : Fin 31) : curvatureBox 1 1 2 j=curvatureData11_2 j := by
  revert j
  decide +kernel
lemma curvatureData11_2_pre (j : Fin 31) : (curvatureExpInput 1 1 2 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData11_3_calc (j : Fin 31) : curvatureBox 1 1 3 j=curvatureData11_3 j := by
  revert j
  decide +kernel
lemma curvatureData11_3_pre (j : Fin 31) : (curvatureExpInput 1 1 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData11_4_calc (j : Fin 31) : curvatureBox 1 1 4 j=curvatureData11_4 j := by
  revert j
  decide +kernel
lemma curvatureData11_4_pre (j : Fin 31) : (curvatureExpInput 1 1 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureTail0_calc : ((curvatureTable00 0 30).add (curvatureTable01 0 15)).mul (RI.point 60)=curvatureTail0 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def ex1b : Fin 23 → Fin 8 → RI := ![ex1b0,ex1b1,ex1b2,ex1b3,ex1b4,ex1b5,ex1b6,ex1b7,ex1b8,ex1b9,ex1b10,ex1b11,ex1b12,ex1b13,ex1b14,ex1b15,ex1b16,ex1b17,ex1b18,ex1b19,ex1b20,ex1b21,ex1b22]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_VariationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def dVariationBox : RI := (RI.sum (fun j : Fin 31 => (columnNorm22 j).mul ((varFreqBox j).pow 1))).mul (piBox.pow 1)

end AtomicTriangular.FiniteCertificate
end

end OAI
end


