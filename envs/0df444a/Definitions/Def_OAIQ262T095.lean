-- Prove2me | Definitions.Def_OAIQ262T095
-- name    : OAIQ262T095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:51:38.474811+00:00
-- url     : https://prove2.me/theorems/03845100-bd1c-49c0-a784-8a7701d0d502
-- title:
--   Definitions bundle OAIQ262T095 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 78 declarations of OpenAI's Lean: 18 definitions and 60 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.inputJJet`, `OAI.AtomicTriangular.Construction.jetFunction`, `OAI.AtomicTriangular.Construction.pairJ`, `OAI.AtomicTriangular.Construction.pairJJet`, `OAI.AtomicTriangular.Construction.rawCurvatureColumn`, `OAI.AtomicTriangular.Construction.tailCurvatureCap`, `OAI.AtomicTriangular.Construction.transformedP`, `OAI.AtomicTriangular.Construction.waveAmplitudeFunction`, `OAI.AtomicTriangular.Construction.waveFunctionJet`, `OAI.AtomicTriangular.Construction.wavePhaseFunction`, `OAI.AtomicTriangular.FiniteCertificate.amplitudeNormBox`, `OAI.AtomicTriangular.FiniteCertificate.cVariationBox`, `OAI.AtomicTriangular.FiniteCertificate.curvatureBox`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable11`, `OAI.AtomicTriangular.FiniteCertificate.dVariationBox`, `OAI.AtomicTriangular.FiniteCertificate.rowAbsNumerator`, `OAI.AtomicTriangular.FiniteCertificate.rowLowerBox`, `OAI.AtomicTriangular.FiniteCertificate.targetEnvTablet`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_ParamA`, `Triangular_Certificate_ParamActual`, `Triangular_Certificate_ParamInterval`, `Triangular_Certificate_ParamNormBase`, `Triangular_Certificate_PolytopeInterval`, `Triangular_Certificate_TargetInterval`, `Triangular_Certificate_WaveExpData`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_ActualInput`, `Triangular_Construction_CurvatureBoxes`, `Triangular_Construction_CurvatureEnvelope`, `Triangular_Construction_FarCurvature`, `Triangular_Construction_FiniteInterpolation`, `Triangular_Construction_NormalizedJets`, `Triangular_Construction_SpectralJetBridge`, `Triangular_Construction_SpectralProduct`, `Triangular_Envelope_EnvelopeSums`, `Triangular_Envelope_TargetEnvelope`, `Triangular_Taylor_CurvatureData10`, `Triangular_Taylor_CurvatureData11`, `Triangular_Taylor_VariationBound`, `Triangular_Taylor_WaveFunction`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T007`, `OAIQ262T008`, `OAIQ262T009`, `OAIQ262T010`, `OAIQ262T011`, `OAIQ262T012`, `OAIQ262T013` and `OAIQ262T014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T142`, `OAIQ262T143`, `OAIQ262T144`, `OAIQ262T145`, `OAIQ262T146` and `OAIQ262T156`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T007
import Definitions.Def_OAIQ262T008
import Definitions.Def_OAIQ262T009
import Definitions.Def_OAIQ262T010
import Definitions.Def_OAIQ262T011
import Definitions.Def_OAIQ262T012
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T014

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

lemma fourier_node_deriv_cancel (n : Node) : waveDerivative 1 n.val = 0 := by
  rw [← (hasDerivAt_P n.val).deriv, deriv_P_node]

end AtomicTriangular.Construction

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
lemma waveExp1_9_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 9)).exp = waveExp1_9 j := by
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
lemma targetExp1_calc : (CI.ofReal (etaPiBox.mul (RI.point 1))).exp = targetExp1 := by decide +kernel
lemma targetExp3_calc : (CI.ofReal (etaPiBox.mul (RI.point 3))).exp = targetExp3 := by decide +kernel
lemma targetExp4_calc : (CI.ofReal (etaPiBox.mul (RI.point 4))).exp = targetExp4 := by decide +kernel
lemma targetExp7_calc : (CI.ofReal (etaPiBox.mul (RI.point 7))).exp = targetExp7 := by decide +kernel
lemma targetExp9_calc : (CI.ofReal (etaPiBox.mul (RI.point 9))).exp = targetExp9 := by decide +kernel
lemma targetExp13_calc : (CI.ofReal (etaPiBox.mul (RI.point 13))).exp = targetExp13 := by decide +kernel
lemma targetExp16_calc : (CI.ofReal (etaPiBox.mul (RI.point 16))).exp = targetExp16 := by decide +kernel
lemma targetExp19_calc : (CI.ofReal (etaPiBox.mul (RI.point 19))).exp = targetExp19 := by decide +kernel
lemma targetExp21_calc : (CI.ofReal (etaPiBox.mul (RI.point 21))).exp = targetExp21 := by decide +kernel
lemma gammaBox_mem (side : Fin 2) (i : Fin 3) (j : Fin 8) : (gammaBox side i j).Mem (gamma side i j) := by
  unfold gammaBox gamma
  split_ifs
  all_goals first
    | simpa using RI.mem_point 0
    | simpa using RI.mem_divNat (RI.mem_point 11) (by norm_num : 0<(25:ℕ))
    | simpa using RI.mem_neg (RI.mem_divNat (RI.mem_point 3) (by norm_num : 0<(500:ℕ)))
    | simpa using RI.mem_divNat (RI.mem_point 3) (by norm_num : 0<(500:ℕ))

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
lemma A1TableRow1_calc (j : Fin 8) : A1CachedBox 1 j = A1TableRow1 j := by
  revert j
  decide +kernel
lemma A1TableRow22_calc (j : Fin 8) : A1CachedBox 22 j = A1TableRow22 j := by
  revert j
  decide +kernel
lemma A2TableRow1_calc (j : Fin 8) : A2CachedBox 1 j = A2TableRow1 j := by
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
lemma boundV_calc (c : Fin 1) : RI.sum (fun j : Fin 31 => (envelopeSumBoxD j).mul (columnNorm22 j))=boundV c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
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

lemma WstarBox_mem : WstarBox.Mem Wstar := RI.mem_divNat (RI.mem_point 61) (by norm_num)
lemma DeltaStarBox_mem : DeltaStarBox.Mem DeltaStar := RI.mem_divNat (RI.mem_point 18) (by norm_num)
lemma UstarBox_mem : UstarBox.Mem Ustar := RI.mem_divNat (RI.mem_point 48) (by norm_num)
lemma PstarBox_mem : PstarBox.Mem Pstar := RI.mem_divNat (RI.mem_point 3) (by norm_num)
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamActual
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamNormBase
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
-- module Solutions.OAIQ262_TG.Triangular_Envelope_TargetEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate AtomicTriangular.L1Kernel

lemma targetEnvelope_enumerate (a : Fin 15) (l : ℕ) :
    targetEnvelope h (enumerateTail (a,l)).val.val =
      targetEnvelope h (tailBase a)*(Real.exp (-36/Z))^l := by
  unfold targetEnvelope
  rw [Q_enumerateTail,D_enumerateTail]
  simp only [sub_self,mul_zero,zero_mul,zero_add,zero_sub,abs_neg]
  change _ * Real.exp ((1-((tailBase a+36*(l:ℤ):ℤ):ℝ))/Z) = _
  rw [show (1-((tailBase a+36*(l:ℤ):ℤ):ℝ))/Z =
    (1-(tailBase a:ℝ))/Z+(l:ℝ)*(-36/Z) by push_cast; ring,
    Real.exp_add,Real.exp_nat_mul]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def targetEnvTablet : Fin 15 → RI := ![targetEnvt36,targetEnvt37,targetEnvt39,targetEnvt40,targetEnvt43,targetEnvt45,targetEnvt48,targetEnvt49,targetEnvt52,targetEnvt55,targetEnvt57,targetEnvt25,targetEnvt27,targetEnvt28,targetEnvt31]
lemma targetRatioBox_calc : (CI.ofReal ((RI.point (-36)).mul targetZBox.invPos)).exp.re=targetRatioBox := by decide +kernel
lemma tailTargetBox_calc : (RI.sum targetEnvTablet).mul (((RI.point 1).sub targetRatioBox).invPos)=tailTargetBox := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

lemma extendFiniteError_norm (u : FiniteCoefficients) : ‖extendFiniteError u‖=‖u‖ := by
  rw [l1_norm,l1_norm,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, |if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩|)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,abs_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 2

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def rawCurvatureColumn (br : Fin 2) (s : ℝ) (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, curvatureWave 1 br s (frequency j)*‖finiteColumn ⟨c.val,by omega⟩ j‖
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvaturePointBox_mem (i : Fin 5) : (curvaturePointBox i).Mem (curvaturePoint i) := by
  fin_cases i <;> (first | (simp [curvaturePointBox,curvaturePoint,RI.Mem,RI.point,RI.divNat,scale]; all_goals first | (norm_num [curvaturePointBox,curvaturePoint,RI.Mem,RI.point,RI.divNat,scale]; done) | rfl | decide) | (norm_num [curvaturePointBox,curvaturePoint,RI.Mem,RI.point,RI.divNat,scale]; done) | norm_num [curvaturePointBox,curvaturePoint,RI.Mem,RI.point,RI.divNat,scale])
def amplitudeNormBox (q br : Fin 2) (j : Fin 31) : RI :=
  if br.val=0 then RI.point 1 else if q.val=0 then lambdaNorm0 j else lambdaNorm1 j
def curvatureBox (q br : Fin 2) (i : Fin 5) (j : Fin 31) : RI :=
  ((taylorPhaseTable q br j).normSq.mul (amplitudeNormBox q br j)).mul
    (curvatureExpInput q br i j).exp.re
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData10_0_calc (j : Fin 31) : curvatureBox 1 0 0 j=curvatureData10_0 j := by
  revert j
  decide +kernel
lemma curvatureData10_0_pre (j : Fin 31) : (curvatureExpInput 1 0 0 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData10_1_calc (j : Fin 31) : curvatureBox 1 0 1 j=curvatureData10_1 j := by
  revert j
  decide +kernel
lemma curvatureData10_1_pre (j : Fin 31) : (curvatureExpInput 1 0 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData10_2_pre (j : Fin 31) : (curvatureExpInput 1 0 2 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData10_3_pre (j : Fin 31) : (curvatureExpInput 1 0 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData10_4_pre (j : Fin 31) : (curvatureExpInput 1 0 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData11_0_pre (j : Fin 31) : (curvatureExpInput 1 1 0 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
def curvatureTable11 : Fin 5 → Fin 31 → RI := ![curvatureData11_0,curvatureData11_1,curvatureData11_2,curvatureData11_3,curvatureData11_4]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_VariationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma varFreqBox_mem (j : Fin 31) : (varFreqBox j).Mem |frequency j| := by
  have hx := RI.mem_divNat (RI.mem_point (frequencyDistance j)) (by norm_num : 0<(18:ℕ))
  change ((RI.point (frequencyDistance j)).divNat 18).Mem _
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  fin_cases j <;> (first | (simp [frequencyDistance, frequency]; all_goals first | (norm_num [frequencyDistance, frequency]; done) | rfl | decide) | (norm_num [frequencyDistance, frequency]; done) | norm_num [frequencyDistance, frequency])
def cVariationBox : RI := ((RI.sum (fun j : Fin 31 => (columnNorm22 j).mul ((varFreqBox j).pow 2))).mul (piBox.pow 2)).divNat 2

def dVariationBox : RI := (RI.sum (fun j : Fin 31 => (columnNorm22 j).mul ((varFreqBox j).pow 1))).mul (piBox.pow 1)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_WaveFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def wavePhaseFunction (q br : Fin 2) : C(Spectrum,ℂ) :=
  if br.val=0 then frequencyFunction - ContinuousMap.const _ ((Real.pi*(damping q-h):ℝ):ℂ)
  else zetaFunction (damping q) h (damping_pos q)
def waveAmplitudeFunction (q br : Fin 2) : C(Spectrum,ℂ) :=
  if br.val=0 then 1 else lambdaFunction (damping q) (damping_pos q)
lemma wavePhaseFunction_apply (q br : Fin 2) (t : Spectrum) :
    wavePhaseFunction q br t=taylorPhase q br t.val := by
  fin_cases br <;> rfl
lemma waveAmplitudeFunction_apply (q br : Fin 2) (t : Spectrum) :
    waveAmplitudeFunction q br t=taylorAmplitude q br t.val := by
  fin_cases br <;> rfl

def waveFunctionJet (q br : Fin 2) (k : ℕ) (s : ℂ) : C(Spectrum,ℂ) :=
  waveAmplitudeFunction q br * NormedSpace.exp (s • wavePhaseFunction q br) * wavePhaseFunction q br^k
lemma waveFunctionJet_apply (q br : Fin 2) (k : ℕ) (s : ℂ) (t : Spectrum) :
    waveFunctionJet q br k s t=finiteWaveJet q br t.val k s := by
  simp only [waveFunctionJet,ContinuousMap.mul_apply,ContinuousMap.pow_apply,
    exponential_apply,ContinuousMap.smul_apply,smul_eq_mul,wavePhaseFunction_apply,
    waveAmplitudeFunction_apply,finiteWaveJet,mul_comm s]
lemma hasDerivAt_waveFunctionJet (q br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (waveFunctionJet q br k) (waveFunctionJet q br (k+1) s) s := by
  have hh := ((hasDerivAt_exp_smul_const (wavePhaseFunction q br) s).const_mul
    (waveAmplitudeFunction q br)).mul_const ((wavePhaseFunction q br)^k)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try simp only [waveFunctionJet,pow_succ])
  all_goals first | rfl | (ext t; simp [ContinuousMap.mul_apply,ContinuousMap.pow_apply]; ring)

lemma norm_finiteWaveJet_two (q br : Fin 2) (s t : ℝ) :
    ‖finiteWaveJet q br t 2 s‖=curvatureWave q br s t := by
  simp only [finiteWaveJet,norm_mul,norm_pow,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,curvatureWave]
  ring

def inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) : ℂ :=
  tailSpectral a (waveFunctionJet 0 br k s)+finiteSpectral a (waveFunctionJet 1 br k s)
def pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) : ℂ :=
  inputJJet a₁ 0 k s+inputJJet a₂ 1 k s
def pairJ (a₁ a₂ : InputCoefficients) (s : ℝ) : ℝ := (pairJJet a₁ a₂ 0 s).re
lemma hasDerivAt_inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (inputJJet a br k) (inputJJet a br (k+1) s) s := by
  exact ((tailSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)).add
    ((finiteSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 1 br k s))
lemma hasDerivAt_pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) :
    HasDerivAt (pairJJet a₁ a₂ k) (pairJJet a₁ a₂ (k+1) s) s :=
  (hasDerivAt_inputJJet a₁ 0 k s).add (hasDerivAt_inputJJet a₂ 1 k s)
lemma pairJ_contDiff (a₁ a₂ : InputCoefficients) : ContDiff ℝ ⊤ (pairJ a₁ a₂) := by
  have hh : Differentiable ℂ (pairJJet a₁ a₂ 0) := fun s => (hasDerivAt_pairJJet a₁ a₂ 0 s).differentiableAt
  exact hh.contDiff.real_of_complex
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

def tailCurvatureCap (br : Fin 2) (i : Fin 5) : ℝ :=
  curvatureWave 0 br (curvaturePoint i) (if br.val=1 ∧ i.val=0 then 0 else 5/6)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_NormalizedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction

def jetFunction (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) : C(Spectrum,ℂ) :=
  ⟨fun t => jetMultiplier (damping q) v n d t.val,
    (continuous_jetMultiplier (damping_pos q) v n d).comp continuous_subtype_val⟩
lemma jetFunction_apply (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) (t : Spectrum) :
    jetFunction q v n d t=jetMultiplier (damping q) v n d t.val := rfl

lemma negativeJet_linear (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (T (waveFunctionJet q 1 0 n)) (T (waveFunctionJet q 1 1 n))=
      T (jetFunction q v n d) := by
  have he : jetFunction q v n d =
      (exp (Real.pi*(v-h)*(n:ℂ))*(Q n:ℂ)⁻¹) •
        (if d.val=0 then -waveFunctionJet q 1 0 n else
          ((D n:ℂ)-Real.pi*(v-h)) • waveFunctionJet q 1 0 n-waveFunctionJet q 1 1 n) := by
    ext t
    simp only [ContinuousMap.smul_apply,smul_eq_mul,jetFunction_apply]
    split_ifs with hd
    · simpa only [negativeJet,hd,↓reduceIte,ContinuousMap.neg_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,waveFunctionJet_apply] using (negativeJet_wave q v n d t.val).symm
    · simpa only [negativeJet,hd,↓reduceIte,ContinuousMap.neg_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,waveFunctionJet_apply] using (negativeJet_wave q v n d t.val).symm
  rw [he]
  unfold negativeJet
  split_ifs <;> simp only [map_smul,map_neg,map_sub,smul_eq_mul]
lemma finiteSpectral_jet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (finiteSpectral (coefficientInput C a w) (jetFunction q v n d)).re=
      ∑ c : Fin 22, a c*jet (damping q) v n d (finiteColumn ⟨c.val,by omega⟩) := by
  rw [finiteSpectral_coefficient_apply]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [mul_re]
  simp only [ofReal_re,ofReal_im,zero_mul,sub_zero]
  congr 1
  unfold jet
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [jetFunction_apply,mul_comm]
lemma spectralP_jet (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (spectralP (jetFunction q v n d)).re=jet (damping q) v n d (finiteColumn 22) := by
  unfold spectralP jet
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change fourierCoeff j*jetMultiplier _ _ _ _ _ = jetMultiplier _ _ _ _ _*fourierCoeff j
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_SpectralJetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma spectralC_of_restriction (n : Node) (f : C(Spectrum,ℂ)) (g : ℝ → ℂ)
    (hg : ∀ t (ht : t∈Spectrum), f ⟨t,ht⟩=g t) : spectralC n f=spectralCVector n.val g := by
  unfold spectralC spectralCVector
  apply Finset.sum_congr rfl
  intro l _
  simp only [smul_eq_mul]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  change ((frequency l:ℂ)-(t:ℂ))*exp (-I*Real.pi*(t:ℂ)*(n.val:ℂ))*extend f t =
    (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*(n.val:ℂ))*g t)
  have hm := interval_frequency_subset l ht
  rw [extend_on f t hm,hg]
  simp only [Complex.real_smul,ofReal_sub]
  ring
lemma spectralD_of_restriction (n : Node) (f : C(Spectrum,ℂ)) (g : ℝ → ℂ)
    (hg : ∀ t (ht : t∈Spectrum), f ⟨t,ht⟩=g t) : spectralD n f=spectralDVector n.val g := by
  unfold spectralD spectralDVector
  apply Finset.sum_congr rfl
  intro l _
  simp only [smul_eq_mul]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  have hm := interval_frequency_subset l ht
  rw [extend_on f t hm,hg]
lemma spectralC_jetFunction (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (n : Node) :
    spectralC n (jetFunction q v m d)=(tailJetVector (damping q) v m n.val 0 d) := by
  rw [spectralC_of_restriction n _ (jetMultiplier (damping q) v m d) (fun _ _ => rfl)]
  symm
  exact spectralCVector_map (PiLp.proj 1 (fun _ : Fin 2 => ℂ) d) n.val _ (continuous_jetVector (damping_pos q) v m)
lemma spectralD_jetFunction (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (n : Node) :
    spectralD n (jetFunction q v m d)=(tailJetVector (damping q) v m n.val 1 d) := by
  rw [spectralD_of_restriction n _ (jetMultiplier (damping q) v m d) (fun _ _ => rfl)]
  symm
  exact spectralDVector_map (PiLp.proj 1 (fun _ : Fin 2 => ℂ) d) n.val _ (continuous_jetVector (damping_pos q) v m)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_SpectralProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

lemma tailColumnSpectral_jet (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (p : TailNode × Fin 2) :
    (tailColumnSpectral p (jetFunction q v m d)).re=tailJet (damping q) v m p.1.val.val p.2 d := by
  unfold tailColumnSpectral tailJet tailJetVector
  split_ifs with hc
  · rw [spectralCCLM_apply,spectralC_jetFunction]
    rfl
  · rw [spectralDCLM_apply,spectralD_jetFunction]
    rfl
lemma inputJJet_negative (a : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (inputJJet a 1 0 n) (inputJJet a 1 1 n)=
      tailSpectral a (jetFunction 0 v n d)+finiteSpectral a (jetFunction 1 v n d) := by
  unfold inputJJet
  rw [negativeJet_add,negativeJet_linear,negativeJet_linear]
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
lemma extendFiniteError_fixed (u : FiniteCoefficients) (i : Fin 2) :
    extendFiniteError u ⟨i.val,by omega⟩=0 := by
  change (if hi : i.val<2 then _ else _)=_
  simp only [i.isLt,↓reduceDIte]
lemma extendFiniteError_shift (u : FiniteCoefficients) (i : Fin 20) :
    extendFiniteError u ⟨i.val+2,by omega⟩=u i := by
  change (if hi : i.val+2<2 then 0 else u ⟨i.val+2-2,by omega⟩)=_
  simp only [show ¬(i.val+2<2) by omega,↓reduceDIte]
  congr 1
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FarCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def transformedP (s : ℝ) : ℝ := (spectralPCLM (waveFunctionJet 0 1 0 s)).re
lemma hasDerivAt_spectralP_wave (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (fun t => spectralPCLM (waveFunctionJet 0 br k t))
      (spectralPCLM (waveFunctionJet 0 br (k+1) s)) s :=
  spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)
lemma transformedP_contDiff : ContDiff ℝ ⊤ transformedP := by
  exact (show Differentiable ℂ (fun s => spectralPCLM (waveFunctionJet 0 1 0 s)) from
    fun s => (hasDerivAt_spectralP_wave 1 0 s).differentiableAt).contDiff.real_of_complex
end AtomicTriangular.Construction
end

end OAI
end


