-- Prove2me | Definitions.Def_OAIQ250T149
-- name    : OAIQ250T149
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:04:59.600231+00:00
-- url     : https://prove2.me/theorems/5235db24-ab2e-4d9f-b0be-860dc7b85a63
-- title:
--   Definitions bundle OAIQ250T149 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 80 declarations of OpenAI's Lean: 9 definitions and 71 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.jetFunction`, `OAI.AtomicTriangular.Construction.rawTailCurvature`, `OAI.AtomicTriangular.Construction.tailTarget`, `OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox`, `OAI.AtomicTriangular.FiniteCertificate.amplitudeNormBox`, `OAI.AtomicTriangular.FiniteCertificate.cVariationBox`, `OAI.AtomicTriangular.FiniteCertificate.curvatureBox`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable11`, `OAI.AtomicTriangular.FiniteCertificate.plusInverseBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_Inverse`, `Triangular_Certificate_ParamA`, `Triangular_Certificate_ParamU`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_ActualInput`, `Triangular_Construction_CurvatureAnalytic`, `Triangular_Construction_CurvatureBoxes`, `Triangular_Construction_CurvatureEnvelope`, `Triangular_Construction_CurvatureSums`, `Triangular_Construction_FiniteInterpolation`, `Triangular_Construction_FiniteTargetBridge`, `Triangular_Construction_NormalizedJets`, `Triangular_Construction_SpectralJetBridge`, `Triangular_Construction_SpectralProduct`, `Triangular_Envelope_EnvelopeSums`, `Triangular_Envelope_TargetEnvelope`, `Triangular_Taylor_CoefficientSpectral`, `Triangular_Taylor_CurvatureData00`, `Triangular_Taylor_CurvatureData10`, `Triangular_Taylor_CurvatureData11`, `Triangular_Taylor_VariationBound`, `Triangular_Taylor_WaveFunction`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T003`, `OAIQ250T004`, `OAIQ250T005`, `OAIQ250T006`, `OAIQ250T007`, `OAIQ250T008`, `OAIQ250T009`, `OAIQ250T010` and `OAIQ250T011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T050`.
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
import Definitions.Def_OAIQ250T011

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
def plusInverseBox (i j : Fin 20) : RI := (plusApproxBox i j).widen 10000000000000000000000000000000000000

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamU
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
lemma UminusTableRow0_calc (j : Fin 8) : UminusCachedBox 0 j = UminusTableRow0 j := by
  revert j
  decide +kernel
lemma UminusTableRow1_calc (j : Fin 8) : UminusCachedBox 1 j = UminusTableRow1 j := by
  revert j
  decide +kernel
lemma UminusTableRow2_calc (j : Fin 8) : UminusCachedBox 2 j = UminusTableRow2 j := by
  revert j
  decide +kernel
lemma UminusTableRow3_calc (j : Fin 8) : UminusCachedBox 3 j = UminusTableRow3 j := by
  revert j
  decide +kernel
lemma UminusTableRow4_calc (j : Fin 8) : UminusCachedBox 4 j = UminusTableRow4 j := by
  revert j
  decide +kernel
lemma UminusTableRow5_calc (j : Fin 8) : UminusCachedBox 5 j = UminusTableRow5 j := by
  revert j
  decide +kernel
lemma UminusTableRow6_calc (j : Fin 8) : UminusCachedBox 6 j = UminusTableRow6 j := by
  revert j
  decide +kernel
lemma UminusTableRow7_calc (j : Fin 8) : UminusCachedBox 7 j = UminusTableRow7 j := by
  revert j
  decide +kernel
lemma UminusTableRow8_calc (j : Fin 8) : UminusCachedBox 8 j = UminusTableRow8 j := by
  revert j
  decide +kernel
lemma UminusTableRow9_calc (j : Fin 8) : UminusCachedBox 9 j = UminusTableRow9 j := by
  revert j
  decide +kernel
lemma UminusTableRow10_calc (j : Fin 8) : UminusCachedBox 10 j = UminusTableRow10 j := by
  revert j
  decide +kernel
lemma UminusTableRow11_calc (j : Fin 8) : UminusCachedBox 11 j = UminusTableRow11 j := by
  revert j
  decide +kernel
lemma UminusTableRow12_calc (j : Fin 8) : UminusCachedBox 12 j = UminusTableRow12 j := by
  revert j
  decide +kernel
lemma UminusTableRow13_calc (j : Fin 8) : UminusCachedBox 13 j = UminusTableRow13 j := by
  revert j
  decide +kernel
lemma UminusTableRow14_calc (j : Fin 8) : UminusCachedBox 14 j = UminusTableRow14 j := by
  revert j
  decide +kernel
lemma UminusTableRow15_calc (j : Fin 8) : UminusCachedBox 15 j = UminusTableRow15 j := by
  revert j
  decide +kernel
lemma UminusTableRow16_calc (j : Fin 8) : UminusCachedBox 16 j = UminusTableRow16 j := by
  revert j
  decide +kernel
lemma UminusTableRow17_calc (j : Fin 8) : UminusCachedBox 17 j = UminusTableRow17 j := by
  revert j
  decide +kernel
lemma UminusTableRow18_calc (j : Fin 8) : UminusCachedBox 18 j = UminusTableRow18 j := by
  revert j
  decide +kernel
lemma UminusTableRow19_calc (j : Fin 8) : UminusCachedBox 19 j = UminusTableRow19 j := by
  revert j
  decide +kernel
lemma UminusTable_calc (i : Fin 20) (j : Fin 8) : UminusCachedBox i j = UminusTable i j := by
  fin_cases i
  · exact UminusTableRow0_calc j
  · exact UminusTableRow1_calc j
  · exact UminusTableRow2_calc j
  · exact UminusTableRow3_calc j
  · exact UminusTableRow4_calc j
  · exact UminusTableRow5_calc j
  · exact UminusTableRow6_calc j
  · exact UminusTableRow7_calc j
  · exact UminusTableRow8_calc j
  · exact UminusTableRow9_calc j
  · exact UminusTableRow10_calc j
  · exact UminusTableRow11_calc j
  · exact UminusTableRow12_calc j
  · exact UminusTableRow13_calc j
  · exact UminusTableRow14_calc j
  · exact UminusTableRow15_calc j
  · exact UminusTableRow16_calc j
  · exact UminusTableRow17_calc j
  · exact UminusTableRow18_calc j
  · exact UminusTableRow19_calc j
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
lemma A1TableRow0_calc (j : Fin 8) : A1CachedBox 0 j = A1TableRow0 j := by
  revert j
  decide +kernel
lemma A1TableRow1_calc (j : Fin 8) : A1CachedBox 1 j = A1TableRow1 j := by
  revert j
  decide +kernel
lemma A1TableRow10_calc (j : Fin 8) : A1CachedBox 10 j = A1TableRow10 j := by
  revert j
  decide +kernel
lemma A1TableRow22_calc (j : Fin 8) : A1CachedBox 22 j = A1TableRow22 j := by
  revert j
  decide +kernel
lemma A2TableRow0_calc (j : Fin 8) : A2CachedBox 0 j = A2TableRow0 j := by
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
lemma boundV_calc (c : Fin 1) : RI.sum (fun j : Fin 31 => (envelopeSumBoxD j).mul (columnNorm22 j))=boundV c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_TargetEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate AtomicTriangular.L1Kernel

lemma targetEnvelope_nonneg (v : ℝ) (n : Node) : 0≤targetEnvelope v n.val := by
  have hn : 0<Q n.val := by linarith [(Q_node_bounds n.val n.property.2).1]
  have hZ : 0<Z := by norm_num [Z]
  unfold targetEnvelope
  exact mul_nonneg (mul_nonneg (div_nonneg Q_one_pos.le hn.le) (by positivity)) (Real.exp_pos _).le
lemma gaussianTarget_pair_bound {z : ℝ} (hz : 0<z) (hzB : z≤Z) (v : ℝ)
    (n : Node) (hn : 1≤n.val) :
    (∑ d : Fin 2, |gaussianTarget v z n.val d|) ≤ targetEnvelope v n.val := by
  have hQ : 0<Q n.val := by linarith [(Q_node_bounds n.val n.property.2).1]
  have hZ : 0<Z := by norm_num [Z]
  have hn' : 0≤(n.val:ℝ)-1 := by
    have hi : (1:ℝ)≤(n.val:ℝ) := by exact_mod_cast hn
    linarith
  have he : Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/z) ≤
      Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/Z) := by
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_left hn' hz hzB
    have hnz : (1-(n.val:ℝ))/z = -(((n.val:ℝ)-1)/z) := by ring
    have hnZ : (1-(n.val:ℝ))/Z = -(((n.val:ℝ)-1)/Z) := by ring
    rw [hnz,hnZ]
    linarith
  have hb : z+|-1+(Real.pi*(v-h)-D n.val)*z| ≤ 1+Z+Z*|Real.pi*(v-h)-D n.val| := by
    have ha := abs_add_le (-1:ℝ) ((Real.pi*(v-h)-D n.val)*z)
    rw [abs_mul,abs_of_pos hz] at ha
    norm_num at ha
    have hm := mul_le_mul_of_nonneg_left hzB (abs_nonneg (Real.pi*(v-h)-D n.val))
    linarith
  have hp : 0≤Q 1/Q n.val := div_nonneg Q_one_pos.le hQ.le
  simp only [Fin.sum_univ_succ,gaussianTarget,Fin.val_zero,Fin.val_succ,Fin.isValue,
    ↓reduceIte,Nat.one_ne_zero,Nat.reduceAdd,abs_mul,abs_of_nonneg hp,abs_of_pos (Real.exp_pos _),abs_of_pos hz]
  unfold targetEnvelope
  calc
    _ = (Q 1/Q n.val)*(z+|-1+(Real.pi*(v-h)-D n.val)*z|)*
        Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/z) := by ring
    _ ≤ (Q 1/Q n.val)*(1+Z+Z*|Real.pi*(v-h)-D n.val|)*
        Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/Z) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb hp) he (Real.exp_pos _).le
        (by positivity)
lemma summable_targetEnvelope : Summable (fun n : TailNode => targetEnvelope h n.val.val) := by
  apply tailEnumeration.summable_iff.mp
  apply (summable_prod_of_nonneg (fun p => targetEnvelope_nonneg h (enumerateTail p).val)).mpr
  refine ⟨fun a => ?_,(hasSum_fintype _).summable⟩
  change Summable (fun l : ℕ => targetEnvelope h (enumerateTail (a,l)).val.val)
  simp_rw [targetEnvelope_enumerate]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le targetRatio_lt).mul_left _
lemma tsum_targetEnvelope : (∑' n : TailNode, targetEnvelope h n.val.val)=tailTargetEnvelope := by
  rw [←tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr summable_targetEnvelope
  change Summable (fun p : Fin 15 × ℕ => targetEnvelope h (enumerateTail p).val.val) at hs
  change (∑' p : Fin 15 × ℕ, targetEnvelope h (enumerateTail p).val.val)=_
  rw [hs.tsum_prod]
  simp_rw [targetEnvelope_enumerate,tsum_mul_left,
    tsum_geometric_of_lt_one (Real.exp_pos _).le targetRatio_lt]
  rw [tsum_fintype,←Finset.sum_mul]
  rfl
lemma tailTarget_bounds {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    Summable (fun p : TailNode × Fin 2 => |gaussianTarget h z p.1.val.val p.2|) ∧
      (∑' p : TailNode × Fin 2, |gaussianTarget h z p.1.val.val p.2|) ≤ tailTargetEnvelope := by
  obtain ⟨hs,hb⟩ := paired_summable_bound (fun (n : TailNode) d => gaussianTarget h z n.val.val d)
    (fun n => targetEnvelope h n.val.val) summable_targetEnvelope
    (fun n => gaussianTarget_pair_bound hz hzB h n.val (by have := n.val.property.1; omega))
  exact ⟨hs,hb.trans_eq tsum_targetEnvelope⟩
def tailTarget (z : ℝ) (hz : 0<z) (hzB : z≤Z) : ℓ¹(TailNode × Fin 2,ℝ) :=
  column (fun p (_ : Unit) => gaussianTarget h z p.1.val.val p.2)
    (fun _ => (tailTarget_bounds hz hzB).1) ()
lemma tailTarget_norm {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖tailTarget z hz hzB‖ ≤ tailTargetEnvelope := by
  rw [l1_norm]
  exact (tailTarget_bounds hz hzB).2
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInput
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def rawTailCurvature (i : Fin 5) : ℝ :=
  60*(curvatureWave 0 0 (curvaturePoint i) (frequency 30)+
    curvatureWave 0 1 (curvaturePoint i) (frequency (if i.val=0 then 15 else 30)))
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma taylorPhase_re_nonpos (q br : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    (taylorPhase q br t).re≤0 := by
  fin_cases br
  · simp only [taylorPhase,↓reduceIte,sub_re,mul_re,mul_im,I_re,I_im,
      ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,zero_sub]
    have hh : h≤damping q := by fin_cases q <;> (first | (simp [damping,h,H]; all_goals first | (norm_num [damping,h,H]; done) | rfl | decide) | (norm_num [damping,h,H]; done) | norm_num [damping,h,H])
    exact neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh))
  · change (I*Real.pi*zeta (damping q) h t).re≤0
    rw [wavePhase_re]
    have hh := (frequencyDecay_pos q 0 ht).le
    change 0≤Real.pi*(damping q*Xwave (damping q) t-h) at hh
    nlinarith

lemma curvatureWave_nonneg (q br : Fin 2) (s t : ℝ) : 0 ≤ curvatureWave q br s t := by
  unfold curvatureWave; positivity
lemma curvatureWave_antitone (q br : Fin 2) {s u t : ℝ} (ht : |t|≤5/6) (hsu : s≤ u) :
    curvatureWave q br u t ≤ curvatureWave q br s t := by
  unfold curvatureWave
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsu (taylorPhase_re_nonpos q br ht))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData00_0_pre (j : Fin 31) : (curvatureExpInput 0 0 0 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_1_pre (j : Fin 31) : (curvatureExpInput 0 0 1 j).normSq.hi ≤ scale*1024^2 := by
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
lemma curvatureData10_0_calc (j : Fin 31) : curvatureBox 1 0 0 j=curvatureData10_0 j := by
  revert j
  decide +kernel
lemma curvatureData10_1_calc (j : Fin 31) : curvatureBox 1 0 1 j=curvatureData10_1 j := by
  revert j
  decide +kernel
lemma curvatureData10_2_calc (j : Fin 31) : curvatureBox 1 0 2 j=curvatureData10_2 j := by
  revert j
  decide +kernel
lemma curvatureData10_3_calc (j : Fin 31) : curvatureBox 1 0 3 j=curvatureData10_3 j := by
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
def curvatureTable11 : Fin 5 → Fin 31 → RI := ![curvatureData11_0,curvatureData11_1,curvatureData11_2,curvatureData11_3,curvatureData11_4]
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
lemma curvatureColumn0_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 0 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_0 c := by
  revert c
  decide +kernel
lemma curvatureColumn0_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 1 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_1 c := by
  revert c
  decide +kernel
lemma curvatureColumn0_2_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 2 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_2 c := by
  revert c
  decide +kernel
lemma curvatureColumn0_3_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 3 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_3 c := by
  revert c
  decide +kernel
lemma curvatureColumn0_4_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 4 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_4 c := by
  revert c
  decide +kernel
lemma curvatureColumn1_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable11 0 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn1_0 c := by
  revert c
  decide +kernel
lemma curvatureColumn1_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable11 1 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn1_1 c := by
  revert c
  decide +kernel
lemma curvatureColumn1_2_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable11 2 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn1_2 c := by
  revert c
  decide +kernel
lemma curvatureColumn1_3_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable11 3 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn1_3 c := by
  revert c
  decide +kernel
lemma curvatureColumn1_4_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable11 4 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn1_4 c := by
  revert c
  decide +kernel
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
def cVariationBox : RI := ((RI.sum (fun j : Fin 31 => (columnNorm22 j).mul ((varFreqBox j).pow 2))).mul (piBox.pow 2)).divNat 2

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_WaveFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma norm_finiteWaveJet_two (q br : Fin 2) (s t : ℝ) :
    ‖finiteWaveJet q br t 2 s‖=curvatureWave q br s t := by
  simp only [finiteWaveJet,norm_mul,norm_pow,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,curvatureWave]
  ring
lemma pairJJet_iterated (a₁ a₂ : InputCoefficients) (k : ℕ) :
    (fun s : ℝ => (pairJJet a₁ a₂ k s).re)=iteratedDeriv k (pairJ a₁ a₂) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,←hk]
    exact funext fun s => ((hasDerivAt_pairJJet a₁ a₂ k s).real_of_complex).deriv.symm
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CoefficientSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma finiteSpectral_wave_bound (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (s : ℝ) {M : ℝ} (hb : ∀ c : Fin 22, rawCurvatureColumn br s c ≤ M) :
    ‖finiteSpectral (coefficientInput C a w) (waveFunctionJet 1 br 2 s)‖ ≤ ‖a‖*M := by
  rw [finiteSpectral_coefficient_apply]
  calc
    _ ≤ ∑ c : Fin 22, ‖(a c:ℂ)*(∑ j : Fin 31, finiteColumn ⟨c.val,by omega⟩ j * waveFunctionJet 1 br 2 s ⟨frequency j,frequency_mem j⟩)‖ := norm_sum_le _ _
    _ ≤ ∑ c : Fin 22, |a c| * rawCurvatureColumn br s c := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,waveFunctionJet_apply,norm_finiteWaveJet_two]
      exact le_of_eq (mul_comm _ _)
    _ ≤ ∑ c : Fin 22, |a c| * M := Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hb c) (abs_nonneg _)
    _ = _ := by rw [←Finset.sum_mul,l1_norm,tsum_fintype]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

lemma rawCurvatureColumn_antitone (br : Fin 2) (c : Fin 22) {u s : ℝ} (hus : u≤ s) :
    rawCurvatureColumn br s c ≤ rawCurvatureColumn br u c := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (curvatureWave_antitone 1 br (abs_le.mpr (frequency_mem j)) hus) (norm_nonneg _)
lemma tailCurvatureCap_nonneg (br : Fin 2) (i : Fin 5) : 0≤tailCurvatureCap br i := curvatureWave_nonneg _ _ _ _
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_NormalizedJets
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_SpectralJetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_SpectralProduct
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteTargetBridge
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


