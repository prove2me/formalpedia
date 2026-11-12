-- Prove2me | Definitions.Def_OAIQ250T085
-- name    : OAIQ250T085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:44:57.646519+00:00
-- url     : https://prove2.me/theorems/0d2b7c96-909a-4519-bff3-2845bf8783a7
-- title:
--   Definitions bundle OAIQ250T085 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 47 declarations of OpenAI's Lean: 4 definitions and 43 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.complexInputSchwartz`, `OAI.AtomicTriangular.Construction.inputSchwartz`, `OAI.AtomicTriangular.Construction.pairSchwartz`, `OAI.AtomicTriangular.FiniteCertificate.R0Box`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_JetMatrix`, `Triangular_Certificate_ParamA`, `Triangular_Certificate_ParamActual`, `Triangular_Certificate_ParamNorm`, `Triangular_Construction_CurvatureEnvelope`, `Triangular_Construction_FarCurvature`, `Triangular_Construction_FiniteInterpolation`, `Triangular_Construction_NodeJets`, `Triangular_Construction_SpectralProduct`, `Triangular_Schwartz_FourierPair`, `Triangular_Schwartz_Realness`, `Triangular_Schwartz_Regularity`, `Triangular_Schwartz_SpectralCLM`, `Triangular_Schwartz_TailSpectral`, `Triangular_Taylor_CoefficientSpectral`, `Triangular_Taylor_CurvatureData00`, `Triangular_Taylor_CurvatureData01`, `Triangular_Taylor_VariationBound`, `Triangular_Taylor_WaveFunction`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T047`, `OAIQ250T048`, `OAIQ250T049`, `OAIQ250T050` and `OAIQ250T051` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T101` and `OAIQ250T104`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T047
import Definitions.Def_OAIQ250T048
import Definitions.Def_OAIQ250T049
import Definitions.Def_OAIQ250T050
import Definitions.Def_OAIQ250T051

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def R0Box (i : Fin 20) (j : Fin 3) : RI := jetMatrixTable i (if j.val<2 then ⟨j.val,by omega⟩ else 22)
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
lemma A2Table_calc (i : Fin 23) (j : Fin 8) : A2CachedBox i j = A2Table i j := by
  fin_cases i
  · exact A2TableRow0_calc j
  · exact A2TableRow1_calc j
  · exact A2TableRow2_calc j
  · exact A2TableRow3_calc j
  · exact A2TableRow4_calc j
  · exact A2TableRow5_calc j
  · exact A2TableRow6_calc j
  · exact A2TableRow7_calc j
  · exact A2TableRow8_calc j
  · exact A2TableRow9_calc j
  · exact A2TableRow10_calc j
  · exact A2TableRow11_calc j
  · exact A2TableRow12_calc j
  · exact A2TableRow13_calc j
  · exact A2TableRow14_calc j
  · exact A2TableRow15_calc j
  · exact A2TableRow16_calc j
  · exact A2TableRow17_calc j
  · exact A2TableRow18_calc j
  · exact A2TableRow19_calc j
  · exact A2TableRow20_calc j
  · exact A2TableRow21_calc j
  · exact A2TableRow22_calc j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_TailSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction
open MeasureTheory

lemma integralDBasis_eq (n : Node) : integralDBasis n = dBasis n := by
  apply (continuous_integralDBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_dBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [dBasis_eq n hsn]
  unfold integralDBasis
  simp_rw [exponential_first_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_one, mul_assoc, exp_frequency_sub]
    _ = P s := by
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hz, sub_zero, P_fourier]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma spectralD_phase (n : Node) (s : ℂ) : spectralD n (phaseFunction s) = dBasis n s := by
  rw [← integralDBasis_eq]
  unfold spectralD integralDBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [← exp_add]
  congr 1
  ring

end AtomicTriangular.Construction
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
lemma parameterExp2_bound : Real.exp (-2/Z) < Wstar := by
  have hx : ((RI.point (-2)).mul ZBox.invPos).Mem (-2/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-2)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox2_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox2,scale,Wstar] at *
  linarith
lemma parameterExp3_bound : Real.exp (-3/Z) < Ustar := by
  have hx : ((RI.point (-3)).mul ZBox.invPos).Mem (-3/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-3)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox3_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox3,scale,Ustar] at *
  linarith
lemma parameterExp6_bound : Real.exp (-6/Z) < Pstar := by
  have hx : ((RI.point (-6)).mul ZBox.invPos).Mem (-6/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-6)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox6_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox6,scale,Pstar] at *
  linarith
end AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma delta_parameter_bound {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    (Z-z)*Real.exp (-2/z) < DeltaStar := by
  let t : ℝ := 1/z-1/Z
  have ht : 0≤t := sub_nonneg.mpr (one_div_le_one_div_of_le hz hzB)
  have hid : Z-z = Z*z*t := by
    have hZ : Z ≠ 0 := by norm_num [Z]
    dsimp [t]
    field_simp
  have he : Real.exp (-2/z) = Real.exp (-2/Z)*Real.exp (-(2*t)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have h1 : (Z-z)*Real.exp (-2/z) ≤ Z^2*Real.exp (-2/Z)*(t*Real.exp (-(2*t))) := by
    rw [hid,he]
    have hh := mul_le_mul_of_nonneg_left hzB
      (show 0≤Z*t*Real.exp (-2/Z)*Real.exp (-(2*t)) by
        have hZ : 0 < Z := by norm_num [Z]
        positivity)
    nlinarith
  have h2 := Real.mul_exp_neg_le_exp_neg_one (2*t)
  have h3 := mul_le_mul_of_nonneg_left h2
    (show 0≤Z^2*Real.exp (-2/Z) by positivity)
  have h4 := mul_le_mul_of_nonneg_left parameterExp2_bound.le
    (show 0≤Z^2*(369/1000:ℝ) by positivity)
  have h5 := mul_le_mul_of_nonneg_left exp_neg_one_bound.le
    (show 0≤Z^2*Real.exp (-2/Z) by positivity)
  norm_num [Z,Wstar,DeltaStar] at *
  nlinarith
lemma actualParameter_mem {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ParameterPolytope (actualParameter z) := by
  have hw := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤2)).trans parameterExp2_bound.le
  have hu := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤3)).trans parameterExp3_bound.le
  have hp := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤6)).trans parameterExp6_bound.le
  have hzp : z*Real.exp (-6/z) ≤ Pstar :=
    (mul_le_of_le_one_left (Real.exp_pos _).le (hzB.trans (by norm_num [Z]))).trans hp
  refine ⟨z,Real.exp (-2/z),(Z-z)*Real.exp (-2/z),Real.exp (-3/z),
    z*Real.exp (-3/z),z*Real.exp (-6/z),Real.exp (-6/z),hz.le,hzB,
    (Real.exp_pos _).le,hw,mul_nonneg (sub_nonneg.mpr hzB) (Real.exp_pos _).le,
    (delta_parameter_bound hz hzB).le,(Real.exp_pos _).le,hu,
    mul_nonneg hz.le (Real.exp_pos _).le,mul_le_mul_of_nonneg_right hzB (Real.exp_pos _).le,
    mul_nonneg hz.le (Real.exp_pos _).le,hzp,(Real.exp_pos _).le,hp,?_⟩
  unfold actualParameter
  congr 1
  ring_nf
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma A1AbsNumerators_calc (i : Fin 23) : rowAbsNumerator (A1Table i) = A1AbsNumerators i := by
  revert i
  decide +kernel
lemma A2AbsNumerators_calc (i : Fin 23) : rowAbsNumerator (A2Table i) = A2AbsNumerators i := by
  revert i
  decide +kernel
end AtomicTriangular.FiniteCertificate
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
lemma curvatureData00_0_calc (j : Fin 31) : curvatureBox 0 0 0 j=curvatureData00_0 j := by
  revert j
  decide +kernel
lemma curvatureData00_1_calc (j : Fin 31) : curvatureBox 0 0 1 j=curvatureData00_1 j := by
  revert j
  decide +kernel
lemma curvatureData00_2_calc (j : Fin 31) : curvatureBox 0 0 2 j=curvatureData00_2 j := by
  revert j
  decide +kernel
lemma curvatureData00_3_calc (j : Fin 31) : curvatureBox 0 0 3 j=curvatureData00_3 j := by
  revert j
  decide +kernel
lemma curvatureData00_4_calc (j : Fin 31) : curvatureBox 0 0 4 j=curvatureData00_4 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData01_0_calc (j : Fin 31) : curvatureBox 0 1 0 j=curvatureData01_0 j := by
  revert j
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

lemma cVariationBox_mem : cVariationBox.Mem cVariation := by
  have hx := RI.mem_mul (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (fourierNorm_mem j) (RI.mem_pow (varFreqBox_mem j) 2))) (RI.mem_pow piBox_mem 2)
  have hy := RI.mem_divNat hx (by norm_num : 0<2)
  simpa only [cVariationBox,cVariation,coeffAbs,sq_abs,Nat.cast_ofNat] using hy
lemma cVariation_lt : cVariation < 119 := by
  have hx := ri_mem_lt cVariationBox_mem 119 1 (by norm_num) (by decide +kernel)
  simpa using hx

lemma dVariationBox_mem : dVariationBox.Mem dVariation := by
  have hx := RI.mem_mul (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (fourierNorm_mem j) (RI.mem_pow (varFreqBox_mem j) 1))) (RI.mem_pow piBox_mem 1)
  simpa only [dVariationBox,dVariation,coeffAbs,pow_one] using hx
lemma dVariation_lt : dVariation < 119 := by
  have hx := ri_mem_lt dVariationBox_mem 119 1 (by norm_num) (by decide +kernel)
  simpa using hx
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

lemma waveFunctionJet_uniform (q br : Fin 2) (s : ℝ) {M : ℝ} (hM : 0≤M)
    (hb : ∀ t : ℝ, |t|≤5/6 → curvatureWave q br s t≤M) :
    ‖waveFunctionJet q br 2 s‖≤M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro t
  rw [waveFunctionJet_apply,norm_finiteWaveJet_two]
  exact hb t.val (abs_le.mpr t.property)

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
lemma tail_pair_norm119 (n : Node) (u v : ℝ) :
    ‖(u:ℂ) • spectralCCLM n+(v:ℂ) • spectralDCLM n‖ ≤ 119*(|u|+|v|) := by
  have h0 := (spectralCCLM_norm n).trans cVariation_lt.le
  have h1 := (spectralDCLM_norm n).trans dVariation_lt.le
  have hsum := norm_add_le ((u:ℂ) • spectralCCLM n) ((v:ℂ) • spectralDCLM n)
  have hsm := add_le_add (complex_smul_clm_bound u (spectralCCLM n))
    (complex_smul_clm_bound v (spectralDCLM n))
  have hh : ‖(u:ℂ) • spectralCCLM n+(v:ℂ) • spectralDCLM n‖ ≤
      |u| * ‖spectralCCLM n‖+|v| * ‖spectralDCLM n‖ := by
    exact hsum.trans hsm
  nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg u),mul_le_mul_of_nonneg_left h1 (abs_nonneg v)]
lemma tailSeries_norm (w : TailCoefficients) :
    ‖∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val)‖ ≤ 119*‖w‖ := by
  have hh := norm_series_bound (fun n : TailNode => (w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val)
    (fun n => |w (n,0)|+|w (n,1)|) (tail_pairs_summable w) 119
    (fun n => tail_pair_norm119 n.val (w (n,0)) (w (n,1)))
  rw [tail_pairs_norm] at hh
  exact hh
lemma tailSpectral_zero_constant_norm (a : TrigonometricCoefficients) (w : TailCoefficients) :
    ‖tailSpectral (coefficientInput 0 a w)‖ ≤ 119*‖w‖ := by
  rw [tailSpectral_zero_constant]
  exact tailSeries_norm w
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

lemma tailCurvatureCap_bound (br : Fin 2) (i : Fin 5) {s t : ℝ}
    (hs : curvaturePoint i≤ s) (ht : |t|≤5/6) : curvatureWave 0 br s t≤tailCurvatureCap br i := by
  apply (curvatureWave_antitone 0 br ht hs).trans
  fin_cases br
  · exact curvature_tail_direct ht
  · by_cases hi : i=0
    · subst i
      exact curvature_tail_zero ht
    · have hu : 1 ≤ curvaturePoint i := by fin_cases i <;> (first | (simp [curvaturePoint] at *; all_goals first | (norm_num [curvaturePoint] at *; done) | rfl | decide) | (norm_num [curvaturePoint] at *; done) | norm_num [curvaturePoint] at *)
      have hval : ¬i.val=0 := by simpa only [Fin.val_eq_zero_iff] using hi
      simp only [tailCurvatureCap,true_and,hval,↓reduceIte]
      convert curvature_tail_positive hu ht using 1 <;> rfl
lemma tailSpectral_curvature (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
    ‖tailSpectral (coefficientInput 0 a w) (waveFunctionJet 0 br 2 s)‖≤119*‖w‖*tailCurvatureCap br i := by
  exact ((tailSpectral _).le_opNorm _).trans (mul_le_mul (tailSpectral_zero_constant_norm a w)
    (waveFunctionJet_uniform _ _ _ (tailCurvatureCap_nonneg br i) (fun t ht => tailCurvatureCap_bound br i hs ht))
    (norm_nonneg _) (by positivity))
end AtomicTriangular.Construction
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

lemma cBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) : cBasis n m.val = 0 := by
  rw [cBasis_eq n (by exact_mod_cast hmn),P_node,zero_div]

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

lemma tailColumnSpectral_norm (p : TailNode × Fin 2) : ‖tailColumnSpectral p‖≤119 := by
  unfold tailColumnSpectral
  split_ifs
  · exact (spectralCCLM_norm _).trans cVariation_lt.le
  · exact (spectralDCLM_norm _).trans dVariation_lt.le
lemma summable_tail_columns (w : TailCoefficients) :
    Summable (fun p => (w p:ℂ) • tailColumnSpectral p) := by
  exact summable_l1_complex_smul w tailColumnSpectral 119 tailColumnSpectral_norm
lemma tailSpectral_product (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput C a w)= (C:ℂ) • spectralPCLM+
      ∑' p : TailNode × Fin 2,(w p:ℂ) • tailColumnSpectral p := by
  have he := tsum_prod_fin_two (fun p => (w p:ℂ) • tailColumnSpectral p) (summable_tail_columns w)
  rw [he,tailSpectral_coefficient]
  rfl
lemma summable_tail_columns_apply (w : TailCoefficients) (f : C(Spectrum,ℂ)) :
    Summable (fun p => (w p:ℂ)*tailColumnSpectral p f) := by
  simpa only [ContinuousLinearMap.apply_apply,smul_apply,smul_eq_mul] using
    ((ContinuousLinearMap.apply ℂ ℂ f).summable (summable_tail_columns w))
lemma tailSpectral_product_apply (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (f : C(Spectrum,ℂ)) :
    tailSpectral (coefficientInput C a w) f=(C:ℂ)*spectralP f+
      ∑' p : TailNode × Fin 2,(w p:ℂ)*tailColumnSpectral p f := by
  rw [tailSpectral_product,add_apply,smul_apply,smul_eq_mul,spectralPCLM_apply]
  congr 1
  exact (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tail_columns w)
lemma tailSpectral_jet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) :
    (tailSpectral (coefficientInput C a w) (jetFunction q v m d)).re=
      C*jet (damping q) v m d (finiteColumn 22)+
      ∑' p : TailNode × Fin 2,w p*tailJet (damping q) v m p.1.val.val p.2 d := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,spectralP_jet,tailColumnSpectral_jet]
lemma inputJJet_negative_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (inputJJet (coefficientInput C a w) 1 0 n)
      (inputJJet (coefficientInput C a w) 1 1 n)).re=
      C*jet h v n d (finiteColumn 22)+
      (∑' p : TailNode × Fin 2,w p*tailJet h v n p.1.val.val p.2 d)+
      ∑ c : Fin 22,a c*jet H v n d (finiteColumn ⟨c.val,by omega⟩) := by
  rw [inputJJet_negative,add_re,tailSpectral_jet,finiteSpectral_jet]
  rfl
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
lemma extendFiniteError_transformed (u : FiniteCoefficients) (i : Fin 20) :
    (∑ c : Fin 22,extendFiniteError u c*jet H H (rowNode i).val (rowDerivative i)
      (finiteColumn ⟨c.val,by omega⟩))=Roperator u i := by
  have hh := finiteRow_sum 0 (extendFiniteError u) i
  have h0 : extendFiniteError u 0=0 := extendFiniteError_fixed u 0
  have h1 : extendFiniteError u 1=0 := extendFiniteError_fixed u 1
  erw [h0] at hh
  simp only [extendFiniteError_shift,zero_mul,zero_add,mul_zero,add_zero] at hh
  rw [hh,Roperator_apply]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FarCurvature
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

lemma realP_jet_zero (n : Node) : realP n.val=0 ∧ deriv realP n.val=0 := by
  have he (s : ℝ) : (spectralPCLM (waveFunctionJet 0 0 0 s)).re=realP s := by
    rw [(spectralP_direct _).1,P_ofReal,ofReal_re]
  constructor
  · rw [←he,(spectralP_direct _).1]
    norm_cast
    rw [P_node,zero_re]
  · have hh := ((hasDerivAt_spectralP_wave 0 0 (n.val:ℂ)).real_of_complex).deriv
    simp only [he] at hh
    rw [hh,(spectralP_direct _).2]
    norm_cast
    rw [deriv_P_node,zero_re]
lemma rawConstantCurvature_antitone {u s : ℝ} (hus : u ≤ s) :
    rawConstantCurvature s ≤ rawConstantCurvature u := by
  unfold rawConstantCurvature
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (curvatureWave_antitone 0 1 (abs_le.mpr (frequency_mem j)) hus) (norm_nonneg _)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology SchwartzMap
open Complex Filter Set
namespace AtomicTriangular.Construction

lemma uniform_basis_bound (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (n : Node) (s : ℂ), |s.im| ≤ R → ‖cBasis n s‖ ≤ M ∧ ‖dBasis n s‖ ≤ M := by
  let A := max R 2
  let M := stripBound A
  have hM : 0 ≤ M := stripBound_nonneg A
  refine ⟨M,hM,?_⟩
  intro n s hs
  have hmapP : Set.MapsTo P (Metric.ball (n.val : ℂ) 2) (Metric.closedBall (P n.val) M) := by
    intro w hw
    simp only [Metric.mem_closedBall, P_node, dist_zero_right]
    exact P_strip_bound A w ((im_le_dist_int w n.val).trans
      ((Metric.mem_ball.mp hw).le.trans (le_max_right _ _)))
  have hd : ∀ w ∈ Metric.ball (n.val : ℂ) 2, ‖dBasis n w‖ ≤ M/2 := by
    intro w hw
    exact Complex.norm_dslope_le_div_of_mapsTo_ball differentiable_P.differentiableOn hmapP hw
  have hmapD : Set.MapsTo (dBasis n) (Metric.ball (n.val : ℂ) 1)
      (Metric.closedBall (dBasis n n.val) (M/2)) := by
    intro w hw
    simp only [Metric.mem_closedBall, dBasis_node, dist_zero_right]
    apply hd w
    exact (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
  have hc : ∀ w ∈ Metric.ball (n.val : ℂ) 1, ‖cBasis n w‖ ≤ M/2 := by
    intro w hw
    simpa [cBasis] using Complex.norm_dslope_le_div_of_mapsTo_ball
      (differentiable_dBasis n).differentiableOn hmapD hw
  have hPs : ‖P s‖ ≤ M := P_strip_bound A s (hs.trans (le_max_left _ _))
  have hhalf : M/2 ≤ M := by linarith
  by_cases hnear : dist s (n.val : ℂ) < 1
  · exact ⟨(hc s hnear).trans hhalf,
      (hd s (lt_trans hnear (by norm_num : (1 : ℝ) < 2))).trans hhalf⟩
  · have hfar : 1 ≤ ‖s - (n.val : ℂ)‖ := by simpa [dist_eq_norm] using le_of_not_gt hnear
    have hne : s ≠ (n.val : ℂ) := by intro he; norm_num [he] at hfar
    rw [cBasis_eq n hne, dBasis_eq n hne, norm_div, norm_div, norm_pow]
    constructor
    · exact (div_le_self (norm_nonneg _) (one_le_pow₀ hfar)).trans hPs
    · exact (div_le_self (norm_nonneg _) hfar).trans hPs

lemma differentiable_tailInput (a : InputCoefficients) : Differentiable ℂ (tailInput a) := by
  intro s
  obtain ⟨M,hM,hB⟩ := uniform_basis_bound (|s.im|+1)
  let U : Set ℂ := {w | |w.im| < |s.im|+1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_im.abs continuous_const
  have hs : s ∈ U := by dsimp [U] <;> linarith
  have hd : DifferentiableOn ℂ
      (fun w => ∑' n : TailNode, ((a.tailC n:ℂ)*cBasis n.val w+(a.tailD n:ℂ)*dBasis n.val w)) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm (a.summable.mul_right M)
    · intro n
      exact ((differentiable_cBasis n.val).const_mul _ |>.add
        ((differentiable_dBasis n.val).const_mul _)).differentiableOn
    · exact hU
    · intro n w hw
      exact tail_summand_norm_bound a hB n w (le_of_lt hw)
  exact ((differentiable_P s).const_mul _).add (hd.differentiableAt (hU.mem_nhds hs))

lemma tailInput_strip (a : InputCoefficients) (R : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, |s.im| ≤ R → ‖tailInput a s‖ ≤ M := by
  obtain ⟨M,hM,hB⟩ := uniform_basis_bound R
  refine ⟨|a.C| *stripBound R + ∑' n : TailNode, (|a.tailC n|+|a.tailD n|)*M,?_⟩
  intro s hs
  have hsum := (a.summable.mul_right M).of_norm_bounded
    (fun n => tail_summand_norm_bound a hB n s hs)
  unfold tailInput
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (P_strip_bound R s hs) (abs_nonneg a.C)
  · exact (norm_tsum_le_tsum_norm hsum.norm).trans
      (hsum.norm.tsum_le_tsum (fun n => tail_summand_norm_bound a hB n s hs) (a.summable.mul_right M))

def inputSchwartz (a : InputCoefficients) : 𝓢(Plane,ℝ) :=
  Analysis.dampedEntireSchwartz (Real.pi*h*b) (mul_pos (mul_pos Real.pi_pos (by norm_num [h])) b_pos) b
    (tailInput a) (differentiable_tailInput a) (tailInput_strip a 1) +
  Analysis.dampedEntireSchwartz (Real.pi*H*b) (mul_pos (mul_pos Real.pi_pos (by norm_num [H])) b_pos) b
    (finiteInput a) (differentiable_finiteInput a) (finiteInput_strip a 1)

lemma inputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    inputSchwartz a x = Real.exp (-Real.pi*h*radial x)*(tailInput a (radial x)).re +
      Real.exp (-Real.pi*H*radial x)*(finiteInput a (radial x)).re := by
  simp only [inputSchwartz,add_apply,Analysis.dampedEntireSchwartz_apply,radial]
  push_cast
  congr 3 <;> ring

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma inputComplex_re (a : InputCoefficients) (x : Plane) : (inputComplex a x).re = inputSchwartz a x := by
  rw [inputSchwartz_apply]
  simp [inputComplex,Complex.mul_re,← Complex.ofReal_mul,← Complex.ofReal_neg,Complex.exp_ofReal_re]
lemma inputComplex_eq (a : InputCoefficients) (x : Plane) : inputComplex a x = (inputSchwartz a x:ℂ) := by
  rw [← inputComplex_re]
  exact (Complex.conj_eq_iff_re.mp (inputComplex_real a x)).symm

def complexInputSchwartz (a : InputCoefficients) : 𝓢(Plane,ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (inputSchwartz a)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

def pairSchwartz (a₁ a₂ : InputCoefficients) : 𝓢(Plane,ℝ) :=
  (complexInputSchwartz a₁ + 𝓕 (complexInputSchwartz a₂)).postcompCLM Complex.reCLM
end AtomicTriangular.Construction
end

end OAI
end


