-- Prove2me | Definitions.Def_OAIQ262T158
-- name    : OAIQ262T158
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T20:41:29.900596+00:00
-- url     : https://prove2.me/theorems/965c721e-ce4f-4f8d-84dd-17450f04d5f5
-- title:
--   Definitions bundle OAIQ262T158 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 70 declarations of OpenAI's Lean: 3 definitions and 67 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.complexInputSchwartz`, `OAI.AtomicTriangular.Construction.inputSchwartz`, `OAI.AtomicTriangular.Construction.pairSchwartz`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_JetMatrix`, `Triangular_Certificate_ParamInterval`, `Triangular_Certificate_ParamU`, `Triangular_Certificate_TargetInterval`, `Triangular_Construction_CurvatureBoxes`, `Triangular_Envelope_TargetEnvelope`, `Triangular_Schwartz_FourierPair`, `Triangular_Schwartz_InputCLM`, `Triangular_Schwartz_Realness`, `Triangular_Schwartz_Regularity`, `Triangular_Schwartz_SpectralCLM`, `Triangular_Schwartz_TailSpectral`, `Triangular_Taylor_TaylorPhase`, `Triangular_Taylor_VariationBound`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139`, `OAIQ262T140`, `OAIQ262T142`, `OAIQ262T143` and `OAIQ262T146` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T193` and `OAIQ262T194`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T137
import Definitions.Def_OAIQ262T138
import Definitions.Def_OAIQ262T139
import Definitions.Def_OAIQ262T140
import Definitions.Def_OAIQ262T142
import Definitions.Def_OAIQ262T143
import Definitions.Def_OAIQ262T146

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullJetRow3_calc (col : Fin 23) : fullJetBox 3 col = fullJetRow3 col := by
  revert col
  decide +kernel
lemma fullJetRow4_calc (col : Fin 23) : fullJetBox 4 col = fullJetRow4 col := by
  revert col
  decide +kernel
lemma fullJetRow5_calc (col : Fin 23) : fullJetBox 5 col = fullJetRow5 col := by
  revert col
  decide +kernel
lemma fullJetRow6_calc (col : Fin 23) : fullJetBox 6 col = fullJetRow6 col := by
  revert col
  decide +kernel
lemma fullJetRow7_calc (col : Fin 23) : fullJetBox 7 col = fullJetRow7 col := by
  revert col
  decide +kernel
lemma fullJetRow8_calc (col : Fin 23) : fullJetBox 8 col = fullJetRow8 col := by
  revert col
  decide +kernel
lemma fullJetRow9_calc (col : Fin 23) : fullJetBox 9 col = fullJetRow9 col := by
  revert col
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
lemma targetCoefficientBox_mem (n : Fin 10) : (targetCoefficientBox n).Mem (targetCoefficient n) := by
  have he : ((Complex.exp ((Real.pi*eta*(finiteNode n):ℝ):ℂ))).re = Real.exp (Real.pi*eta*(finiteNode n)) := by rw [Complex.exp_ofReal_re]
  have hq : ∀ n : Fin 10, 0 < (QTable n).lo := by decide +kernel
  unfold targetCoefficient
  rw [div_eq_mul_inv]
  apply RI.mem_mul (RI.mem_mul QBox1_mem (RI.mem_invPos (QTable_mem n) (hq n)))
  simpa only [he] using (targetExpTable_mem n).1

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
lemma UplusTableRow0_calc (j : Fin 8) : UplusCachedBox 0 j = UplusTableRow0 j := by
  revert j
  decide +kernel
lemma UplusTableRow1_calc (j : Fin 8) : UplusCachedBox 1 j = UplusTableRow1 j := by
  revert j
  decide +kernel
lemma UplusTableRow2_calc (j : Fin 8) : UplusCachedBox 2 j = UplusTableRow2 j := by
  revert j
  decide +kernel
lemma UplusTableRow3_calc (j : Fin 8) : UplusCachedBox 3 j = UplusTableRow3 j := by
  revert j
  decide +kernel
lemma UplusTableRow4_calc (j : Fin 8) : UplusCachedBox 4 j = UplusTableRow4 j := by
  revert j
  decide +kernel
lemma UplusTableRow5_calc (j : Fin 8) : UplusCachedBox 5 j = UplusTableRow5 j := by
  revert j
  decide +kernel
lemma UplusTableRow6_calc (j : Fin 8) : UplusCachedBox 6 j = UplusTableRow6 j := by
  revert j
  decide +kernel
lemma UplusTableRow7_calc (j : Fin 8) : UplusCachedBox 7 j = UplusTableRow7 j := by
  revert j
  decide +kernel
lemma UplusTableRow8_calc (j : Fin 8) : UplusCachedBox 8 j = UplusTableRow8 j := by
  revert j
  decide +kernel
lemma UplusTableRow9_calc (j : Fin 8) : UplusCachedBox 9 j = UplusTableRow9 j := by
  revert j
  decide +kernel
lemma UplusTableRow10_calc (j : Fin 8) : UplusCachedBox 10 j = UplusTableRow10 j := by
  revert j
  decide +kernel
lemma UplusTableRow11_calc (j : Fin 8) : UplusCachedBox 11 j = UplusTableRow11 j := by
  revert j
  decide +kernel
lemma UplusTableRow12_calc (j : Fin 8) : UplusCachedBox 12 j = UplusTableRow12 j := by
  revert j
  decide +kernel
lemma UplusTableRow13_calc (j : Fin 8) : UplusCachedBox 13 j = UplusTableRow13 j := by
  revert j
  decide +kernel
lemma UplusTableRow14_calc (j : Fin 8) : UplusCachedBox 14 j = UplusTableRow14 j := by
  revert j
  decide +kernel
lemma UplusTableRow15_calc (j : Fin 8) : UplusCachedBox 15 j = UplusTableRow15 j := by
  revert j
  decide +kernel
lemma UplusTableRow16_calc (j : Fin 8) : UplusCachedBox 16 j = UplusTableRow16 j := by
  revert j
  decide +kernel
lemma UplusTableRow17_calc (j : Fin 8) : UplusCachedBox 17 j = UplusTableRow17 j := by
  revert j
  decide +kernel
lemma UplusTableRow18_calc (j : Fin 8) : UplusCachedBox 18 j = UplusTableRow18 j := by
  revert j
  decide +kernel
lemma UplusTableRow19_calc (j : Fin 8) : UplusCachedBox 19 j = UplusTableRow19 j := by
  revert j
  decide +kernel
lemma UplusTable_calc (i : Fin 20) (j : Fin 8) : UplusCachedBox i j = UplusTable i j := by
  fin_cases i
  · exact UplusTableRow0_calc j
  · exact UplusTableRow1_calc j
  · exact UplusTableRow2_calc j
  · exact UplusTableRow3_calc j
  · exact UplusTableRow4_calc j
  · exact UplusTableRow5_calc j
  · exact UplusTableRow6_calc j
  · exact UplusTableRow7_calc j
  · exact UplusTableRow8_calc j
  · exact UplusTableRow9_calc j
  · exact UplusTableRow10_calc j
  · exact UplusTableRow11_calc j
  · exact UplusTableRow12_calc j
  · exact UplusTableRow13_calc j
  · exact UplusTableRow14_calc j
  · exact UplusTableRow15_calc j
  · exact UplusTableRow16_calc j
  · exact UplusTableRow17_calc j
  · exact UplusTableRow18_calc j
  · exact UplusTableRow19_calc j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_TailSpectral
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

lemma integralCBasis_eq (n : Node) : integralCBasis n = cBasis n := by
  apply (continuous_integralCBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_cBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [cBasis_eq n hsn]
  unfold integralCBasis
  simp_rw [exponential_second_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) -
        (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) * (s-n.val) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_sub, mul_one, mul_assoc, exp_frequency_sub]
      ring
    _ = P s := by
      have hd : (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_deriv_cancel n
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hd, hz, zero_mul, sub_zero, sub_zero, P_fourier]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma spectralC_phase (n : Node) (s : ℂ) : spectralC n (phaseFunction s) = cBasis n s := by
  rw [← integralCBasis_eq]
  unfold spectralC integralCBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [mul_assoc,← exp_add]
  congr 2
  ring

end AtomicTriangular.Construction
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

lemma tailTarget_norm {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖tailTarget z hz hzB‖ ≤ tailTargetEnvelope := by
  rw [l1_norm]
  exact (tailTarget_bounds hz hzB).2
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
lemma targetExpInput_mem (q : Fin 2) (n : ℤ) :
    (targetExpInput q n).Mem (Real.pi*(damping q-h)*n+(1-n)/Z) := by
  apply RI.mem_add (RI.mem_mul (targetRateBox_mem q) (RI.mem_point n))
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_point (1-n))
    (RI.mem_invPos targetZBox_mem (by decide +kernel))
lemma targetExpf9_mem : targetExpf9.Mem (Real.exp (Real.pi*(damping 1-h)*(9:ℤ)+(1-(9:ℤ))/Z)) := by
  rw [← targetExpf9_calc]
  exact ri_exp_mem (targetExpInput_mem 1 9) (by decide +kernel)
lemma targetExpf12_mem : targetExpf12.Mem (Real.exp (Real.pi*(damping 1-h)*(12:ℤ)+(1-(12:ℤ))/Z)) := by
  rw [← targetExpf12_calc]
  exact ri_exp_mem (targetExpInput_mem 1 12) (by decide +kernel)
lemma targetExpf13_mem : targetExpf13.Mem (Real.exp (Real.pi*(damping 1-h)*(13:ℤ)+(1-(13:ℤ))/Z)) := by
  rw [← targetExpf13_calc]
  exact ri_exp_mem (targetExpInput_mem 1 13) (by decide +kernel)
lemma targetExpf16_mem : targetExpf16.Mem (Real.exp (Real.pi*(damping 1-h)*(16:ℤ)+(1-(16:ℤ))/Z)) := by
  rw [← targetExpf16_calc]
  exact ri_exp_mem (targetExpInput_mem 1 16) (by decide +kernel)
lemma targetExpf19_mem : targetExpf19.Mem (Real.exp (Real.pi*(damping 1-h)*(19:ℤ)+(1-(19:ℤ))/Z)) := by
  rw [← targetExpf19_calc]
  exact ri_exp_mem (targetExpInput_mem 1 19) (by decide +kernel)
lemma targetExpf21_mem : targetExpf21.Mem (Real.exp (Real.pi*(damping 1-h)*(21:ℤ)+(1-(21:ℤ))/Z)) := by
  rw [← targetExpf21_calc]
  exact ri_exp_mem (targetExpInput_mem 1 21) (by decide +kernel)
lemma targetExpt36_mem : targetExpt36.Mem (Real.exp (Real.pi*(damping 0-h)*(36:ℤ)+(1-(36:ℤ))/Z)) := by
  rw [← targetExpt36_calc]
  exact ri_exp_mem (targetExpInput_mem 0 36) (by decide +kernel)
lemma targetExpt37_mem : targetExpt37.Mem (Real.exp (Real.pi*(damping 0-h)*(37:ℤ)+(1-(37:ℤ))/Z)) := by
  rw [← targetExpt37_calc]
  exact ri_exp_mem (targetExpInput_mem 0 37) (by decide +kernel)
lemma targetExpt39_mem : targetExpt39.Mem (Real.exp (Real.pi*(damping 0-h)*(39:ℤ)+(1-(39:ℤ))/Z)) := by
  rw [← targetExpt39_calc]
  exact ri_exp_mem (targetExpInput_mem 0 39) (by decide +kernel)
lemma targetExpt40_mem : targetExpt40.Mem (Real.exp (Real.pi*(damping 0-h)*(40:ℤ)+(1-(40:ℤ))/Z)) := by
  rw [← targetExpt40_calc]
  exact ri_exp_mem (targetExpInput_mem 0 40) (by decide +kernel)
lemma targetExpt43_mem : targetExpt43.Mem (Real.exp (Real.pi*(damping 0-h)*(43:ℤ)+(1-(43:ℤ))/Z)) := by
  rw [← targetExpt43_calc]
  exact ri_exp_mem (targetExpInput_mem 0 43) (by decide +kernel)
lemma targetExpt45_mem : targetExpt45.Mem (Real.exp (Real.pi*(damping 0-h)*(45:ℤ)+(1-(45:ℤ))/Z)) := by
  rw [← targetExpt45_calc]
  exact ri_exp_mem (targetExpInput_mem 0 45) (by decide +kernel)
lemma targetExpt48_mem : targetExpt48.Mem (Real.exp (Real.pi*(damping 0-h)*(48:ℤ)+(1-(48:ℤ))/Z)) := by
  rw [← targetExpt48_calc]
  exact ri_exp_mem (targetExpInput_mem 0 48) (by decide +kernel)
lemma targetExpt49_mem : targetExpt49.Mem (Real.exp (Real.pi*(damping 0-h)*(49:ℤ)+(1-(49:ℤ))/Z)) := by
  rw [← targetExpt49_calc]
  exact ri_exp_mem (targetExpInput_mem 0 49) (by decide +kernel)
lemma targetExpt52_mem : targetExpt52.Mem (Real.exp (Real.pi*(damping 0-h)*(52:ℤ)+(1-(52:ℤ))/Z)) := by
  rw [← targetExpt52_calc]
  exact ri_exp_mem (targetExpInput_mem 0 52) (by decide +kernel)
lemma targetExpt55_mem : targetExpt55.Mem (Real.exp (Real.pi*(damping 0-h)*(55:ℤ)+(1-(55:ℤ))/Z)) := by
  rw [← targetExpt55_calc]
  exact ri_exp_mem (targetExpInput_mem 0 55) (by decide +kernel)
lemma targetExpt57_mem : targetExpt57.Mem (Real.exp (Real.pi*(damping 0-h)*(57:ℤ)+(1-(57:ℤ))/Z)) := by
  rw [← targetExpt57_calc]
  exact ri_exp_mem (targetExpInput_mem 0 57) (by decide +kernel)
lemma targetExpt25_mem : targetExpt25.Mem (Real.exp (Real.pi*(damping 0-h)*(25:ℤ)+(1-(25:ℤ))/Z)) := by
  rw [← targetExpt25_calc]
  exact ri_exp_mem (targetExpInput_mem 0 25) (by decide +kernel)
lemma targetExpt27_mem : targetExpt27.Mem (Real.exp (Real.pi*(damping 0-h)*(27:ℤ)+(1-(27:ℤ))/Z)) := by
  rw [← targetExpt27_calc]
  exact ri_exp_mem (targetExpInput_mem 0 27) (by decide +kernel)
lemma targetExpt28_mem : targetExpt28.Mem (Real.exp (Real.pi*(damping 0-h)*(28:ℤ)+(1-(28:ℤ))/Z)) := by
  rw [← targetExpt28_calc]
  exact ri_exp_mem (targetExpInput_mem 0 28) (by decide +kernel)
lemma targetExpt31_mem : targetExpt31.Mem (Real.exp (Real.pi*(damping 0-h)*(31:ℤ)+(1-(31:ℤ))/Z)) := by
  rw [← targetExpt31_calc]
  exact ri_exp_mem (targetExpInput_mem 0 31) (by decide +kernel)
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma amplitudeNormBox_mem (q br : Fin 2) (j : Fin 31) :
    (amplitudeNormBox q br j).Mem ‖taylorAmplitude q br (frequency j)‖ := by
  fin_cases br
  · simpa [amplitudeNormBox,taylorAmplitude] using ri1_mem
  · fin_cases q
    · simpa [amplitudeNormBox,taylorAmplitude] using lambdaNorm0_mem j
    · simpa [amplitudeNormBox,taylorAmplitude] using lambdaNorm1_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma tailSpectral_phase (a : InputCoefficients) (s : ℂ) :
    tailSpectral a (phaseFunction s) = tailInput a s := by
  simp only [tailSpectral_apply,spectralP_phase,spectralC_phase,spectralD_phase,tailInput]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_Regularity
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
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

def complexInputSchwartz (a : InputCoefficients) : 𝓢(Plane,ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (inputSchwartz a)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma inputComplex_spectral (a : InputCoefficients) (x : Plane) : inputComplex a x =
    exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ)) +
    exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ)) := by
  rw [tailSpectral_phase,finiteSpectral_phase]
  rfl
def pairSchwartz (a₁ a₂ : InputCoefficients) : 𝓢(Plane,ℝ) :=
  (complexInputSchwartz a₁ + 𝓕 (complexInputSchwartz a₂)).postcompCLM Complex.reCLM
end AtomicTriangular.Construction
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

lemma cVariationBox_mem : cVariationBox.Mem cVariation := by
  have hx := RI.mem_mul (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (fourierNorm_mem j) (RI.mem_pow (varFreqBox_mem j) 2))) (RI.mem_pow piBox_mem 2)
  have hy := RI.mem_divNat hx (by norm_num : 0<2)
  simpa only [cVariationBox,cVariation,coeffAbs,sq_abs,Nat.cast_ofNat] using hy
lemma cVariation_lt : cVariation < 119 := by
  have hx := ri_mem_lt cVariationBox_mem 119 1 (by norm_num) (by decide +kernel)
  simpa using hx
end AtomicTriangular.FiniteCertificate
end

end OAI
end


