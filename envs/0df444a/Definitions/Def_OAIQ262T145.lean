-- Prove2me | Definitions.Def_OAIQ262T145
-- name    : OAIQ262T145
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:22:27.810783+00:00
-- url     : https://prove2.me/theorems/acf974e2-9632-4586-94ae-4438fc26816c
-- title:
--   Definitions bundle OAIQ262T145 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 1 definition and 16 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.directJetFunction`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_CurvatureEnvelope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean), [`Triangular_Construction_DirectCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/DirectCoordinates.lean), [`Triangular_Construction_DirectWaveJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/DirectWaveJets.lean), [`Triangular_Construction_FarCurvature`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FarCurvature.lean), [`Triangular_Construction_FinitePairBridge`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FinitePairBridge.lean), [`Triangular_Taylor_CurvatureData00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData00.lean), [`Triangular_Taylor_CurvatureData01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData01.lean), [`Triangular_Taylor_WaveFunction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/WaveFunction.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T095` and `OAIQ262T096` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T159`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T095
import Definitions.Def_OAIQ262T096

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
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
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData01
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
lemma curvatureData01_1_calc (j : Fin 31) : curvatureBox 0 1 1 j=curvatureData01_1 j := by
  revert j
  decide +kernel
lemma curvatureData01_2_calc (j : Fin 31) : curvatureBox 0 1 2 j=curvatureData01_2 j := by
  revert j
  decide +kernel
lemma curvatureData01_4_calc (j : Fin 31) : curvatureBox 0 1 4 j=curvatureData01_4 j := by
  revert j
  decide +kernel
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
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_DirectWaveJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma waveFunctionJet_direct_zero (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 0 s=exp (-(Real.pi:ℂ)*(damping q-h)*s) • phaseFunction s := by
  ext t
  rw [waveFunctionJet_apply]
  simp only [finiteWaveJet,taylorAmplitude,taylorPhase,Fin.val_zero,↓reduceIte,pow_zero,mul_one,one_mul,
    ContinuousMap.smul_apply,smul_eq_mul,phaseFunction]
  simp only [ofReal_mul,ofReal_sub,ContinuousMap.coe_mk]
  rw [show (I*Real.pi*(t.val:ℂ)-(Real.pi:ℂ)*(damping q-h))*s=
    -(Real.pi:ℂ)*(damping q-h)*s+I*Real.pi*(t.val:ℂ)*s by ring,exp_add]
lemma waveFunctionJet_zero_phase (s : ℂ) : waveFunctionJet 0 0 0 s=phaseFunction s := by
  rw [waveFunctionJet_direct_zero]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,exp_zero,one_smul]
lemma hasDerivAt_phaseFunction (s : ℂ) : HasDerivAt phaseFunction (waveFunctionJet 0 0 1 s) s := by
  have he : phaseFunction=waveFunctionJet 0 0 0 := (funext waveFunctionJet_zero_phase).symm
  rw [he]
  exact hasDerivAt_waveFunctionJet 0 0 0 s
lemma spectralP_direct (s : ℂ) :
    spectralPCLM (waveFunctionJet 0 0 0 s)=P s ∧
    spectralPCLM (waveFunctionJet 0 0 1 s)=deriv P s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralPCLM_apply,spectralP_phase]
  · have he : (fun s => spectralPCLM (phaseFunction s))=P := funext fun s => by rw [spectralPCLM_apply,spectralP_phase]
    have hh := (spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
end AtomicTriangular.Construction
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

def directJetFunction (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) : C(Spectrum,ℂ) :=
  (exp (Real.pi*(v-h)*(n:ℂ))*(Q n:ℂ)⁻¹) •
    (if d.val=0 then -waveFunctionJet q 0 0 n else
      ((D n:ℂ)-Real.pi*(v-h)) • waveFunctionJet q 0 0 n-waveFunctionJet q 0 1 n)
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
lemma inputJJet_constant (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C a w) br k s=
      (C:ℂ)*spectralPCLM (waveFunctionJet 0 br k s)+inputJJet (coefficientInput 0 a w) br k s := by
  simp only [inputJJet,tailSpectral_coefficient,finiteSpectral_coefficient_apply,
    add_apply,smul_apply,smul_eq_mul,ofReal_zero,zero_mul,zero_add]
  ring

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FinitePairBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma finiteSpectrum_input (side : Fin 2) (e : Fin 8 → ℝ) (br : Fin 2) (k : ℕ) (s : ℂ) :
    (∑ q : Fin 2,∑ j : Fin 31,(∑ r : Fin 8,(e r:ℂ)*finiteSpectrum side q j r)*finiteWaveJet q br (frequency j) k s)=
      inputJJet (coefficientInput ((gamma side *ᵥ e) 2) (finiteApprox side e) 0) br k s := by
  simp only [finiteSpectrum_dot,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [inputJJet,tailSpectral_zero_coeff,finiteSpectral_coefficient_apply]
  simp only [_root_.smul_apply,smul_eq_mul,spectralPCLM_apply,spectralP,
    waveFunctionJet_apply,Finset.mul_sum,Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro j _
    ring
lemma finiteJJet_pair (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) :
    finiteJJet side e k s=
      pairJJet (coefficientInput ((gamma side *ᵥ e) 2) (finiteApprox side e) 0)
        (coefficientInput ((gamma (otherSide side) *ᵥ e) 2) (finiteApprox (otherSide side) e) 0) k s := by
  unfold finiteJJet
  simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib,←mul_assoc]
  rw [Finset.sum_comm (f:=fun r q => ∑ j : Fin 31,(e r:ℂ)*finiteSpectrum side q j r*finiteWaveJet q 0 (frequency j) k s)]
  rw [Finset.sum_comm (f:=fun r q => ∑ j : Fin 31,(e r:ℂ)*finiteSpectrum (otherSide side) q j r*finiteWaveJet q 1 (frequency j) k s)]
  simp_rw [Finset.sum_comm (f:=fun r j => (e r:ℂ)*finiteSpectrum side _ j r*finiteWaveJet _ 0 (frequency j) k s),←Finset.sum_mul]
  simp_rw [Finset.sum_comm (f:=fun r j => (e r:ℂ)*finiteSpectrum (otherSide side) _ j r*finiteWaveJet _ 1 (frequency j) k s),←Finset.sum_mul]
  rw [finiteSpectrum_input,finiteSpectrum_input]
  rfl
end AtomicTriangular.Construction
end

end OAI
end


