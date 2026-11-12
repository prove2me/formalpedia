-- Prove2me | Definitions.Def_OAIQ262T144
-- name    : OAIQ262T144
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:24:14.25405+00:00
-- url     : https://prove2.me/theorems/be750cb0-e721-4669-a7d7-2af6cb9b8206
-- title:
--   Definitions bundle OAIQ262T144 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 3 definitions and 13 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.ordinarySignRow`, `OAI.AtomicTriangular.Construction.rawRemainderConstant`, `OAI.AtomicTriangular.FiniteCertificate.remainderBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_CurvatureEnvelope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean), [`Triangular_Construction_CurvatureSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureSums.lean), [`Triangular_Construction_FarCurvature`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FarCurvature.lean), [`Triangular_Signs_RemainderBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderBoxes.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_CoefficientSpectral`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CoefficientSpectral.lean), [`Triangular_Taylor_CurvatureData00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData00.lean), [`Triangular_Taylor_CurvatureData01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData01.lean), [`Triangular_Taylor_CurvatureData11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData11.lean), [`Triangular_Taylor_WaveFunction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/WaveFunction.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T034`, `OAIQ262T085`, `OAIQ262T095`, `OAIQ262T096`, `OAIQ262T097` and `OAIQ262T132` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T159`, `OAIQ262T160`, `OAIQ262T161`, `OAIQ262T162`, `OAIQ262T163`, `OAIQ262T173` and `OAIQ262T180`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T034
import Definitions.Def_OAIQ262T085
import Definitions.Def_OAIQ262T095
import Definitions.Def_OAIQ262T096
import Definitions.Def_OAIQ262T097
import Definitions.Def_OAIQ262T132

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
lemma curvatureData00_0_calc (j : Fin 31) : curvatureBox 0 0 0 j=curvatureData00_0 j := by
  revert j
  decide +kernel
lemma curvatureData00_1_calc (j : Fin 31) : curvatureBox 0 0 1 j=curvatureData00_1 j := by
  revert j
  decide +kernel
lemma curvatureData00_2_calc (j : Fin 31) : curvatureBox 0 0 2 j=curvatureData00_2 j := by
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
lemma curvatureData01_3_calc (j : Fin 31) : curvatureBox 0 1 3 j=curvatureData01_3 j := by
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
lemma curvatureData11_1_calc (j : Fin 31) : curvatureBox 1 1 1 j=curvatureData11_1 j := by
  revert j
  decide +kernel
lemma curvatureData11_2_calc (j : Fin 31) : curvatureBox 1 1 2 j=curvatureData11_2 j := by
  revert j
  decide +kernel
lemma curvatureData11_4_calc (j : Fin 31) : curvatureBox 1 1 4 j=curvatureData11_4 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
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
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CoefficientSpectral
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

lemma rawCurvatureColumn_antitone (br : Fin 2) (c : Fin 22) {u s : ℝ} (hus : u≤ s) :
    rawCurvatureColumn br s c ≤ rawCurvatureColumn br u c := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (curvatureWave_antitone 1 br (abs_le.mpr (frequency_mem j)) hus) (norm_nonneg _)
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

lemma transformedP_jet (k : ℕ) :
    (fun s : ℝ => (spectralPCLM (waveFunctionJet 0 1 k s)).re)=iteratedDeriv k transformedP := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,←hk]
    exact funext fun s => ((hasDerivAt_spectralP_wave 1 k s).real_of_complex).deriv.symm
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction

def rawRemainderConstant (br : Fin 2) (n : Fin 7) : ℝ :=
  ∑ j : Fin 31, remainderWave 0 br (nearNode n) (nearRadius n) (frequency j)*‖fourierCoeff j‖
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderBox (q br : Fin 2) (n : Fin 7) (j : Fin 31) (dnorm : RI) : RI :=
  (((((taylorPhaseTable q br j).normSq.mul (amplitudeNormBox q br j)).mul
    (remainderExpInput q br n j).exp.re).mul (((nearRadiusBox n).mul dnorm).pow 21)).divNat (23).factorial).mul
    ((RI.point 1).sub (((nearRadiusBox n).mul dnorm).divNat 24)).invPos
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def ordinarySignRow (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) : ℝ :=
  if side.val=0 then (if l.val=0 then ordinaryOffset n r else 0) -
    taylorRow side (nearNode n) (nearDisplacement n y) l.val r
  else taylorRow side (nearNode n) (nearDisplacement n y) l.val r
end AtomicTriangular.Construction
end

end OAI
end


