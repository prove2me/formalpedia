-- Prove2me | Definitions.Def_OAIQ262T146
-- name    : OAIQ262T146
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T20:15:25.557204+00:00
-- url     : https://prove2.me/theorems/8382f478-786e-4ec2-a4cc-4a79cbcd6144
-- title:
--   Definitions bundle OAIQ262T146 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 38 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Construction_ActualInterpolation`, `Triangular_Construction_CoefficientAddition`, `Triangular_Construction_FiniteRemainder`, `Triangular_Construction_Normalization`, `Triangular_Construction_TailInterpolation`, `Triangular_Schwartz_SpectralCLM`, `Triangular_Schwartz_TailSpectral`, `Triangular_Signs_GaussianDeleted`, `Triangular_Signs_RemainderData0`, `Triangular_Signs_RemainderData1`, `Triangular_Signs_RemainderData2`, `Triangular_Signs_RemainderData3`, `Triangular_Signs_SineGlobal`, `Triangular_Signs_SineGridChecks`, `Triangular_Taylor_FiniteTaylorError`, `Triangular_Taylor_FiniteTaylorIdentity`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T092`, `OAIQ262T094`, `OAIQ262T095`, `OAIQ262T096`, `OAIQ262T097`, `OAIQ262T098`, `OAIQ262T099`, `OAIQ262T100`, `OAIQ262T101`, `OAIQ262T102`, `OAIQ262T103`, `OAIQ262T104`, `OAIQ262T105`, `OAIQ262T106`, `OAIQ262T107`, `OAIQ262T108`, `OAIQ262T109`, `OAIQ262T110`, `OAIQ262T111`, `OAIQ262T112`, `OAIQ262T113`, `OAIQ262T114`, `OAIQ262T115`, `OAIQ262T116`, `OAIQ262T117`, `OAIQ262T118`, `OAIQ262T119`, `OAIQ262T120`, `OAIQ262T121`, `OAIQ262T122`, `OAIQ262T123`, `OAIQ262T124`, `OAIQ262T125`, `OAIQ262T126`, `OAIQ262T127`, `OAIQ262T128`, `OAIQ262T129`, `OAIQ262T130`, `OAIQ262T131`, `OAIQ262T132`, `OAIQ262T133`, `OAIQ262T134`, `OAIQ262T135` and `OAIQ262T136` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T158`, `OAIQ262T159` and `OAIQ262T166`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T092
import Definitions.Def_OAIQ262T094
import Definitions.Def_OAIQ262T095
import Definitions.Def_OAIQ262T096
import Definitions.Def_OAIQ262T097
import Definitions.Def_OAIQ262T098
import Definitions.Def_OAIQ262T099
import Definitions.Def_OAIQ262T100
import Definitions.Def_OAIQ262T101
import Definitions.Def_OAIQ262T102
import Definitions.Def_OAIQ262T103
import Definitions.Def_OAIQ262T104
import Definitions.Def_OAIQ262T105
import Definitions.Def_OAIQ262T106
import Definitions.Def_OAIQ262T107
import Definitions.Def_OAIQ262T108
import Definitions.Def_OAIQ262T109
import Definitions.Def_OAIQ262T110
import Definitions.Def_OAIQ262T111
import Definitions.Def_OAIQ262T112
import Definitions.Def_OAIQ262T113
import Definitions.Def_OAIQ262T114
import Definitions.Def_OAIQ262T115
import Definitions.Def_OAIQ262T116
import Definitions.Def_OAIQ262T117
import Definitions.Def_OAIQ262T118
import Definitions.Def_OAIQ262T119
import Definitions.Def_OAIQ262T120
import Definitions.Def_OAIQ262T121
import Definitions.Def_OAIQ262T122
import Definitions.Def_OAIQ262T123
import Definitions.Def_OAIQ262T124
import Definitions.Def_OAIQ262T125
import Definitions.Def_OAIQ262T126
import Definitions.Def_OAIQ262T127
import Definitions.Def_OAIQ262T128
import Definitions.Def_OAIQ262T129
import Definitions.Def_OAIQ262T130
import Definitions.Def_OAIQ262T131
import Definitions.Def_OAIQ262T132
import Definitions.Def_OAIQ262T133
import Definitions.Def_OAIQ262T134
import Definitions.Def_OAIQ262T135
import Definitions.Def_OAIQ262T136

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
-- module Solutions.OAIQ262_TG.Triangular_Taylor_FiniteTaylorIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma hasDerivAt_finiteJJet (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteJJet side e k) (finiteJJet side e (k+1) s) s := by
  have hj (r : Fin 8) (q : Fin 2) (j : Fin 31) :=
    ((hasDerivAt_finiteWaveJet q 0 (frequency j) k s).const_mul (finiteSpectrum side q j r)).add
    ((hasDerivAt_finiteWaveJet q 1 (frequency j) k s).const_mul (finiteSpectrum (otherSide side) q j r))
  have hq (r : Fin 8) (q : Fin 2) := HasDerivAt.sum (u := Finset.univ) (fun j _ => hj r q j)
  have hr (r : Fin 8) := (HasDerivAt.sum (u := Finset.univ) (fun q _ => hq r q)).const_mul (e r:ℂ)
  simpa only [finiteJJet,Finset.sum_apply,Pi.add_apply] using!
    HasDerivAt.sum (u := Finset.univ) (fun r _ => hr r)
lemma finiteJJet_re_iterated (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) :
    (fun s : ℝ => (finiteJJet side e k s).re) = iteratedDeriv k (finiteJ side e) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,← hk]
    exact funext fun s => ((hasDerivAt_finiteJJet side e k s).real_of_complex).deriv.symm
lemma taylorRow_dot (side : Fin 2) (m : ℤ) (y : ℝ) (l : ℕ) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8, taylorRow side m y l r*e r) =
      (iteratedDeriv (l+2) (finiteJ side e) m) * y^l / ((l+2).factorial:ℝ) := by
  rw [← finiteJJet_re_iterated]
  simp only [taylorRow,taylorWave_eq,finiteJJet,Complex.ofReal_intCast,
    ← mul_div_assoc,← add_div,← Finset.sum_div]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  simp only [Finset.sum_mul,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Complex.re_sum,← Complex.ofReal_natCast,Complex.div_ofReal_re,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.add_re]
  ring
lemma finiteTaylor_exact (side : Fin 2) (m : ℤ) (y : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) :
    finiteTaylor side m y e τ = ∑ l ∈ Finset.range 21,
      (iteratedDeriv (l+2) (finiteJ side e) m) * y^l / ((l+2).factorial:ℝ) * τ^l := by
  unfold finiteTaylor
  apply Finset.sum_congr rfl
  intro l hl
  rw [taylorRow_dot]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_TailInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma pairJJet_negative (a₁ a₂ : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (pairJJet a₁ a₂ 0 n) (pairJJet a₁ a₂ 1 n)=
      negativeJet v n d (inputJJet a₁ 0 0 n) (inputJJet a₁ 0 1 n)+
      negativeJet v n d (inputJJet a₂ 1 0 n) (inputJJet a₂ 1 1 n) := by
  exact negativeJet_add _ _ _ _ _ _ _
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma negativeJet_injective (v : ℝ) (n : Node) (a b c d : ℂ)
    (h0 : (negativeJet v n.val 0 a b).re=(negativeJet v n.val 0 c d).re)
    (h1 : (negativeJet v n.val 1 a b).re=(negativeJet v n.val 1 c d).re) :
    a.re=c.re ∧ b.re=d.re := by
  simp only [negativeJet_re,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte] at h0 h1
  have hp : Real.exp (Real.pi*(v-h)*n.val)/Q n.val≠0 := div_ne_zero (Real.exp_ne_zero _) (Q_node_ne n)
  have ha : a.re=c.re := by
    have hh := mul_left_cancel₀ hp h0
    linarith
  have hb := mul_left_cancel₀ hp h1
  constructor
  · exact ha
  · rw [ha] at hb
    linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CoefficientAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma inputJJet_split (C : ℝ) (a da : TrigonometricCoefficients) (w : TailCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C (a+da) w) br k s=
      inputJJet (coefficientInput C a 0) br k s+inputJJet (coefficientInput 0 da w) br k s := by
  have hzero (T : C(Spectrum,ℂ) →L[ℂ] ℂ) : (0:ℂ) • T=0 := by
    ext f
    exact zero_mul _
  simp only [hzero,inputJJet,tailSpectral_coefficient,finiteSpectral_coefficient_apply,
    lp.coeFn_add,lp.coeFn_zero,Pi.zero_apply,add_zero,tsum_zero,Pi.add_apply,ofReal_add,ofReal_zero,zero_add,_root_.add_apply,
    _root_.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData0_00_pre (j : Fin 31) : (remainderExpInput 0 0 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_01_pre (j : Fin 31) : (remainderExpInput 0 1 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_10_pre (j : Fin 31) : (remainderExpInput 1 0 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_11_pre (j : Fin 31) : (remainderExpInput 1 1 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData1_00_pre (j : Fin 31) : (remainderExpInput 0 0 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData1_01_pre (j : Fin 31) : (remainderExpInput 0 1 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData1_10_pre (j : Fin 31) : (remainderExpInput 1 0 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData1_11_pre (j : Fin 31) : (remainderExpInput 1 1 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData2_00_pre (j : Fin 31) : (remainderExpInput 0 0 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData2_01_pre (j : Fin 31) : (remainderExpInput 0 1 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData2_10_pre (j : Fin 31) : (remainderExpInput 1 0 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData2_11_pre (j : Fin 31) : (remainderExpInput 1 1 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData3_00_pre (j : Fin 31) : (remainderExpInput 0 0 3 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 3).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData3_01_pre (j : Fin 31) : (remainderExpInput 0 1 3 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 3).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData3_10_pre (j : Fin 31) : (remainderExpInput 1 0 3 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 3).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData3_11_pre (j : Fin 31) : (remainderExpInput 1 1 3 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 3).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma inputJJet_zero_tail (C : ℝ) (a : TrigonometricCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C a 0) br k s=
      (C:ℂ)*(∑ j : Fin 31,fourierCoeff j*finiteWaveJet 0 br (frequency j) k s)+
      ∑ c : Fin 22,(a c:ℂ)*(∑ j : Fin 31,finiteColumn ⟨c.val,by omega⟩ j*finiteWaveJet 1 br (frequency j) k s) := by
  rw [inputJJet,tailSpectral_zero_coeff,finiteSpectral_coefficient_apply]
  simp only [_root_.smul_apply,smul_eq_mul,spectralPCLM_apply,spectralP,waveFunctionJet_apply]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_FiniteTaylorError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma complexDeleted_finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (m v : ℝ) :
    (complexDeleted (fun k s => finiteJJet side e k s) m v).re=deletedSecond (finiteJ side e) m (m+v) := by
  apply complexDeleted_re
  · intro s; rfl
  · simpa only [iteratedDeriv_one] using congrFun (finiteJJet_re_iterated side e 1) m
  · exact congrFun (finiteJJet_re_iterated side e 2) m
lemma complexTaylor_finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (m : ℤ) (y τ : ℝ) :
    (complexTaylor (fun k s => finiteJJet side e k s) m (y*τ)).re=finiteTaylor side m y e τ := by
  rw [finiteTaylor_exact]
  simp only [complexTaylor,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Complex.ofReal_natCast,Complex.div_ofReal_re,←Complex.ofReal_pow,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [congrFun (finiteJJet_re_iterated side e (j+2)) m,mul_pow]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_GaussianDeleted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
lemma gaussian_deleted_nonneg {z : ℝ} (hz : 0<z) (m v : ℝ) :
    0 ≤ deletedSecond (gaussianG z) m (m+v) := by
  apply deletedSecond_lower ((gaussianG_contDiff z).of_le (by norm_num))
  intro t _
  rw [gaussianG_second hz]
  exact div_nonneg (mul_nonneg (div_nonneg Q_one_pos.le hz.le) (Real.exp_pos _).le) (by norm_num)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cell_geometry (u : Fin 30) (k : Fin 100) :
    0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
    (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18) := by
  fin_cases u
  · exact cellGeometry00 k
  · exact cellGeometry01 k
  · exact cellGeometry02 k
  · exact cellGeometry03 k
  · exact cellGeometry04 k
  · exact cellGeometry05 k
  · exact cellGeometry06 k
  · exact cellGeometry07 k
  · exact cellGeometry08 k
  · exact cellGeometry09 k
  · exact cellGeometry10 k
  · exact cellGeometry11 k
  · exact cellGeometry12 k
  · exact cellGeometry13 k
  · exact cellGeometry14 k
  · exact cellGeometry15 k
  · exact cellGeometry16 k
  · exact cellGeometry17 k
  · exact cellGeometry18 k
  · exact cellGeometry19 k
  · exact cellGeometry20 k
  · exact cellGeometry21 k
  · exact cellGeometry22 k
  · exact cellGeometry23 k
  · exact cellGeometry24 k
  · exact cellGeometry25 k
  · exact cellGeometry26 k
  · exact cellGeometry27 k
  · exact cellGeometry28 k
  · exact cellGeometry29 k
lemma cell_factors (u : Fin 30) (k : Fin 100) :
    (∀ j : Fin 15,0 ≤ cellFactor u k j) ∧ cellBarrier u < ∏ j : Fin 15,(cellFactor u k j)^2 := by
  fin_cases u
  · exact cellFactors00 k
  · exact cellFactors01 k
  · exact cellFactors02 k
  · exact cellFactors03 k
  · exact cellFactors04 k
  · exact cellFactors05 k
  · exact cellFactors06 k
  · exact cellFactors07 k
  · exact cellFactors08 k
  · exact cellFactors09 k
  · exact cellFactors10 k
  · exact cellFactors11 k
  · exact cellFactors12 k
  · exact cellFactors13 k
  · exact cellFactors14 k
  · exact cellFactors15 k
  · exact cellFactors16 k
  · exact cellFactors17 k
  · exact cellFactors18 k
  · exact cellFactors19 k
  · exact cellFactors20 k
  · exact cellFactors21 k
  · exact cellFactors22 k
  · exact cellFactors23 k
  · exact cellFactors24 k
  · exact cellFactors25 k
  · exact cellFactors26 k
  · exact cellFactors27 k
  · exact cellFactors28 k
  · exact cellFactors29 k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma realP_local_strict (u : Fin 30) {x : ℝ} (hx : x∈Icc 0 1)
    (hy : (localHalf u:ℝ)*x≠0) :
    (cellBarrier u:ℝ)*((localHalf u:ℝ)*x)^2 < realP ((localCenter u:ℝ)+(localHalf u:ℝ)*x) := by
  obtain ⟨k,hk⟩ := unit_grid_cover hx
  exact realP_cell_lower u k (cell_geometry u k) (cell_factors u k).1 (cell_factors u k).2
    (cell_displacement u k hk) hy
lemma realP_local_lower (u : Fin 30) {x : ℝ} (hx : x∈Icc 0 1) :
    (cellBarrier u:ℝ)*((localHalf u:ℝ)*x)^2 ≤ realP ((localCenter u:ℝ)+(localHalf u:ℝ)*x) := by
  by_cases hy : (localHalf u:ℝ)*x=0
  · simpa only [hy,zero_pow (by norm_num : 2≠0),mul_zero,add_zero] using realP_nonneg (localCenter u)
  · exact (realP_local_strict u hx hy).le
lemma realP_far_lower {s : ℝ} (hs : (23:ℝ)  ≤  s) :
    ∃ m : Node, 25 ≤ m.val ∧ (27/500:ℝ)*(s-m.val)^2 ≤ realP s := by
  let q : ℕ := ⌊(s+5/2)/36⌋₊
  let t : ℝ := s-36*q
  have hq0 : (q:ℝ) ≤ (s+5/2)/36 := Nat.floor_le (by linarith)
  have hq1 : (s+5/2)/36<(q:ℝ)+1 := Nat.lt_floor_add_one _
  have ht : t∈Ico (-(5/2)) (67/2) := by dsimp [t]; constructor <;> linarith
  obtain ⟨u,x,hx,htu,hcell⟩ := local_halfGap_cover ht
  let m : ℤ := 36*(q:ℤ)+localCenter u
  have hm : 25 ≤ m := by
    by_cases hq : q=0
    · have ht0 : t=s := by simp [t,hq]
      have hg := (local_boundary_geometry u).2.2.2.2.2.1
      by_contra! hh
      have hu : localCenter u<25 := by simpa [m,hq] using hh
      have hhB : (localBoundary (u.val+1):ℝ) ≤ 23 := by exact_mod_cast hg hu
      linarith [hcell.2]
    · have hqc : (1:ℤ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      have huc := (local_boundary_geometry u).2.2.2.1
      dsimp [m]
      omega
  have hmres : m%36∈residues := by
    simpa only [m,Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_emod] using
      (local_boundary_geometry u).2.2.2.2.1
  refine ⟨⟨m,by omega,hmres⟩,hm,?_⟩
  have hp := realP_local_lower u hx
  have hp' := mul_le_mul_of_nonneg_right (cellBarrier_lower u) (sq_nonneg ((localHalf u:ℝ)*x))
  have hP : realP t=realP s := by
    convert realP_periodic.sub_nat_mul_eq q using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [t]
    ring_nf
  have hsm : s-(m:ℝ)=(localHalf u:ℝ)*x := by
    dsimp [m,t] at *
    push_cast
    linarith
  change (27/500:ℝ)*(s-(m:ℝ))^2 ≤ realP s
  rw [hsm,←hP,htu]
  exact hp'.trans hp
lemma realP_middle_lower {s : ℝ} (hs : s∈Icc (29/2) 23) :
    ∃ m : ℤ,m∈({16,19,21}:Finset ℤ) ∧ (3:ℝ)*(s-m)^2 ≤ realP s := by
  by_cases he : s=23
  · subst s
    refine ⟨21,by simp,?_⟩
    have hh := realP_local_lower (21:Fin 30) (x:=1) (by simp)
    have hc : localCenter (21:Fin 30)=21 ∧ localHalf (21:Fin 30)=2 ∧ cellBarrier (21:Fin 30)=3 := by decide +kernel
    rw [hc.1,hc.2.1,hc.2.2] at hh
    norm_num at hh ⊢
    exact hh
  · obtain ⟨u,x,hx,htu,hcell⟩ := local_halfGap_cover (t:=s) (by constructor <;> linarith [hs.1,hs.2])
    have hu : 16 ≤ u.val ∧ u.val ≤ 21 := by
      have hg := local_boundary_geometry u
      constructor
      · by_contra! h
        have hh : (localBoundary (u.val+1):ℝ) ≤ 29/2 := by
          have ht := Rat.cast_le (K:=ℝ) |>.mpr (hg.2.2.2.2.2.2.1 h)
          norm_num at ht ⊢
          exact ht
        linarith [hcell.2,hs.1,hs.2]
      · by_contra! h
        have hh : (23:ℝ) ≤ localBoundary u.val := by exact_mod_cast hg.2.2.2.2.2.2.2 h
        have hss : s<23 := lt_of_le_of_ne hs.2 he
        linarith [hcell.1,hss]
    refine ⟨localCenter u,(strong_local_geometry u hu).1,?_⟩
    have hh := realP_local_lower u hx
    rw [(strong_local_geometry u hu).2] at hh
    norm_num only [Rat.cast_ofNat] at hh
    rw [htu]
    simpa only [add_sub_cancel_left] using hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma waveFunctionJet_transformed_zero (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 1 0 s=transformedFunction (damping q) h (damping_pos q) s := by
  simp only [waveFunctionJet,waveAmplitudeFunction,wavePhaseFunction,Fin.val_one,Nat.one_ne_zero,↓reduceIte,pow_zero,mul_one,transformedFunction]
lemma inputJJet_transformed_zero (a : InputCoefficients) (s : ℂ) :
    inputJJet a 1 0 s=transformedInput a s := by
  rw [inputJJet,waveFunctionJet_transformed_zero,waveFunctionJet_transformed_zero]
  rfl
lemma gaussian_normalization {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
    Real.exp (-Real.pi*h*radial x)*gaussianG (gaussianZ α) (radial x)/normalizingDen (gaussianZ α)=
      AtomicTriangular.gaussian α x := by
  have hz := (gaussianZ_bounds hα).1
  have he : (-Real.pi*h*radial x)+(1-radial x)/gaussianZ α-1/gaussianZ α = -Real.pi*α*‖x‖^2 := by
    simp only [gaussianZ,radial]
    field_simp [b_pos.ne']
    ring
  rw [gaussianG,normalizingDen,AtomicTriangular.gaussian]
  have hc : Q 1*gaussianZ α≠0 := mul_ne_zero Q_one_pos.ne' hz.ne'
  calc
    _ = Real.exp (-Real.pi*h*radial x)*Real.exp ((1-radial x)/gaussianZ α)/Real.exp (1/gaussianZ α) := by field_simp [Q_one_pos.ne',hz.ne']
    _ = _ := by rw [←Real.exp_add,←Real.exp_sub,he]
end AtomicTriangular.Construction
end

end OAI
end


