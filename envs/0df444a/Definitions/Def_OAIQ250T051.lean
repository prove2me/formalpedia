-- Prove2me | Definitions.Def_OAIQ250T051
-- name    : OAIQ250T051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:40.722953+00:00
-- url     : https://prove2.me/theorems/ab1a74ce-ceb6-413a-9620-8d2a629efa77
-- title:
--   Definitions bundle OAIQ250T051 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 70 declarations of OpenAI's Lean: 11 definitions and 59 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.directJetFunction`, `OAI.AtomicTriangular.Construction.finiteJ`, `OAI.AtomicTriangular.Construction.finiteJJet`, `OAI.AtomicTriangular.Construction.finiteTaylor`, `OAI.AtomicTriangular.Construction.outputComplex`, `OAI.AtomicTriangular.Construction.pairComplex`, `OAI.AtomicTriangular.Construction.rawConstantCurvature`, `OAI.AtomicTriangular.Construction.taylorRow`, `OAI.AtomicTriangular.Construction.taylorWave`, `OAI.AtomicTriangular.Construction.transformedFunction`, `OAI.AtomicTriangular.Construction.transformedInput`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Construction_ActualInterpolation`, `Triangular_Construction_CoefficientAddition`, `Triangular_Construction_CurvatureAnalytic`, `Triangular_Construction_CurvatureBoxes`, `Triangular_Construction_CurvatureSums`, `Triangular_Construction_DirectCoordinates`, `Triangular_Construction_DirectWaveJets`, `Triangular_Construction_FarCurvature`, `Triangular_Construction_FiniteCoordinates`, `Triangular_Construction_FinitePairBridge`, `Triangular_Construction_Normalization`, `Triangular_Construction_TailCoordinates`, `Triangular_Construction_TailInterpolation`, `Triangular_Schwartz_FourierCLM`, `Triangular_Schwartz_FourierPair`, `Triangular_Schwartz_InputCLM`, `Triangular_Schwartz_SpectralCLM`, `Triangular_Signs_DeletedAccuracy`, `Triangular_Signs_GaussianDeleted`, `Triangular_Signs_SineGrid1`, `Triangular_Signs_SineGridAnalytic`, `Triangular_Signs_SineGridDefs`, `Triangular_Taylor_CoefficientSpectral`, `Triangular_Taylor_CurvatureData00`, `Triangular_Taylor_CurvatureData01`, `Triangular_Taylor_FiniteTaylorIdentity`, `Triangular_Taylor_Taylor`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T003`, `OAIQ250T005`, `OAIQ250T008`, `OAIQ250T010` and `OAIQ250T011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T085`, `OAIQ250T086`, `OAIQ250T089`, `OAIQ250T093` and `OAIQ250T098`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T005
import Definitions.Def_OAIQ250T008
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def taylorWave (q branch : Fin 2) (m : ℤ) (l : ℕ) (t : ℝ) : ℂ :=
  taylorAmplitude q branch t * exp (taylorPhase q branch t*m) *
    (taylorPhase q branch t)^(l+2) / ((l+2).factorial:ℂ)

def taylorRow (side : Fin 2) (m : ℤ) (y : ℝ) (l : ℕ) (r : Fin 8) : ℝ :=
  y^l*(∑ q : Fin 2, ∑ j : Fin 31,
    (finiteSpectrum side q j r*taylorWave q 0 m l (frequency j) +
    finiteSpectrum (otherSide side) q j r*taylorWave q 1 m l (frequency j))).re

def finiteTaylor (side : Fin 2) (m : ℤ) (y : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  ∑ l ∈ Finset.range 21, (∑ r : Fin 8, taylorRow side m y l r*e r)*τ^l

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

def rawConstantCurvature (s : ℝ) : ℝ :=
  (∑ j : Fin 31, curvatureWave 0 1 s (frequency j)*‖fourierCoeff j‖)/2
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

lemma spectralP_phase (s : ℂ) : spectralP (phaseFunction s) = P s := by
  exact (P_fourier s).symm

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform RealInnerProductSpace
open Complex Filter Set MeasureTheory GaussianFourier
namespace AtomicTriangular.Construction

def transformedFunction (k v : ℝ) (hk : 0 < k) (s : ℂ) : C(Spectrum,ℂ) :=
  lambdaFunction k hk * NormedSpace.exp (s • zetaFunction k v hk)
lemma transformedFunction_apply (k v : ℝ) (hk : 0 < k) (s : ℂ) (t : Spectrum) :
    transformedFunction k v hk s t = transformedWave k v t.val s := by
  simp only [transformedFunction,ContinuousMap.mul_apply,exponential_apply]
  change lambda k t.val * exp (s*(I*Real.pi*zeta k v t.val)) = _
  unfold transformedWave
  congr 2
  ring
lemma fourier_atomFunction {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (atomFunction k) w = exp (-(Real.pi:ℂ)*v*(radial w:ℂ)) •
      transformedFunction k v hk (radial w:ℂ) := by
  ext t
  have hh := clm_fourier (ContinuousMap.evalCLM ℂ t) (atomFunction k) (integrable_atomFunction hk) w
  have ha := transformed_spectral_wave hk v t.val w
  change 𝓕 (fun x => atomFunction k x t) w = (𝓕 (atomFunction k) w) t at hh
  rw [← hh]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
    exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))) w =
    exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedFunction k v hk (radial w:ℂ) t
  rw [transformedFunction_apply]
  exact ha
lemma fourier_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*S (transformedFunction k v hk (radial w:ℂ)) := by
  have hh := clm_fourier S (atomFunction k) (integrable_atomFunction hk) w
  have he : (fun x => S (atomFunction k x)) =
      (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
    ext x
    simp only [atomFunction,map_smul,smul_eq_mul]
  rw [he,fourier_atomFunction hk v,map_smul] at hh
  exact hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma tailSpectral_apply (a : InputCoefficients) (f : C(Spectrum,ℂ)) :
    tailSpectral a f = (a.C:ℂ)*spectralP f +
      ∑' n : TailNode, ((a.tailC n:ℂ)*spectralC n.val f + (a.tailD n:ℂ)*spectralD n.val f) := by
  have ht := (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tailSpectral a)
  simpa only [tailSpectral,add_apply, smul_apply,
    ContinuousLinearMap.apply_apply,smul_eq_mul,spectralPCLM_apply,
    spectralCCLM_apply,spectralDCLM_apply] using congrArg (fun x => (a.C:ℂ)*spectralP f+x) ht

lemma atomSpectral_finiteC_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient j) (phaseFunction s) = finiteC j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteC_fourier]
  rfl
lemma atomSpectral_finiteD_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient j) (phaseFunction s) = finiteD j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteD_fourier]
  rfl

lemma finiteSpectral_phase (a : InputCoefficients) (s : ℂ) :
    finiteSpectral a (phaseFunction s) = finiteInput a s := by
  simp only [finiteSpectral,sum_apply,add_apply,
    smul_apply,smul_eq_mul,atomSpectral_finiteC_phase,atomSpectral_finiteD_phase,finiteInput]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_FiniteTaylorIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma hasDerivAt_finiteWaveJet (q br : Fin 2) (t : ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteWaveJet q br t k) (finiteWaveJet q br t (k+1) s) s := by
  unfold finiteWaveJet
  have hh := (((hasDerivAt_id s).const_mul (taylorPhase q br t)).cexp.const_mul
    (taylorAmplitude q br t)).mul_const ((taylorPhase q br t)^k)
  simpa only [finiteWaveJet,mul_one,one_mul,pow_succ,mul_assoc,mul_comm,mul_left_comm,
    id_eq] using hh

def finiteJJet (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ r : Fin 8, (e r:ℂ) * (∑ q : Fin 2, ∑ j : Fin 31,
    (finiteSpectrum side q j r * finiteWaveJet q 0 (frequency j) k s +
    finiteSpectrum (otherSide side) q j r * finiteWaveJet q 1 (frequency j) k s))
def finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (s : ℝ) : ℝ := (finiteJJet side e 0 s).re
lemma hasDerivAt_finiteJJet (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteJJet side e k) (finiteJJet side e (k+1) s) s := by
  have hj (r : Fin 8) (q : Fin 2) (j : Fin 31) :=
    ((hasDerivAt_finiteWaveJet q 0 (frequency j) k s).const_mul (finiteSpectrum side q j r)).add
    ((hasDerivAt_finiteWaveJet q 1 (frequency j) k s).const_mul (finiteSpectrum (otherSide side) q j r))
  have hq (r : Fin 8) (q : Fin 2) := HasDerivAt.sum (u := Finset.univ) (fun j _ => hj r q j)
  have hr (r : Fin 8) := (HasDerivAt.sum (u := Finset.univ) (fun q _ => hq r q)).const_mul (e r:ℂ)
  simpa only [finiteJJet,Finset.sum_apply,Pi.add_apply] using!
    HasDerivAt.sum (u := Finset.univ) (fun r _ => hr r)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_DirectWaveJets
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
lemma atomC_direct (a : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient a) (waveFunctionJet 0 0 0 s)=finiteC a s ∧
    atomSpectral (FiniteCertificate.cCoefficient a) (waveFunctionJet 0 0 1 s)=deriv (finiteC a) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,atomSpectral_finiteC_phase]
  · have he : (fun s => atomSpectral (FiniteCertificate.cCoefficient a) (phaseFunction s))=finiteC a := funext (atomSpectral_finiteC_phase a)
    have hh := ((atomSpectral (FiniteCertificate.cCoefficient a)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma atomD_direct (a : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient a) (waveFunctionJet 0 0 0 s)=finiteD a s ∧
    atomSpectral (FiniteCertificate.dCoefficient a) (waveFunctionJet 0 0 1 s)=deriv (finiteD a) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,atomSpectral_finiteD_phase]
  · have he : (fun s => atomSpectral (FiniteCertificate.dCoefficient a) (phaseFunction s))=finiteD a := funext (atomSpectral_finiteD_phase a)
    have hh := ((atomSpectral (FiniteCertificate.dCoefficient a)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma waveFunctionJet_direct_one (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 1 s= exp (-(Real.pi:ℂ)*(damping q-h)*s) •
      (waveFunctionJet 0 0 1 s-(Real.pi*(damping q-h):ℂ) • phaseFunction s) := by
  have he : waveFunctionJet q 0 0 = fun t => exp (-(Real.pi:ℂ)*(damping q-h)*t) • phaseFunction t := funext (waveFunctionJet_direct_zero q)
  have hh := (((hasDerivAt_id s).const_mul (-(Real.pi:ℂ)*(damping q-h))).cexp.smul (hasDerivAt_phaseFunction s)).deriv
  have hj := (hasDerivAt_waveFunctionJet q 0 0 s).deriv
  rw [he] at hj
  change deriv (fun t => exp (-(Real.pi:ℂ)*(damping q-h)*t) • phaseFunction t) s = _ at hh
  rw [←hj,hh]
  simp only [id_eq,mul_one]
  module
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
lemma tailSpectral_zero_coeff (C : ℝ) (a : TrigonometricCoefficients) :
    tailSpectral (coefficientInput C a 0)=(C:ℂ) • spectralPCLM := by
  ext f
  simp [tailSpectral_apply,coefficientInput,spectralPCLM_apply]
lemma tailSpectral_zero_constant (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput 0 a w)=
      ∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val) := by
  have hz : (0:ℂ) • spectralPCLM=(0:C(Spectrum,ℂ) →L[ℂ] ℂ) := by
    ext f
    change (0:ℂ)*_=0
    exact zero_mul _
  change (0:ℂ) • spectralPCLM+_= _
  rw [hz,zero_add]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_DirectCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma damped_wave_re (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (n : ℤ) :
    (T (waveFunctionJet q 0 0 n)).re=Real.exp (-Real.pi*(damping q-h)*n)*(T (waveFunctionJet 0 0 0 n)).re ∧
    (T (waveFunctionJet q 0 1 n)).re=Real.exp (-Real.pi*(damping q-h)*n)*
      ((T (waveFunctionJet 0 0 1 n)).re-Real.pi*(damping q-h)*(T (waveFunctionJet 0 0 0 n)).re) := by
  have he : exp (-(Real.pi:ℂ)*(damping q-h)*(n:ℂ))=(Real.exp (-Real.pi*(damping q-h)*n):ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; rfl
  constructor
  · rw [waveFunctionJet_direct_zero,map_smul,←waveFunctionJet_zero_phase,he]
    simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  · rw [waveFunctionJet_direct_one,map_smul,map_sub,map_smul,←waveFunctionJet_zero_phase,he]
    simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,sub_re,mul_im,sub_im,mul_zero,add_zero]
lemma negativeJet_direct_re (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (T (waveFunctionJet q 0 0 n)) (T (waveFunctionJet q 0 1 n))).re=
      Real.exp (Real.pi*(v-damping q)*n)/(Q n)*
        (if d.val=0 then -(T (waveFunctionJet 0 0 0 n)).re else
          (D n-Real.pi*(v-damping q))*(T (waveFunctionJet 0 0 0 n)).re-(T (waveFunctionJet 0 0 1 n)).re) := by
  rw [negativeJet_re,(damped_wave_re T q n).1,(damped_wave_re T q n).2]
  have he : Real.exp (Real.pi*(v-h)*n)*Real.exp (-Real.pi*(damping q-h)*n)=
      Real.exp (Real.pi*(v-damping q)*n) := by rw [←Real.exp_add]; congr 1; ring
  split_ifs
  · linear_combination (-(T (waveFunctionJet 0 0 0 n)).re/(Q n))*he
  · linear_combination (((D n-Real.pi*(v-damping q))*(T (waveFunctionJet 0 0 0 n)).re-(T (waveFunctionJet 0 0 1 n)).re)/(Q n))*he

def directJetFunction (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) : C(Spectrum,ℂ) :=
  (exp (Real.pi*(v-h)*(n:ℂ))*(Q n:ℂ)⁻¹) •
    (if d.val=0 then -waveFunctionJet q 0 0 n else
      ((D n:ℂ)-Real.pi*(v-h)) • waveFunctionJet q 0 0 n-waveFunctionJet q 0 1 n)
lemma negativeJet_direct_linear (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (T (waveFunctionJet q 0 0 n)) (T (waveFunctionJet q 0 1 n))=
      T (directJetFunction q v n d) := by
  unfold directJetFunction negativeJet
  split_ifs <;> simp only [map_smul,map_neg,map_sub,smul_eq_mul]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma finiteSpectral_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (v : ℝ) (n : ℤ) (d : Fin 2) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 v n d)).re=
      ∑ c : Fin 22,a c*(atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 v n d)).re := by
  rw [finiteSpectral_coefficient]
  simp only [sum_apply,smul_apply,smul_eq_mul,re_sum,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_TailCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
attribute [local instance] Classical.propDecidable
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma inputJJet_direct_negative (a : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (inputJJet a 0 0 n) (inputJJet a 0 1 n)=
      tailSpectral a (directJetFunction 0 v n d)+finiteSpectral a (directJetFunction 1 v n d) := by
  unfold inputJJet
  rw [negativeJet_add,negativeJet_direct_linear,negativeJet_direct_linear]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_TailInterpolation
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInterpolation
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_FinitePairBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma finiteSpectrum_dot (side q : Fin 2) (j : Fin 31) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8,(e r:ℂ)*finiteSpectrum side q j r)=
      if q.val=0 then ((gamma side *ᵥ e) 2:ℂ)*fourierCoeff j
      else ∑ c : Fin 22,(finiteApprox side e c:ℂ)*finiteColumn ⟨c.val,by omega⟩ j := by
  by_cases hq : q.val=0
  · simp only [finiteSpectrum,hq,↓reduceIte,Acoefficient_constant,Matrix.mulVec,dotProduct,
      ofReal_sum,ofReal_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  · simp only [finiteSpectrum,hq,↓reduceIte,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    change (∑ r : Fin 8,(e r:ℂ)*(finiteColumn ⟨c.val,by omega⟩ j*(Acoefficient side ⟨c.val,by omega⟩ r:ℂ)))=
      ((∑ r : Fin 8,Acoefficient side ⟨c.val,by omega⟩ r*e r:ℝ):ℂ)*finiteColumn ⟨c.val,by omega⟩ j
    simp only [ofReal_sum,ofReal_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
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

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CoefficientAddition
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

lemma curvatureWave_direct (q : Fin 2) (s t : ℝ) :
    curvatureWave q 0 s t = Real.pi^2*(t^2+(damping q-h)^2)*Real.exp (-Real.pi*(damping q-h)*s) := by
  unfold curvatureWave
  rw [←Complex.normSq_eq_norm_sq]
  simp only [taylorPhase,taylorAmplitude,Fin.val_zero,↓reduceIte,norm_one,mul_one,
    Complex.normSq_apply,sub_re,sub_im,mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,
    zero_mul,mul_zero,one_mul,sub_zero,zero_sub,zero_add]
  ring_nf
lemma curvatureWave_transformed (q : Fin 2) (s t : ℝ) :
    curvatureWave q 1 s t = Real.pi^2*(h^2+(4/3-2*damping q*h)*Xwave (damping q) t)*
      Real.sqrt (Xwave (damping q) t)*Real.exp (-Real.pi*(damping q*Xwave (damping q) t-h)*s) := by
  simp only [curvatureWave,taylorPhase,taylorAmplitude,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [norm_wavePhase (damping_pos q),norm_lambda (damping_pos q),wavePhase_re,mul_pow,
    Real.sq_sqrt]
  rw [←normSq_zeta (damping_pos q)]
  exact normSq_nonneg _
lemma curvatureWave_even (q br : Fin 2) (s t : ℝ) :
    curvatureWave q br s (-t)=curvatureWave q br s t := by
  fin_cases br
  · simp [curvatureWave_direct]
  · simp [curvatureWave_transformed,Xwave,waveDen]
lemma curvatureWave_abs (q br : Fin 2) (s t : ℝ) :
    curvatureWave q br s |t|=curvatureWave q br s t := by
  rcases le_total 0 t with ht|ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht,curvatureWave_even]
lemma curvature_tail_direct {s t : ℝ} (ht : |t|≤5/6) :
    curvatureWave 0 0 s t ≤ curvatureWave 0 0 s (5/6) := by
  rw [curvatureWave_direct,curvatureWave_direct]
  norm_num [damping]
  have hh : t^2≤(5/6:ℝ)^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by norm_num)).mpr ht
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hh)]
lemma curvature_tail_zero {t : ℝ} (_ht : |t|≤5/6) :
    curvatureWave 0 1 0 t ≤ curvatureWave 0 1 0 0 := by
  rw [curvatureWave_transformed,curvatureWave_transformed]
  simp only [mul_zero,Real.exp_zero,mul_one]
  have hx : Xwave (damping 0) t≤Xwave (damping 0) 0 := by
    rw [←show Xwave (damping 0) |t|=Xwave (damping 0) t by simp [Xwave,waveDen]]
    exact Xwave_antitone (damping_pos 0) le_rfl (abs_nonneg t)
  have h1 : 0≤4/3-2*damping 0*h := by norm_num [damping,h]
  apply mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hx h1) _) (sq_nonneg _)) (Real.sqrt_le_sqrt hx) (Real.sqrt_nonneg _)
  exact mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (mul_nonneg h1 (Xwave_pos (damping_pos 0) 0).le))
lemma curvature_tail_positive {s t : ℝ} (hs : 1 ≤ s) (ht : |t| ≤ 5/6) :
    curvatureWave 0 1 s t ≤ curvatureWave 0 1 s (5/6) := by
  rw [←curvatureWave_abs 0 1 s t]
  rw [curvatureWave_transformed,curvatureWave_transformed]
  have hx := Xwave_pos (damping_pos 0) (5/6)
  have hxy := Xwave_antitone (damping_pos 0) (abs_nonneg t) ht
  have hbase : (3/2:ℝ)≤Real.pi*h*Xwave h (5/6) := by
    have hp := Real.pi_gt_three
    norm_num [Xwave,waveDen,h] at *
    linarith
  have hb : (3/2:ℝ)≤(Real.pi*damping 0*s)*Xwave (damping 0) (5/6) := by
    change (3/2:ℝ)≤(Real.pi*h*s)*Xwave h (5/6)
    have hh : 0 ≤ h := by norm_num [h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg Real.pi_pos.le (mul_nonneg hh hx.le))]
  have hh := Envelope.linear_sqrt_exp_antitone hx hxy (sq_nonneg h)
    (show 0≤4/3-2*damping 0*h by norm_num [damping,h]) hb
  have he (x : ℝ) : Real.exp (-Real.pi*(damping 0*x-h)*s) =
      Real.exp (Real.pi*h*s)*Real.exp (-(Real.pi*damping 0*s)*x) := by
    rw [←Real.exp_add]; congr 1; ring
  rw [he,he]
  convert mul_le_mul_of_nonneg_left hh (show 0≤Real.pi^2*Real.exp (Real.pi*h*s) by positivity) using 1 <;> first | rfl | ring
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
lemma curvatureData00_2_pre (j : Fin 31) : (curvatureExpInput 0 0 2 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_3_pre (j : Fin 31) : (curvatureExpInput 0 0 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_4_pre (j : Fin 31) : (curvatureExpInput 0 0 4 j).normSq.hi ≤ scale*1024^2 := by
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
lemma curvatureData01_0_pre (j : Fin 31) : (curvatureExpInput 0 1 0 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_1_pre (j : Fin 31) : (curvatureExpInput 0 1 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_2_pre (j : Fin 31) : (curvatureExpInput 0 1 2 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_3_pre (j : Fin 31) : (curvatureExpInput 0 1 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_4_pre (j : Fin 31) : (curvatureExpInput 0 1 4 j).normSq.hi ≤ scale*1024^2 := by
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
lemma curvatureConstant3_calc : (RI.sum (fun j : Fin 31 => (curvatureTable01 3 j).mul (columnNorm22 j))).divNat 2=curvatureConstant3 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma local_geometry (u : Fin 30) :
    |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j := by
  exact (show ∀ u : Fin 30, |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j by decide +kernel) u
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma sin_abs_local (u : Fin 30) (j : Fin 15) (y : ℝ) :
    |Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|=
      |Real.sin (Real.pi*((localPhase u j:ℝ)+y)/36)| := by
  have he : (localCenter u:ℝ)-residue j=localPhase u j+36*(localShift u j:ℝ) := by
    exact_mod_cast (local_geometry u).2.2 j
  rw [show (localCenter u:ℝ)+y-residue j=(localPhase u j:ℝ)+y+36*(localShift u j:ℝ) by linarith,
    show Real.pi*((localPhase u j:ℝ)+y+36*(localShift u j:ℝ))/36=
      Real.pi*((localPhase u j:ℝ)+y)/36+(localShift u j:ℝ)*Real.pi by ring,
    Real.sin_add_int_mul_pi,abs_mul,abs_zpow]
  norm_num
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

lemma transformedP_jet (k : ℕ) :
    (fun s : ℝ => (spectralPCLM (waveFunctionJet 0 1 k s)).re)=iteratedDeriv k transformedP := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,←hk]
    exact funext fun s => ((hasDerivAt_spectralP_wave 1 k s).real_of_complex).deriv.symm
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

def transformedInput (a : InputCoefficients) (s : ℂ) : ℂ :=
  tailSpectral a (transformedFunction h h h_pos s) +
    finiteSpectral a (transformedFunction H h H_pos s)
def outputComplex (a : InputCoefficients) (x : Plane) : ℂ :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*transformedInput a (radial x)
lemma outputComplex_radial (a : InputCoefficients) (x y : Plane) (hxy : ‖x‖=‖y‖) : outputComplex a x = outputComplex a y := by
  simp only [outputComplex,radial,hxy]

def pairComplex (a₁ a₂ : InputCoefficients) : Plane → ℂ := inputComplex a₁ + outputComplex a₂
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma finiteJ_contDiff (side : Fin 2) (e : Fin 8 → ℝ) : ContDiff ℝ ⊤ (finiteJ side e) := by
  have he : finiteJ side e=pairJ (coefficientInput ((gamma side *ᵥ e) 2) (finiteApprox side e) 0)
      (coefficientInput ((gamma (otherSide side) *ᵥ e) 2) (finiteApprox (otherSide side) e) 0) := by
    funext s; exact congrArg Complex.re (finiteJJet_pair side e 0 s)
  rw [he]
  exact pairJ_contDiff _ _
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_GaussianDeleted
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
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors11 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 11 k j) ∧ cellBarrier 11 < ∏ j : Fin 15,(cellFactor 11 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 11 k j) ∧ cellBarrier 11 < ∏ j : Fin 15,(cellFactor 11 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors12 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 12 k j) ∧ cellBarrier 12 < ∏ j : Fin 15,(cellFactor 12 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 12 k j) ∧ cellBarrier 12 < ∏ j : Fin 15,(cellFactor 12 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors13 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 13 k j) ∧ cellBarrier 13 < ∏ j : Fin 15,(cellFactor 13 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 13 k j) ∧ cellBarrier 13 < ∏ j : Fin 15,(cellFactor 13 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Normalization
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


