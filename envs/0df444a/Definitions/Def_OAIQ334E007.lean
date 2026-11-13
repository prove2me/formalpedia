-- Prove2me | Definitions.Def_OAIQ334E007
-- name    : OAIQ334E007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T12:54:24.73964+00:00
-- url     : https://prove2.me/theorems/82b264ed-d529-4f7a-928b-5afd061b3698
-- title:
--   Definitions bundle OAIQ334E007 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 33 definitions and 13 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.Spectrum`, `OAI.AtomicTriangular.Construction.atomFunction`, `OAI.AtomicTriangular.Construction.atomSpectral`, `OAI.AtomicTriangular.Construction.cVariation`, `OAI.AtomicTriangular.Construction.coeffAbs`, `OAI.AtomicTriangular.Construction.dVariation`, `OAI.AtomicTriangular.Construction.extend`, `OAI.AtomicTriangular.Construction.finiteSpectral`, `OAI.AtomicTriangular.Construction.frequencyFunction`, `OAI.AtomicTriangular.Construction.gaussian`, `OAI.AtomicTriangular.Construction.inputComplex`, `OAI.AtomicTriangular.Construction.integralCBasis`, `OAI.AtomicTriangular.Construction.integralDBasis`, `OAI.AtomicTriangular.Construction.integralLinear`, `OAI.AtomicTriangular.Construction.lambdaFunction`, `OAI.AtomicTriangular.Construction.outputComplex`, `OAI.AtomicTriangular.Construction.pairComplex`, `OAI.AtomicTriangular.Construction.phaseFunction`, `OAI.AtomicTriangular.Construction.radial`, `OAI.AtomicTriangular.Construction.spectralC`, `OAI.AtomicTriangular.Construction.spectralCCLM`, `OAI.AtomicTriangular.Construction.spectralCLinear`, `OAI.AtomicTriangular.Construction.spectralD`, `OAI.AtomicTriangular.Construction.spectralDCLM`, `OAI.AtomicTriangular.Construction.spectralDLinear`, `OAI.AtomicTriangular.Construction.spectralP`, `OAI.AtomicTriangular.Construction.spectralPCLM`, `OAI.AtomicTriangular.Construction.spectralParameter`, `OAI.AtomicTriangular.Construction.tailSpectral`, `OAI.AtomicTriangular.Construction.tailVariation`, `OAI.AtomicTriangular.Construction.transformedFunction`, `OAI.AtomicTriangular.Construction.transformedInput`, `OAI.AtomicTriangular.Construction.zetaFunction`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Basic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Basic.lean), [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Construction_Normalization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean), [`Triangular_Schwartz_FourierCLM`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/FourierCLM.lean), [`Triangular_Schwartz_FourierPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/FourierPair.lean), [`Triangular_Schwartz_InputCLM`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/InputCLM.lean), [`Triangular_Schwartz_SpectralCLM`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/SpectralCLM.lean), [`Triangular_Schwartz_TailSpectral`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/TailSpectral.lean).
--
--   **Imports.** It imports the bundle `OAIQ334E006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ334E009`, `OAIQ334E027` and `OAIQ334E031`; the proof of `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_eu`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ334E006

section
-- module Solutions.OAIQ334_EU.Triangular_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex Polynomial

namespace AtomicTriangular.Construction

def radial (x : Plane) : ℝ := b*‖x‖^2

def inputComplex (a : InputCoefficients) (x : Plane) : ℂ :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailInput a (radial x) +
    exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteInput a (radial x)

end AtomicTriangular.Construction

end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveIntervals
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

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

lemma complex_gaussian_transform (a : ℂ) (ha : 0 < a.re) (w : Plane) :
    𝓕 (fun x : Plane => Complex.exp (-(Real.pi : ℂ) * a * ‖x‖ ^ 2)) w =
      a⁻¹ * Complex.exp (-(Real.pi : ℂ) * ‖w‖ ^ 2 / a) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ha0 : a ≠ 0 := by intro h; subst a; simp at ha
  have hh : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  have hg := fourier_gaussian_innerProductSpace hh w
  have hf : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rw [hf] at hg
  norm_num at hg
  have hfun : (fun x : Plane => Complex.exp (-(Real.pi : ℂ) * a * ‖x‖ ^ 2)) =
      (fun x : Plane => Complex.exp (-((Real.pi : ℂ) * a * ‖x‖ ^ 2))) := by
    funext x
    congr 1
    ring
  rw [hfun, hg]
  have hquot : (Real.pi : ℂ) / ((Real.pi : ℂ) * a) = a⁻¹ := by field_simp
  rw [hquot]
  congr 2
  field_simp

def spectralParameter (k t : ℝ) : ℂ := (b:ℂ)*((k:ℂ)-I*t)

end AtomicTriangular.Construction

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_TailSpectral
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

def integralDBasis (n : Node) (s : ℂ) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (I*Real.pi * ∫ t in (0:ℝ)..frequency l, exp (I*Real.pi*(t:ℂ)*(s-n.val)))

def integralCBasis (n : Node) (s : ℂ) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (-(Real.pi:ℂ)^2 * ∫ t in (0:ℝ)..frequency l,
      ((frequency l:ℂ)-t)*exp (I*Real.pi*(t:ℂ)*(s-n.val)))

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction
abbrev Spectrum := Set.Icc (-(5/6):ℝ) (5/6)

def coeffAbs (l : Fin 31) : ℝ := ‖fourierCoeff l‖
lemma fourierCoeff_norm (l : Fin 31) : ‖fourierCoeff l‖ = coeffAbs l := rfl
def dVariation : ℝ := (∑ l : Fin 31, coeffAbs l * |frequency l|)*Real.pi
def cVariation : ℝ := (∑ l : Fin 31, coeffAbs l * (frequency l)^2)*Real.pi^2/2

 def extend (f : C(Spectrum,ℂ)) (t : ℝ) : ℂ := f (Set.projIcc (-(5/6)) (5/6) (by norm_num) t)
lemma continuous_extend (f : C(Spectrum,ℂ)) : Continuous (extend f) := by
  exact f.continuous.comp continuous_projIcc
lemma norm_extend_le (f : C(Spectrum,ℂ)) (t : ℝ) : ‖extend f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

def spectralC (n : Node) (f : C(Spectrum,ℂ)) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (-(Real.pi:ℂ)^2 * ∫ t in (0:ℝ)..frequency l,
      ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t)

def spectralD (n : Node) (f : C(Spectrum,ℂ)) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (I*Real.pi * ∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t)

def spectralP (f : C(Spectrum,ℂ)) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * f ⟨frequency l,frequency_mem l⟩

lemma norm_first_integral_le (f : ℝ → ℂ) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M) (t : ℝ) :
    ‖∫ r in (0:ℝ)..t, f r‖ ≤ M*|t| := by
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r _ => hM r) (a := 0) (b := t)

lemma norm_second_integral_le (f : ℝ → ℂ) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M) (t : ℝ) :
    ‖∫ r in (0:ℝ)..t, ((t:ℂ)-r)*f r‖ ≤ M*t^2/2 := by
  by_cases ht : 0 ≤ t
  · calc
      _ ≤ ∫ r in (0:ℝ)..t, (t-r)*M := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht
        · exact ae_of_all volume fun r hr => by
            rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr hr.2)]
            exact mul_le_mul_of_nonneg_left (hM r) (sub_nonneg.mpr hr.2)
        · exact (show Continuous (fun r : ℝ => (t-r)*M) by fun_prop).intervalIntegrable 0 t
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun _ : ℝ => t) (g := fun x : ℝ => x)
          intervalIntegrable_const (continuous_id.intervalIntegrable _ _), integral_id]
        simp only [intervalIntegral.integral_const, sub_zero, zero_pow, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, smul_eq_mul]
        ring
  · have ht' := le_of_not_ge ht
    rw [intervalIntegral.integral_symm, norm_neg]
    calc
      _ ≤ ∫ r in t..(0:ℝ), (r-t)*M := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht'
        · exact ae_of_all volume fun r hr => by
            rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr hr.1.le)]
            calc
              _ ≤ (-(t-r))*M := mul_le_mul_of_nonneg_left (hM r) (by linarith [hr.1])
              _ = _ := by ring
        · exact (show Continuous (fun r : ℝ => (r-t)*M) by fun_prop).intervalIntegrable t 0
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => t)
          (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id]
        simp only [intervalIntegral.integral_const, zero_sub, zero_pow, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, smul_eq_mul]
        ring

lemma spectralD_bound (n : Node) (f : C(Spectrum,ℂ)) :
    ‖spectralD n f‖ ≤ dVariation*‖f‖ := by
  have hb (l : Fin 31) : ‖∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t‖ ≤ ‖f‖*|frequency l| := by
    apply norm_first_integral_le
    intro t
    rw [norm_mul,norm_exp_neg_phase,one_mul]
    exact norm_extend_le f t
  calc
    _ ≤ ∑ l : Fin 31, (coeffAbs l * |frequency l|) * (Real.pi*‖f‖) := by
      unfold spectralD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      simp only [norm_mul,norm_exp_phase,fourierCoeff_norm,mul_one,Complex.norm_I,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
      calc
        _ ≤ coeffAbs l * (Real.pi * (‖f‖*|frequency l|)) := by
          have hp : 0 ≤ coeffAbs l := by rw [←fourierCoeff_norm]; positivity
          gcongr
          exact hb l
        _ = _ := by ring
    _ = _ := by rw [←Finset.sum_mul]; dsimp [dVariation] <;> ring

lemma spectralC_bound (n : Node) (f : C(Spectrum,ℂ)) :
    ‖spectralC n f‖ ≤ cVariation*‖f‖ := by
  have hb (l : Fin 31) : ‖∫ t in (0:ℝ)..frequency l,
      ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t‖ ≤
      ‖f‖*(frequency l)^2/2 := by
    have hi := norm_second_integral_le (fun t => exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t) ‖f‖
      (fun t => by rw [norm_mul,norm_exp_neg_phase,one_mul]; exact norm_extend_le f t) (frequency l)
    simpa only [mul_assoc] using hi
  calc
    _ ≤ ∑ l : Fin 31, (coeffAbs l * (frequency l)^2) * (Real.pi^2/2*‖f‖) := by
      unfold spectralC
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      simp only [norm_mul,norm_exp_phase,fourierCoeff_norm,mul_one,norm_neg,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      calc
        _ ≤ coeffAbs l * (Real.pi^2 * (‖f‖*(frequency l)^2/2)) := by
          have hp : 0 ≤ coeffAbs l := by rw [←fourierCoeff_norm]; positivity
          gcongr
          exact hb l
        _ = _ := by ring
    _ = _ := by rw [←Finset.sum_mul]; dsimp [cVariation] <;> ring

def integralLinear (w : ℝ → ℂ) (hw : Continuous w) (t : ℝ) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ r in (0:ℝ)..t, w r * extend f r
  map_add' f g := by
    simp only [extend,ContinuousMap.add_apply,mul_add]
    apply intervalIntegral.integral_add
    · exact (hw.mul (continuous_extend f)).intervalIntegrable 0 t
    · exact (hw.mul (continuous_extend g)).intervalIntegrable 0 t
  map_smul' c f := by
    simp only [extend,ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm (w _) c]
    exact intervalIntegral.integral_const_mul _ _

def spectralCLinear (n : Node) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n.val) * (-(Real.pi:ℂ)^2)) •
    integralLinear (fun t => ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val))
      (by fun_prop) (frequency l)

def spectralDLinear (n : Node) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n.val) * (I*Real.pi)) •
    integralLinear (fun t => exp (-I*Real.pi*(t:ℂ)*n.val))
      (by fun_prop) (frequency l)

lemma spectralCLinear_apply (n : Node) (f : C(Spectrum,ℂ)) :
    spectralCLinear n f = spectralC n f := by
  simp [spectralCLinear,spectralC,integralLinear,mul_assoc]
lemma spectralDLinear_apply (n : Node) (f : C(Spectrum,ℂ)) :
    spectralDLinear n f = spectralD n f := by
  simp [spectralDLinear,spectralD,integralLinear,mul_assoc]

def spectralCCLM (n : Node) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  (spectralCLinear n).mkContinuous cVariation (by
    intro f; rw [spectralCLinear_apply]; exact spectralC_bound n f)
def spectralDCLM (n : Node) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  (spectralDLinear n).mkContinuous dVariation (by
    intro f; rw [spectralDLinear_apply]; exact spectralD_bound n f)
def spectralPCLM : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  ∑ l : Fin 31, fourierCoeff l • ContinuousMap.evalCLM ℂ ⟨frequency l,frequency_mem l⟩

def phaseFunction (s : ℂ) : C(Spectrum,ℂ) :=
  ⟨fun t => exp (I*Real.pi*(t.val:ℂ)*s), by fun_prop⟩

def frequencyFunction : C(Spectrum,ℂ) := ⟨fun t => I*Real.pi*(t.val:ℂ), by fun_prop⟩

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_FourierCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform RealInnerProductSpace
open Complex Filter Set MeasureTheory GaussianFourier
namespace AtomicTriangular.Construction

def lambdaFunction (k : ℝ) (hk : 0 < k) : C(Spectrum,ℂ) :=
  ⟨fun t => lambda k t.val, by
    unfold lambda
    apply Continuous.div
    · fun_prop
    · unfold waveDen; fun_prop
    · intro t; exact_mod_cast (mul_pos b_pos (waveDen_pos hk t.val)).ne'⟩

def zetaFunction (k v : ℝ) (hk : 0 < k) : C(Spectrum,ℂ) :=
  ⟨fun t => I*Real.pi*zeta k v t.val, by
    have hX : Continuous (Xwave k) := by
      unfold Xwave
      exact continuous_const.div (by unfold waveDen; fun_prop) (fun t => (waveDen_pos hk t).ne')
    unfold zeta
    fun_prop⟩

def transformedFunction (k v : ℝ) (hk : 0 < k) (s : ℂ) : C(Spectrum,ℂ) :=
  lambdaFunction k hk * NormedSpace.exp (s • zetaFunction k v hk)

def atomFunction (k : ℝ) (x : Plane) : C(Spectrum,ℂ) :=
  exp (-(Real.pi:ℂ)*k*(radial x:ℂ)) • phaseFunction (radial x:ℂ)
def gaussian (k : ℝ) (x : Plane) : ℝ := Real.exp (-Real.pi*k*radial x)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

def tailVariation : ℝ := cVariation+dVariation

def tailSpectral (a : InputCoefficients) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  (a.C:ℂ) • spectralPCLM + ∑' n : TailNode,
    ((a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val)

def atomSpectral (S : Fin 31 → ℂ) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  ∑ j : Fin 31, S j • ContinuousMap.evalCLM ℂ ⟨frequency j,frequency_mem j⟩

def finiteSpectral (a : InputCoefficients) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  ∑ j : Fin 11,
    ((a.finiteC j:ℂ) • atomSpectral (FiniteCertificate.cCoefficient ⟨j.val,by omega⟩) +
     (a.finiteD j:ℂ) • atomSpectral (FiniteCertificate.dCoefficient ⟨j.val,by omega⟩))

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma h_pos : 0 < h := by norm_num [h]
lemma H_pos : 0 < H := by norm_num [H]

def transformedInput (a : InputCoefficients) (s : ℂ) : ℂ :=
  tailSpectral a (transformedFunction h h h_pos s) +
    finiteSpectral a (transformedFunction H h H_pos s)
def outputComplex (a : InputCoefficients) (x : Plane) : ℂ :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*transformedInput a (radial x)

def pairComplex (a₁ a₂ : InputCoefficients) : Plane → ℂ := inputComplex a₁ + outputComplex a₂
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma complex_fourier_smul (c : ℂ) (f : Plane → ℂ) : 𝓕 (c • f)=c • 𝓕 f := by
  ext w
  simp only [Real.fourier_eq,Pi.smul_apply,smul_comm _ c,MeasureTheory.integral_smul]
end AtomicTriangular.Construction
end

end OAI
end


