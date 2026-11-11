-- Prove2me | Definitions.Def_OAIQ239Tc002
-- name    : OAIQ239Tc002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:09:55.42938+00:00
-- url     : https://prove2.me/theorems/6fc01a66-7680-4eb1-99db-b7d58ca30164
-- title:
--   Definitions bundle OAIQ239Tc002 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 144 declarations of OpenAI's Lean: 42 definitions, 2 instances and 100 theorems. The definitions and types are `OAI.TamingCompatibility.Concentration.cutKernel`, `OAI.TamingCompatibility.Concentration.radialCoefficient`, `OAI.TamingCompatibility.Concentration.rationalKernel`, `OAI.TamingCompatibility.Concentration.testOne`, `OAI.TamingCompatibility.EuclideanEnergy.Pair`, `OAI.TamingCompatibility.EuclideanEnergy.pair`, `OAI.TamingCompatibility.EuclideanSobolev.boundedDistributionCLM`, `OAI.TamingCompatibility.EuclideanSobolev.boundedToLpTop`, `OAI.TamingCompatibility.EuclideanSobolevOperators.affineDistribution`, `OAI.TamingCompatibility.EuclideanSobolevOperators.affineHomeomorph`, `OAI.TamingCompatibility.EuclideanSobolevOperators.affineSchwartz`, `OAI.TamingCompatibility.EuclideanSobolevOperators.normalizedCutoff`, `OAI.TamingCompatibility.EuclideanSobolevOperators.zoomDistribution`, `OAI.TamingCompatibility.FiberCoordinates.complexCoordinates`, `OAI.TamingCompatibility.FiberCoordinates.coordinates`, `OAI.TamingCompatibility.FourierCutoff.kernel`, `OAI.TamingCompatibility.FourierCutoff.modulate`, `OAI.TamingCompatibility.FourierCutoff.multiply`, `OAI.TamingCompatibility.FourierCutoff.pairing`, `OAI.TamingCompatibility.FourierCutoff.pairingCLM`, `OAI.TamingCompatibility.FourierCutoff.phase`, `OAI.TamingCompatibility.FourierIdentification.inverseTop`, `OAI.TamingCompatibility.Fredholm.nullspace`, `OAI.TamingCompatibility.HilbertSobolev.basisIndex`, `OAI.TamingCompatibility.HilbertSobolev.coefficientSize`, `OAI.TamingCompatibility.HilbertSobolev.differentialPerturbation`, `OAI.TamingCompatibility.HilbertSobolev.frozenCoefficient`, `OAI.TamingCompatibility.HilbertSobolev.frozenPrincipal`, `OAI.TamingCompatibility.HilbertSobolev.multiplyLp`, `OAI.TamingCompatibility.HilbertSobolev.principalDerivativeError`, `OAI.TamingCompatibility.HilbertSobolev.principalInBasis`, `OAI.TamingCompatibility.HilbertSobolev.weight`, `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model`, `OAI.TamingCompatibility.ManifoldForms.Smooth`, `OAI.TamingCompatibility.ManifoldForms.Space`, `OAI.TamingCompatibility.ManifoldForms.exteriorDerivative`, `OAI.TamingCompatibility.ManifoldForms.pullback`, `OAI.TamingCompatibility.ManifoldHodge.instNormedAddCommGroupTangentSpaceRealSpaceModel`, `OAI.TamingCompatibility.Neumann.inverseEquiv` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_AffineBase`, `TamingCompatibility_Charts_AffineLocal`, `TamingCompatibility_Charts_Coordinates`, `TamingCompatibility_Charts_LocalFormalAdjoint`, `TamingCompatibility_Charts_RealTestLocality`, `TamingCompatibility_Charts_ShrinkingCutoff`, `TamingCompatibility_Concentration_ConcentrationKernel`, `TamingCompatibility_Currents_BoundedDistribution`, `TamingCompatibility_Currents_PlaneMeasure`, `TamingCompatibility_DifferentialForms_Bessel`, `TamingCompatibility_DifferentialForms_ContDiffApply`, `TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding`, `TamingCompatibility_DifferentialForms_FunSmul`, `TamingCompatibility_DifferentialForms_Helmholtz`, `TamingCompatibility_DifferentialForms_Kernel`, `TamingCompatibility_DifferentialForms_NegativeWeightMoment`, `TamingCompatibility_DifferentialForms_Product`, `TamingCompatibility_DifferentialForms_RadialCoefficientProfiles`, `TamingCompatibility_DifferentialForms_ScaledLower`, `TamingCompatibility_DifferentialForms_StarTwoComp`, `TamingCompatibility_Elliptic_ChartGarding`, `TamingCompatibility_Elliptic_CriticalRescaleH1`, `TamingCompatibility_Elliptic_DirectionalPrincipal`, `TamingCompatibility_Elliptic_FrozenCoefficient`, `TamingCompatibility_Elliptic_FrozenSystem`, `TamingCompatibility_Elliptic_InteriorRegularity`, `TamingCompatibility_Elliptic_LocalGarding`, `TamingCompatibility_Elliptic_NeumannSeries`, `TamingCompatibility_Elliptic_PrincipalDerivativeError`, `TamingCompatibility_Elliptic_PrincipalNormalize`, `TamingCompatibility_Elliptic_PrincipalTransport`, `TamingCompatibility_Elliptic_SecondDerivative`, `TamingCompatibility_Elliptic_SobolevBounded`, `TamingCompatibility_Functional_FourierCutoff`, `TamingCompatibility_Functional_SobolevSpace`, `TamingCompatibility_HeatFlow_VariationalResolvent`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc005`, `OAIQ239Tc006`, `OAIQ239Tc007` and `OAIQ239Tc008`; the statement `OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility

section
-- module Solutions.OAIQ239_TC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_FourierCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped BoundedContinuousFunction

open _root_.MeasureTheory FourierTransform
open scoped BoundedContinuousFunction RealInnerProductSpace ENNReal

namespace TamingCompatibility.FourierCutoff

lemma fourierChar_sub_bound (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ ≤
      2 * Real.pi * ‖a-b‖ := by
  have heq : (Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ) =
      ((Real.fourierChar (a-b) : ℂ)-1) * (Real.fourierChar b : ℂ) := by
    rw [sub_mul, one_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, sub_add_cancel]
  rw [heq, norm_mul, Circle.norm_coe, mul_one, Real.fourierChar_apply]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (a-b))
  rw [mul_comm (((2 * Real.pi * (a-b)) : ℝ) : ℂ) Complex.I]
  refine h.trans_eq ?_
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_sub_bound (x y ξ : E) :
    ‖(Real.fourierChar ⟪ξ,x⟫ : ℂ) - (Real.fourierChar ⟪ξ,y⟫ : ℂ)‖ ≤
      (2 * Real.pi * ‖ξ‖) * ‖x-y‖ := by
  refine (fourierChar_sub_bound _ _).trans ?_
  rw [← inner_sub_right]
  have h := norm_inner_le_norm (𝕜 := ℝ) ξ (x-y)
  calc
    2 * Real.pi * ‖⟪ξ,x-y⟫‖ ≤ 2 * Real.pi * (‖ξ‖ * ‖x-y‖) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

def phase (x : E) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ => (Real.fourierChar ⟪ξ,x⟫ : ℂ))
    (by fun_prop) 1 (fun ξ => le_of_eq (Circle.norm_coe (Real.fourierChar ⟪ξ,x⟫)))

def modulate (g : Lp ℂ 2 (volume : Measure E)) (x : E) : Lp ℂ 2 (volume : Measure E) :=
  ((phase x).memLp_top (μ := volume)).toLp _ • g

lemma modulate_coe (g : Lp ℂ 2 (volume : Measure E)) (x : E) :
    modulate g x =ᵐ[volume] fun ξ => (Real.fourierChar ⟪ξ,x⟫ : ℂ) * g ξ := by
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (((phase x).memLp_top (μ := volume)).toLp _) g,
    ((phase x).memLp_top (μ := volume)).coeFn_toLp] with ξ h1 h2
  change modulate g x ξ = (((phase x).memLp_top (μ := volume)).toLp _) ξ * g ξ at h1
  rw [h1, h2]
  rfl

lemma modulate_sub_norm_le (g : Lp ℂ 2 (volume : Measure E))
    {R : ℝ} (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0) (x y : E) :
    ‖modulate g x - modulate g y‖ ≤ (2 * Real.pi * R * ‖x-y‖) * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (modulate g x) (modulate g y),
    modulate_coe g x, modulate_coe g y, hg] with ξ hs hx hy hξ
  rw [hs, Pi.sub_apply, hx, hy, ← sub_mul, norm_mul]
  by_cases h : R < ‖ξ‖
  · simp [hξ h]
  · have hb := phase_sub_bound x y ξ
    have hb' : (2 * Real.pi * ‖ξ‖) * ‖x-y‖ ≤ (2 * Real.pi * R) * ‖x-y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_of_not_gt h) (by positivity)) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (hb.trans hb') (norm_nonneg _)

lemma continuous_modulate (g : Lp ℂ 2 (volume : Measure E))
    {R : ℝ} (hR : 0 ≤ R) (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0) :
    Continuous (modulate g) := by
  let C : NNReal := ⟨2 * Real.pi * R * ‖g‖, by positivity⟩
  apply (show LipschitzWith C (modulate g) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖modulate g x - modulate g y‖ ≤ (2 * Real.pi * R * ‖g‖) * ‖x-y‖
  convert modulate_sub_norm_le g hg x y using 1
  all_goals try with_reducible_and_instances rfl
  ring

def multiply (g : Lp ℂ 2 (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 1 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun u => g • u
      map_add' := fun u v => Lp.add_smul g u v
      map_smul' := fun c u => (Lp.smul_comm c g u).symm }
    ‖g‖ (fun u => Lp.norm_smul_le g u)

def pairing (g : Lp ℂ 2 (volume : Measure E)) : Lp F 2 (volume : Measure E) →L[ℂ] F :=
  (L1.integralCLM' ℂ) ∘L multiply g

lemma pairing_norm_le (g : Lp ℂ 2 (volume : Measure E)) (u : Lp F 2 (volume : Measure E)) :
    ‖pairing g u‖ ≤ ‖g‖ * ‖u‖ := by
  change ‖L1.integralCLM' ℂ (g • u)‖ ≤ _
  rw [← L1.integral_eq' ℂ]
  exact (L1.norm_integral_le _).trans (Lp.norm_smul_le g u)

def pairingCLM : Lp ℂ 2 (volume : Measure E) →L[ℂ] (Lp F 2 (volume : Measure E) →L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := pairing
      map_add' := fun g h => by
        ext u
        change L1.integralCLM' ℂ ((g+h) • u) =
          L1.integralCLM' ℂ (g • u) + L1.integralCLM' ℂ (h • u)
        rw [Lp.smul_add, map_add]
      map_smul' := fun c g => by
        ext u
        change L1.integralCLM' ℂ ((c • g) • u) = c • L1.integralCLM' ℂ (g • u)
        rw [Lp.smul_assoc, map_smul] }
    1 (fun g => by
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (pairing_norm_le g))

end TamingCompatibility.FourierCutoff

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Kernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
open _root_.MeasureTheory
open scoped BoundedContinuousFunction
noncomputable section
open _root_.MeasureTheory FourierTransform
open scoped BoundedContinuousFunction RealInnerProductSpace ENNReal
namespace TamingCompatibility.FourierCutoff

variable {E F K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [MetricSpace K] [CompactSpace K]

lemma pairing_modulate_eq_inverse (g : Lp ℂ 2 (volume : Measure E))
    (u : Lp F 2 (volume : Measure E)) (x : E) :
    pairing (modulate g x) u = Real.Lp.fourierTransformInv (multiply g u) x := by
  change L1.integralCLM' ℂ (modulate g x • u) = _
  rw [← L1.integral_eq' ℂ, L1.integral_eq_integral, Real.Lp.fourierTransformInv_apply, Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (modulate g x) u,
    Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) g u, modulate_coe g x] with ξ h1 h2 h3
  change _ = (Real.fourierChar ⟪ξ,x⟫ : ℂ) • (g • u : Lp F 1 (volume : Measure E)) ξ
  rw [h1, h2]
  change modulate g x ξ • u ξ = (Real.fourierChar ⟪ξ,x⟫ : ℂ) • (g ξ • u ξ)
  rw [h3, mul_smul]

def kernel (loc : C(K,E)) (g : Lp ℂ 2 (volume : Measure E))
    {R : ℝ} (hR : 0 ≤ R) (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0) :
    K →ᵇ (Lp F 2 (volume : Measure E) →L[ℂ] F) :=
  .mkOfCompact ⟨fun x => pairingCLM (modulate g (loc x)),
    pairingCLM.continuous.comp ((continuous_modulate g hR hg).comp loc.continuous)⟩

end TamingCompatibility.FourierCutoff

end
end

noncomputable section
open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace ENNReal ContDiff

namespace TamingCompatibility.FourierIdentification

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma ae_eq_of_distribution_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp F p (volume : Measure E)) (g : Lp F q (volume : Measure E))
    (h : (f : 𝓢'(E,F)) = (g : 𝓢'(E,F))) : f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable (Fact.out : 1 ≤ p))
    ((Lp.memLp g).locallyIntegrable (Fact.out : 1 ≤ q))
  intro φ hφ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hc.comp_left rfl
  have hd' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  have heq := congrArg (fun u : 𝓢'(E,F) => u (hc'.toSchwartzMap hd')) h
  simpa using heq

lemma integral_inverse_smul_swap {f : E → ℂ} {g : E → F}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕⁻ f x • g x) = ∫ x, f x • 𝓕⁻ g x := by
  simpa [FourierTransformInv.fourierInv, VectorFourier.fourierIntegral,
    real_inner_comm] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -(innerₗ E))
      Real.continuous_fourierChar (by
        change Continuous (fun p : E × E => -⟪p.1,p.2⟫)
        exact continuous_inner.neg) hf hg)

def inverseTop (f : Lp F 1 (volume : Measure E)) : Lp F ⊤ (volume : Measure E) :=
  ((Real.Lp.fourierTransformInv f).memLp_top (μ := volume)).toLp _

omit [CompleteSpace F] in
lemma inverseTop_coe (f : Lp F 1 (volume : Measure E)) :
    inverseTop f =ᵐ[volume] Real.Lp.fourierTransformInv f :=
  ((Real.Lp.fourierTransformInv f).memLp_top (μ := volume)).coeFn_toLp

lemma inverseTop_to_distribution (f : Lp F 1 (volume : Measure E)) :
    𝓕⁻ (f : 𝓢'(E,F)) = (inverseTop f : 𝓢'(E,F)) := by
  ext φ
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  calc
    (∫ x, 𝓕⁻ φ x • f x) = ∫ x, φ x • Real.Lp.fourierTransformInv f x := by
      simpa only [SchwartzMap.fourierInv_coe, Real.Lp.fourierTransformInv_apply] using
        integral_inverse_smul_swap φ.integrable (L1.integrable_coeFn f)
    _ = ∫ x, φ x • inverseTop f x := by
      apply integral_congr_ae
      filter_upwards [inverseTop_coe f] with x hx
      rw [hx]

lemma distribution_eq_of_ae_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp F p (volume : Measure E)) (g : Lp F q (volume : Measure E))
    (h : f =ᵐ[volume] g) : (f : 𝓢'(E,F)) = (g : 𝓢'(E,F)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

end TamingCompatibility.FourierIdentification

namespace TamingCompatibility.FourierIdentification
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem inverse_L1_L2 (f : Lp F 1 (volume : Measure E))
    (g : Lp F 2 (volume : Measure E)) (h : f =ᵐ[volume] g) :
    Real.Lp.fourierTransformInv f =ᵐ[volume] (𝓕⁻ g : Lp F 2 (volume : Measure E)) := by
  apply (inverseTop_coe f).symm.trans
  apply ae_eq_of_distribution_eq
  rw [← inverseTop_to_distribution, distribution_eq_of_ae_eq f g h,
    Lp.fourierInv_toTemperedDistribution_eq]

end TamingCompatibility.FourierIdentification

end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_SobolevSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal

namespace TamingCompatibility.HilbertSobolev

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {E F}

lemma lp_injective : Function.Injective
    (Lp.toTemperedDistributionCLM F (volume : Measure E) 2) := by
  exact LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot)

def multiplyLp (g : Lp ℂ ∞ (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun f => g • f
      map_add' := fun f h => Lp.add_smul g f h
      map_smul' := fun c f => (Lp.smul_comm c g f).symm }
    ‖g‖ (fun f => Lp.norm_smul_le g f)

lemma toLp_top_norm_le {g : E → ℂ} (hg : MemLp g ∞ (volume : Measure E))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C) :
    ‖hg.toLp g‖ ≤ C := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  have hle := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure E))
    (Filter.Eventually.of_forall hb)
  exact (ENNReal.toReal_mono (by finiteness) hle).trans_eq
    (ENNReal.toReal_ofReal hC)

omit [CompleteSpace F] in
lemma bessel_fourierMultiplier_comm (s : ℝ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    besselPotential E F s (fourierMultiplierCLM F g u) =
      fourierMultiplierCLM F g (besselPotential E F s u) := by
  rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply hg (by fun_prop),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) hg]
  rw [mul_comm]

def weight (a : ℝ) (x : E) : ℂ := ((1 + ‖x‖ ^ 2) ^ (a / 2) : ℝ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weight_temperate (a : ℝ) : (weight (E := E) a).HasTemperateGrowth := by
  unfold weight
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weight_le_one {a : ℝ} (ha : a ≤ 0) (x : E) : ‖weight a x‖ ≤ 1 := by
  rw [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)

lemma weight_memLp_top {a : ℝ} (ha : a ≤ 0) :
    MemLp (weight (E := E) a) ∞ (volume : Measure E) :=
  memLp_top_of_bound (weight_temperate a).1.continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (weight_le_one ha))

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Bessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction
namespace TamingCompatibility.RellichWeight
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bessel (s : ℝ) (hs : 0 ≤ s) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ((1+‖x‖^2)^(-s/2) : ℝ)) (Complex.continuous_ofReal.comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-s/2)).1.continuous) 1 (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith))

end TamingCompatibility.RellichWeight

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Helmholtz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal

namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev basisIndex (E : Type*) [AddCommGroup E] [Module ℝ E] := Fin (Module.finrank ℝ E)

end TamingCompatibility.HilbertSobolev
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def coefficientSize : ℕ → 𝓢(E,ℂ) → ℝ
  | 0, g => ‖g.toBoundedContinuousFunction‖
  | n+1, g => coefficientSize n g +
      ∑ i : basisIndex E, coefficientSize n (∂_{stdOrthonormalBasis ℝ E i} g)

omit [MeasurableSpace E] [BorelSpace E] in
lemma coefficientSize_nonneg (n : ℕ) (g : 𝓢(E,ℂ)) : 0 ≤ coefficientSize n g := by
  induction n generalizing g with
  | zero => exact norm_nonneg _
  | succ n ih => exact add_nonneg (ih g) (Finset.sum_nonneg (fun i _ => ih _))

omit [MeasurableSpace E] [BorelSpace E] in
lemma coefficientSize_le_succ (n : ℕ) (g : 𝓢(E,ℂ)) :
    coefficientSize n g ≤ coefficientSize (n+1) g := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => coefficientSize_nonneg n _))

omit [MeasurableSpace E] [BorelSpace E] in
lemma coefficientSize_derivative_le (n : ℕ) (g : 𝓢(E,ℂ)) (i : basisIndex E) :
    coefficientSize n (∂_{stdOrthonormalBasis ℝ E i} g) ≤ coefficientSize (n+1) g := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : basisIndex E => coefficientSize n (∂_{stdOrthonormalBasis ℝ E j} g))
    (fun j _ => coefficientSize_nonneg n _) (Finset.mem_univ i)
  exact h.trans (le_add_of_nonneg_left (coefficientSize_nonneg n g))

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_NeumannSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.Neumann
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

def inverseEquiv (A : G →L[ℂ] G) (hA : ‖A‖ < 1) : G ≃L[ℂ] G :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub (-A) (by simpa using hA))

lemma inverseEquiv_apply (A : G →L[ℂ] G) (hA : ‖A‖ < 1) (x : G) :
    inverseEquiv A hA x = x + A x := by
  change ((1 : G →L[ℂ] G) - (-A)) x = _
  simp

theorem existsUnique (A : G →L[ℂ] G) (hA : ‖A‖ < 1) (y : G) :
    ∃! x, x + A x = y := by
  let L := inverseEquiv A hA
  refine ⟨L.symm y, ?_, ?_⟩
  · exact (inverseEquiv_apply A hA _).symm.trans (L.apply_symm_apply y)
  · intro z hz
    apply L.injective
    rw [L.apply_symm_apply, inverseEquiv_apply]
    exact hz
end TamingCompatibility.Neumann

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def differentialPerturbation
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  ∑ i, ∑ j, smulLeftCLM F (a i j)
    (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u))

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_AffineBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def affineSchwartz (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢(E,ℂ) →L[ℂ] 𝓢(E,ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 r hr))).comp
      (SchwartzMap.compSubConstCLM ℂ (-p))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma affineSchwartz_apply (p x : E) (r : ℝ) (hr : r ≠ 0) (φ : 𝓢(E,ℂ)) :
    affineSchwartz p r hr φ x = φ (r • x + p) := by
  simp [affineSchwartz, Units.smul_def]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma affineSchwartz_derivative (p : E) (r : ℝ) (hr : r ≠ 0) (φ : 𝓢(E,ℂ)) (v : E) :
    ∂_{v} (affineSchwartz p r hr φ) = r • affineSchwartz p r hr (∂_{v} φ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have he : (affineSchwartz p r hr φ : E → ℂ) = fun y => φ (r • y + p) := by
    funext y
    exact affineSchwartz_apply p y r hr φ
  have hd := (φ.hasFDerivAt (r • x + p)).comp x
    (((hasFDerivAt_id x).const_smul r).add_const p)
  dsimp only [Function.comp_def, Pi.smul_apply, id_eq] at hd
  rw [he, hd.fderiv]
  simp [affineSchwartz_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

def affineDistribution (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  PointwiseConvergenceCLM.precomp F (affineSchwartz p r hr)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma affineDistribution_apply (p : E) (r : ℝ) (hr : r ≠ 0)
    (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    affineDistribution p r hr u φ = u (affineSchwartz p r hr φ) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma affineDistribution_derivative (p : E) (r : ℝ) (hr : r ≠ 0)
    (u : 𝓢'(E,F)) (v : E) :
    affineDistribution p r hr (∂_{v} u) = r • ∂_{v} (affineDistribution p r hr u) := by
  ext φ
  simp only [affineDistribution_apply, lineDerivOp_apply_apply,
    affineSchwartz_derivative, map_neg, smul_apply, smul_neg]
  congr 1
  exact ContinuousLinearMap.map_smul_of_tower (show 𝓢(E,ℂ) →L[ℂ] F from u) r _

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
lemma memLp_comp_affine (p : E) (r : ℝ) (hr : r ≠ 0) {f : E → F}
    (hf : MemLp f 2 (volume : Measure E)) :
    MemLp (fun x => f (r • x + p)) 2 (volume : Measure E) := by
  have ht := hf.comp_measurePreserving (measurePreserving_add_right volume p)
  have hm : MemLp (fun x => f (x+p)) 2 (Measure.map (fun x : E => r • x) volume) := by
    rw [Measure.map_addHaar_smul volume hr]
    exact ht.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (measurable_const_smul r).aemeasurable

lemma affineDistribution_lp (p : E) (r : ℝ) (hr : r ≠ 0)
    (f : Lp F 2 (volume : Measure E)) :
    ∃ g : Lp F 2 (volume : Measure E),
      affineDistribution p r hr (f : 𝓢'(E,F)) = (g : 𝓢'(E,F)) := by
  let c : ℝ := |(r ^ Module.finrank ℝ E)⁻¹|
  let h : E → F := fun y => c • f (r⁻¹ • y + (-(r⁻¹ • p)))
  have hh : MemLp h 2 (volume : Measure E) :=
    (memLp_comp_affine (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) (Lp.memLp f)).const_smul c
  refine ⟨hh.toLp h, ?_⟩
  ext φ
  rw [affineDistribution_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hi : (∫ y, φ y • (hh.toLp h) y) = ∫ y, φ y • h y := by
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with y hy
    rw [hy]
  rw [hi]
  simp only [affineSchwartz_apply]
  let k : E → F := fun y => φ (y+p) • f (r⁻¹ • y)
  have he : (∫ x, φ (r • x+p) • f x) = c • ∫ y, k y := by
    have heq : (fun x => φ (r • x+p) • f x) = fun x => k (r • x) := by
      funext x
      simp [k, inv_smul_smul₀ hr]
    rw [heq, Measure.integral_comp_smul]
  rw [he]
  have ha := integral_add_right_eq_self (μ := (volume : Measure E)) (fun y : E => φ y • h y) p
  rw [← ha]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  change c • (φ (y+p) • f (r⁻¹ • y)) =
    φ (y+p) • (c • f (r⁻¹ • (y+p) + -(r⁻¹ • p)))
  rw [smul_add, add_neg_cancel_right]
  exact smul_comm c (φ (y+p)) _

lemma memSobolev_zero_affine (p : E) (r : ℝ) (hr : r ≠ 0)
    {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (affineDistribution p r hr u) := by
  obtain ⟨f, hf⟩ := hu
  have he : u = (f : 𝓢'(E,F)) := by simpa using hf
  rw [he]
  obtain ⟨g,hg⟩ := affineDistribution_lp p r hr f
  refine ⟨g, ?_⟩
  simpa using hg

end TamingCompatibility.EuclideanSobolevOperators

end
end

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma affine_inverse_point (p x : E) {r : ℝ} (hr : r ≠ 0) :
    r⁻¹ • (r • x+p) + -(r⁻¹ • p) = x := by
  simp only [smul_add,smul_smul,inv_mul_cancel₀ hr,one_smul,add_neg_cancel_right]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma affineDistribution_product (p : E) (r : ℝ) (hr : r ≠ 0)
    (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    affineDistribution p r hr (smulLeftCLM F g u) =
      smulLeftCLM F (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) g)
        (affineDistribution p r hr u) := by
  ext φ
  simp only [affineDistribution_apply,smulLeftCLM_apply_apply]
  congr 1
  ext x
  rw [affineSchwartz_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) g).hasTemperateGrowth]
  simp only [affineSchwartz_apply,affine_inverse_point p x hr]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma affineDistribution_inverse (p : E) (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) :
    affineDistribution (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) (affineDistribution p r hr u) = u := by
  ext φ
  simp only [affineDistribution_apply]
  congr 1
  ext x
  simp only [affineSchwartz_apply,affine_inverse_point p x hr]

def zoomDistribution (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  affineDistribution (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma zoomDistribution_product (p : E) (r : ℝ) (hr : r ≠ 0)
    (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    zoomDistribution p r hr (smulLeftCLM F g u) =
      smulLeftCLM F (affineSchwartz p r hr g) (zoomDistribution p r hr u) := by
  rw [zoomDistribution,affineDistribution_product]
  have hp : -((r⁻¹)⁻¹ • -(r⁻¹ • p)) = p := by
    simp only [inv_inv,smul_neg,smul_smul,mul_inv_cancel₀ hr,one_smul,neg_neg]
  rw [hp]
  simp only [inv_inv]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma zoomDistribution_second (p : E) (r : ℝ) (hr : r ≠ 0)
    (v w : E) (u : 𝓢'(E,F)) :
    zoomDistribution p r hr (∂_{v} (∂_{w} u)) =
      (r⁻¹*r⁻¹) • ∂_{v} (∂_{w} (zoomDistribution p r hr u)) := by
  simp only [zoomDistribution,affineDistribution_derivative,lineDerivOp_smul,smul_smul]

end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_BoundedDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace
namespace TamingCompatibility.EuclideanSobolev
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma integral_fourierInv_smul (φ : 𝓢(E,ℂ)) (v : Lp F 1 (volume : Measure E)) :
    (∫ x, (𝓕⁻ φ) x • v x) = ∫ x, φ x • (𝓕⁻ (v : E → F)) x := by
  have hflip : (-(innerₗ E)).flip = -(innerₗ E) := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -(innerₗ E))
    (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner.neg φ.integrable
    (memLp_one_iff_integrable.mp (Lp.memLp v))
  rw [hflip] at h
  rw [SchwartzMap.fourierInv_coe]
  exact h

end TamingCompatibility.EuclideanSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_NegativeWeightMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace
namespace TamingCompatibility.EuclideanSobolev
open TemperedDistribution
open scoped ENNReal ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma negative_weight_moment (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    r^n * (1+r^2)^(-(2*(n:ℝ))/2) ≤ 1 := by
  have he : -(2*(n:ℝ))/2 = -(n:ℝ) := by ring
  rw [he, Real.rpow_neg (by positivity), Real.rpow_natCast]
  apply (mul_inv_le_iff₀ (pow_pos (by positivity) _)).mpr
  simp only [one_mul]
  exact pow_le_pow_left₀ hr (by nlinarith [sq_nonneg (r - 1/2)]) n

lemma fourier_moments_of_all_orders {u : 𝓢'(E,F)}
    (hu : ∀ s : ℝ, MemSobolev s 2 u)
    (v : Lp F 1 (volume : Measure E)) (hv : 𝓕 u = (v : 𝓢'(E,F))) (n : ℕ) :
    Integrable (fun ξ : E => ‖ξ‖^n * ‖v ξ‖) := by
  let s : ℝ := Module.finrank ℝ E + 1
  have hs : Module.finrank ℝ E < 2*s := by
    dsimp [s]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  have hn : MemSobolev s 2 (besselPotential E F (2*(n:ℝ)) u) := by
    rw [memSobolev_besselPotential_iff]
    exact hu _
  obtain ⟨w,hw⟩ := hn.fourier_memL1 hs
  let b := RellichWeight.bessel (E := E) (2*(n:ℝ)) (by positivity)
  have hb : (b : E → ℂ).HasTemperateGrowth := by
    change (fun x : E => Complex.ofReal ((1+‖x‖^2)^(-(2*(n:ℝ))/2))).HasTemperateGrowth
    fun_prop
  let z : Lp F 1 (volume : Measure E) := ((b.memLp_top (μ := volume)).toLp b) • w
  have hz : (z : 𝓢'(E,F)) = (v : 𝓢'(E,F)) := by
    rw [Lp.toTemperedDistribution_smul_eq hb (b.memLp_top (μ := volume)), ← hw]
    change smulLeftCLM F (fun x : E => Complex.ofReal ((1+‖x‖^2)^(-(2*(n:ℝ))/2)))
      (𝓕 (besselPotential E F (2 * (n:ℝ)) u)) = _
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      besselPotential_besselPotential_apply]
    simpa using hv
  have hzv : z = v := (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) hz
  have hae : ∀ᵐ ξ ∂(volume : Measure E), v ξ = b ξ • w ξ := by
    filter_upwards [Lp.coeFn_lpSMul (r := (1:ℝ≥0∞)) ((b.memLp_top (μ := volume)).toLp b) w,
      (b.memLp_top (μ := volume)).coeFn_toLp] with ξ hz hb'
    change z ξ = _ at hz
    rw [hzv] at hz
    change v ξ = ((b.memLp_top (μ := volume)).toLp b) ξ • w ξ at hz
    rw [hb'] at hz
    exact hz
  apply (memLp_one_iff_integrable.mp (Lp.memLp w)).norm.mono'
    ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm)
  filter_upwards [hae] with ξ hξ
  change ‖‖ξ‖^n * ‖v ξ‖‖ ≤ ‖w ξ‖
  rw [hξ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change ‖ξ‖^n * (‖(((1+‖ξ‖^2)^(-(2*(n:ℝ))/2) : ℝ) : ℂ)‖ * ‖w ξ‖) ≤ ‖w ξ‖
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right (negative_weight_moment n ‖ξ‖ (norm_nonneg ξ))
    (norm_nonneg (w ξ))).trans_eq (one_mul _)

end TamingCompatibility.EuclideanSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalDerivativeError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian FourierTransform
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def principalDerivativeError (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (v : E) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  ∑ i, ∑ j, smulLeftCLM F (∂_{v} (a i j) : 𝓢(E,ℂ))
    (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u))

end TamingCompatibility.HilbertSobolev

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_InteriorRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology Manifold ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] in

lemma exists_outer_cutoff {U : Set E} (hU : IsOpen U) (g : 𝓢(E,ℂ))
    (hg : HasCompactSupport (g : E → ℂ)) (hgU : tsupport g ⊆ U) :
    ∃ h : 𝓢(E,ℂ), HasCompactSupport (h : E → ℂ) ∧ tsupport h ⊆ U ∧
      ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨t,ht,hgt,htU⟩ := exists_compact_between hg hU hgU
  obtain ⟨h,he,hz,-⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,E) (n := (⊤ : ℕ∞)) (isClosed_tsupport g) hgt
  let f : E → ℂ := fun x => (h x : ℂ)
  have hs : ContDiff ℝ ∞ f := by
    exact Complex.ofRealCLM.contDiff.comp h.contMDiff.contDiff
  have hft : tsupport f ⊆ t := by
    apply closure_minimal _ ht.isClosed
    intro x hx
    by_contra hn
    exact hx (by simp only [f, hz x hn, Complex.ofReal_zero])
  have hf : HasCompactSupport f := ht.of_isClosed_subset (isClosed_tsupport f) hft
  refine ⟨hf.toSchwartzMap hs, hf, hft.trans htU, ?_⟩
  intro x hx
  filter_upwards [he.filter_mono (nhds_le_nhdsSet hx)] with y hy
  change (h y : ℂ) = 1
  simp [hy]

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma linearSchwartz_derivative (L : E ≃L[ℝ] E) (φ : 𝓢(E,ℂ)) (v : E) :
    ∂_{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (∂_{L v} φ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [((φ.hasFDerivAt (L x)).comp x L.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
lemma memLp_comp_linearEquiv (L : E ≃L[ℝ] E) {f : E → F}
    (hf : MemLp f 2 (volume : Measure E)) :
    MemLp (fun x => f (L x)) 2 (volume : Measure E) := by
  have hm : MemLp f 2 (Measure.map L volume) := by
    rw [show Measure.map L volume = ENNReal.ofReal |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| • volume from
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map L.continuous.measurable.aemeasurable

end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_AffineLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def affineHomeomorph (p : E) (r : ℝ) (hr : r ≠ 0) : E ≃ₜ E :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 r hr)).toHomeomorph.trans
    (Homeomorph.addRight p)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma affineHomeomorph_apply (p x : E) (r : ℝ) (hr : r ≠ 0) :
    affineHomeomorph p r hr x = r • x+p := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma affineSchwartz_comp_inverse (p : E) (r : ℝ) (hr : r ≠ 0) (g : 𝓢(E,ℂ)) :
    affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) (affineSchwartz p r hr g) = g := by
  ext x
  simp only [affineSchwartz_apply,smul_add,smul_neg,smul_smul,mul_inv_cancel₀ hr,
    one_smul,neg_add_cancel_right]

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped Manifold ContDiff
noncomputable section
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
namespace TamingCompatibility.FormSmoothness

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {k : ℕ} {n : WithTop ℕ∞}

local instance instFiniteDimensionalRealContinuousMultilinearMapFin_solutions : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective

omit [FiniteDimensional ℝ E] in

lemma contDiffOn_of_linear_embedding {f : D → E} {s : Set D}
    (L : E →L[ℝ] F) (hL : Function.Injective L)
    (h : ContDiffOn ℝ n (fun x => L (f x)) s) : ContDiffOn ℝ n f s := by
  let R := L.toLinearMap.leftInverse.toContinuousLinearMap
  have hr : ∀ x, R (L x) = x :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hL)
  simpa only [Function.comp_def, hr] using R.contDiff.comp_contDiffOn h

local instance instFiniteDimensionalRealContinuousAlternatingMapFin_solutions_r0bdd6f_1 : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective (ContinuousAlternatingMap.toContinuousMultilinearMapLinear)
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective
omit [FiniteDimensional ℝ F] in

lemma ContDiffOn.compAlternating {α : D → F [⋀^Fin k]→L[ℝ] ℝ}
    {A : D → E →L[ℝ] F} {s : Set D}
    (hα : ContDiffOn ℝ n α s) (hA : ContDiffOn ℝ n A s) :
    ContDiffOn ℝ n (fun x => (α x).compContinuousLinearMap (A x)) s := by
  apply contDiffOn_of_linear_embedding
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  let P : ContinuousMultilinearMap ℝ (fun _ : Fin k => E →L[ℝ] F)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin k => E) (fun _ => F) ℝ
  have hPc : ContDiff ℝ n P :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ) (ι := Fin k)
      (E := fun _ => E →L[ℝ] F) (F :=
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) P
  have hP := hPc.comp_contDiffOn (contDiffOn_pi.mpr (fun _ => hA))
  have hC : ContDiff ℝ n (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ :
      (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ) :=
    ContinuousLinearMap.contDiff _
  exact hP.clm_apply (hC.comp_contDiffOn hα)

omit [FiniteDimensional ℝ F] in

lemma contDiff_compAlternating :
    ContDiff ℝ n (fun p : (F [⋀^Fin k]→L[ℝ] ℝ) × (E →L[ℝ] F) =>
      p.1.compContinuousLinearMap p.2) := by
  rw [← contDiffOn_univ]
  exact ContDiffOn.compAlternating contDiffOn_fst contDiffOn_snd

omit [FiniteDimensional ℝ F] in
lemma ContDiffAt.compAlternating {α : D → F [⋀^Fin k]→L[ℝ] ℝ}
    {A : D → E →L[ℝ] F} {x : D}
    (hα : ContDiffAt ℝ n α x) (hA : ContDiffAt ℝ n A x) :
    ContDiffAt ℝ n (fun y => (α y).compContinuousLinearMap (A y)) x :=
  contDiff_compAlternating.contDiffAt.comp x (hα.prodMk hA)

end TamingCompatibility.FormSmoothness

namespace TamingCompatibility.ManifoldForms

open TamingCompatibility.FormSmoothness

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Model := 𝓘(ℝ, Space)

abbrev Form (X : Type*) [TopologicalSpace X] [ChartedSpace Space X] (k : ℕ) :=
  (x : X) → (TangentSpace Model x) [⋀^Fin k]→L[ℝ] ℝ

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

def pullback (α : Form X k) (f : Space → X) : Space → Space [⋀^Fin k]→L[ℝ] ℝ :=
  fun y => (α (f y)).compContinuousLinearMap (mfderiv Model Model f y)

def Smooth (α : Form X k) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ContDiffOn ℝ ∞ (pullback α f) U

def exteriorDerivative (α : Form X k) : Form X (k + 1) :=
  fun x => extDeriv (pullback α (extChartAt Model x).symm) (extChartAt Model x x)

lemma extDerivWithin_eq_of_mem {α : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    {U : Set Space} {y : Space} (hU : IsOpen U) (hy : y ∈ U) :
    extDerivWithin α U y = extDeriv α y := by
  unfold extDerivWithin extDeriv
  rw [fderivWithin_of_mem_nhds (hU.mem_nhds hy)]

omit [IsManifold Model ∞ X] in
lemma pullback_comp (α : Form X k) {f : Space → X} {g : Space → Space} {y : Space}
    (hf : MDifferentiableAt Model Model f (g y))
    (hg : DifferentiableAt ℝ g y) :
    pullback α (f ∘ g) y = (pullback α f (g y)).compContinuousLinearMap (fderiv ℝ g y) := by
  unfold pullback
  rw [mfderiv_comp y hf hg.mdifferentiableAt, mfderiv_eq_fderiv]
  ext v
  rfl

end TamingCompatibility.ManifoldForms

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.FiberCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (k : ℕ)

def coordinates : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k → ι) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k → ι => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun a : Fin k → ι =>
      ContinuousAlternatingMap.apply ℝ E ℝ (fun i => b (a i)))

omit [Fintype ι] [DecidableEq ι] in
lemma coordinates_injective : Function.Injective (coordinates b k) := by
  intro α β h
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply b.ext_alternating
  intro a _
  exact congrArg (fun v : EuclideanSpace ℝ (Fin k → ι) => v a) h

def complexCoordinates : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℂ (Fin k → ι) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k → ι => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun a : Fin k → ι =>
      Complex.ofRealCLM ∘L ContinuousAlternatingMap.apply ℝ E ℝ (fun i => b (a i)))

omit [Fintype ι] [DecidableEq ι] in
lemma complexCoordinates_injective : Function.Injective (complexCoordinates b k) := by
  intro α β h
  apply coordinates_injective b k
  ext a
  exact Complex.ofReal_injective (congrArg (fun v : EuclideanSpace ℂ (Fin k → ι) => v a) h)

end TamingCompatibility.FiberCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalFormalAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalFormalAdjoint
open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D E F : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace E] in
lemma inner_integrable (u v : 𝓢(D,E)) : Integrable (fun x => ⟪u x,v x⟫) :=
  (SchwartzMap.bilinLeftCLM (innerSL ℝ) v.hasTemperateGrowth u).integrable

end TamingCompatibility.LocalFormalAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RealTestLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open Set Filter TemperedDistribution
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma postcomp_support {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G →L[ℝ] H) (φ : 𝓢(E,G)) :
    tsupport (SchwartzMap.postcompCLM L φ) ⊆ tsupport φ :=
  tsupport_comp_subset (map_zero L) φ

lemma real_imag_decomposition (φ : 𝓢(E,ℂ)) :
    φ = SchwartzMap.postcompCLM Complex.ofRealCLM (SchwartzMap.postcompCLM Complex.reCLM φ) +
      Complex.I • SchwartzMap.postcompCLM Complex.ofRealCLM (SchwartzMap.postcompCLM Complex.imCLM φ) := by
  ext x
  simp only [SchwartzMap.postcompCLM_apply,_root_.add_apply,_root_.smul_apply,
    Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,smul_eq_mul]
  simpa only [mul_comm] using (Complex.re_add_im (φ x)).symm

lemma real_tests_equal {U : Set E} {u v : 𝓢'(E,F)}
    (h : ∀ φ : 𝓢(E,ℝ), HasCompactSupport (φ : E → ℝ) → tsupport φ ⊆ U →
      u (SchwartzMap.postcompCLM Complex.ofRealCLM φ) =
      v (SchwartzMap.postcompCLM Complex.ofRealCLM φ))
    (φ : 𝓢(E,ℂ)) (hc : HasCompactSupport (φ : E → ℂ)) (hU : tsupport φ ⊆ U) : u φ = v φ := by
  have hr := postcomp_support Complex.reCLM φ
  have hi := postcomp_support Complex.imCLM φ
  have her := h (SchwartzMap.postcompCLM Complex.reCLM φ)
    (hc.of_isClosed_subset (isClosed_tsupport _) hr) (hr.trans hU)
  have hei := h (SchwartzMap.postcompCLM Complex.imCLM φ)
    (hc.of_isClosed_subset (isClosed_tsupport _) hi) (hi.trans hU)
  conv_lhs => rw [real_imag_decomposition φ]
  conv_rhs => rw [real_imag_decomposition φ]
  simp only [map_add,map_smul,her,hei]

lemma localize_eq_of_real_tests {U : Set E} {u v : 𝓢'(E,F)}
    (h : ∀ φ : 𝓢(E,ℝ), HasCompactSupport (φ : E → ℝ) → tsupport φ ⊆ U →
      u (SchwartzMap.postcompCLM Complex.ofRealCLM φ) =
      v (SchwartzMap.postcompCLM Complex.ofRealCLM φ))
    (g : 𝓢(E,ℂ)) (hc : HasCompactSupport (g : E → ℂ)) (hU : tsupport g ⊆ U) :
    smulLeftCLM F g u = smulLeftCLM F g v := by
  ext φ
  apply real_tests_equal h
  · exact hc.of_isClosed_subset (isClosed_tsupport _)
      ((SchwartzMap.tsupport_smulLeftCLM_subset g φ).trans inter_subset_right)
  · exact (SchwartzMap.tsupport_smulLeftCLM_subset g φ).trans (inter_subset_right.trans hU)
end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DirectionalPrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma derivative_basis (b : OrthonormalBasis κ ℝ E) (v : E) (u : 𝓢'(E,F)) :
    ∂_{v} u = ∑ i, ⟪b i,v⟫ • ∂_{b i} u := by
  have he := b.sum_repr v
  conv_lhs => rw [← he]
  simp only [lineDerivOp_left_sum,lineDerivOp_left_smul,OrthonormalBasis.repr_apply_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma scalar_product_smul (g : 𝓢(E,ℂ)) (r : ℝ) (u : 𝓢'(E,F)) :
    smulLeftCLM F ((r • g) : 𝓢(E,ℂ)) u = r • smulLeftCLM F g u := by
  ext φ
  simp only [smulLeftCLM_apply_apply,_root_.smul_apply]
  have he : SchwartzMap.smulLeftCLM ℂ (r • g) φ = r • SchwartzMap.smulLeftCLM ℂ g φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (r • g).hasTemperateGrowth]
    simp only [_root_.smul_apply]
    rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
    exact smul_assoc r (g x) (φ x)
  rw [he]
  exact ContinuousLinearMap.map_smul_of_tower (show 𝓢(E,ℂ) →L[ℂ] F from u) r _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma scalar_product_sum {τ : Type*} [Fintype τ] (g : τ → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    smulLeftCLM F (∑ i,g i : 𝓢(E,ℂ)) u = ∑ i,smulLeftCLM F (g i) u := by
  ext φ
  simp only [smulLeftCLM_apply_apply,_root_.sum_apply]
  have he : SchwartzMap.smulLeftCLM ℂ (∑ i,g i : 𝓢(E,ℂ)) φ = ∑ i,SchwartzMap.smulLeftCLM ℂ (g i) φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (∑ i,g i).hasTemperateGrowth]
    simp only [_root_.sum_apply]
    simp only [SchwartzMap.smulLeftCLM_apply_apply (g _).hasTemperateGrowth,Finset.sum_smul]
  rw [he,map_sum]

def principalInBasis (b : OrthonormalBasis κ ℝ E) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (k l : κ) : 𝓢(E,ℂ) :=
  ∑ i, ∑ j, (⟪b k,v i⟫ * ⟪b l,v j⟫) • g i j

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_FrozenCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution Filter Function EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Topology ContDiff BoundedContinuousFunction
section CoefficientBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma continuous_bounded_family {A : Type*} [TopologicalSpace A]
    (f : A → E →ᵇ ℂ) {K : Set E} (hK : IsCompact K)
    (hf : Continuous (fun p : A × E => f p.1 p.2))
    (hs : ∀ t, Function.support (f t) ⊆ K) : Continuous f := by
  let g : A → C(E,ℂ) := fun t => (f t).toContinuousMap
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g hf
  rw [continuous_iff_continuousAt]
  intro t
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  have h := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
    (hg.continuousAt (x := t))) K hK
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with s hs'
  intro x
  by_cases hx : x ∈ K
  · exact hs' x hx
  · have ht : f t x = 0 := by_contra fun hh => hx (hs t hh)
    have hst : f s x = 0 := by_contra fun hh => hx (hs s hh)
    simp only [ht, hst, dist_self]
    exact hε

omit [FiniteDimensional ℝ E] in
lemma family_derivative_smooth (f : ℝ → 𝓢(E,ℂ))
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2)) (v : E) :
    ContDiff ℝ ∞ (fun p : ℝ × E => (∂_{v} (f p.1) : 𝓢(E,ℂ)) p.2) := by
  have hf' : ContDiff ℝ ∞ (fun p : (ℝ × E) × E => f p.1.1 p.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hf'.fderiv_apply (𝕜 := ℝ)
    (f := fun q : ℝ × E => fun x : E => f q.1 x) (g := fun p : ℝ × E => p.2)
    (k := fun _ : ℝ × E => v) contDiff_snd contDiff_const (show (∞ : WithTop ℕ∞)+1 ≤ (∞ : WithTop ℕ∞) by simp)
  simpa only [Function.uncurry, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hd

lemma coefficientSize_continuous_family (n : ℕ) (f : ℝ → 𝓢(E,ℂ))
    {K : Set E} (hK : IsCompact K) (hs : ∀ t, tsupport (f t) ⊆ K)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2)) :
    Continuous (fun t => coefficientSize n (f t)) := by
  induction n generalizing f with
  | zero =>
    apply (continuous_bounded_family (fun t => (f t).toBoundedContinuousFunction)
      hK hf.continuous (fun t => (subset_tsupport _).trans (hs t))).norm
  | succ n ih =>
    apply (ih f hs hf).add
    apply continuous_finsetSum
    intro i _
    exact ih (fun t => ∂_{stdOrthonormalBasis ℝ E i} (f t))
      (fun t => (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans (hs t))
      (family_derivative_smooth f hf _)

def frozenCoefficient (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) (r : ℝ) : 𝓢(E,ℂ) :=
  (hχ.mul_right (f' := fun x => f (p + r • x) - f p)).toSchwartzMap
    ((χ.smooth ⊤).mul ((hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id))).sub
      contDiff_const))

omit [FiniteDimensional ℝ E] in
lemma frozenCoefficient_apply (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) (r : ℝ) (x : E) :
    frozenCoefficient χ hχ f hf p r x = χ x * (f (p + r • x) - f p) := rfl

omit [FiniteDimensional ℝ E] in
lemma frozenCoefficient_zero (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) :
    frozenCoefficient χ hχ f hf p 0 = 0 := by
  ext x
  simp [frozenCoefficient_apply]

lemma coefficientSize_zero (n : ℕ) : coefficientSize (E := E) n 0 = 0 := by
  induction n with
  | zero =>
    have h : (0 : 𝓢(E,ℂ)).toBoundedContinuousFunction = 0 := by ext x; rfl
    simp only [coefficientSize, h, norm_zero]
  | succ n ih => simp only [coefficientSize, LineDeriv.lineDerivOp_zero, ih,
      Finset.sum_const_zero, add_zero]

theorem frozenCoefficient_size_tendsto_zero (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) :
    Tendsto (fun r => coefficientSize n (frozenCoefficient χ hχ f hf p r))
      (𝓝 0) (𝓝 0) := by
  have hs (r : ℝ) : tsupport (frozenCoefficient χ hχ f hf p r) ⊆ tsupport χ :=
    tsupport_mul_subset_left
  have hfamily : ContDiff ℝ ∞ (fun q : ℝ × E =>
      frozenCoefficient χ hχ f hf p q.1 q.2) :=
    ((χ.smooth ⊤).comp contDiff_snd).mul
      ((hf.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))).sub contDiff_const)
  have hh := (coefficientSize_continuous_family n _ hχ hs hfamily).continuousAt (x := 0)
  simpa only [ContinuousAt, frozenCoefficient_zero, coefficientSize_zero] using hh

end CoefficientBounds

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def frozenPrincipal (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) (r : ℝ) :
    basisIndex E → basisIndex E → 𝓢(E,ℂ) :=
  fun i j => frozenCoefficient χ hχ (a i j) (ha i j) p r

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma inner_linear_basis (d : OrthonormalBasis ι ℝ E) (L : E ≃L[ℝ] E) (a x : E) :
    ⟪a,L x⟫ = ∑ i, ⟪d i,x⟫ * ⟪a,L (d i)⟫ := by
  have h := congrArg (fun y => ⟪a,L y⟫) (d.sum_repr x)
  simp only [map_sum,map_smul,inner_sum,inner_smul_right,OrthonormalBasis.repr_apply_apply] at h
  exact h.symm

lemma sum_gram_transform (a b : ι → ℝ) (c : ℝ) (u : κ → ι → ℝ) :
    (∑ i, ∑ j, (a i*b j)*(c * ∑ k,u k i*u k j)) =
      c * ∑ k,(∑ i,a i*u k i)*(∑ j,b j*u k j) := by
  simp only [Finset.mul_sum,Finset.sum_mul]
  have he (i j : ι) (k : κ) : a i*b j*(c*(u k i*u k j)) = c*(a i*u k i*(b j*u k j)) := by ring
  simp only [he]
  calc
    _ = ∑ i, ∑ k, ∑ j,c*(a i*u k i*(b j*u k j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gram_covariance (d : OrthonormalBasis ι ℝ E) (L : E ≃L[ℝ] E)
    (a b : E) (c : ℝ) (u : κ → E) :
    (∑ i, ∑ j, (⟪a,L (d i)⟫ * ⟪b,L (d j)⟫) *
      (c * ∑ k,⟪d i,u k⟫ * ⟪d j,u k⟫)) = c * ∑ k,⟪a,L (u k)⟫ * ⟪b,L (u k)⟫ := by
  rw [sum_gram_transform]
  apply congrArg (fun x : ℝ => c*x)
  apply Finset.sum_congr rfl
  intro k _
  rw [inner_linear_basis d L a (u k),inner_linear_basis d L b (u k)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma localized_coefficient_congr (χ : 𝓢(E,ℂ)) {a b : E → ℂ}
    (ha : Function.HasTemperateGrowth a) (hb : Function.HasTemperateGrowth b)
    (h : ∀ x ∈ tsupport χ, a x = b x) (u : 𝓢'(E,F)) :
    smulLeftCLM F χ (smulLeftCLM F a u) = smulLeftCLM F χ (smulLeftCLM F b u) := by
  rw [smulLeftCLM_smulLeftCLM_apply ha χ.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply hb χ.hasTemperateGrowth]
  apply congrArg (fun f : E → ℂ => smulLeftCLM F f u)
  funext x
  by_cases hx : x ∈ tsupport χ
  · simp only [Pi.mul_apply,h x hx]
  · simp only [Pi.mul_apply,image_eq_zero_of_notMem_tsupport hx,mul_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma local_frozen_product (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : 𝓢(E,ℂ)) (p : E) (r : ℝ) (hr : r ≠ 0) (c : ℂ) (hgp : g p = c)
    (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (smulLeftCLM F (frozenCoefficient χ hχ (fun x => -g x)
      (g.smooth ⊤).neg p r) u) =
      -smulLeftCLM F ψ (smulLeftCLM F (affineSchwartz p r hr g) u) +
      c • smulLeftCLM F ψ u := by
  let a := affineSchwartz p r hr g
  have ht : Function.HasTemperateGrowth (fun x => -a x+c) :=
    a.hasTemperateGrowth.neg.add (by fun_prop)
  rw [localized_coefficient_congr ψ
    (frozenCoefficient χ hχ (fun x => -g x) (g.smooth ⊤).neg p r).hasTemperateGrowth ht
    (fun x hx => by
      simp only [frozenCoefficient_apply,hψ x hx,one_mul,hgp,neg_sub_neg,
        a,affineSchwartz_apply,add_comm (r • x) p]
      ring)]
  change smulLeftCLM F ψ (smulLeftCLM F (- (a : E → ℂ) + fun _ => c) u) = _
  rw [smulLeftCLM_add a.hasTemperateGrowth.neg (by fun_prop),
    smulLeftCLM_neg a.hasTemperateGrowth]
  simp only [_root_.add_apply,_root_.neg_apply,smulLeftCLM_const,map_add,map_neg,
    map_smul]
  rfl

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ContDiffApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section

section

noncomputable section
namespace TamingCompatibility.FormSmooth
open ContinuousAlternatingMap
variable {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : WithTop ℕ∞} {U : Set D}

lemma contDiffOn_apply {k : ℕ} {α : D → E [⋀^Fin k]→L[ℝ] F} {v : Fin k → D → E}
    (hα : ContDiffOn ℝ n α U) (hv : ∀ i, ContDiffOn ℝ n (v i) U) :
    ContDiffOn ℝ n (fun x => α x (fun i => v i x)) U := by
  induction k with
  | zero =>
    convert (ContinuousAlternatingMap.apply ℝ E F (Fin.elim0 : Fin 0 → E)).contDiff.comp_contDiffOn hα using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    change α x (fun i => v i x) = α x Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  | succ k ih =>
    let a : D → E [⋀^Fin k]→L[ℝ] F := fun x => (α x).curryLeft (v 0 x)
    have ha : ContDiffOn ℝ n a U := by
      exact (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).contDiff.comp_contDiffOn hα).clm_apply (hv 0))
    have h := ih ha (fun i => hv i.succ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    change α x (fun i => v i x) = α x (Matrix.vecCons (v 0 x) (fun i => v i.succ x))
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma contDiffOn_apply_two {α : D → E [⋀^Fin 2]→L[ℝ] F} {v w : D → E}
    (hα : ContDiffOn ℝ n α U) (hv : ContDiffOn ℝ n v U) (hw : ContDiffOn ℝ n w U) :
    ContDiffOn ℝ n (fun x => α x ![v x,w x]) U := by
  have h : ∀ i : Fin 2, ContDiffOn ℝ n (![v,w] i) U := by
    intro i
    fin_cases i
    · exact hv
    · exact hw
  convert contDiffOn_apply hα h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  congr 1
  ext i
  fin_cases i <;> rfl

end TamingCompatibility.FormSmooth
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_StarTwoComp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

local instance instNormedAddCommGroupTangentSpaceRealSpaceModel (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)

end TamingCompatibility.ManifoldHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FunSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.EuclideanStokes
open _root_.MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma integral_directional_eq_zero {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (v : E) : (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hc' : HasCompactSupport (fun x => fderiv ℝ f x v) := by
    exact hc.fderiv_apply (𝕜 := ℝ) v
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
    (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hi := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := μ) (f := fun _ : E => (1 : ℝ)) (f' := fun _ => (0 : ℝ))
    (g := f) (g' := fun x => fderiv ℝ f x v) (v := v)
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simp only [ContinuousLinearMap.mul_apply',zero_mul]; exact integrable_zero _ _ _)
    (by simpa using hd.continuous.integrable_of_hasCompactSupport hc')
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).hasLineDerivAt v))
    (fun x _ => (hf.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt v)
  simpa using hi

lemma integral_extDeriv_eq_zero {k : ℕ} {α : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α) (v : Fin (k+1) → E) :
    (∫ x, extDeriv α x v ∂μ) = 0 := by
  have hs (i : Fin (k+1)) : ContDiff ℝ ∞ (fun x => α x (i.removeNth v)) :=
    (ContinuousAlternatingMap.apply ℝ E ℝ (i.removeNth v)).contDiff.comp hα
  have hk (i : Fin (k+1)) : HasCompactSupport (fun x => α x (i.removeNth v)) :=
    hc.comp_left (g := fun a : E [⋀^Fin k]→L[ℝ] ℝ => a (i.removeNth v)) rfl
  have he : (fun x => extDeriv α x v) =
      (fun x => ∑ i : Fin (k+1), (-1 : ℝ) ^ i.val * fderiv ℝ (fun y => α y (i.removeNth v)) x (v i)) := by
    ext x
    simpa only [smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using extDeriv_apply (hα.differentiable (by simp) x) v
  rw [he,integral_finsetSum]
  · simp_rw [integral_const_mul,integral_directional_eq_zero (μ := μ) (hs _) (hk _),mul_zero]
    simp
  · intro i _
    apply Integrable.const_mul
    have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => α y (i.removeNth v)) x (v i)) :=
      ((hs i).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
    exact hd.continuous.integrable_of_hasCompactSupport
      ((hk i).fderiv_apply (𝕜 := ℝ) (v i))
end TamingCompatibility.EuclideanStokes

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_LocalGarding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace

namespace TamingCompatibility.EuclideanEnergy
abbrev Pair := EuclideanSpace ℝ (Fin 2)
def pair (a b : ℝ) : Pair := WithLp.toLp 2 ![a,b]
lemma pair_norm_sq (a b : ℝ) : ‖pair a b‖^2 = a^2 + b^2 := by
  simp [pair, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

lemma norm_add_sq_le {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    ‖u + v‖^2 ≤ 2 * ‖u‖^2 + 2 * ‖v‖^2 := by
  have h := norm_add_le u v
  have hs := sq_nonneg (‖u‖ - ‖v‖)
  nlinarith [norm_nonneg (u+v), norm_nonneg u, norm_nonneg v]

lemma norm_sum_four_sq_le {E : Type*} [SeminormedAddCommGroup E] (f : Fin 4 → E) :
    ‖∑ i, f i‖^2 ≤ 4 * ∑ i, ‖f i‖^2 := by
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.reduceSucc, Fin.fin_one_eq_zero,
    Fin.sum_univ_zero, add_zero]
  have h := norm_add_sq_le (f 0 + f 1) (f 2 + f 3)
  have h1 := norm_add_sq_le (f 0) (f 1)
  have h2 := norm_add_sq_le (f 2) (f 3)
  simp only [add_assoc] at h
  linarith

lemma pair_continuous {D : Type*} [TopologicalSpace D] {f g : D → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => pair (f x) (g x)) := by
  unfold pair
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  fun_prop

end TamingCompatibility.EuclideanEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_ChartGarding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanEnergy
open _root_.MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
lemma norm_add_sq_bound (u v : F) : ‖u+v‖^2 ≤ 2*(‖u‖^2+‖v‖^2) := by
  have h := norm_add_le u v
  have hs := sq_nonneg (‖u‖-‖v‖)
  nlinarith [norm_nonneg (u+v),norm_nonneg u,norm_nonneg v]

end TamingCompatibility.EuclideanEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_VariationalResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped RealInnerProductSpace

namespace TamingCompatibility.Fredholm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def nullspace (K : H →L[ℝ] H) : Submodule ℝ H := (1 - K).ker

omit [CompleteSpace H] in
lemma mem_nullspace (K : H →L[ℝ] H) (x : H) : x ∈ nullspace K ↔ K x = x := by
  change x - K x = 0 ↔ K x = x
  exact sub_eq_zero.trans eq_comm

instance instIsClosedCoeSubmoduleRealNullspace (K : H →L[ℝ] H) : _root_.IsClosed (nullspace K : Set H) := (1 - K).isClosed_ker

instance instCompleteSpaceSubtypeMemSubmoduleRealNullspace (K : H →L[ℝ] H) : CompleteSpace (nullspace K) := _root_.IsClosed.completeSpace_coe

omit [CompleteSpace H] in

lemma map_orthogonal_nullspace (K : H →L[ℝ] H) (hK : K.toLinearMap.IsSymmetric)
    (x : H) (hx : x ∈ (nullspace K)ᗮ) : K x ∈ (nullspace K)ᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  change ⟪y, K.toLinearMap x⟫ = 0
  rw [← hK y x]
  change ⟪K y, x⟫ = 0
  rw [(mem_nullspace K y).mp hy]
  exact hx y hy

end TamingCompatibility.Fredholm

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScaledLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma zoomDistribution_inverse (p : E) (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) :
    affineDistribution p r hr (zoomDistribution p r hr u) = u := by
  have h := affineDistribution_inverse (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) u
  simpa only [zoomDistribution,inv_inv,smul_neg,smul_smul,mul_inv_cancel₀ hr,one_smul,neg_neg] using h

lemma local_cutoff_one (χ ψ : 𝓢(E,ℂ)) (h : ∀ x ∈ tsupport ψ, χ x = 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (smulLeftCLM F χ u) = smulLeftCLM F ψ u := by
  rw [localized_coefficient_congr ψ χ.hasTemperateGrowth
    (show Function.HasTemperateGrowth (fun _ : E => (1 : ℂ)) by fun_prop) h u,
    smulLeftCLM_const,one_smul]

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_FrozenSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_unit_cutoff : ∃ χ : 𝓢(E,ℂ), HasCompactSupport (χ : E → ℂ) ∧
    ∀ x ∈ Metric.ball (0 : E) 1, χ x = 1 := by
  let b : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
  have hs : ContDiff ℝ ∞ (fun x => (b x : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hc : HasCompactSupport (fun x => (b x : ℂ)) := by
    exact b.hasCompactSupport.comp_left (show (fun t : ℝ => (t : ℂ)) 0 = 0 by rfl)
  refine ⟨hc.toSchwartzMap hs,hc,fun x hx => ?_⟩
  change (b x : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx),Complex.ofReal_one]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma principalInBasis_apply (B : OrthonormalBasis κ ℝ E) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (a b : κ) (x : E) :
    principalInBasis B v g a b x = ∑ i, ∑ j, ((⟪B a,v i⟫ * ⟪B b,v j⟫ : ℝ) : ℂ) * g i j x := by
  simp only [principalInBasis,_root_.sum_apply,_root_.smul_apply,Complex.real_smul]

lemma normalized_principal_center [DecidableEq κ]
    (d : OrthonormalBasis ι ℝ E) (B : OrthonormalBasis κ ℝ E)
    (L : E ≃L[ℝ] E) (v : ι → E) (s c k : ℝ)
    (hL : ∀ i, L (v i) = s • d i) (hc : c*(s*s) = k)
    (g : ι → ι → 𝓢(E,ℂ)) (p : E)
    (hg : ∀ i j, g i j p = (c * ∑ t,⟪d i,v t⟫ * ⟪d j,v t⟫ : ℝ)) (a b : κ) :
    principalInBasis B (fun i => L (d i))
      (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (g i j)) a b (L p) =
      if a=b then (k : ℂ) else 0 := by
  rw [principalInBasis_apply]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply,hg,← Complex.ofReal_mul,← Complex.ofReal_sum]
  rw [gram_covariance]
  simp only [hL,inner_smul_right]
  have he : (∑ t,(s*⟪B a,d t⟫)*(s*⟪B b,d t⟫)) = (s*s)*⟪B a,B b⟫ := by
    rw [← d.sum_inner_mul_inner (B a) (B b),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (d i) (B b)]
    ring
  rw [he,← mul_assoc,hc,B.inner_eq_ite]
  split_ifs <;> simp

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SobolevBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def boundedToLpTop : (E →ᵇ F) →L[ℂ] Lp F ⊤ (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun f => (f.memLp_top (μ := volume)).toLp f
      map_add' := fun f g => by
        ext1
        filter_upwards [(f+g).memLp_top.coeFn_toLp,f.memLp_top.coeFn_toLp,
          g.memLp_top.coeFn_toLp,Lp.coeFn_add (f.memLp_top.toLp f) (g.memLp_top.toLp g)] with x h1 h2 h3 h4
        simp only [h1,h4,Pi.add_apply,h2,h3,BoundedContinuousFunction.add_apply]
      map_smul' := fun c f => by
        ext1
        filter_upwards [(c • f).memLp_top.coeFn_toLp,f.memLp_top.coeFn_toLp,
          Lp.coeFn_smul c (f.memLp_top.toLp f)] with x h1 h2 h3
        simp only [h1,h3,Pi.smul_apply,h2,BoundedContinuousFunction.smul_apply,RingHom.id_apply] }
    1 (fun f => by
      change ‖(f.memLp_top (μ := volume)).toLp f‖ ≤ 1 * ‖f‖
      rw [one_mul,Lp.norm_toLp,
        eLpNorm_exponent_top]
      have hle := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure E))
        (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
      exact (ENNReal.toReal_mono (by finiteness) hle).trans_eq
        (ENNReal.toReal_ofReal (norm_nonneg f)))

omit [CompleteSpace F] in
lemma boundedToLpTop_injective : Function.Injective (boundedToLpTop (E := E) (F := F)) := by
  intro f g h
  apply DFunLike.coe_injective
  apply (f.continuous.ae_eq_iff_eq (volume : Measure E) g.continuous).mp
  have he := Lp.ext_iff.mp h
  exact f.memLp_top.coeFn_toLp.symm.trans (he.trans g.memLp_top.coeFn_toLp)

def boundedDistributionCLM : (E →ᵇ F) →L[ℂ] 𝓢'(E,F) :=
  (Lp.toTemperedDistributionCLM F volume ⊤).comp boundedToLpTop

lemma boundedDistributionCLM_injective :
    Function.Injective (boundedDistributionCLM (E := E) (F := F)) := by
  intro f g h
  apply boundedToLpTop_injective
  exact (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) h

end TamingCompatibility.EuclideanSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalRescaleH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.CriticalSobolev
open _root_.MeasureTheory
open scoped SchwartzMap ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma opNorm_le_sum_basis (L : E →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (stdOrthonormalBasis ℝ E i)‖ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  calc
    ‖L x‖ = ‖∑ i, (b.repr x i) • L (b i)‖ := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      simp only [map_smul]
    _ ≤ ∑ i, ‖(b.repr x i) • L (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖L (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have hi : ‖b.repr x i‖ ≤ ‖x‖ := by
        simpa only [LinearIsometryEquiv.norm_map] using PiLp.norm_apply_le (b.repr x) i
      exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; exact mul_comm _ _
end TamingCompatibility.CriticalSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ShrinkingCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open Set Filter
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalizedCutoff (L : E ≃L[ℝ] E) (q : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L
    (affineSchwartz (-(r⁻¹ • L q)) r⁻¹ (inv_ne_zero hr) χ)

end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def rationalKernel (r : ℝ) (z : V) : ℝ := r^4/(r^2+‖z‖^2)^3

lemma rationalKernel_smooth {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (rationalKernel (V := V) r) := by
  unfold rationalKernel
  exact contDiff_const.div ((contDiff_const.add (contDiff_norm_sq ℝ)).pow 3)
    (fun z => by positivity)

section Measure
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [SecondCountableTopology V] in
lemma finite_convolution_smooth (μ : Measure V) [IsFiniteMeasure μ]
    (k : V → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ContDiff ℝ ∞ (fun x => ∫ y, k (x-y) ∂μ) := by
  have hh := hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    ((integrable_const (1:ℝ)).locallyIntegrable (μ := μ)) hk
  have he : convolution (fun _ : V => (1:ℝ)) k (ContinuousLinearMap.mul ℝ ℝ) μ =
      (fun x => ∫ y, k (x-y) ∂μ) := by
    funext x
    simp only [convolution_def,ContinuousLinearMap.mul_apply',one_mul]
  rw [he] at hh
  exact hh

end Measure

def cutKernel (η : V → ℝ) (r : ℝ) (z : V) : ℝ := η z*rationalKernel r z

lemma cutKernel_smooth {r : ℝ} (hr : 0 < r) (η : V → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (cutKernel η r) := hη.mul (rationalKernel_smooth hr)

omit [InnerProductSpace ℝ V] in
lemma cutKernel_compact (η : V → ℝ) (hη : HasCompactSupport η) (r : ℝ) :
    HasCompactSupport (cutKernel η r) := hη.mul_right

end TamingCompatibility.Concentration

end
end

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace TamingCompatibility.Concentration

def radialCoefficient (r t : ℝ) : ℝ := r^4/(r^2+t^2)^4

end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialCoefficientProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E]

def firstOrderSource (V : E → E) (u : E → ℝ) (z : E) : ℝ :=
  fderiv ℝ u z (V z)

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_PlaneMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace TamingCompatibility.Concentration
open ContinuousAlternatingMap
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def testOne (h : V → ℝ) (v : V) : V → V [⋀^Fin 1]→L[ℝ] ℝ :=
  fun y => h y • ofSubsingletonLIE (0 : Fin 1) (innerSL ℝ v)

lemma testOne_smooth {h : V → ℝ} (hh : ContDiff ℝ ∞ h) (v : V) :
    ContDiff ℝ ∞ (testOne h v) := hh.smul contDiff_const

lemma testOne_compact {h : V → ℝ} (hh : HasCompactSupport h) (v : V) :
    HasCompactSupport (testOne h v) := hh.smul_right

lemma testOne_support (h : V → ℝ) (v : V) : tsupport (testOne h v) ⊆ tsupport h :=
  tsupport_smul_subset_left _ _

end TamingCompatibility.Concentration

end
end

end OAI
end


