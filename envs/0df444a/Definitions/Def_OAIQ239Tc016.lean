-- Prove2me | Definitions.Def_OAIQ239Tc016
-- name    : OAIQ239Tc016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:25:23.618787+00:00
-- url     : https://prove2.me/theorems/46e29527-9493-4489-8fa1-57d974b0d97f
-- title:
--   Definitions bundle OAIQ239Tc016 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 6 definitions and 13 theorems. The definitions and types are `OAI.TamingCompatibility.HilbertSobolev.localizationErrorH`, `OAI.TamingCompatibility.HodgeFrozenEnergy.flatSystem`, `OAI.TamingCompatibility.HodgeMatrixEnergy.constantSystem`, `OAI.TamingCompatibility.HodgeMatrixEnergy.system`, `OAI.TamingCompatibility.HodgeNormalOperator.rawPrincipal`, `OAI.TamingCompatibility.ManifoldForms.closedForms`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/ContDiffLinearEmbedding.lean), [`TamingCompatibility_DifferentialForms_QuantitativeInterior`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/QuantitativeInterior.lean), [`TamingCompatibility_Hodge_HodgeFrameDifferential`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeFrameDifferential.lean), [`TamingCompatibility_Hodge_HodgeFrozenEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeFrozenEnergy.lean), [`TamingCompatibility_Hodge_HodgeGeometricCoefficients`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGeometricCoefficients.lean), [`TamingCompatibility_Hodge_HodgeMatrixEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeMatrixEnergy.lean), [`TamingCompatibility_Hodge_HodgeSymbol`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSymbol.lean).
--
--   **Imports.** It imports the bundles `OAIQ239Tc011`, `OAIQ239Tc012` and `OAIQ239Tc013` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc020`; the proof of `OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ239Tc011
import Definitions.Def_OAIQ239Tc012
import Definitions.Def_OAIQ239Tc013

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

namespace TamingCompatibility.ManifoldForms

open TamingCompatibility.FormSmoothness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

def closedForms (X : Type*) [TopologicalSpace X] [ChartedSpace Space X]
    [IsManifold Model ∞ X] (k : ℕ) : Submodule ℝ (smoothForms X k) :=
  LinearMap.ker d

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_QuantitativeInterior
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def localizationErrorH (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (g : 𝓢(E,ℂ)) : H E F ((n:ℝ)+1) →L[ℂ] H E F n :=
  -(((2*Real.pi)^2)⁻¹ : ℝ) • ∑ i, secondCommutatorH n g
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) +
  ∑ i, ∑ j, product n (a i j) ∘L secondCommutatorH n g
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMatrixEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.HodgeMatrixEnergy
open EuclideanEnergy

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
def system (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (f : Field) (x : V) : Q := (∑ i, a i x (derivative f i x)) + b x (value f x)
def constantSystem (c : Fin 4 → W →L[ℝ] Q) (f : Field) (x : V) : Q :=
  ∑ i, c i (derivative f i x)

lemma principalError_bound (a : Fin 4 → V → W →L[ℝ] Q)
    (f : Field) (x : V) {δ : ℝ} (ha : ∀ i, ‖a i x‖ ≤ δ) :
    ‖∑ i, a i x (derivative f i x)‖^2 ≤ 4*δ^2*gradient f x := by
  refine (norm_sum_four_sq_le _).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [gradient,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (a i x).le_opNorm (derivative f i x)
  have hm := mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (derivative f i x))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h.trans hm) 2

lemma system_integrable (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (f : Field) {δ C : ℝ} (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) :
    Integrable (fun x => ‖system a b f x‖^2) := by
  have hcont : Continuous (system a b f) := by
    apply Continuous.add _ (hbc.clm_apply (value_continuous f))
    apply continuous_finsetSum
    intro i _
    exact (hac i).clm_apply (value_continuous (fun j => coordinateDeriv i (f j)))
  have hdom := ((gradient_integrable f).const_mul (8*δ^2)).add
    ((value_integrable f).const_mul (2*C^2))
  refine hdom.mono' (hcont.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := norm_add_sq_le (∑ i, a i x (derivative f i x)) (b x (value f x))
  have hp := principalError_bound a f x (ha x)
  have hl := lowerError_bound b f x (hb x)
  dsimp only [system,Pi.add_apply]
  nlinarith
lemma constantSystem_integrable (c : Fin 4 → W →L[ℝ] Q) (f : Field) :
    Integrable (fun x => ‖constantSystem c f x‖^2) := by
  have h := system_integrable (fun i _ => c i) (fun _ => 0) f
    (δ := ∑ i, ‖c i‖) (C := 0) (fun _ => continuous_const) continuous_const
    (fun _ i => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    (fun _ => by simp)
  simpa only [system,zero_apply,add_zero,constantSystem] using h

lemma comparison_pointwise (c : Fin 4 → W →L[ℝ] Q)
    (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (f : Field) (x : V) {δ C : ℝ} (ha : ∀ i, ‖a i x-c i‖ ≤ δ) (hb : ‖b x‖ ≤ C) :
    ‖constantSystem c f x‖^2 ≤ 2*‖system a b f x‖^2 +
      16*δ^2*gradient f x + 4*C^2*‖value f x‖^2 := by
  let E : Q := ∑ i, (a i x-c i) (derivative f i x)
  let L : Q := b x (value f x)
  have he : constantSystem c f x = system a b f x + -(E+L) := by
    simp only [constantSystem,system,E,L,sub_apply,Finset.sum_sub_distrib]
    abel
  have h0 := norm_add_sq_le (system a b f x) (-(E+L))
  rw [← he,norm_neg] at h0
  have h1 := norm_add_sq_le E L
  have hE := principalError_bound (fun i y => a i y-c i) f x ha
  have hL := lowerError_bound b f x hb
  change ‖E‖^2 ≤ _ at hE
  change ‖L‖^2 ≤ _ at hL
  nlinarith

theorem garding (c : Fin 4 → W →L[ℝ] Q) {K δ C : ℝ} (hK : 0 < K)
    (hsmall : 16*K*δ^2 ≤ 1/2)
    (henergy : ∀ f : Field, (∫ x, gradient f x) ≤ K * (∫ x, ‖constantSystem c f x‖^2))
    (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x-c i‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) (f : Field) :
    (∫ x, gradient f x) ≤ 4*K*(∫ x, ‖system a b f x‖^2) +
      8*K*C^2*(∫ x, ‖value f x‖^2) := by
  have ha' (x : V) (i : Fin 4) : ‖a i x‖ ≤ δ + ∑ j, ‖c j‖ := by
    calc
      ‖a i x‖ ≤ ‖a i x-c i‖ + ‖c i‖ := norm_le_norm_sub_add _ _
      _ ≤ δ + ∑ j, ‖c j‖ := add_le_add (ha x i)
        (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have hS := system_integrable a b f hac hbc ha' hb
  have hG := gradient_integrable f
  have hF := value_integrable f
  have hcomp := integral_mono (constantSystem_integrable c f)
    (((hS.const_mul 2).add (hG.const_mul (16*δ^2))).add (hF.const_mul (4*C^2)))
    (fun x => comparison_pointwise c a b f x (ha x) (hb x))
  dsimp only [Pi.add_apply] at hcomp
  erw [integral_add ((hS.const_mul 2).add (hG.const_mul (16*δ^2))) (hF.const_mul (4*C^2)),
    integral_add (hS.const_mul 2) (hG.const_mul (16*δ^2)),
    integral_const_mul,integral_const_mul,integral_const_mul] at hcomp
  have hcompK := mul_le_mul_of_nonneg_left hcomp hK.le
  have hcoerce := henergy f
  have hG0 : 0 ≤ ∫ x, gradient f x := integral_nonneg (gradient_nonneg f)
  have hsmallG := mul_le_mul_of_nonneg_right hsmall hG0
  nlinarith
end TamingCompatibility.HodgeMatrixEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSymbol
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace
namespace TamingCompatibility.HodgeFlatEnergy
open EuclideanEnergy
open DirectionalEnergy (directionDeriv)

theorem energy_eq_gradient (b : Fin 4 → V) (a : Fin 6 → S) : energy b a = gradientEnergy b a := by
  simp only [energy,gradientEnergy,Fin.sum_univ_succ]
  simp [delta,star, directionDeriv_neg,
    pairing_add_left,pairing_add_right,pairing_sub_left,pairing_sub_right,
    pairing_neg_left,pairing_neg_right]
  simp only [pairing_field_swap,pairing_partial_swap]
  ring
end TamingCompatibility.HodgeFlatEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrozenEnergy
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.swapMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv
namespace TamingCompatibility.HodgeFrozenEnergy
open EuclideanEnergy HodgeMatrixEnergy HodgeNormalSymbol
open DirectionalEnergy (directionDeriv)

lemma gradient_basis_control (b : Module.Basis (Fin 4) ℝ V) (f : Field) (x : V) :
    gradient f x ≤ DirectionalEnergy.coordinateConstant b * directionalGradient b f x := by
  have h (i : Fin 4) (j : Fin 6) := DirectionalEnergy.covector_basis_sq b (fderiv ℝ (f j) x) i
  have hdir (i : Fin 4) : (∑ j : Fin 6, (coordinateDeriv i (f j) x)^2) ≤
      (∑ t, (b.repr (e i) t)^2) * directionalGradient b f x := by
    calc
      _ ≤ ∑ j : Fin 6, (∑ t, (b.repr (e i) t)^2) *
          ∑ t : Fin 4, (directionDeriv b t (f j) x)^2 := by
        exact Finset.sum_le_sum (fun j _ => by
          simpa only [coordinateDeriv,directionDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv] using h i j)
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm

  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdir i)
  have hg : gradient f x = ∑ i : Fin 4, ∑ j : Fin 6, (coordinateDeriv i (f j) x)^2 := by
    simp only [HodgeMatrixEnergy.gradient,HodgeMatrixEnergy.derivative,value_norm]
  rw [← hg,← Finset.sum_mul] at he
  refine he.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · simp [DirectionalEnergy.coordinateConstant]
  · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

def flatSystem (b : Fin 4 → V) (f : Field) (x : V) : Q := WithLp.toLp 2
  ![HodgeFlatEnergy.delta b f 0 x,HodgeFlatEnergy.delta b f 1 x,
    HodgeFlatEnergy.delta b f 2 x,HodgeFlatEnergy.delta b f 3 x,
    HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) 0 x,
    HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) 1 x,
    HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) 2 x,
    HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) 3 x]

lemma frozen_system (b : Fin 4 → V) (f : Field) (x : V) :
    constantSystem (coefficient b) f x = flatSystem b f x := by
  ext k
  fin_cases k <;>
    simp [constantSystem,coefficient,normalSymbol_apply,symbol,UnitaryFrame.interior,
      UnitaryFrame.star,derivative,value,flatSystem,HodgeFlatEnergy.delta,HodgeFlatEnergy.star,
      HodgeFlatEnergy.directionDeriv_neg,directionDeriv_expansion,Fin.sum_univ_succ] <;> ring

lemma flatSystem_integral (b : Fin 4 → V) (f : Field) :
    (∫ x, ‖flatSystem b f x‖^2) = HodgeFlatEnergy.energy b f := by
  have he (x : V) : ‖flatSystem b f x‖^2 =
      (∑ i : Fin 4, (HodgeFlatEnergy.delta b f i x)^2) +
        ∑ i : Fin 4, (HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) i x)^2 := by
    simp [flatSystem,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
    ring
  simp_rw [he]
  rw [integral_add]
  · rw [integral_finsetSum,integral_finsetSum]
    · simp only [HodgeFlatEnergy.energy,HodgeFlatEnergy.pairing,pow_two]
    · intro i _; exact schwartz_sq_integrable _
    · intro i _; exact schwartz_sq_integrable _
  · exact integrable_finsetSum _ (fun i _ => schwartz_sq_integrable _)
  · exact integrable_finsetSum _ (fun i _ => schwartz_sq_integrable _)

theorem frozen_energy (b : Module.Basis (Fin 4) ℝ V) (f : Field) :
    (∫ x, gradient f x) ≤ DirectionalEnergy.coordinateConstant b *
      (∫ x, ‖constantSystem (coefficient b) f x‖^2) := by
  have h := integral_mono (gradient_integrable f)
    ((directionalGradient_integrable b f).const_mul (DirectionalEnergy.coordinateConstant b))
    (gradient_basis_control b f)
  rw [integral_const_mul,directionalGradient_integral] at h
  simp_rw [frozen_system]
  rw [flatSystem_integral,HodgeFlatEnergy.energy_eq_gradient]
  exact h
end TamingCompatibility.HodgeFrozenEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame
open HodgeNormalSymbol (W Q)

def rawPrincipal (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (ψ φ : Fin 6 → MetricForms.Form V 2) (i : Fin 4) : W →L[ℝ] Q :=
  left b ∘L starThreeCLM g F ∘L wedgeBy (EuclideanSpace.proj i) ∘L combine φ +
    right b ∘L starThreeCLM g F ∘L wedgeBy (EuclideanSpace.proj i) ∘L combine ψ

lemma operator_expansion (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (ψ φ : Fin 6 → V → MetricForms.Form V 2) (f : Fin 6 → V → ℝ) {x : V}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x)
    (hψ : ∀ j, DifferentiableAt ℝ (ψ j) x) (hφ : ∀ j, DifferentiableAt ℝ (φ j) x) :
    left b (starThree g F (extDeriv (fun y => ∑ j, f j y • φ j y) x)) +
      right b (starThree g F (extDeriv (fun y => ∑ j, f j y • ψ j y) x)) =
      (∑ i : Fin 4, rawPrincipal g F b (fun j => ψ j x) (fun j => φ j x) i
        (WithLp.toLp 2 (fun j => fderiv ℝ (f j) x (e i)))) +
      lower g F b ψ φ x (WithLp.toLp 2 (fun j => f j x)) := by
  rw [extDeriv_frame f φ hf hφ,extDeriv_frame f ψ hf hψ]
  simp only [rawPrincipal,lower,_root_.add_apply,ContinuousLinearMap.comp_apply,
    combine_apply,combineThree_apply,wedgeBy_apply]
  change left b (starThreeCLM g F (_ + _)) + right b (starThreeCLM g F (_ + _)) = _
  simp only [map_add,_root_.map_sum]
  rw [Finset.sum_add_distrib]
  abel
end TamingCompatibility.HodgeNormalOperator

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory Filter Topology
open scoped SchwartzMap
namespace TamingCompatibility.HodgeMatrixEnergy
open EuclideanEnergy
open MatrixEnergy (continuous_cutoff cutoff_bound exists_small_error)
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

lemma system_patch_eq (c : Fin 4 → W →L[ℝ] Q)
    (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    {x₀ : V} (φ : ContDiffBump x₀) (f : Field)
    (hf : ∀ j, tsupport (f j) ⊆ Metric.closedBall x₀ φ.rIn) (x : V) :
    system (patchPrincipal c a φ) (patchLower b φ) f x = system a b f x := by
  by_cases hx : x ∈ Metric.closedBall x₀ φ.rIn
  · simp only [system,patchPrincipal,patchLower,φ.one_of_mem_closedBall hx,
      one_smul,sub_add_cancel]
  · have hn (j : Fin 6) : x ∉ tsupport (f j) := fun h => hx (hf j h)
    have hv : value f x = 0 := by
      ext j
      change f j x = 0
      exact image_eq_zero_of_notMem_tsupport (hn j)
    have hd (i : Fin 4) : derivative f i x = 0 := by
      ext j
      change coordinateDeriv i (f j) x = 0
      exact image_eq_zero_of_notMem_tsupport (fun h => hn j (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
    simp only [system,hv,hd,map_zero,Finset.sum_const_zero,add_zero]

theorem local_garding (c : Fin 4 → W →L[ℝ] Q) {K : ℝ} (hK : 0 < K)
    (henergy : ∀ f : Field, (∫ x, gradient f x) ≤
      K * (∫ x, ‖constantSystem c f x‖^2))
    {U : Set V} (hU : IsOpen U) {x₀ : V} (hx₀ : x₀ ∈ U)
    (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ha : ∀ i, ContinuousOn (a i) U) (hb : ContinuousOn b U)
    (ha₀ : ∀ i, a i x₀ = c i) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∀ f : Field, (∀ j, tsupport (f j) ⊆ Metric.closedBall x₀ r) →
        (∫ x, gradient f x) ≤ 4*K * (∫ x, ‖system a b f x‖^2) +
          8*K*C^2 * (∫ x, ‖value f x‖^2) := by
  obtain ⟨δ,hδ,hsmall⟩ := exists_small_error hK
  let C := ‖b x₀‖ + 1
  have hC : 0 < C := by dsimp only [C] <;> positivity
  have hae : ∀ᶠ x in 𝓝 x₀, ∀ i, ‖a i x-c i‖ ≤ δ := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun x => ‖a i x-c i‖) x₀ :=
      (((ha i).continuousAt (hU.mem_nhds hx₀)).sub continuousAt_const).norm
    have hz : ‖a i x₀-c i‖ < δ := by simpa only [ha₀ i,sub_self,norm_zero] using hδ
    exact (hc.eventually (gt_mem_nhds hz)).mono (fun _ h => h.le)
  have hbe : ∀ᶠ x in 𝓝 x₀, ‖b x‖ ≤ C := by
    have hz : ‖b x₀‖ < C := by dsimp only [C] <;> linarith
    exact (((hb.continuousAt (hU.mem_nhds hx₀)).norm).eventually
      (gt_mem_nhds hz)).mono (fun _ h => h.le)
  have he : ∀ᶠ x in 𝓝 x₀, x ∈ U ∧ (∀ i, ‖a i x-c i‖ ≤ δ) ∧ ‖b x‖ ≤ C :=
    (show ∀ᶠ x in 𝓝 x₀, x ∈ U from hU.mem_nhds hx₀).and (hae.and hbe)
  obtain ⟨ε,hε,hεgood⟩ := Metric.mem_nhds_iff.mp he
  let φ : ContDiffBump x₀ := {
    rIn := ε/4
    rOut := ε/2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hgood (x : V) (hx : x ∈ tsupport φ) :
      x ∈ U ∧ (∀ i, ‖a i x-c i‖ ≤ δ) ∧ ‖b x‖ ≤ C := by
    rw [φ.tsupport_eq] at hx
    apply hεgood
    have hh := Metric.mem_closedBall.mp hx
    change dist x x₀ ≤ ε/2 at hh
    exact Metric.mem_ball.mpr (by linarith)
  have hφU : tsupport φ ⊆ U := fun x hx => (hgood x hx).1
  have ha' := patchPrincipal_continuous hU c a ha φ hφU
  have hb' : Continuous (patchLower b φ) := continuous_cutoff hU hb φ hφU
  have hap (x : V) (i : Fin 4) : ‖patchPrincipal c a φ i x-c i‖ ≤ δ :=
    patchPrincipal_bound c a hδ.le (fun x hx => (hgood x hx).2.1) φ (Set.Subset.refl _) x i
  have hbp (x : V) : ‖patchLower b φ x‖ ≤ C :=
    cutoff_bound hC.le (fun x hx => (hgood x hx).2.2) φ (Set.Subset.refl _) x
  refine ⟨ε/4,C,by positivity,hC,?_,?_⟩
  · intro x hx
    apply hφU
    rw [φ.tsupport_eq]
    simpa only [φ,show (2:ℝ)*(ε/4) = ε/2 by ring] using hx
  · intro f hf
    have h := garding c hK hsmall henergy (patchPrincipal c a φ) (patchLower b φ)
      ha' hb' hap hbp f
    simpa only [system_patch_eq c a b φ f hf] using h

end TamingCompatibility.HodgeMatrixEnergy

end
end

end
end

end OAI
end


