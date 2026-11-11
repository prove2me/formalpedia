-- Prove2me | Definitions.Def_OAIQ239Tc013
-- name    : OAIQ239Tc013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:19:46.361488+00:00
-- url     : https://prove2.me/theorems/9bd5c93d-326f-4226-b837-3ecf25c28887
-- title:
--   Definitions bundle OAIQ239Tc013 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 4 definitions and 13 theorems. The definitions and types are `OAI.TamingCompatibility.HilbertSobolev.matrixLowerH`, `OAI.TamingCompatibility.HodgeFlatEnergy.gradientEnergy`, `OAI.TamingCompatibility.HodgeFrozenEnergy.directionalGradient`, `OAI.TamingCompatibility.HodgeStarGeometry.swapMap`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_DifferentialForms_QuantitativeInterior`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/QuantitativeInterior.lean), [`TamingCompatibility_Hodge_HodgeFrozenEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeFrozenEnergy.lean), [`TamingCompatibility_Hodge_HodgeGeometricCoefficients`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGeometricCoefficients.lean), [`TamingCompatibility_Hodge_HodgeStarGeometry`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeStarGeometry.lean), [`TamingCompatibility_Hodge_HodgeSymbol`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSymbol.lean).
--
--   **Imports.** It imports the bundles `OAIQ239Tc005`, `OAIQ239Tc006`, `OAIQ239Tc007` and `OAIQ239Tc008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc016`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ239Tc005
import Definitions.Def_OAIQ239Tc006
import Definitions.Def_OAIQ239Tc007
import Definitions.Def_OAIQ239Tc008

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_QuantitativeInterior
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

def matrixLowerH {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) : H E F ((n:ℝ)+1) →L[ℂ] H E F n :=
  (∑ i, product n (b i) ∘L fiberOperator n (L i) ∘L derivative ((n:ℝ)+1) (v i)) +
  ∑ i, product n (c i) ∘L fiberOperator n (K i) ∘L inclusion (by linarith : (n:ℝ) ≤ n+1)

end TamingCompatibility.HilbertSobolev

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

lemma pairing_add_left (a b c : S) : pairing (a+b) c = pairing a c+pairing b c := by
  simp only [pairing,add_apply,add_mul]
  exact integral_add (schwartz_mul_integrable a c) (schwartz_mul_integrable b c)
lemma pairing_add_right (a b c : S) : pairing a (b+c) = pairing a b+pairing a c := by
  simp only [pairing,add_apply,mul_add]
  exact integral_add (schwartz_mul_integrable a b) (schwartz_mul_integrable a c)
lemma pairing_sub_left (a b c : S) : pairing (a-b) c = pairing a c-pairing b c := by
  rw [sub_eq_add_neg,pairing_add_left,pairing_neg_left,sub_eq_add_neg]
lemma pairing_sub_right (a b c : S) : pairing a (b-c) = pairing a b-pairing a c := by
  rw [sub_eq_add_neg,pairing_add_right,pairing_neg_right,sub_eq_add_neg]
lemma pairing_partial_swap (b : Fin 4 → V) (i j : Fin 4) (f g : S) :
    pairing (directionDeriv b i f) (directionDeriv b j g) =
      pairing (directionDeriv b j f) (directionDeriv b i g) :=
  DirectionalEnergy.partial_mul_integral_swap b i j f g

lemma pairing_field_swap (b : Fin 4 → V) (i j : Fin 4) (f g : S) :
    pairing (directionDeriv b i f) (directionDeriv b j g) =
      pairing (directionDeriv b i g) (directionDeriv b j f) := by
  rw [pairing_partial_swap, pairing_comm]

lemma directionDeriv_neg (b : Fin 4 → V) (i : Fin 4) (f : S) :
    directionDeriv b i (-f) = -directionDeriv b i f := by
  ext x
  simp [directionDeriv]

def gradientEnergy (b : Fin 4 → V) (a : Fin 6 → S) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 6, pairing (directionDeriv b i (a j)) (directionDeriv b i (a j))

end TamingCompatibility.HodgeFlatEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrozenEnergy
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

def directionalGradient (b : Fin 4 → V) (f : Field) (x : V) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 6, (directionDeriv b i (f j) x)^2
lemma directionalGradient_integrable (b : Fin 4 → V) (f : Field) :
    Integrable (directionalGradient b f) :=
  integrable_finsetSum _ (fun _ _ => integrable_finsetSum _
    (fun _ _ => schwartz_sq_integrable _))
lemma directionalGradient_integral (b : Fin 4 → V) (f : Field) :
    (∫ x, directionalGradient b f x) = HodgeFlatEnergy.gradientEnergy b f := by
  unfold directionalGradient
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp only [HodgeFlatEnergy.pairing,pow_two]
    · intro j _; exact schwartz_sq_integrable _
  · intro i _
    exact integrable_finsetSum _ (fun j _ => schwartz_sq_integrable _)

lemma directionDeriv_expansion (b : Fin 4 → V) (j : Fin 4) (f : S) (x : V) :
    directionDeriv b j f x = ∑ i : Fin 4, b j i * coordinateDeriv i f x := by
  simp only [directionDeriv,coordinateDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have he : b j = ∑ i, b j i • e i := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e]
      using ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr (b j)).symm
  conv_lhs => rw [he]
  simp only [map_sum,map_smul,smul_eq_mul]

end TamingCompatibility.HodgeFrozenEnergy

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

lemma patchPrincipal_continuous {U : Set V} (hU : IsOpen U)
    (c : Fin 4 → W →L[ℝ] Q) (a : Fin 4 → V → W →L[ℝ] Q)
    (ha : ∀ i, ContinuousOn (a i) U) {x₀ : V} (φ : ContDiffBump x₀)
    (hφ : tsupport φ ⊆ U) (i : Fin 4) : Continuous (patchPrincipal c a φ i) :=
  (continuous_cutoff hU ((ha i).sub continuousOn_const) φ hφ).add continuous_const

lemma patchPrincipal_bound {U : Set V} (c : Fin 4 → W →L[ℝ] Q)
    (a : Fin 4 → V → W →L[ℝ] Q) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ x ∈ U, ∀ i, ‖a i x-c i‖ ≤ δ) {x₀ : V} (φ : ContDiffBump x₀)
    (hφ : tsupport φ ⊆ U) (x : V) (i : Fin 4) : ‖patchPrincipal c a φ i x-c i‖ ≤ δ := by
  simpa only [patchPrincipal,add_sub_cancel_right] using
    cutoff_bound hδ (fun x hx => ha x hx i) φ hφ x

end TamingCompatibility.HodgeMatrixEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeStarGeometry
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.HodgeStarGeometry
open HodgeNormalSymbol HodgeNormalOperator HodgeFrame MetricModel MetricForms MetricHodge
open scoped ContDiff Topology RealInnerProductSpace
open ContinuousAlternatingMap Filter
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def swapMap : Q →L[ℝ] Q := LinearMap.toContinuousLinearMap {
  toFun := swap
  map_add' := by intro a b; ext i; fin_cases i <;> simp [swap]
  map_smul' := by intro c a; ext i; fin_cases i <;> simp [swap] }
@[simp] lemma swapMap_apply (u : Q) : swapMap u = swap u := rfl

end TamingCompatibility.HodgeStarGeometry

end
end

end

end OAI
end


