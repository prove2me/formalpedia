-- Prove2me | Definitions.Def_OAIQ239Tc006
-- name    : OAIQ239Tc006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:14:36.906933+00:00
-- url     : https://prove2.me/theorems/b8c824eb-d076-4145-8eb8-cb63a14ecd04
-- title:
--   Definitions bundle OAIQ239Tc006 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 114 declarations of OpenAI's Lean: 24 definitions and 90 theorems. The definitions and types are `OAI.TamingCompatibility.ComplexMatrix.normalizedFullSquare`, `OAI.TamingCompatibility.ComplexMatrix.principalScalar`, `OAI.TamingCompatibility.ComplexMatrix.weightedAdj`, `OAI.TamingCompatibility.DirectionalEnergy.codifferential`, `OAI.TamingCompatibility.DirectionalEnergy.coordinateConstant`, `OAI.TamingCompatibility.DirectionalEnergy.directionDeriv`, `OAI.TamingCompatibility.DirectionalEnergy.gradientEnergy`, `OAI.TamingCompatibility.EuclideanEnergy.coordinateDeriv`, `OAI.TamingCompatibility.EuclideanEnergy.gradientEnergy`, `OAI.TamingCompatibility.ExteriorForms.dc`, `OAI.TamingCompatibility.ExteriorForms.oneLinear`, `OAI.TamingCompatibility.ExteriorForms.wedgeTwo`, `OAI.TamingCompatibility.LocalMatrixOperator.normalizeFrame`, `OAI.TamingCompatibility.ManifoldForms.jAction`, `OAI.TamingCompatibility.ManifoldHodge.codifferential`, `OAI.TamingCompatibility.ManifoldHodge.coordinateMetric`, `OAI.TamingCompatibility.ManifoldHodge.flatMetric`, `OAI.TamingCompatibility.ManifoldHodge.instNormedSpaceRealTangentSpaceSpaceModel`, `OAI.TamingCompatibility.ManifoldHodge.inverseChartEquiv`, `OAI.TamingCompatibility.ManifoldHodge.starThree`, `OAI.TamingCompatibility.ManifoldHodge.starTwo`, `OAI.TamingCompatibility.ManifoldHodge.tangentMetric`, `OAI.TamingCompatibility.ManifoldTop.volumeForm`, `OAI.TamingCompatibility.MetricHodge.starTwo`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_AffineBase`, `TamingCompatibility_Charts_LocalFormalAdjoint`, `TamingCompatibility_Currents_BoundedDistribution`, `TamingCompatibility_DifferentialForms_ComplexReal`, `TamingCompatibility_DifferentialForms_ConstantGeometricEnergy`, `TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding`, `TamingCompatibility_DifferentialForms_DirectionalEnergy`, `TamingCompatibility_DifferentialForms_FirstOrderAntiDdc`, `TamingCompatibility_DifferentialForms_Form`, `TamingCompatibility_DifferentialForms_FormEquiv`, `TamingCompatibility_DifferentialForms_FormPairing`, `TamingCompatibility_DifferentialForms_Helmholtz`, `TamingCompatibility_DifferentialForms_Kernel`, `TamingCompatibility_DifferentialForms_Linear`, `TamingCompatibility_DifferentialForms_NegativeWeightMoment`, `TamingCompatibility_DifferentialForms_PerturbationNeg`, `TamingCompatibility_DifferentialForms_ScalarSquare`, `TamingCompatibility_DifferentialForms_ScaledLower`, `TamingCompatibility_DifferentialForms_Sign`, `TamingCompatibility_DifferentialForms_Space`, `TamingCompatibility_DifferentialForms_StarTwoComp`, `TamingCompatibility_DifferentialForms_TestEvaluation`, `TamingCompatibility_DifferentialForms_TestLinear`, `TamingCompatibility_DifferentialForms_UnitaryVectors`, `TamingCompatibility_Elliptic_DirectionH1`, `TamingCompatibility_Elliptic_LocalGarding`, `TamingCompatibility_Elliptic_PrincipalDerivativeError`, `TamingCompatibility_Elliptic_PrincipalTransport`, `TamingCompatibility_Elliptic_SobolevBounded`, `TamingCompatibility_Elliptic_SquarePrincipal`, `TamingCompatibility_Functional_ChartNormalTest`, `TamingCompatibility_Functional_NormalizedFrame`, `TamingCompatibility_Hodge_HodgeCommutatorPowers`, `TamingCompatibility_Hodge_HodgeDifferentialLocality`, `TamingCompatibility_Hodge_HodgePairAllTests`, `TamingCompatibility_Hodge_HodgeTestPairing`, `TamingCompatibility_Hodge_LocalCodifferential`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc000`, `OAIQ239Tc001`, `OAIQ239Tc002` and `OAIQ239Tc003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc010`, `OAIQ239Tc011`, `OAIQ239Tc012` and `OAIQ239Tc013`; the proof of `OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc000
import Definitions.Def_OAIQ239Tc001
import Definitions.Def_OAIQ239Tc002
import Definitions.Def_OAIQ239Tc003

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Kernel
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

theorem compact_inverse_cutoff [ProperSpace F] (loc : C(K,E))
    (g : Lp ℂ 2 (volume : Measure E)) {R : ℝ} (hR : 0 ≤ R)
    (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0) :
    IsCompactOperator (CompactKernel.operator (kernel (F := F) loc g hR hg)) :=
  CompactKernel.compact_operator _

lemma inverse_cutoff_apply (loc : C(K,E)) (g : Lp ℂ 2 (volume : Measure E))
    {R : ℝ} (hR : 0 ≤ R) (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0)
    (u : Lp F 2 (volume : Measure E)) (x : K) :
    CompactKernel.operator (kernel loc g hR hg) u x =
      Real.Lp.fourierTransformInv (multiply g u) (loc x) :=
  pairing_modulate_eq_inverse g u (loc x)

end TamingCompatibility.FourierCutoff

end
end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Helmholtz
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
namespace TamingCompatibility.EuclideanGreen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
open TemperedDistribution

theorem helmholtz_green (f : 𝓢'(E,F)) :
    helmholtz (besselPotential E F (-2) f) = f := by
  rw [← bessel_two_eq_helmholtz, besselPotential_besselPotential_apply]
  norm_num

end TamingCompatibility.EuclideanGreen

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PerturbationNeg
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma helmholtz_cutoff (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    EuclideanGreen.helmholtz (smulLeftCLM F g u) =
      smulLeftCLM F g (EuclideanGreen.helmholtz u) -
      (((2*Real.pi)^2)⁻¹ : ℝ) • ∑ i : basisIndex E, secondCommutator g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) u := by
  simp only [EuclideanGreen.helmholtz,
    TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E),
    distribution_second_product, Finset.sum_add_distrib, smul_add,
    map_sub, ContinuousLinearMap.map_smul_of_tower, map_sum]
  abel

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_AffineBase
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
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] [CompleteSpace G] in
lemma affineDistribution_fiberMap (p : E) (r : ℝ) (hr : r ≠ 0)
    (K : F →L[ℂ] G) (u : 𝓢'(E,F)) :
    affineDistribution p r hr (HilbertSobolev.fiberMap K u) =
      HilbertSobolev.fiberMap K (affineDistribution p r hr u) := rfl

end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalFormalAdjoint
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma multiply_pairing (a : 𝓢(D,E →L[ℝ] F)) (u : 𝓢(D,E)) (v : 𝓢(D,F)) (x : D) :
    ⟪multiply a a.hasTemperateGrowth u x, v x⟫ =
      ⟪u x, multiply (adjointCoefficient a) (adjointCoefficient a).hasTemperateGrowth v x⟫ :=
  (ContinuousLinearMap.adjoint_inner_right (a x) (u x) (v x)).symm

lemma directional_formal_adjoint (a : 𝓢(D,E →L[ℝ] F)) (e : D)
    (u : 𝓢(D,E)) (v : 𝓢(D,F)) :
    (∫ x, ⟪multiply a a.hasTemperateGrowth (∂_{e} u) x, v x⟫) =
      -∫ x, ⟪u x, (∂_{e} (multiply (adjointCoefficient a)
        (adjointCoefficient a).hasTemperateGrowth v)) x⟫ := by
  simp_rw [multiply_pairing]
  have h := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
    u (multiply (adjointCoefficient a) (adjointCoefficient a).hasTemperateGrowth v)
    (innerSL ℝ) e (μ := volume)
  change (∫ x, ⟪u x, (∂_{e} (multiply (adjointCoefficient a)
    (adjointCoefficient a).hasTemperateGrowth v)) x⟫) =
      -∫ x, ⟪(∂_{e} u) x, multiply (adjointCoefficient a)
        (adjointCoefficient a).hasTemperateGrowth v x⟫ at h
  linarith

variable {ι : Type*} [Fintype ι]

lemma firstOrder_pairing (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F)) (b : 𝓢(D,E →L[ℝ] F))
    (u : 𝓢(D,E)) (v : 𝓢(D,F)) :
    (∫ x, ⟪firstOrder e a b u x, v x⟫) = ∫ x, ⟪u x, formalAdjoint e a b v x⟫ := by
  simp only [firstOrder, formalAdjoint, _root_.add_apply,
    _root_.neg_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_add_right, inner_sum, sum_inner,
    inner_neg_right]
  rw [integral_add, integral_add]
  · rw [integral_neg, integral_finsetSum, integral_finsetSum]
    · simp only [lineDerivOpCLM_apply]
      rw [show (∑ i, ∫ x, ⟪multiply (a i) (a i).hasTemperateGrowth (∂_{e i} u) x, v x⟫) =
          -∑ i, ∫ x, ⟪u x, (∂_{e i} (multiply (adjointCoefficient (a i))
            (adjointCoefficient (a i)).hasTemperateGrowth v)) x⟫ by
        simp only [directional_formal_adjoint, Finset.sum_neg_distrib]]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall (multiply_pairing b u v))
    · intro i _
      exact inner_integrable _ _
    · intro i _
      exact inner_integrable _ _
  · exact (integrable_finsetSum Finset.univ (fun _ _ => inner_integrable _ _)).neg
  · exact inner_integrable _ _
  · exact integrable_finsetSum Finset.univ (fun _ _ => inner_integrable _ _)
  · exact inner_integrable _ _

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  [CompleteSpace E] [CompleteSpace F] in
lemma weighted_firstOrder (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F))
    (b : 𝓢(D,E →L[ℝ] F)) (ρ : D → ℝ) (hρ : ρ.HasTemperateGrowth)
    (u : 𝓢(D,E)) (x : D) :
    firstOrder e (fun i => weightedCoefficient ρ (a i)) (weightedCoefficient ρ b) u x =
      ρ x • firstOrder e a b u x := by
  simp only [firstOrder, _root_.add_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, multiply_apply, weightedCoefficient_apply ρ hρ,
    _root_.smul_apply, smul_add, Finset.smul_sum]

end TamingCompatibility.LocalFormalAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_BoundedDistribution
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

lemma inverseFourier_boundedDistribution (v : Lp F 1 (volume : Measure E)) :
    𝓕⁻ (v : 𝓢'(E,F)) = boundedDistribution (Real.Lp.fourierTransformInv v) := by
  ext φ
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    boundedDistribution_apply]
  simpa using integral_fourierInv_smul φ v

theorem exists_boundedContinuous_representative {s : ℝ} (hs : Module.finrank ℝ E < 2*s)
    {u : 𝓢'(E,F)} (hu : TemperedDistribution.MemSobolev s 2 u) :
    ∃ g : E →ᵇ F, u = boundedDistribution g := by
  obtain ⟨v,hv⟩ := hu.fourier_memL1 hs
  refine ⟨Real.Lp.fourierTransformInv v, ?_⟩
  rw [← inverseFourier_boundedDistribution, ← hv, fourierInv_fourier_eq]

end TamingCompatibility.EuclideanSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FormPairing
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
namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

lemma pairing_symm (α β : E [⋀^Fin k]→L[ℝ] ℝ) : pairing β α = pairing α β :=
  real_inner_comm _ _

lemma pairing_self_nonneg (α : E [⋀^Fin k]→L[ℝ] ℝ) : 0 ≤ pairing α α :=
  real_inner_self_nonneg

lemma pairing_self_eq_zero {α : E [⋀^Fin k]→L[ℝ] ℝ} : pairing α α = 0 ↔ α = 0 := by
  rw [pairing, inner_self_eq_zero]
  exact ⟨fun h => sharp_injective (h.trans (map_zero sharp).symm), fun h => by simp [h]⟩

end TamingCompatibility.FormMetric

namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

lemma pairing_smul_right (c : ℝ) (α β : E [⋀^Fin k]→L[ℝ] ℝ) :
    pairing α (c • β) = c * pairing α β := by
  simp only [pairing, map_smul, real_inner_smul_right]

end TamingCompatibility.FormMetric

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Form
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
namespace TamingCompatibility.MetricForms
open scoped BigOperators
open RealInnerProductSpace ContinuousAlternatingMap
open MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

lemma pairing_three_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (α β : Form D 3) :
    pairing g (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) =
      pairing h α β := by
  let b : OrthonormalBasis (Fin 4) ℝ (MetricModel.Model g) :=
    (stdOrthonormalBasis ℝ (MetricModel.Model g)).reindex (finCongr ((finrank_model g).trans hdim))
  rw [pairing, pairing, FormMetric.pairing_three b,
    FormMetric.pairing_three (b.map (isometryEquiv g h L hL))]
  rfl

end TamingCompatibility.MetricForms

end

end OAI
end

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

omit [IsManifold Model ∞ X] in
lemma pullback_congr_eventually (α : Form X k) {f g : Space → X} {y : Space}
    (hfg : f =ᶠ[𝓝 y] g) : pullback α f =ᶠ[𝓝 y] pullback α g := by
  filter_upwards [hfg.eventuallyEq_nhds] with z hz
  have hv := hz.self_of_nhds
  unfold pullback
  rw [hz.mfderiv_eq, hv]
  all_goals (ext vectors; rfl)

lemma smooth_chart (α : Form X k) (hα : Smooth α) (x : X) :
    ContDiffOn ℝ ∞ (pullback α (extChartAt Model x).symm) (extChartAt Model x).target :=
  hα _ _ (isOpen_extChartAt_target x) (contMDiffOn_extChartAt_symm x)

theorem smooth_of_charts {α : Form X k}
    (hα : ∀ x, ContDiffOn ℝ ∞ (pullback α (extChartAt Model x).symm)
      (extChartAt Model x).target) : Smooth α := by
  intro f U hU hf y hy
  let p := f y
  let e := extChartAt Model p
  let g : Space → Space := e ∘ f
  let β := pullback α e.symm
  have hfy : ContMDiffAt Model Model ∞ f y := (hf y hy).contMDiffAt (hU.mem_nhds hy)
  have hgy : ContMDiffAt Model Model ∞ g y :=
    (contMDiffAt_extChartAt (I := Model) (x := p)).comp y hfy
  have hegy : g y ∈ e.target := e.map_source (mem_extChartAt_source p)
  have hβ : ContDiffAt ℝ ∞ β (g y) :=
    ((hα p) (g y) hegy).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hegy)
  have hgf : e.symm ∘ g =ᶠ[𝓝 y] f := by
    have hs : ∀ᶠ z in 𝓝 y, f z ∈ e.source :=
      hfy.continuousAt.eventually (extChartAt_source_mem_nhds p)
    filter_upwards [hs] with z hz
    exact e.left_inv hz
  have hpb : (fun z => (β (g z)).compContinuousLinearMap (fderiv ℝ g z)) =ᶠ[𝓝 y]
      pullback α f := by
    have hs : ∀ᶠ z in 𝓝 y, f z ∈ e.source :=
      hfy.continuousAt.eventually (extChartAt_source_mem_nhds p)
    filter_upwards [hs, hU.mem_nhds hy, pullback_congr_eventually α hgf] with z hz hzU hpz
    have hgz : ContMDiffAt Model Model ∞ g z :=
      (contMDiffAt_extChartAt' (I := Model) (by simpa only [e, extChartAt_source] using hz)).comp z
        ((hf z hzU).contMDiffAt (hU.mem_nhds hzU))
    have hez : ContMDiffAt Model Model ∞ e.symm (g z) :=
      ((contMDiffOn_extChartAt_symm p) (g z) (e.map_source hz)).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds (e.map_source hz))
    rw [← pullback_comp α (hez.mdifferentiableAt (by simp))
      ((contMDiffAt_iff_contDiffAt.mp hgz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
    exact hpz
  have hg : ContDiffAt ℝ ∞ g y := contMDiffAt_iff_contDiffAt.mp hgy
  have hdg : ContDiffAt ℝ ∞ (fderiv ℝ g) y := hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (((hβ.comp y hg).compAlternating hdg).congr_of_eventuallyEq hpb.symm).contDiffWithinAt

theorem pullback_exteriorDerivative (α : Form X k) (hα : Smooth α)
    {f : Space → X} {U : Set Space} (hU : IsOpen U)
    (hf : ContMDiffOn Model Model ∞ f U) {y : Space} (hy : y ∈ U) :
    pullback (exteriorDerivative α) f y = extDerivWithin (pullback α f) U y := by
  let p := f y
  let e := extChartAt Model p
  let g : Space → Space := e ∘ f
  let β := pullback α e.symm
  have hfy : ContMDiffAt Model Model ∞ f y := (hf y hy).contMDiffAt (hU.mem_nhds hy)
  have hgy : ContMDiffAt Model Model ∞ g y :=
    (contMDiffAt_extChartAt (I := Model) (x := p)).comp y hfy
  have hegy : g y ∈ e.target := e.map_source (mem_extChartAt_source p)
  have hβ : ContDiffAt ℝ ∞ β (g y) :=
    ((smooth_chart α hα p) (g y) hegy).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hegy)
  have hgf : e.symm ∘ g =ᶠ[𝓝 y] f := by
    have hs : ∀ᶠ z in 𝓝 y, f z ∈ e.source :=
      hfy.continuousAt.eventually (extChartAt_source_mem_nhds p)
    filter_upwards [hs] with z hz
    exact e.left_inv hz
  have hpb : (fun z => (β (g z)).compContinuousLinearMap (fderiv ℝ g z)) =ᶠ[𝓝 y]
      pullback α f := by
    have hs : ∀ᶠ z in 𝓝 y, f z ∈ e.source :=
      hfy.continuousAt.eventually (extChartAt_source_mem_nhds p)
    filter_upwards [hs, hU.mem_nhds hy, pullback_congr_eventually α hgf] with z hz hzU hpz
    have hgz : ContMDiffAt Model Model ∞ g z :=
      (contMDiffAt_extChartAt' (I := Model) (by simpa only [e, extChartAt_source] using hz)).comp z
        ((hf z hzU).contMDiffAt (hU.mem_nhds hzU))
    have hez : ContMDiffAt Model Model ∞ e.symm (g z) :=
      ((contMDiffOn_extChartAt_symm p) (g z) (e.map_source hz)).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds (e.map_source hz))
    rw [← pullback_comp α (hez.mdifferentiableAt (by simp))
      ((contMDiffAt_iff_contDiffAt.mp hgz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
    exact hpz
  have hdg : fderiv ℝ g y = mfderiv Model Model f y := by
    rw [← mfderiv_eq_fderiv]
    have he : MDifferentiableAt Model Model (extChartAt Model p) p :=
      (contMDiffAt_extChartAt (n := ∞) (I := Model) (x := p)).mdifferentiableAt (by simp)
    change mfderiv Model Model ((extChartAt Model p) ∘ f) y = _
    rw [mfderiv_comp y he (hfy.mdifferentiableAt (by simp))]
    ext v
    change mfderiv Model Model (extChartAt Model p) p (mfderiv Model Model f y v) = _
    rw [mfderiv_extChartAt_self]
    rfl
  rw [extDerivWithin_eq_of_mem hU hy, ← hpb.extDeriv_eq,
    extDeriv_pullback (hβ.differentiableAt (by simp))
      (contMDiffAt_iff_contDiffAt.mp hgy) (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr le_top), hdg]
  rfl

theorem Smooth.exteriorDerivative {α : Form X k} (hα : Smooth α) :
    Smooth (exteriorDerivative α) := by
  intro f U hU hf
  have hd : ContDiffOn ℝ ∞ (extDerivWithin (pullback α f) U) U := by
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Space ℝ).contDiff.comp_contDiffOn
      ((contDiffOn_infty_iff_fderivWithin hU.uniqueDiffOn).mp (hα f U hU hf)).2
  apply hd.congr
  intro y hy
  exact pullback_exteriorDerivative α hα hU hf hy

omit [IsManifold Model ∞ X] in
lemma pullback_smul (c : ℝ) (α : Form X k) (f : Space → X) :
    pullback (c • α) f = c • pullback α f := rfl

omit [IsManifold Model ∞ X] in
lemma Smooth.smul (c : ℝ) {α : Form X k} (hα : Smooth α) : Smooth (c • α) := by
  intro f U hU hf
  rw [pullback_smul]
  exact (hα f U hU hf).const_smul c

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Space
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

namespace TamingCompatibility.ManifoldForms

open TamingCompatibility.FormSmoothness TamingCompatibility.SmoothAlmostComplex Bundle

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

def jAction (J : SmoothAlmostComplex.AlmostComplexStructure X) (α : Form X k) : Form X k :=
  fun x => (α x).compContinuousLinearMap (J.endomorphism x)

lemma pullback_jAction_chart (J : SmoothAlmostComplex.AlmostComplexStructure X)
    (α : Form X k) (x : X) {z : Space} (hz : z ∈ (extChartAt Model x).target) :
    pullback (jAction J α) (extChartAt Model x).symm z =
      (pullback α (extChartAt Model x).symm z).compContinuousLinearMap
        (SmoothAlmostComplex.coord J (trivializationAt Space (TangentSpace Model) x)
          ((extChartAt Model x).symm z)) := by
  let e := extChartAt Model x
  let te := trivializationAt Space (TangentSpace Model) x
  have hs : e.symm z ∈ (chartAt Space x).source := by
    simpa only [e, extChartAt_source] using e.map_target hz
  have ht : e.symm z ∈ te.baseSet := by
    simpa only [te, TangentBundle.trivializationAt_baseSet] using hs
  have hd : mfderiv Model Model e.symm z = te.symmL ℝ (e.symm z) := by
    rw [TangentBundle.symmL_trivializationAt hs]
    change mfderiv Model Model e.symm z =
      mfderivWithin Model Model e.symm (Set.range Model) (e (e.symm z))
    rw [e.right_inv hz]
    simp only [Model, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]
  apply ContinuousAlternatingMap.ext
  intro v
  change (α (e.symm z)) (fun i => J.endomorphism (e.symm z)
      (mfderiv Model Model e.symm z (v i))) =
    (α (e.symm z)) (fun i => mfderiv Model Model e.symm z
      (te.continuousLinearMapAt ℝ (e.symm z) (J.endomorphism (e.symm z)
        (te.symmL ℝ (e.symm z) (v i)))))
  apply congrArg (α (e.symm z))
  funext i
  rw [hd]
  exact (te.symmL_continuousLinearMapAt (R := ℝ) ht
    (J.endomorphism (e.symm z) (te.symmL ℝ (e.symm z) (v i)))).symm

theorem Smooth.jAction {α : Form X k} (hα : Smooth α)
    (J : SmoothAlmostComplex.AlmostComplexStructure X) : Smooth (jAction J α) := by
  apply smooth_of_charts
  intro x
  apply ((smooth_chart α hα x).compAlternating
    (SmoothAlmostComplex.contDiffOn_coord_chart J x)).congr
  intro z hz
  exact pullback_jAction_chart J α x hz

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma IsSmooth.jAction {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) : IsSmooth (jAction J α) := by
  exact ManifoldForms.Smooth.jAction hα
    (⟨J.endomorphism, J.square, J.smooth⟩ : SmoothAlmostComplex.AlmostComplexStructure X)

lemma IsSmooth.invariantPart {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) : IsSmooth (invariantPart J α) :=
  (hα.add (hα.jAction J)).smul _

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Linear
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {E D P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
  {k : ℕ}

def oneLinear (a : Form (E := E) 1) : E →L[ℝ] ℝ := (ofSubsingletonLIE (0 : Fin 1)).symm a
lemma oneLinear_apply (a : Form (E := E) 1) (u : E) : oneLinear a u = a ![u] := by
  change a (fun _ => u) = a ![u]
  congr 1
  ext i
  fin_cases i
  rfl

def wedgeTwo (a b : Form (E := E) 2) : Form (E := E) 4 :=
  volumeSquare (a+b) - volumeSquare a - volumeSquare b

lemma volumeSquare_apply_vec (F : Form (E := E) 2) (v : Fin 4 → E) :
    volumeSquare F v = F ![v 0,v 1] * F ![v 2,v 3] -
      F ![v 0,v 2] * F ![v 1,v 3] + F ![v 0,v 3] * F ![v 1,v 2] := by
  have hv : v = ![v 0,v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
  nth_rw 1 [hv]
  exact volumeSquare_apply F _ _ _ _

lemma volumeSquare_comp (F : Form (E := E) 2) (L : D →L[ℝ] E) :
    (volumeSquare F).compContinuousLinearMap L = volumeSquare (F.compContinuousLinearMap L) := by
  ext v
  rw [compContinuousLinearMap_apply,volumeSquare_apply_vec,volumeSquare_apply_vec]
  have he (u w : D) : (F.compContinuousLinearMap L) ![u,w] = F ![L u,L w] := by
    change F (L ∘ ![u,w]) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  simp only [Function.comp_apply,he]

lemma wedgeTwo_comp (a b : Form (E := E) 2) (L : D →L[ℝ] E) :
    (wedgeTwo a b).compContinuousLinearMap L = wedgeTwo (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  have hs (a b : Form (E := E) 4) :
      (a-b).compContinuousLinearMap L = a.compContinuousLinearMap L - b.compContinuousLinearMap L := by
    ext v
    rfl
  have ha : (a+b).compContinuousLinearMap L = a.compContinuousLinearMap L+b.compContinuousLinearMap L := by
    ext v
    rfl
  simp only [wedgeTwo,hs,volumeSquare_comp,ha]

lemma wedgeTwo_apply (a b : Form (E := E) 2) (u v w z : E) :
    wedgeTwo a b ![u,v,w,z] = a ![u,v] * b ![w,z] - a ![u,w] * b ![v,z] +
      a ![u,z] * b ![v,w] + a ![w,z] * b ![u,v] - a ![v,z] * b ![u,w] + a ![v,w] * b ![u,z] := by
  simp only [wedgeTwo, ContinuousAlternatingMap.sub_apply,volumeSquare_apply,
    ContinuousAlternatingMap.add_apply]
  ring

lemma wedgeOne_apply_four (a : E →L[ℝ] ℝ) (b : Form (E := E) 3) (u v w z : E) :
    wedgeOne a b ![u,v,w,z] = a u * b ![v,w,z] - a v * b ![u,w,z] +
      a w * b ![u,v,z] - a z * b ![u,v,w] := by
  rw [wedgeOne, alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 4) ![u,v,w,z] = ![v,w,z] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 4) ![u,v,w,z] = ![u,w,z] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 4) ![u,v,w,z] = ![u,v,z] := by ext i; fin_cases i <;> rfl
  have h3 : Fin.removeNth (3 : Fin 4) ![u,v,w,z] = ![u,v,w] := by ext i; fin_cases i <;> rfl
  simp [Fin.sum_univ_succ,h0,h1,h2,h3,ContinuousLinearMap.smulRight_apply,sub_eq_add_neg]
  ring

lemma wedgeOne_comp (a : E →L[ℝ] ℝ) (b : Form (E := E) k) (L : D →L[ℝ] E) :
    (wedgeOne a b).compContinuousLinearMap L = wedgeOne (a ∘L L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [wedgeOne,compContinuousLinearMap_apply,alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,Function.comp_apply]
  congr 1

lemma oneLinear_comp (a : Form (E := E) 1) (L : D →L[ℝ] E) :
    oneLinear (a.compContinuousLinearMap L) = oneLinear a ∘L L := by
  ext u
  rfl

lemma extDeriv_one (a : E → Form (E := E) 1) (x u v : E) :
    extDeriv a x ![u,v] = (fderiv ℝ a x u) ![v] - (fderiv ℝ a x v) ![u] := by
  rw [extDeriv,alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 2) ![u,v] = ![v] := by ext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) ![u,v] = ![u] := by ext i; fin_cases i; rfl
  simp [Fin.sum_univ_succ,h0,h1,sub_eq_add_neg]

lemma extDeriv_two (b : E → Form (E := E) 2) (x u v w : E) :
    extDeriv b x ![u,v,w] = (fderiv ℝ b x u) ![v,w] -
      (fderiv ℝ b x v) ![u,w] + (fderiv ℝ b x w) ![u,v] := by
  rw [extDeriv,alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 3) ![u,v,w] = ![v,w] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 3) ![u,v,w] = ![u,w] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![u,v,w] = ![u,v] := by ext i; fin_cases i <;> rfl
  simp [Fin.sum_univ_succ,h0,h1,h2,sub_eq_add_neg]
  ring

lemma extDeriv_three (b : E → Form (E := E) 3) (x u v w z : E) :
    extDeriv b x ![u,v,w,z] = (fderiv ℝ b x u) ![v,w,z] -
      (fderiv ℝ b x v) ![u,w,z] + (fderiv ℝ b x w) ![u,v,z] - (fderiv ℝ b x z) ![u,v,w] := by
  rw [extDeriv,alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 4) ![u,v,w,z] = ![v,w,z] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 4) ![u,v,w,z] = ![u,w,z] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 4) ![u,v,w,z] = ![u,v,z] := by ext i; fin_cases i <;> rfl
  have h3 : Fin.removeNth (3 : Fin 4) ![u,v,w,z] = ![u,v,w] := by ext i; fin_cases i <;> rfl
  simp [Fin.sum_univ_succ,h0,h1,h2,h3,sub_eq_add_neg]
  ring

lemma fderiv_wedgeOne {a : E → Form (E := E) 1} {b : E → Form (E := E) k}
    {x : E} (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (u : E) :
    fderiv ℝ (fun y => wedgeOne (oneLinear (a y)) (b y)) x u =
      wedgeOne (oneLinear (a x)) (fderiv ℝ b x u) +
      wedgeOne (oneLinear (fderiv ℝ a x u)) (b x) := by
  exact congrArg (fun L : E →L[ℝ] Form (E := E) (k+1) => L u)
    ((wedgeOneBilinear (E := E) (k := k)).hasFDerivAt_of_bilinear ha.hasFDerivAt hb.hasFDerivAt).fderiv

lemma extDeriv_wedgeOne {a : E → Form (E := E) 1} {b : E → Form (E := E) 2}
    {x : E} (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    extDeriv (fun y => wedgeOne (oneLinear (a y)) (b y)) x =
      wedgeTwo (extDeriv a x) (b x) - wedgeOne (oneLinear (a x)) (extDeriv b x) := by
  ext v
  have hv : v = ![v 0,v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
  rw [hv,extDeriv_three,ContinuousAlternatingMap.sub_apply,wedgeTwo_apply,wedgeOne_apply_four]
  simp only [fderiv_wedgeOne ha hb,ContinuousAlternatingMap.add_apply,
    wedgeOne_apply_three,oneLinear_apply,extDeriv_one,extDeriv_two]
  ring

end TamingCompatibility.ExteriorForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FormEquiv
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
namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap MetricForms MetricModel ExteriorForms
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

def starTwo (g : Metric E) (J : E →L[ℝ] E) (F α : MetricForms.Form E 2) :
    MetricForms.Form E 2 := pairing g α F • F - α.compContinuousLinearMap J

end TamingCompatibility.MetricHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryVectors
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

namespace TamingCompatibility.SmoothHodge
open ContinuousAlternatingMap MetricForms MetricModel MetricHodge FormSmooth
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [FiniteDimensional ℝ E] in
lemma curryLeft_contDiffOn {k : ℕ} {α : D → MetricForms.Form E (k+1)} {v : D → E} {U : Set D}
    (hα : ContDiffOn ℝ ∞ α U) (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (fun x => (α x).curryLeft (v x)) U := by
  let C : MetricForms.Form E (k+1) →L[ℝ] (E →L[ℝ] MetricForms.Form E k) := curryLeftLI.toContinuousLinearMap
  exact ((C.contDiff.comp_contDiffOn hα).clm_apply hv)

lemma comp_contDiffOn {k : ℕ} {α : D → MetricForms.Form E k} {J : D → E →L[ℝ] E} {U : Set D}
    (hα : ContDiffOn ℝ ∞ α U) (hJ : ContDiffOn ℝ ∞ J U) :
    ContDiffOn ℝ ∞ (fun x => (α x).compContinuousLinearMap (J x)) U := by
  apply contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  change ContDiffOn ℝ ∞ (fun x => α x (fun i => J x (Module.finBasis ℝ E (a i)))) U
  exact FormSmooth.contDiffOn_apply hα (fun i => hJ.clm_apply contDiffOn_const)

end TamingCompatibility.SmoothHodge

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
namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap MetricForms MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

lemma starThree_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form D 2) (α : MetricForms.Form D 3) :
    starThree g (F.compContinuousLinearMap L.toContinuousLinearMap) (α.compContinuousLinearMap L.toContinuousLinearMap) =
      (starThree h F α).compContinuousLinearMap L.toContinuousLinearMap := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv,starThree_apply]
  have hc : ((starThree h F α).compContinuousLinearMap L.toContinuousLinearMap) ![v 0] =
      starThree h F α ![L (v 0)] := by rfl
  rw [hc,starThree_apply,volumeSquare_comp]
  have he : ((ExteriorForms.volumeSquare F).compContinuousLinearMap L.toContinuousLinearMap).curryLeft (v 0) =
      ((ExteriorForms.volumeSquare F).curryLeft (L (v 0))).compContinuousLinearMap L.toContinuousLinearMap := by
    ext w
    change ExteriorForms.volumeSquare F (fun i => L (Matrix.vecCons (v 0) w i)) =
      ExteriorForms.volumeSquare F (Matrix.vecCons (L (v 0)) (fun i => L (w i)))
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [he,pairing_three_comp g h L hL hdim]

end TamingCompatibility.MetricHodge

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instNormedAddCommGroupTangentSpaceRealSpaceModel
local instance instNormedSpaceRealTangentSpaceSpaceModel (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)

def tangentMetric (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (x : X) :
    MetricModel.Metric (TangentSpace Model x) where
  bilinear := associatedBilinear J (invariantPart J α) x
  symm := (invariantPart_isInvariant J α).associatedBilinear_symm x
  positive := (tames_invariantPart ht).associatedBilinear_pos x

def starTwo (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (β : TwoForm X) : TwoForm X :=
  fun x => MetricHodge.starTwo (tangentMetric J α ht x) (J.endomorphism x) (invariantPart J α x) (β x)

def starThree (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 3) : ManifoldForms.Form X 1 :=
  fun x => MetricHodge.starThree (tangentMetric J α ht x) (invariantPart J α x) (β x)

def inverseChartEquiv (p : X) (z : Space) (hz : z ∈ (extChartAt Model p).target) :
    Space ≃L[ℝ] TangentSpace Model ((extChartAt Model p).symm z) :=
  ((trivializationAt Space (TangentSpace Model) p).continuousLinearEquivAt ℝ
    ((extChartAt Model p).symm z) (by
      simpa only [TangentBundle.trivializationAt_baseSet,extChartAt_source] using
        (extChartAt Model p).map_target hz)).symm

lemma inverseChartEquiv_coe (p : X) (z : Space) (hz : z ∈ (extChartAt Model p).target) :
    (inverseChartEquiv p z hz).toContinuousLinearMap = mfderiv Model Model (extChartAt Model p).symm z := by
  rw [inverseChart_derivative p hz]
  exact Trivialization.symm_continuousLinearEquivAt_eq' _ _

def flatMetric : MetricModel.Metric Space where
  bilinear := innerSL ℝ
  symm := fun u v => real_inner_comm v u
  positive := fun _ h => real_inner_self_pos.mpr h

def coordinateMetric (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (z : Space) : MetricModel.Metric Space := by
  classical
  exact if hz : z ∈ (extChartAt Model p).target then
    ⟨chartMetric J α p z, chartMetric_symm J α p hz, chartMetric_pos J α ht p hz⟩
  else flatMetric

lemma coordinateMetric_bilinear (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    (coordinateMetric J α ht p z).bilinear = chartMetric J α p z := by
  simp only [coordinateMetric,dite_eq_left hz]

lemma coordinateMetric_pullback (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    (tangentMetric J α ht ((extChartAt Model p).symm z)).bilinear
      (inverseChartEquiv p z hz u) (inverseChartEquiv p z hz v) =
        (coordinateMetric J α ht p z).bilinear u v := by
  rw [coordinateMetric_bilinear J α ht p hz,chartMetric_derivative J α p hz]
  change associatedBilinear J (invariantPart J α) _
    ((inverseChartEquiv p z hz).toContinuousLinearMap u) ((inverseChartEquiv p z hz).toContinuousLinearMap v) = _
  rw [inverseChartEquiv_coe]
  rfl

lemma coordinateJ_conjugate (J : AlmostComplexStructure X) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u : Space) :
    coordinateJ J p z u = (inverseChartEquiv p z hz).symm
      (J.endomorphism ((extChartAt Model p).symm z) (inverseChartEquiv p z hz u)) := by
  let te := trivializationAt Space (TangentSpace Model) p
  have hy : (extChartAt Model p).symm z ∈ te.baseSet := by
    simpa only [te,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      (extChartAt Model p).map_target hz
  change te.continuousLinearMapAt ℝ _ (J.endomorphism _ (te.symmL ℝ _ u)) = _
  simp only [inverseChartEquiv,ContinuousLinearEquiv.symm_symm,
    Trivialization.coe_continuousLinearEquivAt_eq,Trivialization.symm_continuousLinearEquivAt_eq]
  rfl

lemma coordinateJ_intertwine (J : AlmostComplexStructure X) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u : Space) :
    inverseChartEquiv p z hz (coordinateJ J p z u) =
      J.endomorphism ((extChartAt Model p).symm z) (inverseChartEquiv p z hz u) := by
  rw [coordinateJ_conjugate J p hz,ContinuousLinearEquiv.apply_symm_apply]

lemma coordinateJ_square (J : AlmostComplexStructure X) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u : Space) : coordinateJ J p z (coordinateJ J p z u) = -u := by
  apply (inverseChartEquiv p z hz).injective
  rw [coordinateJ_intertwine J p hz,coordinateJ_intertwine J p hz,J.square,map_neg]

lemma coordinateMetric_hermitian (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    (coordinateMetric J α ht p z).bilinear (coordinateJ J p z u) (coordinateJ J p z v) =
      (coordinateMetric J α ht p z).bilinear u v := by
  rw [← coordinateMetric_pullback J α ht p hz,← coordinateMetric_pullback J α ht p hz,
    coordinateJ_intertwine J p hz,coordinateJ_intertwine J p hz]
  exact (invariantPart_isInvariant J α).associatedBilinear_hermitian _ _ _

lemma pullback_starThree (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 3) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (starThree J α ht β) (extChartAt Model p).symm z =
      MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (ManifoldForms.pullback β (extChartAt Model p).symm z) := by
  have he := MetricHodge.starThree_comp (coordinateMetric J α ht p z)
    (tangentMetric J α ht ((extChartAt Model p).symm z)) (inverseChartEquiv p z hz)
    (coordinateMetric_pullback J α ht p hz) (by simp [Space])
    (invariantPart J α ((extChartAt Model p).symm z)) (β ((extChartAt Model p).symm z))
  rw [inverseChartEquiv_coe] at he
  exact he.symm

def codifferential (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : TwoForm X) : ManifoldForms.Form X 1 :=
  -starThree J α ht (ManifoldForms.exteriorDerivative (starTwo J α ht β))

end TamingCompatibility.ManifoldHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Sign
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

namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
variable {E D P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma volumeSquare_contDiffOn {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {U : Set P} {n : WithTop ℕ∞} {F : P → Form (E := E) 2}
    (hF : ContDiffOn ℝ n F U) : ContDiffOn ℝ n (fun x => volumeSquare (F x)) U := by
  apply FormSmooth.contDiffOn_of_basis b
  intro a
  simp_rw [volumeSquare_apply_vec]
  have hf (v : Fin 2 → E) : ContDiffOn ℝ n (fun x => F x v) U :=
    (ContinuousAlternatingMap.apply ℝ E ℝ v).contDiff.comp_contDiffOn hF
  exact ((hf _).mul (hf _)).sub ((hf _).mul (hf _)) |>.add ((hf _).mul (hf _))

end TamingCompatibility.ExteriorForms

namespace TamingCompatibility.ManifoldTop
open Bundle ContinuousAlternatingMap ManifoldHodge ExteriorForms
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

def volumeForm (J : AlmostComplexStructure X) (α : TwoForm X) : ManifoldForms.Form X 4 :=
  fun x => volumeSquare (E := Space) (invariantPart J α x)

end TamingCompatibility.ManifoldTop

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_LocalCodifferential
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

namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma extDeriv_variable_smul {k : ℕ} {f : E → ℝ} {a : E → Form (E := E) k} {x : E}
    (hf : DifferentiableAt ℝ f x) (ha : DifferentiableAt ℝ a x) :
    extDeriv (fun y => f y • a y) x = f x • extDeriv a x + wedgeOne (fderiv ℝ f x) (a x) := by
  simp only [extDeriv,fderiv_fun_smul hf ha,alternatizeUncurryFin_add,
    alternatizeUncurryFin_smul,wedgeOne]
end TamingCompatibility.ExteriorForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_LocalGarding
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
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace

namespace TamingCompatibility.EuclideanEnergy

def coordinateDeriv (i : Fin 4) (f : S) : S := ∂_{e i} f

def gradientEnergy (A B : S) (x : V) : ℝ :=
  ∑ i : Fin 4, ((coordinateDeriv i A x)^2 + (coordinateDeriv i B x)^2)

lemma schwartz_mul_integrable (f g : S) : Integrable (fun x => f x * g x) := by
  exact (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) g.hasTemperateGrowth f).integrable

lemma schwartz_sq_integrable (f : S) : Integrable (fun x => (f x)^2) := by
  simpa only [pow_two] using schwartz_mul_integrable f f

lemma gradientEnergy_integrable (A B : S) : Integrable (gradientEnergy A B) := by
  exact integrable_finsetSum Finset.univ fun i _ =>
    (schwartz_sq_integrable (coordinateDeriv i A)).add (schwartz_sq_integrable (coordinateDeriv i B))

end TamingCompatibility.EuclideanEnergy

namespace TamingCompatibility.EuclideanEnergy

lemma principalError_bound (a : Fin 4 → V → Pair →L[ℝ] V)
    (A B : S) (x : V) {δ : ℝ} (ha : ∀ i, ‖a i x‖ ≤ δ) :
    ‖∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x))‖^2 ≤
      4 * δ^2 * gradientEnergy A B x := by
  refine (norm_sum_four_sq_le _).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [gradientEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (a i x).le_opNorm (pair (coordinateDeriv i A x) (coordinateDeriv i B x))
  have hm := mul_le_mul_of_nonneg_right (ha i)
    (norm_nonneg (pair (coordinateDeriv i A x) (coordinateDeriv i B x)))
  have hh := pow_le_pow_left₀ (norm_nonneg _) (h.trans hm) 2
  rw [mul_pow, pair_norm_sq] at hh
  exact hh

lemma lowerError_bound (b : V → Pair →L[ℝ] V) (A B : S) (x : V) {C : ℝ}
    (hb : ‖b x‖ ≤ C) :
    ‖b x (pair (A x) (B x))‖^2 ≤ C^2 * ((A x)^2 + (B x)^2) := by
  have h := (b x).le_opNorm (pair (A x) (B x))
  have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg (pair (A x) (B x)))
  have hh := pow_le_pow_left₀ (norm_nonneg _) (h.trans hm) 2
  simpa only [mul_pow, pair_norm_sq] using hh

end TamingCompatibility.EuclideanEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_DirectionalEnergy
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
namespace TamingCompatibility.DirectionalEnergy
open EuclideanEnergy

def directionDeriv (b : Fin 4 → V) (i : Fin 4) (f : S) : S := ∂_{b i} f
lemma second_partial_comm (b : Fin 4 → V) (i j : Fin 4) (f : S) :
    directionDeriv b i (directionDeriv b j f) = directionDeriv b j (directionDeriv b i f) := by
  ext x
  simp only [directionDeriv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((f.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  change (fderiv ℝ (fun y => fderiv ℝ f y (b j)) x) (b i) =
    (fderiv ℝ (fun y => fderiv ℝ f y (b i)) x) (b j)
  rw [fderiv_clm_apply hf (differentiableAt_const _),
    fderiv_clm_apply hf (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact ((f.smooth 2).contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num) _ _

lemma partial_mul_integral_swap (b : Fin 4 → V) (i j : Fin 4) (f g : S) :
    (∫ x, directionDeriv b i f x * directionDeriv b j g x) = ∫ x, directionDeriv b j f x * directionDeriv b i g x := by
  have hi := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) f (directionDeriv b j g) (b i)
  have hj := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) f (directionDeriv b i g) (b j)
  change (∫ x, f x * directionDeriv b i (directionDeriv b j g) x) = -(∫ x, directionDeriv b i f x * directionDeriv b j g x) at hi
  change (∫ x, f x * directionDeriv b j (directionDeriv b i g) x) = -(∫ x, directionDeriv b j f x * directionDeriv b i g x) at hj
  rw [second_partial_comm] at hi
  linarith

def codifferential (b : Fin 4 → V) (A B : S) (x : V) : V := WithLp.toLp 2
  ![-directionDeriv b 2 A x - directionDeriv b 3 B x, -directionDeriv b 2 B x + directionDeriv b 3 A x,
    directionDeriv b 0 A x + directionDeriv b 1 B x, directionDeriv b 0 B x - directionDeriv b 1 A x]

def gradientEnergy (b : Fin 4 → V) (A B : S) (x : V) : ℝ :=
  ∑ i : Fin 4, ((directionDeriv b i A x)^2 + (directionDeriv b i B x)^2)

lemma gradientEnergy_integrable (b : Fin 4 → V) (A B : S) : Integrable (gradientEnergy b A B) := by
  exact integrable_finsetSum Finset.univ fun i _ =>
    (schwartz_sq_integrable (directionDeriv b i A)).add (schwartz_sq_integrable (directionDeriv b i B))

lemma codifferential_energy_pointwise (b : Fin 4 → V) (A B : S) (x : V) :
    ‖codifferential b A B x‖^2 = gradientEnergy b A B x +
      2 * (directionDeriv b 2 A x * directionDeriv b 3 B x - directionDeriv b 3 A x * directionDeriv b 2 B x +
        directionDeriv b 0 A x * directionDeriv b 1 B x - directionDeriv b 1 A x * directionDeriv b 0 B x) := by
  simp [codifferential, EuclideanSpace.real_norm_sq_eq, gradientEnergy, Fin.sum_univ_succ]
  ring

theorem codifferential_energy (b : Fin 4 → V) (A B : S) :
    (∫ x, ‖codifferential b A B x‖^2) = ∫ x, gradientEnergy b A B x := by
  have hm (i j : Fin 4) := schwartz_mul_integrable (directionDeriv b i A) (directionDeriv b j B)
  simp_rw [codifferential_energy_pointwise]
  have hC : Integrable (fun x =>
      directionDeriv b 2 A x * directionDeriv b 3 B x - directionDeriv b 3 A x * directionDeriv b 2 B x +
      directionDeriv b 0 A x * directionDeriv b 1 B x - directionDeriv b 1 A x * directionDeriv b 0 B x) :=
    (((hm 2 3).sub (hm 3 2)).add (hm 0 1)).sub (hm 1 0)
  calc
    _ = (∫ x, gradientEnergy b A B x) +
        ∫ x, 2 * (directionDeriv b 2 A x * directionDeriv b 3 B x - directionDeriv b 3 A x * directionDeriv b 2 B x +
          directionDeriv b 0 A x * directionDeriv b 1 B x - directionDeriv b 1 A x * directionDeriv b 0 B x) :=
      integral_add (gradientEnergy_integrable b A B) (hC.const_mul 2)
    _ = _ := by
      have hsub := integral_sub (((hm 2 3).sub (hm 3 2)).add (hm 0 1)) (hm 1 0)
      have hadd := integral_add ((hm 2 3).sub (hm 3 2)) (hm 0 1)
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hadd
      rw [integral_const_mul, hsub, hadd, integral_sub (hm 2 3) (hm 3 2),
        partial_mul_integral_swap b 2 3 A B, partial_mul_integral_swap b 0 1 A B]
      ring

end TamingCompatibility.DirectionalEnergy

end
end

section

noncomputable section
namespace TamingCompatibility.DirectionalEnergy
open EuclideanEnergy
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace

def coordinateConstant (b : Module.Basis (Fin 4) ℝ V) : ℝ :=
  1 + ∑ i : Fin 4, ∑ j : Fin 4, (b.repr (e i) j)^2
lemma coordinateConstant_pos (b : Module.Basis (Fin 4) ℝ V) : 0 < coordinateConstant b := by
  unfold coordinateConstant
  positivity

lemma covector_basis_expansion (b : Module.Basis (Fin 4) ℝ V) (ξ : V →L[ℝ] ℝ) (u : V) :
    ξ u = ∑ j, b.repr u j * ξ (b j) := by
  calc
    ξ u = ξ (∑ j, b.repr u j • b j) := congrArg ξ (b.sum_repr u).symm
    _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]

lemma covector_basis_sq (b : Module.Basis (Fin 4) ℝ V) (ξ : V →L[ℝ] ℝ) (i : Fin 4) :
    (ξ (e i))^2 ≤ (∑ j, (b.repr (e i) j)^2) * ∑ j, (ξ (b j))^2 := by
  rw [covector_basis_expansion b ξ (e i)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma gradient_control (b : Module.Basis (Fin 4) ℝ V) (A B : S) (x : V) :
    EuclideanEnergy.gradientEnergy A B x ≤ coordinateConstant b * gradientEnergy b A B x := by
  have hA (i : Fin 4) := covector_basis_sq b (fderiv ℝ A x) i
  have hB (i : Fin 4) := covector_basis_sq b (fderiv ℝ B x) i
  have hdir (i : Fin 4) : (coordinateDeriv i A x)^2 + (coordinateDeriv i B x)^2 ≤
      (∑ j, (b.repr (e i) j)^2) * gradientEnergy b A B x := by
    simpa only [coordinateDeriv,directionDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv,
      gradientEnergy,Finset.sum_add_distrib,mul_add] using add_le_add (hA i) (hB i)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdir i)
  change EuclideanEnergy.gradientEnergy A B x ≤ _ at h
  rw [← Finset.sum_mul] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (by simp [coordinateConstant])
    (Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

end TamingCompatibility.DirectionalEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ConstantGeometricEnergy
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
open scoped SchwartzMap RealInnerProductSpace

namespace TamingCompatibility.DirectionalEnergy
open EuclideanEnergy
lemma codifferential_integrable_sq (b : Fin 4 → V) (A B : S) :
    Integrable (fun x => ‖codifferential b A B x‖^2) := by
  have hm (i j : Fin 4) := schwartz_mul_integrable (directionDeriv b i A) (directionDeriv b j B)
  simp_rw [codifferential_energy_pointwise]
  exact (gradientEnergy_integrable b A B).add
    (((((hm 2 3).sub (hm 3 2)).add (hm 0 1)).sub (hm 1 0)).const_mul 2)
end TamingCompatibility.DirectionalEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexReal
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
namespace TamingCompatibility.ComplexMatrix
open _root_.MeasureTheory LineDeriv TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {ι : Type*} [Fintype ι] {m n : ℕ}

lemma square_embed (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m))
    (b : 𝓢(D,R n →L[ℝ] R m)) (ρ : 𝓢(D,ℝ)) (u : 𝓢(D,R n)) :
    square e a b ρ (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n)) =
      (SchwartzMap.postcompCLM (embed n)
        (LocalFormalAdjoint.formalAdjoint e (fun i => LocalFormalAdjoint.weightedCoefficient ρ (a i))
          (LocalFormalAdjoint.weightedCoefficient ρ b) (LocalFormalAdjoint.firstOrder e a b u)) : 𝓢'(D,C n)) := by
  rw [square,ContinuousLinearMap.comp_apply,firstOrder_embed,formalAdjoint_embed]
end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstOrderAntiDdc
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dc (J : E → E →L[ℝ] E) (f : E → ℝ) (x : E) : Form (E := E) 1 :=
  ofSubsingletonLIE (0 : Fin 1) (-(fderiv ℝ f x).comp (J x))

end TamingCompatibility.ExteriorForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_NegativeWeightMoment
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

theorem exists_smooth_representative {u : 𝓢'(E,F)}
    (hu : ∀ s : ℝ, MemSobolev s 2 u) :
    ∃ g : E →ᵇ F, ContDiff ℝ ∞ (g : E → F) ∧ u = boundedDistribution g := by
  have hs : Module.finrank ℝ E < 2*((Module.finrank ℝ E : ℝ)+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  obtain ⟨v,hv⟩ := (hu _).fourier_memL1 hs
  refine ⟨Real.Lp.fourierTransformInv v, ?_, ?_⟩
  · have hc : ContDiff ℝ ∞ (𝓕 (v : E → F)) :=
      Real.contDiff_fourier (fun n _ => fourier_moments_of_all_orders hu v hv n)
    have he : (Real.Lp.fourierTransformInv v : E → F) = 𝓕⁻ (v : E → F) := by
      ext x
      exact Real.Lp.fourierTransformInv_apply v x
    rw [he]
    have he' : 𝓕⁻ (v : E → F) = (𝓕 (v : E → F)) ∘ Neg.neg := by
      ext x
      exact Real.fourierInv_eq_fourier_neg _ x
    rw [he']
    exact hc.comp contDiff_neg
  · rw [← inverseFourier_boundedDistribution, ← hv, fourierInv_fourier_eq]

end TamingCompatibility.EuclideanSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalDerivativeError
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
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian FourierTransform
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma helmholtz_derivative (v : E) (u : 𝓢'(E,F)) :
    EuclideanGreen.helmholtz (∂_{v} u) = ∂_{v} (EuclideanGreen.helmholtz u) := by
  rw [← EuclideanGreen.bessel_two_eq_helmholtz, ← EuclideanGreen.bessel_two_eq_helmholtz]
  apply (FourierTransform.fourierEquiv ℂ 𝓢'(E,F)).injective
  change 𝓕 (besselPotential E F 2 (∂_{v} u)) = 𝓕 (∂_{v} (besselPotential E F 2 u))
  simp only [fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
    fourier_lineDerivOp_eq, map_smul]
  congr 1
  rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  rw [mul_comm]

lemma principalDerivativeError_memSobolev (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (v : E)
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+2) 2 u) :
    MemSobolev n 2 (principalDerivativeError a v u) := by
  apply memSobolev_sum
  intro i _
  apply memSobolev_sum
  intro j _
  apply memSobolev_nat_product
  convert hu.lineDerivOp.lineDerivOp using 1
  all_goals try with_reducible_and_instances rfl
  ring

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SquarePrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} {m n : ℕ}

def principalScalar (a : ι → 𝓢(D,R 2 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (i j : ι) : 𝓢(D,ℂ) :=
  (1/2:ℂ) • (principalMatrix a ρ i j 0 0 + principalMatrix a ρ j i 0 0)

end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_ChartNormalTest
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
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms EuclideanEnergy
open scoped RealInnerProductSpace

def normalizeFrame (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) : V ≃L[ℝ] V :=
  (MetricModel.equiv g).symm.trans
    (basisOfFrame g (by simp [V]) b hb).repr.toContinuousLinearEquiv

lemma normalizeFrame_apply (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (i : Fin 4) :
    normalizeFrame g b hb (b i) = e i := by
  change (basisOfFrame g (by simp [V]) b hb).repr (ofOriginal g (b i)) = _
  rw [← basisOfFrame_apply g (by simp [V]) b hb i]
  rw [OrthonormalBasis.repr_self]
  rfl

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {ι : Type*} [Fintype ι] {m : ℕ}

def weightedAdj (ρ : 𝓢(D,ℝ)) (a : 𝓢(D,R 2 →L[ℝ] R m)) :
    Fin 2 → Fin m → 𝓢(D,ℂ) :=
  coefficient (LocalFormalAdjoint.adjointCoefficient (LocalFormalAdjoint.weightedCoefficient ρ a))

end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalTransport
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
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma directionalPrincipal_zoom (p : E) (r : ℝ) (hr : r ≠ 0) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    zoomDistribution p r hr (directionalPrincipal v g u) =
      (r⁻¹*r⁻¹) • directionalPrincipal v (fun i j => affineSchwartz p r hr (g i j))
        (zoomDistribution p r hr u) := by
  simp only [directionalPrincipal,map_sum,zoomDistribution_product,zoomDistribution_second,
    ContinuousLinearMap.map_smul_of_tower,Finset.smul_sum]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma matrixLowerOrder_zoom (p : E) (r : ℝ) (hr : r ≠ 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    zoomDistribution p r hr (matrixLowerOrder b L v c K u) =
      matrixLowerOrder (fun i => r⁻¹ • affineSchwartz p r hr (b i)) L v
        (fun i => affineSchwartz p r hr (c i)) K (zoomDistribution p r hr u) := by
  simp only [matrixLowerOrder,map_add,map_sum,zoomDistribution_product]
  simp only [zoomDistribution,affineDistribution_fiberMap,affineDistribution_derivative,
    ContinuousLinearMap.map_smul_of_tower,scalar_product_smul]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScaledLower
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

lemma matrixLowerOrder_scale (r : ℝ)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    r • matrixLowerOrder b L v c K u =
      matrixLowerOrder (fun i => r • b i) L v (fun i => r • c i) K u := by
  simp only [matrixLowerOrder,smul_add,Finset.smul_sum,scalar_product_smul]

lemma rescaled_system (p : E) (r : ℝ) (hr : r ≠ 0) (d : ι → E)
    (g : ι → ι → 𝓢(E,ℂ))
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    {τ : Type*} [Fintype τ] (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    (r*r) • zoomDistribution p r hr (-directionalPrincipal d g u + matrixLowerOrder b L v c K u) =
      -directionalPrincipal d (fun i j => affineSchwartz p r hr (g i j)) (zoomDistribution p r hr u) +
      matrixLowerOrder (fun i => r • affineSchwartz p r hr (b i)) L v
        (fun i => (r*r) • affineSchwartz p r hr (c i)) K (zoomDistribution p r hr u) := by
  simp only [map_add,map_neg,directionalPrincipal_zoom,matrixLowerOrder_zoom,smul_add,smul_neg,smul_smul]
  have h1 : (r*r)*(r⁻¹*r⁻¹) = 1 := by field_simp
  have h2 : r*r*r⁻¹ = r := by field_simp
  rw [h1,one_smul,matrixLowerOrder_scale]
  simp only [smul_smul,h2]

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TestEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {n m : ℕ} {ι : Type*} [Fintype ι]

lemma square_component_apply (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m))
    (b : 𝓢(D,R n →L[ℝ] R m)) (ρ : 𝓢(D,ℝ)) (u : 𝓢(D,R n))
    (φ : 𝓢(D,ℝ)) (j : Fin n) :
    (square e a b ρ (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      ((∫ x, ρ x * ⟪LocalFormalAdjoint.firstOrder e a b u x,
        LocalFormalAdjoint.firstOrder e a b (componentTest j φ) x⟫ : ℝ) : ℂ) := by
  rw [square_embed,embedded_component_apply]
  congr 1
  have h := LocalFormalAdjoint.firstOrder_pairing e
    (fun i => LocalFormalAdjoint.weightedCoefficient ρ (a i))
    (LocalFormalAdjoint.weightedCoefficient ρ b) (componentTest j φ)
    (LocalFormalAdjoint.firstOrder e a b u)
  simp_rw [LocalFormalAdjoint.weighted_firstOrder e a b ρ ρ.hasTemperateGrowth] at h
  simpa only [real_inner_smul_left,real_inner_smul_right,real_inner_comm] using h.symm
end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DirectionH1
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
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma direction_norm_sq_bound (L : V →L[ℝ] F) (v : V) (hv : ‖v‖ ≤ 1) :
    ‖L v‖^2 ≤ 4 * ∑ i : Fin 4, ‖L (e i)‖^2 := by
  have hexp : v = ∑ i : Fin 4, v i • e i := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e] using
      ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v).symm
  have hc (i : Fin 4) : ‖v i‖ ≤ 1 := by
    rw [← EuclideanSpace.basisFun_inner]
    exact (norm_inner_le_norm _ _).trans (by simpa using hv)
  have hn : ‖L v‖ ≤ ∑ i : Fin 4, ‖L (e i)‖ := by
    conv_lhs => rw [hexp,map_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      rw [map_smul,norm_smul]
      exact (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)).trans_eq (one_mul _))
  have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 4 => ‖L (e i)‖)
  simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at hsq
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hsq

lemma direction_integral_bound (u : 𝓢(V,F)) (v : V) (hv : ‖v‖ ≤ 1) :
    (∫ x, ‖(∂_{v} u) x‖^2) ≤ 4 * ∑ i : Fin 4, ∫ x, ‖(∂_{e i} u) x‖^2 := by
  have hi (w : V) : Integrable (fun x => ‖(∂_{w} u) x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (SchwartzMap.continuous _).aestronglyMeasurable).mp
      ((∂_{w} u).memLp 2 volume)
  calc
    _ ≤ ∫ x, 4 * ∑ i : Fin 4, ‖(∂_{e i} u) x‖^2 := by
      apply integral_mono (hi v) ((integrable_finsetSum _ fun i _ => hi (e i)).const_mul 4)
      intro x
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact direction_norm_sq_bound (fderiv ℝ u x) v hv
    _ = _ := by rw [integral_const_mul,integral_finsetSum _ fun i _ => hi (e i)]
end TamingCompatibility.EuclideanEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TestLinear
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

namespace TamingCompatibility.ComplexMatrix
open Set
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma realComponent_support {n : ℕ} (q : 𝓢(E,R n)) (j : Fin n) :
    tsupport (realComponent q j) ⊆ tsupport q :=
  tsupport_comp_subset (map_zero (EuclideanSpace.proj (𝕜 := ℝ) j)) q
end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalizedFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy HilbertSobolev
open scoped RealInnerProductSpace SchwartzMap

lemma exists_scaled_normalize (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (c k : ℝ) (hc : 0 < c) (hk : 0 < k) :
    ∃ (L : V ≃L[ℝ] V) (s : ℝ), c*(s*s)=k ∧ ∀ i, L (b i)=s • e i := by
  let s := Real.sqrt (k/c)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hk hc)
  refine ⟨(normalizeFrame g b hb).trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := V) (Units.mk0 s (ne_of_gt hs))),s,?_,?_⟩
  · have hh : s*s = k/c := by simpa only [← sq] using Real.sq_sqrt (le_of_lt (div_pos hk hc))
    rw [hh]
    field_simp
  · intro i
    change s • normalizeFrame g b hb (b i) = _
    rw [normalizeFrame_apply]

lemma exists_principal_normalization (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (c k : ℝ) (hc : 0 < c) (hk : 0 < k)
    (G : Fin 4 → Fin 4 → 𝓢(V,ℂ)) (p : V)
    (hG : ∀ i j, G i j p = (c * ∑ t,b t i * b t j : ℝ)) :
    ∃ L : V ≃L[ℝ] V, ∀ a d,
      principalInBasis (stdOrthonormalBasis ℝ V) (fun i => L (e i))
        (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (G i j)) a d (L p) =
        if a=d then (k : ℂ) else 0 := by
  obtain ⟨L,s,hcL,hL⟩ := exists_scaled_normalize g b hb c k hc hk
  let d := EuclideanSpace.basisFun (Fin 4) ℝ
  have hd (i : Fin 4) : d i = e i := by simp only [d,EuclideanSpace.basisFun_apply,e]
  refine ⟨L,fun a t => ?_⟩
  have hh := normalized_principal_center d (stdOrthonormalBasis ℝ V) L b s c k
    (by simpa only [hd] using hL) hcL G p (by
      intro i j
      rw [hG]
      congr 2
      apply Finset.sum_congr rfl
      intro t _
      simp only [d,EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left,map_one,one_mul]) a t
  simpa only [hd] using hh

end TamingCompatibility.LocalMatrixOperator

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

lemma boundedDistributionCLM_apply (f : E →ᵇ F) :
    boundedDistributionCLM f = boundedDistribution f := rfl

end TamingCompatibility.EuclideanSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeTestPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open TemperedDistribution
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma product_embed_schwartz {n : ℕ} (ρ : 𝓢(E,ℝ)) (q : 𝓢(E,R n)) :
    SchwartzMap.smulLeftCLM (C n) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (SchwartzMap.postcompCLM (embed n) q) =
    SchwartzMap.postcompCLM (embed n) (SchwartzMap.smulLeftCLM (R n) ρ q) := by
  ext z i
  simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth,SchwartzMap.postcompCLM_apply,embed_apply,
    PiLp.smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairAllTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open scoped SchwartzMap
lemma real_full_decompose {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (q : 𝓢(E,R n)) :
    (q : E → R n) = ∑ j, (componentTest j (realComponent q j) : E → R n) := by
  classical
  ext x k
  simp [componentTest_apply,EuclideanSpace.single,Pi.single_apply]
end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCommutatorPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

def normalizedFullSquare
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) : 𝓢'(V,C 6) →L[ℂ] 𝓢'(V,C 6) :=
  (smulLeftCLM (C 6) θ).comp (fullShiftedSquare a b ρ 0)

lemma operator_power_order (P : 𝓢'(V,C 6) →L[ℂ] 𝓢'(V,C 6))
    (hP : ∀ (n : ℕ) {u}, MemSobolev ((n:ℝ)+2) 2 u → MemSobolev n 2 (P u))
    (k n : ℕ) {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2*k) 2 u) :
    MemSobolev n 2 ((P^k) u) := by
  induction k generalizing n with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp]
    apply hP n
    have h := ih (n+2)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
    apply h
    convert hu using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast <;> ring)

lemma operator_power_commutator_order (P : 𝓢'(V,C 6) →L[ℂ] 𝓢'(V,C 6))
    (M : C 6 →L[ℂ] C 6)
    (hP : ∀ (n : ℕ) {u}, MemSobolev ((n:ℝ)+2) 2 u → MemSobolev n 2 (P u))
    (hC : ∀ (n : ℕ) {u}, MemSobolev ((n:ℝ)+1) 2 u →
      MemSobolev n 2 (P (fiberMap M u)-fiberMap M (P u)))
    (k n : ℕ) {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2*k+1) 2 u) :
    MemSobolev n 2 ((P^(k+1)) (fiberMap M u)-fiberMap M ((P^(k+1)) u)) := by
  induction k generalizing n with
  | zero => simpa using hC n (by simpa using hu)
  | succ k ih =>
    have he : (P ^ (k+1+1)) (fiberMap M u)-fiberMap M ((P^(k+1+1)) u) =
        P ((P^(k+1)) (fiberMap M u)-fiberMap M ((P^(k+1)) u)) +
          (P (fiberMap M ((P^(k+1)) u))-fiberMap M (P ((P^(k+1)) u))) := by
      rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,map_sub]
      abel
    rw [he]
    apply MemSobolev.add
    · apply hP n
      have h := ih (n+2)
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
      apply h
      convert hu using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast <;> ring)
    · apply hC n
      have h := operator_power_order P hP (k+1) (n+1) (u := u)
      norm_num only [Nat.cast_add, Nat.cast_one] at h
      apply h
      convert hu using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast <;> ring)

end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeDifferentialLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution Filter Set
open LocalMatrixOperator EuclideanEnergy
open scoped SchwartzMap LineDeriv Topology
variable {m : ℕ}

lemma triple_product_cancel (χ θ ρ : 𝓢(V,ℂ))
    (h : ∀ z ∈ tsupport χ, θ z * ρ z = 1) (u : 𝓢'(V,C 6)) :
    smulLeftCLM (C 6) χ (smulLeftCLM (C 6) θ (smulLeftCLM (C 6) ρ u)) =
      smulLeftCLM (C 6) χ u := by
  rw [smulLeftCLM_smulLeftCLM_apply ρ.hasTemperateGrowth θ.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply (ρ.hasTemperateGrowth.mul θ.hasTemperateGrowth)
      χ.hasTemperateGrowth]
  have he : ((ρ : V → ℂ) * θ) * χ = (χ : V → ℂ) := by
    ext z
    change (ρ z * θ z) * χ z = χ z
    rw [mul_comm (ρ z) (θ z)]
    by_cases hz : z ∈ tsupport χ
    · rw [h z hz,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]
  rw [he]
end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end


