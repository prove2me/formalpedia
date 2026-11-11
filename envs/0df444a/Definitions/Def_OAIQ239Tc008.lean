-- Prove2me | Definitions.Def_OAIQ239Tc008
-- name    : OAIQ239Tc008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:14:35.946356+00:00
-- url     : https://prove2.me/theorems/3c33c3e5-d038-4d8c-8019-c6489e832386
-- title:
--   Definitions bundle OAIQ239Tc008 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 156 declarations of OpenAI's Lean: 66 definitions, 1 inductive type or structure, 1 instance and 88 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.KernelSeries.correction`, `OAI.TamingCompatibility.GeometricHilbert.KernelSeries.term`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.modelSection`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.centeredChart`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedAddCommGroupMetricTensorV`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedSpaceRealMetricTensorV`, `OAI.TamingCompatibility.GeometricHilbert.VolterraKernel.HeatBound`, `OAI.TamingCompatibility.GeometricHilbert.VolterraKernel.MeasurableKernel`, `OAI.TamingCompatibility.GeometricHilbert.VolterraKernel.convolution`, `OAI.TamingCompatibility.GeometricHilbert.VolterraKernel.spatial`, `OAI.TamingCompatibility.GeometricHilbert.complexComponentCLM`, `OAI.TamingCompatibility.HilbertSobolev.fiberOperator`, `OAI.TamingCompatibility.HilbertSobolev.movingFrozenPrincipal`, `OAI.TamingCompatibility.HilbertSobolev.schwartzToH`, `OAI.TamingCompatibility.HodgeFlatEnergy.pairing`, `OAI.TamingCompatibility.HodgeFlatEnergy.star`, `OAI.TamingCompatibility.HodgeFrame.combine`, `OAI.TamingCompatibility.HodgeFrame.coordinates`, `OAI.TamingCompatibility.HodgeFrame.directionCoordinates`, `OAI.TamingCompatibility.HodgeFrame.wedgeBy`, `OAI.TamingCompatibility.HodgeMatrixEnergy.Field`, `OAI.TamingCompatibility.HodgeMatrixEnergy.patchLower`, `OAI.TamingCompatibility.HodgeMatrixEnergy.patchPrincipal`, `OAI.TamingCompatibility.HodgeMatrixEnergy.value`, `OAI.TamingCompatibility.HodgeStarGeometry.swap`, `OAI.TamingCompatibility.JetOperator.basisDirectionOne`, `OAI.TamingCompatibility.JetOperator.basisDirectionTwo`, `OAI.TamingCompatibility.JetOperator.basisToCoordinate`, `OAI.TamingCompatibility.JetOperator.basisValue`, `OAI.TamingCompatibility.JetOperator.derivativeComponent`, `OAI.TamingCompatibility.JetOperator.derivativeJet`, `OAI.TamingCompatibility.JetOperator.directionOne`, `OAI.TamingCompatibility.JetOperator.directionTwo`, `OAI.TamingCompatibility.JetOperator.exteriorJet`, `OAI.TamingCompatibility.JetOperator.firstOrder`, `OAI.TamingCompatibility.JetOperator.linearTransport`, `OAI.TamingCompatibility.JetOperator.value`, `OAI.TamingCompatibility.LocalMatrixOperator.frameCovector`, `OAI.TamingCompatibility.LocalMatrixOperator.frameRecover`, `OAI.TamingCompatibility.LocalRellich.localInverse` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartLift`, `TamingCompatibility_Charts_ChartUnitaryData`, `TamingCompatibility_Charts_CoefficientCutoff`, `TamingCompatibility_Charts_Coordinates`, `TamingCompatibility_Charts_EuclideanCoordinateLine`, `TamingCompatibility_Charts_FiniteCharts`, `TamingCompatibility_Charts_InverseCutoff`, `TamingCompatibility_Charts_LocalInverse`, `TamingCompatibility_Charts_ManifoldComplexDifferential`, `TamingCompatibility_Charts_MetricCalculus`, `TamingCompatibility_Charts_ScalarChartLift`, `TamingCompatibility_Concentration_ActivationScales`, `TamingCompatibility_DifferentialForms_Bessel`, `TamingCompatibility_DifferentialForms_ChristoffelCLM`, `TamingCompatibility_DifferentialForms_ClosedLiftData`, `TamingCompatibility_DifferentialForms_ComplexEquiv`, `TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding`, `TamingCompatibility_DifferentialForms_Dpos2`, `TamingCompatibility_DifferentialForms_End`, `TamingCompatibility_DifferentialForms_FiberMap`, `TamingCompatibility_DifferentialForms_FormEquiv`, `TamingCompatibility_DifferentialForms_FramePairing`, `TamingCompatibility_DifferentialForms_GeometricFrameTest`, `TamingCompatibility_DifferentialForms_JAction`, `TamingCompatibility_DifferentialForms_JetBasis`, `TamingCompatibility_DifferentialForms_JetOperator`, `TamingCompatibility_DifferentialForms_MetricL2Core`, `TamingCompatibility_DifferentialForms_ParameterCoefficients`, `TamingCompatibility_DifferentialForms_PositiveFunctions`, `TamingCompatibility_DifferentialForms_RadialCoefficientProfiles`, `TamingCompatibility_DifferentialForms_RadialRHSIdentification`, `TamingCompatibility_DifferentialForms_RawJetEstimate`, `TamingCompatibility_DifferentialForms_UnitaryFrame`, `TamingCompatibility_DifferentialForms_WedgeTransform`, `TamingCompatibility_Elliptic_DerivativeIndex`, `TamingCompatibility_Elliptic_NormalSystem`, `TamingCompatibility_Elliptic_RealSobolevLift`, `TamingCompatibility_Elliptic_SchwartzSobolev`, `TamingCompatibility_Elliptic_SobolevBounded`, `TamingCompatibility_Functional_PlaneNormalization`, `TamingCompatibility_Hodge_HodgeDifferentialLocality`, `TamingCompatibility_Hodge_HodgeDirectionCoordinates`, `TamingCompatibility_Hodge_HodgeFrameDifferential`, `TamingCompatibility_Hodge_HodgeFrameH1`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeFrozenEnergy`, `TamingCompatibility_Hodge_HodgeGeometricCoefficients`, `TamingCompatibility_Hodge_HodgeGeometricGarding`, `TamingCompatibility_Hodge_HodgeKernelSeriesCore`, `TamingCompatibility_Hodge_HodgeMatrixEnergy`, `TamingCompatibility_Hodge_HodgeNormalInverse`, `TamingCompatibility_Hodge_HodgeParametrixPartition`, `TamingCompatibility_Hodge_HodgeStarGeometry`, `TamingCompatibility_Hodge_HodgeSymbol`, `TamingCompatibility_Hodge_HodgeVolterraKernel`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc000`, `OAIQ239Tc001`, `OAIQ239Tc002`, `OAIQ239Tc003` and `OAIQ239Tc004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc011`, `OAIQ239Tc012` and `OAIQ239Tc013`; the statements `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual` and `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual` and `OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc000
import Definitions.Def_OAIQ239Tc001
import Definitions.Def_OAIQ239Tc002
import Definitions.Def_OAIQ239Tc003
import Definitions.Def_OAIQ239Tc004

section
-- module Solutions.OAIQ239_TC.Compat
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JAction
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in
lemma IsClosed.add {α β : TwoForm X} (hα : IsClosed α) (hβ : IsClosed β)
    (hαs : IsSmooth α) (hβs : IsSmooth β) : IsClosed (α + β) := by
  intro f U hU hf y hy
  rw [pullback_add, extDerivWithin_add (hU.uniqueDiffWithinAt hy)]
  · rw [hα f U hU hf y hy, hβ f U hU hf y hy, add_zero]
  · exact ((hαs f U hU hf).differentiableOn (by norm_num)) y hy
  · exact ((hβs f U hU hf).differentiableOn (by norm_num)) y hy

omit [IsManifold Model ∞ X] in
lemma IsClosed.smul (c : ℝ) {α : TwoForm X} (hα : IsClosed α) :
    IsClosed (c • α) := by
  intro f U hU hf y hy
  rw [pullback_smul, extDerivWithin_smul c _ (hU.uniqueDiffWithinAt hy),
    hα f U hU hf y hy, smul_zero]

def smoothClosedInvariantForms (J : AlmostComplexStructure X) : Submodule ℝ (TwoForm X) where
  carrier := {α | IsSmooth α ∧ IsClosed α ∧ IsInvariant α J}
  zero_mem' := ⟨IsSmooth.zero, IsClosed.zero, fun _ _ _ => rfl⟩
  add_mem' := by
    intro α β hα hβ
    refine ⟨hα.1.add hβ.1, hα.2.1.add hβ.2.1 hα.1 hβ.1, ?_⟩
    intro x u v
    change eval α x (J.endomorphism x u) (J.endomorphism x v) +
      eval β x (J.endomorphism x u) (J.endomorphism x v) = _
    rw [hα.2.2, hβ.2.2]
    rfl
  smul_mem' := by
    intro c α hα
    refine ⟨hα.1.smul c, hα.2.1.smul c, ?_⟩
    intro x u v
    change c * eval α x (J.endomorphism x u) (J.endomorphism x v) = _
    rw [hα.2.2]
    rfl

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

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

def Closed (α : Form X k) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ∀ y ∈ U,
      extDerivWithin (pullback α f) U y = 0

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartLift
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open FormSmoothness Set
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] {k : ℕ}

def chartLift (p : X) (β : Space → Space [⋀^Fin k]→L[ℝ] ℝ) : Form X k := by
  classical
  exact fun x => if x ∈ (extChartAt Model p).source then
    (β (extChartAt Model p x)).compContinuousLinearMap (mfderiv Model Model (extChartAt Model p) x)
  else 0

omit [T2Space X] in
lemma pullback_chartLift (p : X) (β : Space → Space [⋀^Fin k]→L[ℝ] ℝ)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    pullback (chartLift p β) (extChartAt Model p).symm z = β z := by
  classical
  have hs := (extChartAt Model p).map_target hz
  simp only [pullback,chartLift,ite_eq_left hs,(extChartAt Model p).right_inv hz]
  have hi := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := Model) hz
  simp only [Model,modelWithCornersSelf_coe,Set.range_id,mfderivWithin_univ] at hi
  change (β z).compContinuousLinearMap
    (mfderiv Model Model (extChartAt Model p) ((extChartAt Model p).symm z) ∘L
      mfderiv Model Model (extChartAt Model p).symm z) = _
  erw [hi]
  rfl

end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryFrame
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
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

def J (v : V) : V := WithLp.toLp 2 ![-v 1, v 0, -v 3, v 2]

def wedge (u v : V) : W :=
  WithLp.toLp 2 ![u 0 * v 1 - u 1 * v 0, u 0 * v 2 - u 2 * v 0,
    u 0 * v 3 - u 3 * v 0, u 1 * v 2 - u 2 * v 1,
    u 1 * v 3 - u 3 * v 1, u 2 * v 3 - u 3 * v 2]

def line (v : V) : W := wedge v (J v)

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_FiniteCharts
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
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.ManifoldLocalization
open Set Function
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]

variable (A : FiniteCharts X)

def localizedFunction {k : ℕ} (p : A.centers) (α : ManifoldForms.Form X k) :
    Space → Space [⋀^Fin k]→L[ℝ] ℝ :=
  (extChartAt Model p.val).target.indicator (fun y =>
    A.partition p ((extChartAt Model p.val).symm y) •
      ManifoldForms.pullback α (extChartAt Model p.val).symm y)

end TamingCompatibility.ManifoldLocalization

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

lemma formEquiv_apply (g : Metric E) {k : ℕ} (α : MetricForms.Form E k)
    (v : Fin k → MetricModel.Model g) : formEquiv g k α v = α (fun i => (equiv g) (v i)) := rfl

end TamingCompatibility.MetricHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexEquiv
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
open MetricModel ContinuousAlternatingMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_sub_left (g : Metric E) {k : ℕ} (a b c : Form E k) :
    pairing g (a-b) c = pairing g a c - pairing g b c := by
  change FormMetric.pairing (MetricHodge.formEquiv g k (a-b)) (MetricHodge.formEquiv g k c) = _
  rw [_root_.map_sub]
  simp only [FormMetric.pairing,_root_.map_sub,inner_sub_left]
  rfl
end TamingCompatibility.MetricForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_CoefficientCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

def patchPrincipal (c : Fin 4 → Pair →L[ℝ] V) (a : Fin 4 → V → Pair →L[ℝ] V)
    {x₀ : V} (φ : ContDiffBump x₀) : Fin 4 → V → Pair →L[ℝ] V :=
  fun i x => φ x • (a i x-c i) + c i

end TamingCompatibility.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartUnitaryData
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
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge
open Set MetricForms AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X)
  (J : AlmostComplexStructure X)
  (α : TwoForm X)
  (ht : Tames α J)

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_zero_off {k : ℕ} (p : A.centers) (a : ManifoldForms.Form X k)
    {x : Space} (hx : x ∉ coordinateSupport A p) : localizedFunction A p a x = 0 := by
  unfold localizedFunction
  by_cases he : x ∈ (extChartAt Model p.val).target
  · rw [indicator_of_mem he]
    have hρ : (extChartAt Model p.val).symm x ∉ tsupport (A.partition p) := by
      intro h
      exact hx ⟨_,h,(extChartAt Model p.val).right_inv he⟩
    rw [image_eq_zero_of_notMem_tsupport hρ,zero_smul]
  · exact indicator_of_notMem he _

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_Coordinates
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open _root_.MeasureTheory Set Function
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

def formCoordinates : (Space [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] CoordinateFiber k :=
  FiberCoordinates.complexCoordinates (stdOrthonormalBasis ℝ Space).toBasis k

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
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
namespace TamingCompatibility.ScalarPair
open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv ContDiff

lemma inject_apply (j i : Fin 2) (s : ℝ) : inject j s i = if i=j then (s : ℂ) else 0 := by
  simp [inject]

def make {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s t : 𝓢(E,ℝ)) : 𝓢(E,F) :=
  SchwartzMap.postcompCLM (inject 0) s + SchwartzMap.postcompCLM (inject 1) t

lemma make_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : 𝓢(E,ℝ)) (x : E) (i : Fin 2) : make s t x i = if i=0 then (s x : ℂ) else (t x : ℂ) := by
  fin_cases i <;> simp [make,inject_apply]

lemma make_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : 𝓢(E,ℝ)) (x : E) : ‖make s t x‖^2 = (s x)^2 + (t x)^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_two,make_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma make_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : 𝓢(E,ℝ)) (v : E) : ∂_{v} (make s t) = make (∂_{v} s) (∂_{v} t) := by
  simp only [make,lineDerivOp_add,postcomp_derivative]
end TamingCompatibility.ScalarPair

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricL2Core
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_zero_left (g : Metric E) {k : ℕ} (a : Form E k) : pairing g 0 a = 0 := by
  change FormMetric.pairing (MetricHodge.formEquiv g k 0) (MetricHodge.formEquiv g k a) = 0
  rw [map_zero]
  simp [FormMetric.pairing]
end TamingCompatibility.MetricForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_NormalSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace SchwartzMap

def frameCovector (b : Fin 4 → V) (i : Fin 4) : V := WithLp.toLp 2 (fun j => b j i)

end TamingCompatibility.LocalMatrixOperator

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldComplexDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap ManifoldHodge Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def complexDifferential (J : AlmostComplexStructure X) (f : X → ℝ) : Form X 1 := fun x =>
  ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)
    (-(mfderiv Model 𝓘(ℝ,ℝ) f x).comp (J.endomorphism x))

end TamingCompatibility.ManifoldForms

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

omit [HasContDiffBump E] in
lemma firstOrderSource_smooth (V : E → E) (hV : ContDiff ℝ ∞ V)
    (u : E → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (firstOrderSource V u) := by
  exact (hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply hV

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalInverse
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
namespace TamingCompatibility.LocalRellich
open LocalRestriction HilbertSobolev FourierCutoff FourierIdentification
open _root_.MeasureTheory FourierTransform
open scoped ENNReal RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def localInverse (K : Set E) (hK : MeasurableSet K)
    (g : Lp ℂ ∞ (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℝ] Lp F 2 (localMeasure volume K) :=
  restrict volume K hK ∘L
    ((Lp.fourierTransformₗᵢ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) ∘L
      (multiplyLp g).restrictScalars ℝ

lemma localInverse_norm_le (K : Set E) (hK : MeasurableSet K)
    (g : Lp ℂ ∞ (volume : Measure E)) (u : Lp F 2 (volume : Measure E)) :
    ‖localInverse K hK g u‖ ≤ ‖g‖ * ‖u‖ := by
  change ‖restrict volume K hK (𝓕⁻ (g • u : Lp F 2 (volume : Measure E)))‖ ≤ _
  apply (restrict_norm_le volume K hK _).trans
  change ‖(Lp.fourierTransformₗᵢ E F).symm (g • u)‖ ≤ _
  rw [(Lp.fourierTransformₗᵢ E F).symm.norm_map]
  exact Lp.norm_smul_le g u

end TamingCompatibility.LocalRellich

end

noncomputable section

namespace TamingCompatibility.LocalRellich
open LocalRestriction HilbertSobolev FourierCutoff FourierIdentification RellichTail
open _root_.MeasureTheory FourierTransform Filter
open scoped ENNReal RealInnerProductSpace BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma localInverse_sub (K : Set E) (hK : MeasurableSet K)
    (g h : Lp ℂ ∞ (volume : Measure E)) :
    localInverse (F := F) K hK (g-h) = localInverse K hK g - localInverse K hK h := by
  apply ContinuousLinearMap.ext
  intro u
  change restrict volume K hK ((Lp.fourierTransformₗᵢ E F).symm ((g-h) • u)) =
    restrict volume K hK ((Lp.fourierTransformₗᵢ E F).symm (g • u)) -
    restrict volume K hK ((Lp.fourierTransformₗᵢ E F).symm (h • u))
  rw [sub_eq_add_neg, Lp.smul_add, Lp.neg_smul, map_add, map_neg, map_add, map_neg]
  exact (sub_eq_add_neg _ _).symm

lemma localInverse_sub_norm_le (K : Set E) (hK : MeasurableSet K)
    (g h : Lp ℂ ∞ (volume : Measure E)) :
    ‖localInverse (F := F) K hK g - localInverse K hK h‖ ≤ ‖g-h‖ := by
  rw [← localInverse_sub]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (localInverse_norm_le K hK (g-h))

end TamingCompatibility.LocalRellich

end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Bessel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

lemma bessel_decay (s : ℝ) (hs : 0 < s) :
    ∀ ε > 0, ∃ R ≥ 0, ∀ ξ : E, R < ‖ξ‖ → ‖bessel s hs.le ξ‖ ≤ ε := by
  intro ε hε
  have ht : Tendsto (fun r : ℝ => (1+r^2)^(-s/2)) atTop (𝓝 0) := by
    have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
    convert (tendsto_rpow_neg_atTop (div_pos hs (by norm_num : (0:ℝ)<2))).comp hp using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Function.comp_def, neg_div]
  obtain ⟨R,hR⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro ξ hξ
  change ‖(((1+‖ξ‖^2)^(-s/2) : ℝ) : ℂ)‖ ≤ ε
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (hR ‖ξ‖ ((le_max_left _ _).trans hξ.le)).le

end TamingCompatibility.RellichWeight

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FiberMap
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv
section FiberMaps

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def fiberOperator (s : ℝ) (L : F →L[ℂ] G) : H E F s →L[ℂ] H E G s :=
  L.compLpL 2 volume

end FiberMaps

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DerivativeIndex
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open _root_.MeasureTheory Set Function LineDeriv
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

abbrev ChartH1 := PiLp 2 (fun _ : DerivativeIndex => ChartL2 A k)

def jetComponent (j : DerivativeIndex) :
    𝓢(Space,CoordinateFiber k) →L[ℝ] 𝓢(Space,CoordinateFiber k) :=
  match j with
  | none => ContinuousLinearMap.id ℝ _
  | some i => lineDerivOpCLM ℝ 𝓢(Space,CoordinateFiber k) (stdOrthonormalBasis ℝ Space i)

def zeroth : ChartH1 A k →L[ℝ] ChartL2 A k := PiLp.proj 2 _ none

def jetDistribution (j : DerivativeIndex) (p : A.centers) :
    ChartH1 A k →L[ℝ] 𝓢'(Space,CoordinateFiber k) :=
  (Lp.toTemperedDistributionCLM (CoordinateFiber k) (volume : Measure Space) 2).restrictScalars ℝ ∘L
    PiLp.proj 2 _ p ∘L PiLp.proj 2 _ j

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FramePairing
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
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def scalarDifferential (f : X → ℝ) : Form X 1 := fun x =>
  ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1) (mfderiv Model 𝓘(ℝ,ℝ) f x)

omit [IsManifold Model ∞ X] in
lemma pullback_scalarDifferential {f : X → ℝ} {g : Space → X} {z : Space}
    (hf : MDifferentiableAt Model 𝓘(ℝ,ℝ) f (g z))
    (hg : MDifferentiableAt Model Model g z) :
    pullback (scalarDifferential f) g z =
      ofSubsingletonLIE (0 : Fin 1) (fderiv ℝ (f ∘ g) z) := by
  rw [← mfderiv_eq_fderiv,mfderiv_comp z hf hg]
  ext v
  rfl

omit [IsManifold Model ∞ X] in
lemma scalarDifferential_smooth {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    Smooth (scalarDifferential f) := by
  intro g U hU hg
  have hc : ContDiffOn ℝ ∞ (f ∘ g) U := (hf.comp_contMDiffOn hg).contDiffOn
  have hd := (contDiffOn_infty_iff_fderivWithin hU.uniqueDiffOn).mp hc |>.2
  apply ((ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)).contDiff.comp_contDiffOn hd).congr
  intro z hz
  rw [pullback_scalarDifferential (hf.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) ((hg z hz).contMDiffAt (hU.mem_nhds hz) |>.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    Function.comp_apply,fderivWithin_of_mem_nhds (hU.mem_nhds hz)]

lemma mfderiv_inverseChart_self (x : X) :
    mfderiv Model Model (extChartAt Model x).symm (extChartAt Model x x) =
      ContinuousLinearMap.id ℝ Space := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := Model)
    (x := x) (y := x) (mem_extChartAt_source x)
  rw [ModelWithCorners.Boundaryless.range_eq_univ,mfderivWithin_univ,mfderiv_extChartAt_self] at h
  ext u
  exact congrArg (fun L => L u) h

end TamingCompatibility.ManifoldForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_InverseCutoff
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
namespace TamingCompatibility.SchwartzCutoff
open Set Filter
open scoped ContDiff Topology SchwartzMap Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_reciprocal {U : Set E} (hU : IsOpen U) {w : E → ℝ}
    (hw : ContDiffOn ℝ ∞ w U) {z : E} (hz : z ∈ U) (hwz : w z ≠ 0) :
    ∃ τ : 𝓢(E,ℝ), HasCompactSupport (τ : E → ℝ) ∧ tsupport τ ⊆ U ∧
      ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, τ y * w y = 1 := by
  have he : ∀ᶠ y in 𝓝 z, w y ≠ 0 :=
    (hw.continuousOn.continuousAt (hU.mem_nhds hz)).eventually_ne hwz
  obtain ⟨O,hOsub,hO,hzO⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz) he)
  obtain ⟨K,hK,hzK,hKO⟩ := exists_compact_between (isCompact_singleton (x := z)) hO
    (singleton_subset_iff.mpr hzO)
  obtain ⟨b,hbone,hbzero,-⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,E) (n := (⊤ : ℕ∞)) (isClosed_singleton (x := z)) hzK
  have hbs : tsupport b ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hn
    exact hy (hbzero y hn)
  have hbc : HasCompactSupport (b : E → ℝ) := hK.of_isClosed_subset (isClosed_tsupport b) hbs
  have hwO : ContDiffOn ℝ ∞ (fun y => (w y)⁻¹) O :=
    (hw.mono (fun _ hy => (hOsub hy).1)).inv (fun y hy => (hOsub hy).2)
  let τ : 𝓢(E,ℝ) := schwartz hO hwO b.contMDiff.contDiff hbc (hbs.trans hKO)
  have hτs : tsupport τ ⊆ tsupport b := tsupport_smul_subset_left _ _
  have hbn : ∀ᶠ y in 𝓝 z, b y = 1 :=
    hbone.filter_mono (nhds_le_nhdsSet (mem_singleton z))
  obtain ⟨V,hVsub,hV,hzV⟩ := mem_nhds_iff.mp (inter_mem (hO.mem_nhds hzO) hbn)
  refine ⟨τ,hbc.of_isClosed_subset (isClosed_tsupport τ) hτs,
    hτs.trans (hbs.trans (hKO.trans (fun _ hy => (hOsub hy).1))),V,hV,hzV,
    fun _ hy => (hOsub (hVsub hy).1).1,fun y hy => ?_⟩
  change (b y • (w y)⁻¹) * w y = 1
  rw [(hVsub hy).2,one_smul,inv_mul_cancel₀ (hOsub (hVsub hy).1).2]
end TamingCompatibility.SchwartzCutoff

end
end

section
noncomputable section
namespace TamingCompatibility.SchwartzCutoff
open Set
open scoped ContDiff Topology SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_one_near {U : Set E} (hU : IsOpen U) {p : E} (hp : p ∈ U) :
    ∃ φ : 𝓢(E,ℝ), HasCompactSupport (φ : E → ℝ) ∧ tsupport φ ⊆ U ∧
      ∃ W : Set E, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ x ∈ W, φ x = 1 := by
  obtain ⟨φ,hφ,hφU,W,hW,hpW,hWU,hφone⟩ := exists_reciprocal
    hU (w := fun _ => (1 : ℝ)) contDiffOn_const hp one_ne_zero
  exact ⟨φ,hφ,hφU,W,hW,hpW,hWU,fun x hx => by simpa only [mul_one] using hφone x hx⟩

end TamingCompatibility.SchwartzCutoff

namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory Set
open scoped SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma memSobolevLoc_of_global (n : ℕ) {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) (U : Set E) :
    MemSobolevLoc U n u := fun g _ _ => memSobolev_nat_product n g hu

lemma memSobolevLoc_one_of_global {u : 𝓢'(E,F)} (hu : MemSobolev 1 2 u) (U : Set E) :
    MemSobolevLoc U 1 u := by
  have hu' : MemSobolev (1 : ℕ) 2 u := by simpa only [Nat.cast_one] using hu
  simpa only [Nat.cast_one] using memSobolevLoc_of_global 1 hu' U

lemma schwartz_memSobolevLoc (g : 𝓢(E,F)) (n : ℕ) (U : Set E) :
    MemSobolevLoc U n (g : 𝓢'(E,F)) := memSobolevLoc_of_global n g.memSobolev U

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SchwartzSobolev
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def schwartzToH (s : ℝ) : 𝓢(E,F) →L[ℂ] H E F s :=
  (SchwartzMap.toLpCLM ℂ F 2 (volume : Measure E)).comp
    (SchwartzMap.fourierMultiplierCLM F (fun x : E => ((1+‖x‖^2)^(s/2) : ℝ)))

end TamingCompatibility.HilbertSobolev

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
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma boundedDistribution_schwartz (f : 𝓢(E,F)) :
    boundedDistribution f.toBoundedContinuousFunction = (f : 𝓢'(E,F)) := by
  ext φ
  rw [boundedDistribution_apply,SchwartzMap.toTemperedDistributionCLM_apply_apply volume f φ]
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ParameterCoefficients
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def movingFrozenPrincipal (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p₀ : E) (t : ℝ × E) :
    basisIndex E → basisIndex E → 𝓢(E,ℂ) :=
  fun i j => movingFrozenCoefficient χ hχ (a i j) (ha i j) p₀ t

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PositiveFunctions
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
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility

open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

instance instCompactSpaceMetricUnitOfT2Space [CompactSpace X] [T2Space X]
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    CompactSpace (MetricUnit g) :=
  isCompact_iff_compactSpace.mp (isCompact_metricUnit g)

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftData
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
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace

def frameRecover (g : Metric V) (b : Fin 4 → V) : V →L[ℝ] MetricForms.Form V 1 :=
  ∑ i, (EuclideanSpace.proj i).smulRight (ofSubsingletonLIE (0 : Fin 1) (g.bilinear (b i)))

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JetOperator
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
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap
open scoped SchwartzMap ContDiff LineDeriv
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def value (u : 𝓢(V,F)) (x : V) : Jet F :=
  (u x, (fun i => (∂_{e i} u) x), (fun i j => (∂_{e j} (∂_{e i} u)) x))

def firstOrder (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (u : 𝓢(V,F)) (x : V) : G := ∑ i, a i x ((∂_{e i} u) x) + b x (u x)

def derivativeComponent (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (x : V) (j : Fin 4) : Jet F →L[ℝ] G :=
  (∑ i, ((a i x).comp (projTwo i j) + (fderiv ℝ (a i) x (e j)).comp (projOne i))) +
    (b x).comp (projOne j) + (fderiv ℝ b x (e j)).comp projZero

def derivativeJet (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (x : V) : Jet F →L[ℝ] (V →L[ℝ] G) :=
  ∑ j, (ContinuousLinearMap.smulRightL ℝ V G (EuclideanSpace.proj j)).comp
    (derivativeComponent a b x j)

def exteriorJet (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1) (x : V) :
    Jet F →L[ℝ] MetricForms.Form V 2 :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 1) ℝ V ℝ).comp (derivativeJet a b x)

end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawJetEstimate
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
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap Set LineDeriv
open scoped SchwartzMap ContDiff LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionOne (v : V) : Jet F →L[ℝ] F := ∑ i : Fin 4, (v i) • projOne i

def directionTwo (v w : V) : Jet F →L[ℝ] F :=
  ∑ i : Fin 4, ∑ j : Fin 4, (v i * w j) • projTwo i j

def linearTransport (L : V ≃L[ℝ] V) : Jet F →L[ℝ] Jet F :=
  projZero.prod ((ContinuousLinearMap.pi (fun i : Fin 4 => directionOne (L (e i)))).prod
    (ContinuousLinearMap.pi (fun i : Fin 4 =>
      ContinuousLinearMap.pi (fun j : Fin 4 => directionTwo (L (e i)) (L (e j))))))

end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JetBasis
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
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap Set LineDeriv
open scoped SchwartzMap ContDiff LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]
def basisValue (b : ι → V) (u : 𝓢(V,F)) (x : V) : BasisJet ι F :=
  (u x,(fun i => (∂_{b i} u) x),(fun i j => (∂_{b j} (∂_{b i} u)) x))
def basisDirectionOne (b : Module.Basis ι ℝ V) (v : V) : BasisJet ι F →L[ℝ] F :=
  ∑ i : ι, b.repr v i • basisProjOne i
def basisDirectionTwo (b : Module.Basis ι ℝ V) (v w : V) : BasisJet ι F →L[ℝ] F :=
  ∑ i : ι, ∑ j : ι, (b.repr v i * b.repr w j) • basisProjTwo i j
def basisToCoordinate (b : Module.Basis ι ℝ V) : BasisJet ι F →L[ℝ] Jet F :=
  basisProjZero.prod ((ContinuousLinearMap.pi (fun i : Fin 4 => basisDirectionOne b (e i))).prod
    (ContinuousLinearMap.pi (fun i : Fin 4 =>
      ContinuousLinearMap.pi (fun j : Fin 4 => basisDirectionTwo b (e i) (e j)))))
end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialRHSIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv

def complexComponentCLM (j : Fin 2) : ℝ →L[ℝ] C 2 :=
  (embed 2).comp (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j 1))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ScalarChartLift
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X]

def scalarChartLift (p : X) (f : Space → ℝ) : X → ℝ := by
  classical
  exact fun x => if x ∈ (extChartAt Model p).source then f (extChartAt Model p x) else 0

def scalarLiftSupport (p : X) (f : Space → ℝ) : Set X :=
  (extChartAt Model p).symm '' tsupport f

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarLiftSupport_subset (p : X) {f : Space → ℝ}
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    scalarLiftSupport p f ⊆ (extChartAt Model p).source := by
  rintro _ ⟨z,hz,rfl⟩
  exact (extChartAt Model p).map_target (hf hz)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarLiftSupport_compact (p : X) {f : Space → ℝ}
    (hc : HasCompactSupport f) (hf : tsupport f ⊆ (extChartAt Model p).target) :
    IsCompact (scalarLiftSupport p f) :=
  hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hf)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarChartLift_zero_off (p : X) (f : Space → ℝ)
    {x : X} (hx : x ∉ scalarLiftSupport p f) : scalarChartLift p f x = 0 := by
  unfold scalarChartLift
  split_ifs with hs
  · exact image_eq_zero_of_notMem_tsupport (fun hz => hx ⟨_,hz,(extChartAt Model p).left_inv hs⟩)
  · rfl

lemma scalarChartLift_smooth (p : X) {f : Space → ℝ}
    (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ (scalarChartLift p f) := by
  intro x
  by_cases hk : x ∈ scalarLiftSupport p f
  · have hsrc := scalarLiftSupport_subset p hf hk
    have he : scalarChartLift p f =ᶠ[𝓝 x] fun y => f (extChartAt Model p y) := by
      filter_upwards [(isOpen_extChartAt_source p).mem_nhds hsrc] with y hy
      simp only [scalarChartLift,ite_eq_left hy]
    have hchart := contMDiffAt_extChartAt' (I := Model) (n := ∞)
      (by simpa only [extChartAt_source] using hsrc)
    exact ((contMDiff_iff_contDiff.mpr hs).contMDiffAt.comp x hchart).congr_of_eventuallyEq he
  · have he : scalarChartLift p f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(scalarLiftSupport_compact p hc hf).isClosed.isOpen_compl.mem_nhds hk] with y hy
      exact scalarChartLift_zero_off p f hy
    exact contMDiffAt_const.congr_of_eventuallyEq he

end TamingCompatibility.ManifoldForms

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X]

def vectorChartLift (p : X) (f : Space → Space) : X → Space := by
  classical
  exact fun x => if x ∈ (extChartAt Model p).source then f (extChartAt Model p x) else 0

def vectorLiftSupport (p : X) (f : Space → Space) : Set X :=
  (extChartAt Model p).symm '' tsupport f

end TamingCompatibility.ManifoldForms

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMatrixEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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
abbrev Field := Fin 6 → S

def value (f : Field) (x : V) : W := WithLp.toLp 2 (fun j => f j x)

lemma value_norm (f : Field) (x : V) : ‖value f x‖^2 = ∑ j, (f j x)^2 :=
  EuclideanSpace.real_norm_sq_eq _
lemma value_continuous (f : Field) : Continuous (value f) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 6 => ℝ)).comp (continuous_pi (fun j => (f j).continuous))

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
lemma lowerError_bound (b : V → W →L[ℝ] Q) (f : Field) (x : V) {C : ℝ}
    (hb : ‖b x‖ ≤ C) : ‖b x (value f x)‖^2 ≤ C^2*‖value f x‖^2 := by
  have h := (b x).le_opNorm (value f x)
  have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg (value f x))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h.trans hm) 2

end TamingCompatibility.HodgeMatrixEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSymbol
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

def pairing (f g : S) : ℝ := ∫ x, f x*g x
lemma pairing_neg_left (a b : S) : pairing (-a) b = -pairing a b := by simp [pairing, integral_neg]
lemma pairing_neg_right (a b : S) : pairing a (-b) = -pairing a b := by simp [pairing, integral_neg]
lemma pairing_comm (a b : S) : pairing a b = pairing b a := by simp only [pairing,mul_comm]
def star (a : Fin 6 → S) : Fin 6 → S := ![a 5,-a 4,a 3,a 2,-a 1,a 0]

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
open scoped ContDiff RealInnerProductSpace
namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open FormMetric (pairLeft pairRight)
open HodgeNormalSymbol (W)
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

def coordinates (b : Fin 4 → E) : MetricForms.Form E 2 →L[ℝ] W :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => ContinuousAlternatingMap.apply ℝ E ℝ ![b (pairLeft i),b (pairRight i)])
lemma coordinates_apply (b : Fin 4 → E) (a : MetricForms.Form E 2) (i : Fin 6) :
    coordinates b a i = a ![b (pairLeft i),b (pairRight i)] := rfl

variable [FiniteDimensional ℝ E]

lemma coordinates_injective (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) :
    Function.Injective (coordinates b) := by
  intro a c h
  have he (i : Fin 6) := congrArg (fun v : W => v i) h
  simp only [coordinates_apply] at he
  apply AntiInvariantFrame.frame_ext g hdim b hb
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact he 0 | exact he 1 | exact he 2 | exact he 3 | exact he 4 | exact he 5
    | solve | simp only [AntiInvariantFrame.eval_self]
    | (rw [two_swap a,two_swap c]; congr 1
       first | exact he 0 | exact he 1 | exact he 2 | exact he 3 | exact he 4 | exact he 5)

lemma coordinates_pairing (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a c : MetricForms.Form E 2) :
    ⟪coordinates b a,coordinates b c⟫ = pairing g a c := by
  rw [pairing_two_eq_sum g hdim b hb]
  simp only [PiLp.inner_apply,coordinates_apply,RCLike.inner_apply,conj_trivial,mul_comm]

end TamingCompatibility.HodgeFrame

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeDirectionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def directionCoordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E) :
    UnitaryFrame.V :=
  (basisOfFrame g hdim b hb).repr (ofOriginal g u)

end TamingCompatibility.HodgeFrame

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_PlaneNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def normalPart (a b : V) : V := b - ⟪first a,b⟫ • first a

def second (a b : V) : V := ‖normalPart a b‖⁻¹ • normalPart a b

def area (a b : V) : ℝ := ‖a‖*‖normalPart a b‖

lemma norm_first {a : V} (ha : a ≠ 0) : ‖first a‖ = 1 := by
  simp only [first,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)

lemma normalPart_orthogonal {a : V} (ha : a ≠ 0) (b : V) : ⟪first a,normalPart a b⟫ = 0 := by
  simp only [normalPart,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_first ha,one_pow,mul_one,sub_self]

lemma norm_second {a b : V} (hab : normalPart a b ≠ 0) : ‖second a b‖ = 1 :=
  norm_first hab

lemma first_second_orthogonal {a : V} (ha : a ≠ 0) (b : V) : ⟪first a,second a b⟫ = 0 := by
  rw [second,real_inner_smul_right,normalPart_orthogonal ha,mul_zero]

lemma normalPart_complex_ne_zero (K : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    {a : V} (ha : a ≠ 0) : normalPart a (K a) ≠ 0 := by
  intro h
  have hh : K a = (⟪first a,K a⟫*‖a‖⁻¹) • a := by
    rw [normalPart,sub_eq_zero] at h
    calc
      K a = ⟪first a,K a⟫ • first a := h
      _ = _ := by rw [first,smul_smul]
  let c := ⟪first a,K a⟫*‖a‖⁻¹
  have hc : K a = c • a := hh
  have he : (-1:ℝ) • a = c^2 • a := by
    rw [neg_one_smul,← hK a,hc,map_smul,hc,smul_smul,pow_two]
  have hec : (-1:ℝ) = c^2 := (smul_left_injective ℝ ha) he
  nlinarith [sq_nonneg c]

lemma area_pos {a b : V} (ha : a ≠ 0) (hab : normalPart a b ≠ 0) : 0 < area a b :=
  mul_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hab)

lemma first_continuousAt {a : V} (ha : a ≠ 0) : ContinuousAt first a :=
  (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr ha)).smul continuous_id.continuousAt

lemma normalPart_continuousAt {a b : V} (ha : a ≠ 0) :
    ContinuousAt (fun p : V × V => normalPart p.1 p.2) (a,b) := by
  have hf : ContinuousAt (fun p : V × V => first p.1) (a,b) :=
    by
      exact ContinuousAt.comp (x := (a,b)) (g := first) (f := Prod.fst)
        (first_continuousAt ha) continuous_fst.continuousAt
  exact continuous_snd.continuousAt.sub ((hf.inner continuous_snd.continuousAt).smul hf)

lemma area_continuousAt {a b : V} (ha : a ≠ 0) :
    ContinuousAt (fun p : V × V => area p.1 p.2) (a,b) :=
  continuous_fst.continuousAt.norm.mul (normalPart_continuousAt ha).norm
end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_WedgeTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.UnitaryFrame
open FormMetric

def wedgeTransform (b : Fin 4 → V) : W →L[ℝ] W :=
  ∑ i : Fin 6, (PiLp.proj 2 (fun _ : Fin 6 => ℝ) i).smulRight
    (wedge (b (pairLeft i)) (b (pairRight i)))

end TamingCompatibility.UnitaryFrame

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_RealSobolevLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev Set
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma schwartzToH_coe (s : ℝ) :
    ⇑(schwartzToH (E := E) (F := F) s) =
      (fun f : 𝓢(E,F) => f.toLp 2 (volume : Measure E)) ∘
        (SchwartzMap.fourierMultiplierCLM F (fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ))) := rfl

lemma schwartzToH_dense (s : ℝ) : DenseRange (schwartzToH (E := E) (F := F) s) := by
  rw [schwartzToH_coe]
  exact schwartzLp_dense.comp (schwartz_bessel_surjective s).denseRange SchwartzMap.continuous_toLp

end TamingCompatibility.HilbertSobolev

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
namespace TamingCompatibility.HodgeFrame
open ContinuousAlternatingMap ExteriorForms MetricForms MetricModel
open EuclideanEnergy
open HodgeNormalSymbol (W)

def wedgeBy (ξ : V →L[ℝ] ℝ) : MetricForms.Form V 2 →L[ℝ] MetricForms.Form V 3 :=
  wedgeOneBilinear (ofSubsingletonLIE (0 : Fin 1) ξ)
lemma wedgeBy_apply (ξ : V →L[ℝ] ℝ) (a : MetricForms.Form V 2) :
    wedgeBy ξ a = wedgeOne ξ a := rfl

def combine (a : Fin 6 → MetricForms.Form V 2) : W →L[ℝ] MetricForms.Form V 2 :=
  ∑ j, (EuclideanSpace.proj j).smulRight (a j)
lemma combine_apply (a : Fin 6 → MetricForms.Form V 2) (u : W) :
    combine a u = ∑ j, u j • a j := by
  simp only [combine,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

lemma extDeriv_sum {f : Fin 6 → V → MetricForms.Form V 2} {x : V}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    extDeriv (fun y => ∑ j, f j y) x = ∑ j, extDeriv (f j) x := by
  simp only [extDeriv,fderiv_fun_sum (fun j _ => hf j)]
  change (alternatizeUncurryFinCLM ℝ V ℝ) (∑ j, fderiv ℝ (f j) x) = _
  rw [_root_.map_sum]
  rfl

end TamingCompatibility.HodgeFrame

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
open scoped ContDiff RealInnerProductSpace
namespace TamingCompatibility.HodgeGeometricCoefficients
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame
open HodgeNormalSymbol (W Q)

lemma derivative_smooth {a : V → MetricForms.Form V 2} {U : Set V}
    (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (extDeriv a) U := by
  change ContDiffOn ℝ ∞ (fun x => (alternatizeUncurryFinCLM ℝ V ℝ) (fderiv ℝ a x)) U
  exact (alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn
    (ha.fderiv_of_isOpen (m := ∞) hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end TamingCompatibility.HodgeGeometricCoefficients

end
end

section
noncomputable section
open _root_.MeasureTheory Filter Topology
open scoped SchwartzMap
namespace TamingCompatibility.HodgeMatrixEnergy
open EuclideanEnergy
open MatrixEnergy (exists_small_error)
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
def patchPrincipal (c : Fin 4 → W →L[ℝ] Q) (a : Fin 4 → V → W →L[ℝ] Q)
    {x₀ : V} (φ : ContDiffBump x₀) : Fin 4 → V → W →L[ℝ] Q :=
  fun i x => φ x • (a i x-c i) + c i

def patchLower (b : V → W →L[ℝ] Q) {x₀ : V} (φ : ContDiffBump x₀) : V → W →L[ℝ] Q :=
  fun x => φ x • b x

end TamingCompatibility.HodgeMatrixEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricGarding
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
open scoped ContDiff SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.HodgeGeometricCoefficients
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame
open HodgeNormalSymbol (W Q)
open HodgeMatrixEnergy (Field)

lemma extDeriv_sum_zero {f : Field} {x : V} (hf : ∀ j, x ∉ tsupport (f j))
    (a : Fin 6 → V → MetricForms.Form V 2) : extDeriv (fun y => ∑ j, f j y • a j y) x = 0 := by
  have he : (fun y => ∑ j, f j y • a j y) =ᶠ[𝓝 x] (fun _ => 0) := by
    have h := Filter.eventually_all.mpr (fun j => notMem_tsupport_iff_eventuallyEq.mp (hf j))
    filter_upwards [h] with y hy
    simp only [hy,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  unfold extDeriv
  rw [he.fderiv_eq,fderiv_fun_const]
  exact map_zero _

end TamingCompatibility.HodgeGeometricCoefficients

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge HodgeFrame EuclideanEnergy
open HodgeNormalSymbol (W Q)
lemma vector_fderiv {q : V → W} {z : V} (hd : DifferentiableAt ℝ q z) (i : Fin 4) :
    WithLp.toLp 2 (fun j => fderiv ℝ (fun y => q y j) z (e i)) = fderiv ℝ q z (e i) := by
  ext j
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp z hd.hasFDerivAt
  change HasFDerivAt (fun y => q y j) _ z at hh
  change fderiv ℝ (fun y => q y j) z (e i) = fderiv ℝ q z (e i) j
  rw [hh.fderiv]
  rfl
end TamingCompatibility.HodgeNormalOperator

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff
namespace TamingCompatibility.HodgeMatrixEnergy
open EuclideanEnergy
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma value_smooth (f : Field) : ContDiff ℝ ∞ (value f) :=
  (contDiff_piLp 2).mpr (fun j => (f j).smooth (⊤ : ℕ∞))
end TamingCompatibility.HodgeMatrixEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_MetricCalculus
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity
open scoped ContDiff RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupMetricTensorV : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorV : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace

lemma detGram_contDiff : ContDiff ℝ ∞ (fun M : MetricTensor (V := V) =>
    (MetricDensity.gram (stdOrthonormalBasis ℝ V).toBasis M).det) := by
  rw [← contDiffOn_univ]
  exact MetricDensity.contDiffOn_det (fun i j =>
    ((contDiffOn_id.clm_apply contDiffOn_const).clm_apply contDiffOn_const))

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ChristoffelCLM
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff Topology
open Set Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelDualNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelDualNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelMetricTensorNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelMetricDerivativeNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelMetricDerivativeNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelEndomorphismNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelEndomorphismNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelBilinearNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelBilinearNormedSpace
lemma jointJet_contDiff (G : V → MetricDerivative (V := V)) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (jointJet G) := by
  exact contDiff_snd.sub (((christoffel_contDiff.comp (hG.comp contDiff_fst)).clm_apply
    contDiff_snd |>.clm_apply contDiff_snd).const_smul (1/2 : ℝ))

lemma jointJet_hasFDerivAt (G : V → MetricDerivative (V := V))
    (hG : ContDiff ℝ ∞ G) (p : V) :
    HasFDerivAt (jointJet G) (ContinuousLinearMap.snd ℝ V V) (p,0) := by
  have hC := (christoffel_contDiff.comp (hG.comp contDiff_fst)).differentiable
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (p, (0 : V))
  have hz := hasFDerivAt_snd (𝕜 := ℝ) (p := (p, (0 : V)))
  have h := hz.sub ((hC.hasFDerivAt.clm_apply hz |>.clm_apply hz).const_smul (1/2 : ℝ))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro u
  simp

lemma centeredMap_contDiff (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (centeredMap B G) := by
  exact contDiff_fst.prodMk (contDiff_fst.add
    ((hB.comp contDiff_fst).clm_apply (jointJet_contDiff G hG)))

lemma centeredMap_hasFDerivAt (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G) (p : V) :
    HasFDerivAt (centeredMap B G)
      ((ContinuousLinearMap.fst ℝ V V).prod
        (ContinuousLinearMap.fst ℝ V V + (B p).comp (ContinuousLinearMap.snd ℝ V V))) (p,0) := by
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := (p, (0 : V)))).prodMk
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := (p, (0 : V)))).add
      (((hB.comp contDiff_fst).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (p, (0 : V))).hasFDerivAt.clm_apply
        (jointJet_hasFDerivAt G hG p)))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext u <;> simp [jointJet]

lemma centeredMap_hasStrictFDerivAt (B : V → V →L[ℝ] V)
    (G : V → MetricDerivative (V := V)) (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    HasStrictFDerivAt (centeredMap B G) (centeredDerivative Bp).toContinuousLinearMap (p,0) := by
  have hs := ((centeredMap_contDiff B G hB hG).contDiffAt (x := (p, (0 : V)))).hasStrictFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [(centeredMap_hasFDerivAt B G hB hG p).fderiv] at hs
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl
  ext u <;> simp [centeredDerivative, ContinuousLinearEquiv.skewProd, hBp, add_comm]

def centeredChart (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    OpenPartialHomeomorph (V × V) (V × V) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (centeredMap B G)
    (centeredMap_hasStrictFDerivAt B G hB hG p Bp hBp)

lemma centeredChart_mem_source (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    (p,0) ∈ (centeredChart B G hB hG p Bp hBp).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (centeredMap_hasStrictFDerivAt B G hB hG p Bp hBp)

lemma centeredChart_mem_target (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    (p,p) ∈ (centeredChart B G hB hG p Bp hBp).target := by
  have h := (centeredChart B G hB hG p Bp hBp).map_source
    (centeredChart_mem_source B G hB hG p Bp hBp)
  simpa [centeredChart, HasStrictFDerivAt.toOpenPartialHomeomorph_coe,
    centeredMap, jointJet] using h

lemma centeredChart_symm_center (B : V → V →L[ℝ] V)
    (G : V → MetricDerivative (V := V)) (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    (centeredChart B G hB hG p Bp hBp).symm (p,p) = (p,0) := by
  have hh := (centeredChart B G hB hG p Bp hBp).left_inv
    (centeredChart_mem_source B G hB hG p Bp hBp)
  simpa only [centeredChart,HasStrictFDerivAt.toOpenPartialHomeomorph_coe,
    centeredMap,jointJet,coordinateJet_zero,map_zero,add_zero] using hh

end TamingCompatibility.GeometricHilbert.NormalJets


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets

section FiniteDimensionalDirections
open Set Metric Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] in
lemma dpos_eq_at (F : P × V → W) (p : P) (z : V) (hF : DifferentiableAt ℝ F (p,z)) :
    dpos F (p,z) = fderiv ℝ (fun u => F (p,u)) z := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (c := p) z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)
  exact (hF.hasFDerivAt.comp z hd).fderiv.symm

omit [FiniteDimensional ℝ V] in
lemma dpos_contDiffAt (F : P × V → W) (x : P × V) (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (dpos F) x :=
  (hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiffAt_const

lemma local_linear_bound (F : P × V → W) (K : Set P) (hK : IsCompact K)
    (O : Set (P × V)) (hO : IsOpen O) (hKO : K ×ˢ {(0 : V)} ⊆ O)
    (hF : ∀ x ∈ O, ContDiffAt ℝ ∞ F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ K ×ˢ closedBall (0 : V) r ⊆ O ∧
      ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r → ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖ := by
  obtain ⟨r,hr,hsub⟩ := compact_tube K hK O hO hKO
  have hpc : ContinuousOn (dpos F) (K ×ˢ closedBall (0 : V) r) :=
    fun x hx => ((dpos_contDiffAt F x (hF x (hsub hx))).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn hpc
  refine ⟨max C 0,le_max_right _ _,r,hr,hsub,fun p hp z hz => ?_⟩
  have hd (u : V) (hu : u ∈ closedBall (0 : V) r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) (hsub ⟨hp,hu⟩)).differentiableAt (by simp)
  have hb (u : V) (hu : u ∈ closedBall (0 : V) r) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ max C 0 := by
    rw [← dpos_eq_at F p u (hd u hu)]
    exact (hC (p,u) ⟨hp,hu⟩).trans (le_max_left _ _)
  simpa using (convex_closedBall (0 : V) r).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u hu).comp u ((differentiableAt_const p).prodMk differentiableAt_id)) hb
    (show (0 : V) ∈ closedBall 0 r by simpa using hr.le)
    (show z ∈ closedBall 0 r by simpa using hz)

end FiniteDimensionalDirections
open Filter
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.UniformJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open Set Filter
open scoped ContDiff Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma inverseRegularDomain_open (C : OpenPartialHomeomorph V V)
    (hC : ContDiff ℝ ∞ (C : V → V)) : IsOpen (inverseRegularDomain C) := by
  have ho : IsOpen {x : V | (fderiv ℝ (C : V → V) x).IsInvertible} :=
    (ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := V) (F := V)).preimage
      (hC.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  exact C.symm.continuousOn.isOpen_inter_preimage C.open_target ho

lemma inverseRegularDomain_smooth (C : OpenPartialHomeomorph V V)
    (hC : ContDiff ℝ ∞ (C : V → V)) :
    ContDiffOn ℝ ∞ (C.symm : V → V) (inverseRegularDomain C) := by
  intro y hy
  obtain ⟨L,hL⟩ := hy.2
  apply ContDiffAt.contDiffWithinAt
  apply C.contDiffAt_symm (f₀' := L) hy.1
  · rw [hL]
    exact (hC.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (C.symm y)).hasFDerivAt
  · exact hC.contDiffAt

end TamingCompatibility.GeometricHilbert.NormalJets

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_End
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open scoped ContDiff RealInnerProductSpace
open FlatHeat (V heat)
open Filter Set
open scoped Topology
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def modelSection (t : ℝ) (u : W) (z : V) : W := heat t z • u

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

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
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeStarGeometry
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

 def swap (u : Q) : Q := WithLp.toLp 2 ![u 4,u 5,u 6,u 7,u 0,u 1,u 2,u 3]

end TamingCompatibility.HodgeStarGeometry

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set VolterraBounds
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B]
variable (μ : Measure X) [SFinite μ]

def MeasurableKernel (K : Kernel (X := X) (B := B)) : Prop :=
  StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2)

def spatial (K L : Kernel (X := X) (B := B)) (t s : ℝ) (x y : X) : B :=
  ∫ z, K (t-s) x z * L s z y ∂μ

def convolution (K L : Kernel (X := X) (B := B)) (t : ℝ) (x y : X) : B :=
  ∫ s in Ioo 0 t, spatial μ K L t s x y

omit [NormedAlgebra ℝ B] in
lemma kernel_section (K : Kernel (X := X) (B := B)) (hK : MeasurableKernel K)
    (t : ℝ) : StronglyMeasurable (fun p : X × X => K t p.1 p.2) :=
  hK.comp_measurable (measurable_const.prodMk measurable_id)

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

structure HeatBound (N : ℕ) (T A : ℝ) (K : Kernel (X := X) (B := B)) : Prop where
  measurable : MeasurableKernel K
  nonneg : 0 ≤ A
  sup : ∀ t ∈ Ioc 0 T, ∀ x y, weight N t x y*‖K t x y‖ ≤ A/t^2
  row_int : ∀ t ∈ Ioc 0 T, ∀ x, Integrable (fun y => weight N t x y*‖K t x y‖) μ
  row : ∀ t ∈ Ioc 0 T, ∀ x, (∫ y, weight N t x y*‖K t x y‖ ∂μ) ≤ A
  col_int : ∀ t ∈ Ioc 0 T, ∀ y, Integrable (fun x => weight N t x y*‖K t x y‖) μ
  col : ∀ t ∈ Ioc 0 T, ∀ y, (∫ x, weight N t x y*‖K t x y‖ ∂μ) ≤ A

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPartition
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldLocalization
open Set ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X)
attribute [local instance] Classical.propDecidable

def coordinatePartition (p : A.centers) : Space → ℝ :=
  (extChartAt Model p.val).target.indicator (fun q => A.partition p ((extChartAt Model p.val).symm q))

omit [T2Space X] in
lemma coordinatePartition_smooth_compact (p : A.centers) :
    ContDiff ℝ ∞ (coordinatePartition A p) ∧ HasCompactSupport (coordinatePartition A p) := by
  apply smooth_indicator_of_compact (isOpen_extChartAt_target p.val)
    (coordinateSupport_compact A p) (coordinateSupport_subset A p)
  · exact (A.partition p).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p.val) |>.contDiffOn
  · intro q hq hK
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    exact hK ⟨(extChartAt Model p.val).symm q,hh,(extChartAt Model p.val).right_inv hq⟩

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_support (p : A.centers) :
    Function.support (coordinatePartition A p) ⊆ coordinateSupport A p := by
  intro q hq
  have ht : q ∈ (extChartAt Model p.val).target := by
    by_contra h
    exact hq (Set.indicator_of_notMem h _)
  refine ⟨(extChartAt Model p.val).symm q,subset_tsupport _ ?_,(extChartAt Model p.val).right_inv ht⟩
  change _ ≠ 0
  change coordinatePartition A p q ≠ 0 at hq
  simpa only [coordinatePartition,Set.indicator_of_mem ht] using hq

omit [T2Space X] in
lemma coordinatePartition_tsupport (p : A.centers) :
    tsupport (coordinatePartition A p) ⊆ coordinateSupport A p :=
  closure_minimal (coordinatePartition_support A p) (coordinateSupport_compact A p).isClosed

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_apply (p : A.centers) {x : X}
    (hx : x ∈ (extChartAt Model p.val).source) :
    coordinatePartition A p (extChartAt Model p.val x) = A.partition p x := by
  simp only [coordinatePartition,Set.indicator_of_mem ((extChartAt Model p.val).map_source hx),
    (extChartAt Model p.val).left_inv hx]

end TamingCompatibility.ManifoldLocalization

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelSeriesCore
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelSeries
open _root_.MeasureTheory Set Filter VolterraKernel VolterraBounds
open scoped Topology
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
variable (μ : Measure X) [SFinite μ]

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [MeasurableSpace X] [NormedAlgebra ℝ B] [CompleteSpace B] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
@[simp] lemma clip_of_mem (T : ℝ) (K : Kernel (X := X) (B := B)) {t : ℝ}
    (ht : t ∈ Ioc 0 T) (x y : X) : clip T K t x y = K t x y := ite_eq_left ht

omit [MeasurableSpace X] [NormedAlgebra ℝ B] [CompleteSpace B] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
@[simp] lemma clip_of_not_mem (T : ℝ) (K : Kernel (X := X) (B := B)) {t : ℝ}
    (ht : t ∉ Ioc 0 T) (x y : X) : clip T K t x y = 0 := ite_eq_right ht

def term (T : ℝ) (R : Kernel (X := X) (B := B)) : ℕ → Kernel (X := X) (B := B)
  | 0 => clip T (fun t x y => -R t x y)
  | n+1 => clip T (fun t x y => -convolution μ R (term T R n) t x y)

omit [SFinite μ] [CompleteSpace B] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
@[simp] lemma term_outside (T : ℝ) (R : Kernel (X := X) (B := B))
    (n : ℕ) {t : ℝ} (ht : t ∉ Ioc 0 T) (x y : X) : term μ T R n t x y = 0 := by
  cases n <;> simp only [term, clip_of_not_mem T _ ht]

def correction (T : ℝ) (R : Kernel (X := X) (B := B)) : Kernel (X := X) (B := B) :=
  fun t x y => ∑' n, term μ T R n t x y

end TamingCompatibility.GeometricHilbert.KernelSeries

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_EuclideanCoordinateLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.UnitaryFrame
open scoped ContDiff

def exteriorTransform (B : V →L[ℝ] V) : W →L[ℝ] W :=
  wedgeTransform (fun i => B (EuclideanSpace.single i 1))

end TamingCompatibility.UnitaryFrame

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ActivationScales
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff

def thresholdScale (n : ℕ) : ℝ := stepSize n * Real.exp (-(1/stepSize n))
end TamingCompatibility.SummableCutoff

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
namespace TamingCompatibility
open scoped SchwartzMap

namespace HodgeFrame
open GeometricSymbol UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma coordinates_antiInvariant (b : Fin 4 → E) (J : E →L[ℝ] E)
    (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2) (a : MetricForms.Form E 2) :
    coordinates b ((1/2:ℝ) • (a - a.compContinuousLinearMap J)) =
      UnitaryFrame.antiInvariantPart (coordinates b a) := by
  have hc (x y : E) : (⇑J ∘ ![x,y]) = ![J x,J y] := by
    ext i; fin_cases i <;> rfl
  have hs := GeometricSymbol.eval_swap a (b 0) (b 1)
  have ht := GeometricSymbol.eval_swap a (b 2) (b 3)
  ext i
  fin_cases i <;>
    simp [coordinates_apply,UnitaryFrame.antiInvariantPart,UnitaryFrame.jAction,
      FormMetric.pairLeft,FormMetric.pairRight,h0,h1,h2,h3,
      GeometricSymbol.eval_neg_left,GeometricSymbol.eval_neg_right,hs,ht,
      hc]
end HodgeFrame

end TamingCompatibility

end
end

end
end

end OAI
end


