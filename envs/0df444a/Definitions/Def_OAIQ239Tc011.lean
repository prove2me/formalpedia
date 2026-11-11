-- Prove2me | Definitions.Def_OAIQ239Tc011
-- name    : OAIQ239Tc011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:20:55.039061+00:00
-- url     : https://prove2.me/theorems/f9b6cc6a-e211-41f6-84c8-dca40945132a
-- title:
--   Definitions bundle OAIQ239Tc011 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 22 definitions, 1 inductive type or structure and 66 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricAdjoint.rdd`, `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.GeometricChart.Data.source`, `OAI.TamingCompatibility.GeometricChart.coordinateTest`, `OAI.TamingCompatibility.GeometricChart.manifoldTest`, `OAI.TamingCompatibility.GeometricChart.normalA`, `OAI.TamingCompatibility.GeometricChart.normalB`, `OAI.TamingCompatibility.GeometricChart.scalar`, `OAI.TamingCompatibility.HodgeGeometricCoefficients.lower`, `OAI.TamingCompatibility.HodgeGeometricCoefficients.starFrame`, `OAI.TamingCompatibility.HodgeNormalOperator.lower`, `OAI.TamingCompatibility.LocalMatrixOperator.lower`, `OAI.TamingCompatibility.LocalMatrixOperator.normalLower`, `OAI.TamingCompatibility.LocalMatrixOperator.normalPrincipal`, `OAI.TamingCompatibility.LocalMatrixOperator.normalSymbol`, `OAI.TamingCompatibility.LocalMatrixOperator.principal`, `OAI.TamingCompatibility.ManifoldForms.d`, `OAI.TamingCompatibility.ManifoldForms.smoothForms`, `OAI.TamingCompatibility.ManifoldForms.wedgeOne`, `OAI.TamingCompatibility.ManifoldForms.wedgeTwo`, `OAI.TamingCompatibility.ManifoldTop.coefficient`, `OAI.TamingCompatibility.MatrixEnergy.system`, `OAI.TamingCompatibility.MetricHodge.starThreeCLM`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartEnergyIntegral`, `TamingCompatibility_Charts_ChartMetricBounds`, `TamingCompatibility_Charts_ChartUnitaryData`, `TamingCompatibility_Charts_CoefficientCutoff`, `TamingCompatibility_Charts_FiniteCharts`, `TamingCompatibility_Charts_LocalFrameOperator`, `TamingCompatibility_Charts_LocalMatrixOperator`, `TamingCompatibility_DifferentialForms_ComplexEquiv`, `TamingCompatibility_DifferentialForms_ConstantGeometricEnergy`, `TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding`, `TamingCompatibility_DifferentialForms_DirectionalEnergy`, `TamingCompatibility_DifferentialForms_Form`, `TamingCompatibility_DifferentialForms_FormEquiv`, `TamingCompatibility_DifferentialForms_FramePairing`, `TamingCompatibility_DifferentialForms_FunSmul`, `TamingCompatibility_DifferentialForms_GeometricFrameTest`, `TamingCompatibility_DifferentialForms_Sign`, `TamingCompatibility_DifferentialForms_SingleFamily`, `TamingCompatibility_DifferentialForms_Space`, `TamingCompatibility_DifferentialForms_StarTwoComp`, `TamingCompatibility_DifferentialForms_Wedge`, `TamingCompatibility_Elliptic_LocalMatrixGarding`, `TamingCompatibility_Elliptic_NormalSystem`, `TamingCompatibility_Elliptic_UnitaryLocalGarding`, `TamingCompatibility_Functional_ChartNormalTest`, `TamingCompatibility_Functional_NormalSymbol`, `TamingCompatibility_Hodge_HodgeFrameDifferential`, `TamingCompatibility_Hodge_HodgeGeometricCoefficients`, `TamingCompatibility_Hodge_LocalCodifferential`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc005`, `OAIQ239Tc006`, `OAIQ239Tc007` and `OAIQ239Tc008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc014`, `OAIQ239Tc015` and `OAIQ239Tc016`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc005
import Definitions.Def_OAIQ239Tc006
import Definitions.Def_OAIQ239Tc007
import Definitions.Def_OAIQ239Tc008

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

lemma pairing_symm (g : Metric E) {k : ℕ} (α β : Form E k) :
    pairing g α β = pairing g β α := FormMetric.pairing_symm _ _

lemma pairing_self_nonneg (g : Metric E) {k : ℕ} (α : Form E k) :
    0 ≤ pairing g α α := FormMetric.pairing_self_nonneg _

lemma pairing_self_eq_zero (g : Metric E) {k : ℕ} (α : Form E k) :
    pairing g α α = 0 ↔ α = 0 := by
  rw [pairing, FormMetric.pairing_self_eq_zero]
  constructor
  · intro h
    ext v
    have hv := congrArg (fun a : Form (MetricModel.Model g) k => a (fun i => (equiv g).symm (v i))) h
    simpa only [compContinuousLinearMap_apply, Function.comp_def,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using hv
  · intro h
    ext v
    simp only [h, compContinuousLinearMap_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

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

lemma exteriorDerivative_add {α β : Form X k} (hα : Smooth α) (hβ : Smooth β) :
    exteriorDerivative (α + β) = exteriorDerivative α + exteriorDerivative β := by
  funext x
  unfold exteriorDerivative
  rw [pullback_add]
  apply extDeriv_add
  · exact (((smooth_chart α hα x) _
      ((extChartAt Model x).map_source (mem_extChartAt_source x))).contDiffAt
      (extChartAt_target_mem_nhds x)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact (((smooth_chart β hβ x) _
      ((extChartAt Model x).map_source (mem_extChartAt_source x))).contDiffAt
      (extChartAt_target_mem_nhds x)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

omit [IsManifold Model ∞ X] in
lemma exteriorDerivative_smul (c : ℝ) (α : Form X k) :
    exteriorDerivative (c • α) = c • exteriorDerivative α := by
  funext x
  unfold exteriorDerivative
  rw [pullback_smul, extDeriv_smul]
  rfl

def smoothForms (X : Type*) [TopologicalSpace X] [ChartedSpace Space X] (k : ℕ) :
    Submodule ℝ (Form X k) where
  carrier := {α | Smooth α}
  zero_mem' := Smooth.zero
  add_mem' := Smooth.add
  smul_mem' := Smooth.smul

def d : smoothForms X k →ₗ[ℝ] smoothForms X (k + 1) where
  toFun α := ⟨exteriorDerivative α.1, α.2.exteriorDerivative⟩
  map_add' α β := Subtype.ext (exteriorDerivative_add α.2 β.2)
  map_smul' c α := Subtype.ext (exteriorDerivative_smul c α.1)

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_FiniteCharts
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_add {k : ℕ} (p : A.centers) (α β : ManifoldForms.Form X k) :
    localizedFunction A p (α + β) = localizedFunction A p α + localizedFunction A p β := by
  funext y
  unfold localizedFunction
  rw [ManifoldForms.pullback_add]
  by_cases hy : y ∈ (extChartAt Model p.val).target
  · simp only [indicator_of_mem hy, Pi.add_apply, smul_add]
  · simp only [indicator_of_notMem hy, Pi.add_apply, add_zero]

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_smul {k : ℕ} (p : A.centers) (c : ℝ) (α : ManifoldForms.Form X k) :
    localizedFunction A p (c • α) = c • localizedFunction A p α := by
  funext y
  unfold localizedFunction
  rw [ManifoldForms.pullback_smul]
  by_cases hy : y ∈ (extChartAt Model p.val).target
  · simp only [indicator_of_mem hy, Pi.smul_apply]
    exact smul_comm _ _ _
  · simp only [indicator_of_notMem hy, Pi.smul_apply, smul_zero]

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Space
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

namespace TamingCompatibility
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma IsSmooth.antiInvariantPart {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) : IsSmooth (antiInvariantPart J α) := by
  change IsSmooth ((1 / 2 : ℝ) • (α + -TamingCompatibility.jAction J α))
  convert (hα.add ((hα.jAction J).smul (-1))).smul (1 / 2 : ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  ext x v
  simp
end TamingCompatibility

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

lemma formEquiv_starTwo (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (F α : MetricForms.Form E 2) :
    formEquiv g 2 (starTwo g J F α) =
      HermitianHodge.star (isometry g J hJ).toContinuousLinearMap
        (formEquiv g 2 F) (formEquiv g 2 α) := by
  ext v
  rfl

variable (g : Metric E) (J : E →L[ℝ] E)
  (hJ : ∀ u, J (J u) = -u)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hJ horth hdim hF
lemma starTwo_square (α : MetricForms.Form E 2) :
    starTwo g J F (starTwo g J F α) = α := by
  apply (formEquiv g 2).injective
  rw [formEquiv_starTwo g J horth,formEquiv_starTwo g J horth]
  exact HermitianHodge.star_square (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _

end TamingCompatibility.MetricHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_StarTwoComp
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

variable (g : Metric E) (J : E →L[ℝ] E)
  (hJ : ∀ u, J (J u) = -u)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hJ horth hdim hF
lemma starTwo_self_adjoint (α β : MetricForms.Form E 2) :
    pairing g (starTwo g J F α) β = pairing g α (starTwo g J F β) := by
  change FormMetric.pairing (formEquiv g 2 (starTwo g J F α)) (formEquiv g 2 β) =
    FormMetric.pairing (formEquiv g 2 α) (formEquiv g 2 (starTwo g J F β))
  rw [formEquiv_starTwo g J horth,formEquiv_starTwo g J horth]
  exact HermitianHodge.star_self_adjoint (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _ _

lemma starTwo_antiInvariant (α : MetricForms.Form E 2) :
    starTwo g J F ((1/2 : ℝ) • (α - α.compContinuousLinearMap J)) =
      (1/2 : ℝ) • (α - α.compContinuousLinearMap J) := by
  apply (formEquiv g 2).injective
  rw [formEquiv_starTwo g J horth]
  have he : formEquiv g 2 ((1/2 : ℝ) • (α - α.compContinuousLinearMap J)) =
      GeometricSymbol.antiInvariant (isometry g J horth).toContinuousLinearMap (formEquiv g 2 α) := by
    ext v
    rfl
  rw [he]
  exact HermitianHodge.star_antiInvariant (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _
end TamingCompatibility.MetricHodge

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instNormedAddCommGroupTangentSpaceRealSpaceModel
attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instNormedSpaceRealTangentSpaceSpaceModel
attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instFiniteDimensionalRealTangentSpaceSpaceModel
lemma starTwo_square (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (β : TwoForm X) :
    starTwo J α ht (starTwo J α ht β) = β := by
  funext x
  exact MetricHodge.starTwo_square (tangentMetric J α ht x) (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by change Module.finrank ℝ Space = 4; simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (β x)

lemma starTwo_antiInvariant (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (β : TwoForm X) :
    starTwo J α ht (antiInvariantPart J β) = antiInvariantPart J β := by
  funext x
  exact MetricHodge.starTwo_antiInvariant (tangentMetric J α ht x) (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by change Module.finrank ℝ Space = 4; simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (β x)

end TamingCompatibility.ManifoldHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Sign
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

namespace TamingCompatibility.ManifoldTop
open Bundle ContinuousAlternatingMap ManifoldHodge ExteriorForms
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma pullback_volumeForm (J : AlmostComplexStructure X) (α : TwoForm X) (f : Space → X) (z : Space) :
    ManifoldForms.pullback (volumeForm J α) f z =
      volumeSquare (ManifoldForms.pullback (invariantPart J α) f z) :=
  volumeSquare_comp (E := Space) (D := Space) _ _

lemma volumeForm_smooth (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) :
    ManifoldForms.Smooth (volumeForm J α) := by
  intro f U hU hf
  change ContDiffOn ℝ ∞ (ManifoldForms.pullback (volumeForm J α) f) U
  have he : ManifoldForms.pullback (volumeForm J α) f =
      fun z => volumeSquare (ManifoldForms.pullback (invariantPart J α) f z) :=
    funext (pullback_volumeForm J α f)
  rw [he]
  exact volumeSquare_contDiffOn basis ((hs.invariantPart J) f U hU hf)

lemma volumeForm_ne_zero (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (x : X) :
    volumeForm J α x ≠ 0 := by
  let g : MetricModel.Metric Space :=
    ⟨associatedBilinear J (invariantPart J α) x,
      (invariantPart_isInvariant J α).associatedBilinear_symm x,
      (tames_invariantPart ht).associatedBilinear_pos x⟩
  exact VolumeNormalization.volume_ne_zero g (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm)

def coefficient (J : AlmostComplexStructure X) (α : TwoForm X) (β : ManifoldForms.Form X 4) : X → ℝ :=
  fun x => TopForms.coefficient basis (volumeForm J α x) (β x)

lemma coefficient_chart (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 4) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    coefficient J α β ((extChartAt Model p).symm z) =
      (ManifoldForms.pullback β (extChartAt Model p).symm z basis) /
      (ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis) := by
  have h := TopForms.coefficient_comp basis basis (inverseChartEquiv p z hz)
    (volumeForm J α ((extChartAt Model p).symm z)) (β ((extChartAt Model p).symm z))
    (volumeForm_ne_zero J α ht _)
  erw [inverseChartEquiv_coe] at h
  exact h.symm

lemma coordinateVolume_ne_zero (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    (ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis) ≠ 0 := by
  apply TopForms.eval_ne_zero basis
  have h := TopForms.comp_ne_zero (E := Space) (D := Space) (inverseChartEquiv p z hz)
    (volumeForm J α ((extChartAt Model p).symm z)) (volumeForm_ne_zero J α ht _)
  erw [inverseChartEquiv_coe] at h
  exact h

lemma coefficient_smooth (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) {β : ManifoldForms.Form X 4} (hβ : ManifoldForms.Smooth β) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ (coefficient J α β) := by
  apply scalar_smooth_of_charts
  intro p
  have hn := (ContinuousAlternatingMap.apply ℝ Space ℝ basis).contDiff.comp_contDiffOn
    (ManifoldForms.smooth_chart β hβ p)
  have hd := (ContinuousAlternatingMap.apply ℝ Space ℝ basis).contDiff.comp_contDiffOn
    (ManifoldForms.smooth_chart _ (volumeForm_smooth J α hs) p)
  apply (hn.div hd (fun z hz => coordinateVolume_ne_zero J α ht p hz)).congr
  intro z hz
  exact coefficient_chart J α ht β p hz

lemma coordinateFundamental (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z ![u,v] =
      (coordinateMetric J α ht p z).bilinear (coordinateJ J p z u) v := by
  rw [← coordinateMetric_pullback J α ht p hz,coordinateJ_intertwine J p hz]
  change _ = associatedBilinear J (invariantPart J α) _ _ _
  rw [associatedBilinear_invariantPart_fundamental]
  change _ = invariantPart J α _ ![(inverseChartEquiv p z hz).toContinuousLinearMap u,
    (inverseChartEquiv p z hz).toContinuousLinearMap v]
  rw [inverseChartEquiv_coe]
  change (invariantPart J α _) ((mfderiv Model Model (extChartAt Model p).symm z) ∘ ![u,v]) = _
  congr 1
  ext i
  fin_cases i <;> rfl

lemma abs_coordinateVolume (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    |ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis| =
      ManifoldVolume.chartDensity J α p z := by
  rw [pullback_volumeForm]
  have he := VolumeNormalization.abs_volume_eq_density (coordinateMetric J α ht p z)
    (coordinateJ J p z) (coordinateJ_square J p hz) (coordinateMetric_hermitian J α ht p hz)
    (by simp [Space]) (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
    (coordinateFundamental J α ht p hz) basis
  rw [coordinateMetric_bilinear J α ht p hz,density_basis] at he
  exact he

lemma density_coefficient (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 4) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldVolume.chartDensity J α p z * coefficient J α β ((extChartAt Model p).symm z) =
      OrientationSign.sign (ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis) *
        ManifoldForms.pullback β (extChartAt Model p).symm z basis := by
  rw [coefficient_chart J α ht β p hz,← abs_coordinateVolume J α ht p hz]
  exact OrientationSign.abs_mul_div _ _ (coordinateVolume_ne_zero J α ht p hz)

end TamingCompatibility.ManifoldTop

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FunSmul
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

namespace TamingCompatibility.ManifoldStokes
open Bundle ContinuousAlternatingMap _root_.MeasureTheory Set
open ManifoldForms ManifoldTop ManifoldVolume
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : ManifoldLocalization.FiniteCharts X)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coefficient_add (J : AlmostComplexStructure X) (α : TwoForm X)
    (β γ : ManifoldForms.Form X 4) :
    ManifoldTop.coefficient J α (β + γ) = ManifoldTop.coefficient J α β + ManifoldTop.coefficient J α γ := by
  funext x
  change ((β x) basis + (γ x) basis) / volumeForm J α x basis = _
  exact add_div _ _ _

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coefficient_smul (J : AlmostComplexStructure X) (α : TwoForm X)
    (β : ManifoldForms.Form X 4) (c : ℝ) :
    ManifoldTop.coefficient J α (c • β) = c • ManifoldTop.coefficient J α β := by
  funext x
  change (c * β x basis) / volumeForm J α x basis = c * (β x basis / volumeForm J α x basis)
  exact mul_div_assoc _ _ _

end TamingCompatibility.ManifoldStokes

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SingleFamily
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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

namespace TamingCompatibility.WedgePairing
open RealInnerProductSpace ContinuousAlternatingMap ExteriorForms FormMetric GeometricSymbol
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma wedgeTwo_on_frame (b : OrthonormalBasis (Fin 4) ℝ E) (a c : Form (E := E) 2) :
    wedgeTwo a c b = ⟪coords b a,UnitaryFrame.star (coords b c)⟫ := by
  have he : (b : Fin 4 → E) = ![b 0,b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
  rw [he,wedgeTwo_apply]
  simp [coords,UnitaryFrame.star,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ]
  ring

section Frame
variable (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)
include h0 h1 h2 h3 hF

lemma wedgeTwo_star (a c : Form (E := E) 2) :
    wedgeTwo a (HermitianHodge.star J F c) = FormMetric.pairing a c • volumeSquare F := by
  apply top_ext b.toBasis
  change wedgeTwo a (HermitianHodge.star J F c) b = (FormMetric.pairing a c • volumeSquare F) b
  rw [wedgeTwo_on_frame,HermitianHodge.coords_star b J h0 h1 h2 h3 F hF,
    UnitaryFrame.star_square,ContinuousAlternatingMap.smul_apply,
    volume_on_frame b J h0 h1 h2 h3 F hF]
  rw [smul_eq_mul,mul_one,HermitianHodge.pairing_coords b]

lemma wedgeOne_three (a : Form (E := E) 1) (c : Form (E := E) 3) :
    wedgeOne (oneLinear a) c = -FormMetric.pairing a (HodgeThree.star F c) • volumeSquare F := by
  apply top_ext b.toBasis
  change wedgeOne (oneLinear a) c b = (-FormMetric.pairing a (HodgeThree.star F c) • volumeSquare F) b
  rw [ContinuousAlternatingMap.smul_apply,volume_on_frame b J h0 h1 h2 h3 F hF,smul_eq_mul,mul_one,
    pairing_one b]
  simp_rw [HodgeThree.star_on_frame b J h0 h1 h2 h3 F hF]
  have he : (b : Fin 4 → E) = ![b 0,b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
  nth_rw 1 [he]
  rw [wedgeOne_apply_four]
  have h₀ : (fun l => b (FormMetric.tripleIndices 0 l)) = ![b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
  have h₁ : (fun l => b (FormMetric.tripleIndices 1 l)) = ![b 0,b 2,b 3] := by ext i; fin_cases i <;> rfl
  have h₂ : (fun l => b (FormMetric.tripleIndices 2 l)) = ![b 0,b 1,b 3] := by ext i; fin_cases i <;> rfl
  have h₃ : (fun l => b (FormMetric.tripleIndices 3 l)) = ![b 0,b 1,b 2] := by ext i; fin_cases i <;> rfl
  simp [oneLinear_apply,Fin.sum_univ_succ,h₀,h₁,h₂,h₃]
  ring
end Frame

lemma wedgeTwo_star_intrinsic (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
    (hdim : Module.finrank ℝ E = 4) (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)
    (a c : Form (E := E) 2) :
    wedgeTwo a (HermitianHodge.star J.toContinuousLinearMap F c) = FormMetric.pairing a c • volumeSquare F := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis J hJ hdim
  exact wedgeTwo_star b J.toContinuousLinearMap h0 h1 h2 h3 F hF a c

lemma wedgeOne_three_intrinsic (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
    (hdim : Module.finrank ℝ E = 4) (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)
    (a : Form (E := E) 1) (c : Form (E := E) 3) :
    wedgeOne (oneLinear a) c = -FormMetric.pairing a (HodgeThree.star F c) • volumeSquare F := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis J hJ hdim
  exact wedgeOne_three b J.toContinuousLinearMap h0 h1 h2 h3 F hF a c

end TamingCompatibility.WedgePairing

namespace TamingCompatibility.MetricWedgePairing
open ContinuousAlternatingMap ExteriorForms MetricHodge MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma formEquiv_wedgeTwo (g : Metric E) (a b : ExteriorForms.Form (E := E) 2) :
    formEquiv g 4 (wedgeTwo a b) = wedgeTwo (formEquiv g 2 a) (formEquiv g 2 b) := by
  simp only [wedgeTwo,_root_.map_sub,formEquiv_volume,_root_.map_add]

lemma formEquiv_wedgeOne {degree : ℕ} (g : Metric E) (a : ExteriorForms.Form (E := E) 1) (b : ExteriorForms.Form (E := E) degree) :
    formEquiv g (degree+1) (wedgeOne (oneLinear a) b) = wedgeOne (oneLinear (formEquiv g 1 a)) (formEquiv g degree b) := by
  exact (wedgeOne_comp (oneLinear a) b (equiv g).toContinuousLinearMap).trans
    (congrArg (fun L => wedgeOne L (formEquiv g degree b)) (oneLinear_comp a (equiv g).toContinuousLinearMap).symm)

variable (g : Metric E) (J : E →L[ℝ] E) (hJ : ∀ u, J (J u) = -u)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (hdim : Module.finrank ℝ E = 4) (F : ExteriorForms.Form (E := E) 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hJ horth hdim hF

lemma wedgeTwo_star (a b : ExteriorForms.Form (E := E) 2) :
    wedgeTwo a (starTwo g J F b) = MetricForms.pairing g a b • volumeSquare F := by
  apply (formEquiv g 4).injective
  rw [formEquiv_wedgeTwo,formEquiv_starTwo g J horth,_root_.map_smul,formEquiv_volume]
  exact WedgePairing.wedgeTwo_star_intrinsic (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _ _

lemma wedgeOne_three (a : ExteriorForms.Form (E := E) 1) (b : ExteriorForms.Form (E := E) 3) :
    wedgeOne (oneLinear a) b = -MetricForms.pairing g a (starThree g F b) • volumeSquare F := by
  apply (formEquiv g 4).injective
  rw [formEquiv_wedgeOne,_root_.map_smul,formEquiv_volume]
  have he : formEquiv g 1 (starThree g F b) = HodgeThree.star (formEquiv g 2 F) (formEquiv g 3 b) :=
    (formEquiv g 1).apply_symm_apply _
  change wedgeOne (oneLinear (formEquiv g 1 a)) (formEquiv g 3 b) =
    -FormMetric.pairing (formEquiv g 1 a) (formEquiv g 1 (starThree g F b)) • volumeSquare (formEquiv g 2 F)
  rw [he]
  exact WedgePairing.wedgeOne_three_intrinsic (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _ _

end TamingCompatibility.MetricWedgePairing

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Wedge
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

def wedgeOne (a : Form X 1) (b : Form X k) : Form X (k+1) :=
  fun x => ExteriorForms.wedgeOne (E := Space) (ExteriorForms.oneLinear (E := Space) (a x)) (b x)
def wedgeTwo (a b : Form X 2) : Form X 4 := fun x => ExteriorForms.wedgeTwo (E := Space) (a x) (b x)

omit [IsManifold Model ∞ X] in
lemma pullback_wedgeOne (a : Form X 1) (b : Form X k) (f : Space → X) :
    pullback (wedgeOne a b) f = fun z => ExteriorForms.wedgeOne (ExteriorForms.oneLinear (pullback a f z)) (pullback b f z) := by
  funext z
  change (ExteriorForms.wedgeOne (E := Space) (ExteriorForms.oneLinear (E := Space) (a (f z))) (b (f z))).compContinuousLinearMap _ = _
  exact (ExteriorForms.wedgeOne_comp (E := Space) (D := Space) _ _ _).trans
    (congrArg (fun L => ExteriorForms.wedgeOne L (pullback b f z))
      (ExteriorForms.oneLinear_comp (E := Space) (D := Space) (a (f z)) _).symm)

omit [IsManifold Model ∞ X] in
lemma Smooth.wedgeOne {a : Form X 1} {b : Form X k} (ha : Smooth a) (hb : Smooth b) :
    Smooth (wedgeOne a b) := by
  intro f U hU hf
  rw [pullback_wedgeOne]
  exact ((ExteriorForms.wedgeOneBilinear (E := Space) (k := k)).contDiff.comp_contDiffOn
    (ha f U hU hf)).clm_apply (hb f U hU hf)

lemma exteriorDerivative_wedgeOne {a : Form X 1} {b : Form X 2} (ha : Smooth a) (hb : Smooth b) :
    exteriorDerivative (wedgeOne a b) = wedgeTwo (exteriorDerivative a) b - wedgeOne a (exteriorDerivative b) := by
  funext x
  change extDeriv (pullback (wedgeOne a b) (extChartAt Model x).symm) ((extChartAt Model x) x) = _
  have ha' := (((smooth_chart a ha x) _ (mem_extChartAt_target x)).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hb' := (((smooth_chart b hb x) _ (mem_extChartAt_target x)).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [pullback_wedgeOne,ExteriorForms.extDeriv_wedgeOne ha' hb']
  rw [pullback_at_center,pullback_at_center]
  rfl

omit [IsManifold Model ∞ X] in
lemma pullback_wedgeTwo (a b : Form X 2) (f : Space → X) :
    pullback (wedgeTwo a b) f = fun z => ExteriorForms.wedgeTwo (pullback a f z) (pullback b f z) := by
  funext z
  exact ExteriorForms.wedgeTwo_comp (E := Space) (D := Space) (a (f z)) (b (f z)) _

omit [IsManifold Model ∞ X] in
lemma Smooth.wedgeTwo {a b : Form X 2} (ha : Smooth a) (hb : Smooth b) : Smooth (wedgeTwo a b) := by
  intro f U hU hf
  rw [pullback_wedgeTwo]
  exact ((ExteriorForms.volumeSquare_contDiffOn ManifoldTop.basis ((ha f U hU hf).add (hb f U hU hf))).sub
    (ExteriorForms.volumeSquare_contDiffOn ManifoldTop.basis (ha f U hU hf))).sub
    (ExteriorForms.volumeSquare_contDiffOn ManifoldTop.basis (hb f U hU hf))

end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexEquiv
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
lemma pairing_smul_right (g : Metric E) {k : ℕ} (t : ℝ) (a b : Form E k) :
    pairing g a (t • b) = t * pairing g a b := by
  rw [pairing_symm,pairing_smul_left,pairing_symm g b a]

end TamingCompatibility.MetricForms

namespace TamingCompatibility.GeometricAdjoint
open Bundle ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def rdd (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a : TwoForm X) : TwoForm X := antiInvariantPart J (exteriorDerivative (codifferential J α ht a))
end TamingCompatibility.GeometricAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_LocalCodifferential
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

namespace TamingCompatibility.MetricHodge
open MetricModel MetricForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] OAI.TamingCompatibility.MetricHodge.instFiniteDimensionalRealContinuousMultilinearMapFin_solutions
attribute [local instance] OAI.TamingCompatibility.MetricHodge.instFiniteDimensionalRealContinuousAlternatingMapFin_solutions
def starThreeCLM (g : Metric E) (F : MetricForms.Form E 2) :
    MetricForms.Form E 3 →L[ℝ] MetricForms.Form E 1 :=
  LinearMap.toContinuousLinearMap {
    toFun := starThree g F
    map_add' := starThree_add g F
    map_smul' := fun t a => starThree_smul g F t a }
lemma starThreeCLM_apply (g : Metric E) (F : MetricForms.Form E 2) (a : MetricForms.Form E 3) :
    starThreeCLM g F a = starThree g F a := rfl
end TamingCompatibility.MetricHodge

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldForms ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_codifferential_antiInvariant (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a) (hanti : antiInvariantPart J a = a)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z =
      -MetricHodge.starThree (coordinateMetric J α ht p z)
        (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (ManifoldForms.pullback a (extChartAt Model p).symm) z) := by
  have hstar : starTwo J α ht a = a := by
    rw [← hanti]
    exact starTwo_antiInvariant J α ht a
  change ((-(starThree J α ht (exteriorDerivative (starTwo J α ht a))))
    ((extChartAt Model p).symm z)).compContinuousLinearMap _ = _
  rw [hstar]
  have hneg (b : ManifoldForms.Form X 1) :
      ManifoldForms.pullback (-b) (extChartAt Model p).symm z =
        -ManifoldForms.pullback b (extChartAt Model p).symm z := by ext v; rfl
  change ManifoldForms.pullback (-(starThree J α ht (exteriorDerivative a)))
    (extChartAt Model p).symm z = _
  rw [hneg,pullback_starThree J α ht _ p hz,
    pullback_exteriorDerivative a ha (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hz]
  congr 2
  exact extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz
end TamingCompatibility.ManifoldHodge

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalFrameOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace TamingCompatibility.LocalFrameOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma expansion_at {A B : E → ℝ} {ψ χ : E → MetricForms.Form E 2} {x : E}
    (g : Metric E) (F : MetricForms.Form E 2)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hψ : DifferentiableAt ℝ ψ x) (hχ : DifferentiableAt ℝ χ x) :
    starThree g F (extDeriv (fun y => A y • ψ y + B y • χ y) x) =
      starThree g F (wedgeOne (fderiv ℝ A x) (ψ x)) +
      starThree g F (wedgeOne (fderiv ℝ B x) (χ x)) +
      (A x • starThree g F (extDeriv ψ x) + B x • starThree g F (extDeriv χ x)) := by
  change starThree g F (extDeriv ((fun y => A y • ψ y) + (fun y => B y • χ y)) x) = _
  rw [extDeriv_add (ω₁ := fun y => A y • ψ y) (ω₂ := fun y => B y • χ y) (hA.smul hψ) (hB.smul hχ),
    extDeriv_variable_smul hA hψ, extDeriv_variable_smul hB hχ]
  change starThreeCLM g F
    (A x • extDeriv ψ x + wedgeOne (fderiv ℝ A x) (ψ x) +
      (B x • extDeriv χ x + wedgeOne (fderiv ℝ B x) (χ x))) = _
  simp only [map_add,map_smul,starThreeCLM_apply]
  abel
end TamingCompatibility.LocalFrameOperator

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalMatrixOperator
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
open EuclideanEnergy
open scoped ContDiff RealInnerProductSpace SchwartzMap

def principal (g : Metric V) (F ψ χ : MetricForms.Form V 2) (i : Fin 4) : Pair →L[ℝ] V :=
  oneVector ∘L starThreeCLM g F ∘L
    combine (wedgeOne (EuclideanSpace.proj i) ψ) (wedgeOne (EuclideanSpace.proj i) χ)

def lower (g : Metric V) (F : MetricForms.Form V 2) (ψ χ : V → MetricForms.Form V 2) (x : V) :
    Pair →L[ℝ] V := oneVector ∘L starThreeCLM g F ∘L combine (extDeriv ψ x) (extDeriv χ x)

lemma operator_expansion {A B : V → ℝ} {ψ χ : V → MetricForms.Form V 2} {x : V}
    (g : Metric V) (F : MetricForms.Form V 2)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hψ : DifferentiableAt ℝ ψ x) (hχ : DifferentiableAt ℝ χ x) :
    oneVector (starThree g F (extDeriv (fun y => A y • ψ y + B y • χ y) x)) =
      (∑ i, principal g F (ψ x) (χ x) i
        (pair (fderiv ℝ A x (e i)) (fderiv ℝ B x (e i)))) +
      lower g F ψ χ x (pair (A x) (B x)) := by
  rw [LocalFrameOperator.expansion_at g F hA hB hψ hχ]
  simp only [map_add,map_smul]
  apply congrArg₂ (· + ·)
  · have hA' := covector_expansion (fderiv ℝ A x)
    have hB' := covector_expansion (fderiv ℝ B x)
    conv_lhs => rw [hA',hB']
    change oneVector (starThreeCLM g F (wedgeOneRight (ψ x) _)) +
      oneVector (starThreeCLM g F (wedgeOneRight (χ x) _)) = _
    simp only [_root_.map_sum,map_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [principal,ContinuousLinearMap.comp_apply,combine_pair,map_add,map_smul,
      starThreeCLM_apply,wedgeOneRight_apply]
  · simp only [lower, ContinuousLinearMap.comp_apply, combine_pair, map_add, map_smul,
      starThreeCLM_apply]

end TamingCompatibility.LocalMatrixOperator

end
end

section

noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace SchwartzMap

lemma principal_smooth {U : Set V} {g : V → Metric V} {F ψ χ : V → MetricForms.Form V 2}
    (hstar : ContDiffOn ℝ ∞ (fun x => starThreeCLM (g x) (F x)) U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U) (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => principal (g x) (F x) (ψ x) (χ x) i) U := by
  apply contDiffOn_clm_apply.mpr
  intro q
  have hwψ := (wedgeOneBilinear ((ofSubsingletonLIE (0 : Fin 1))
    (EuclideanSpace.proj i))).contDiff.comp_contDiffOn hψ
  have hwχ := (wedgeOneBilinear ((ofSubsingletonLIE (0 : Fin 1))
    (EuclideanSpace.proj i))).contDiff.comp_contDiffOn hχ

  exact oneVector.contDiff.comp_contDiffOn
    (hstar.clm_apply ((hwψ.const_smul (q 0)).add (hwχ.const_smul (q 1))))

lemma lower_smooth {U : Set V} (hU : IsOpen U)
    {g : V → Metric V} {F ψ χ : V → MetricForms.Form V 2}
    (hstar : ContDiffOn ℝ ∞ (fun x => starThreeCLM (g x) (F x)) U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U) :
    ContDiffOn ℝ ∞ (fun x => lower (g x) (F x) ψ χ x) U := by
  apply contDiffOn_clm_apply.mpr
  intro q
  have hdψ : ContDiffOn ℝ ∞ (fun x => extDeriv ψ x) U :=
    (alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn (hψ.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hdχ : ContDiffOn ℝ ∞ (fun x => extDeriv χ x) U :=
    (alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn (hχ.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  exact oneVector.contDiff.comp_contDiffOn
    (hstar.clm_apply ((hdψ.const_smul (q 0)).add (hdχ.const_smul (q 1))))

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_DirectionalEnergy
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
open EuclideanEnergy MetricForms ExteriorForms MetricHodge AntiInvariantFrame
open scoped RealInnerProductSpace SchwartzMap LineDeriv

lemma oneVector_inner (a : MetricForms.Form V 1) (u : V) :
    inner ℝ (oneVector a) u = a ![u] := by
  have hv : oneVector a = (InnerProductSpace.toDual ℝ V).symm (oneLinear a) := rfl
  rw [hv,InnerProductSpace.toDual_symm_apply,oneLinear_apply]

lemma oneCoordinates_bound (b : Fin 4 → V) (a : MetricForms.Form V 1) :
    ‖oneCoordinates b a‖^2 ≤ evaluationConstant b * ‖oneVector a‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have h (i : Fin 4) : (a ![b i])^2 ≤ ‖b i‖^2 * ‖oneVector a‖^2 := by
    rw [← oneVector_inner]
    have h := sq_le_sq₀ (abs_nonneg _) (by positivity)
      |>.mpr (abs_real_inner_le_norm (oneVector a) (b i))
    simpa only [sq_abs,mul_pow,mul_comm] using h
  change (∑ i, (a ![b i])^2) ≤ _
  refine (Finset.sum_le_sum (fun i _ => h i)).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by simp [evaluationConstant]) (sq_nonneg _)

lemma principal_covectors (g : MetricModel.Metric V) (F ψ χ : MetricForms.Form V 2)
    (ξ η : V →L[ℝ] ℝ) :
    oneVector (starThree g F (wedgeOne ξ ψ + wedgeOne η χ)) =
      ∑ i, principal g F ψ χ i (pair (ξ (e i)) (η (e i))) := by
  rw [starThree_add,map_add]
  conv_lhs => rw [covector_expansion ξ,covector_expansion η]
  change oneVector (starThreeCLM g F (wedgeOneRight ψ _)) +
    oneVector (starThreeCLM g F (wedgeOneRight χ _)) = _
  simp only [map_sum,map_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [principal,ContinuousLinearMap.comp_apply,combine_pair,map_add,map_smul,
    starThreeCLM_apply,wedgeOneRight_apply]

lemma oneCoordinates_star_covectors (g : MetricModel.Metric V)
    (b : Fin 4 → V) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (F : MetricForms.Form V 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (A B : S) (x : V) :
    oneCoordinates b (starThree g F (wedgeOne (fderiv ℝ A x) (realPart g b) +
      wedgeOne (fderiv ℝ B x) (imagPart g b))) = DirectionalEnergy.codifferential b A B x := by
  ext i
  change starThree g F _ ![b i] = _
  rw [starThree_add,ContinuousAlternatingMap.add_apply,
    star_wedge_real g (by simp [V]) b hb J h0 h1 h2 h3 F hF,
    star_wedge_imag g (by simp [V]) b hb J h0 h1 h2 h3 F hF]
  fin_cases i <;> simp [DirectionalEnergy.codifferential,DirectionalEnergy.directionDeriv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] <;> ring

end TamingCompatibility.LocalMatrixOperator

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
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

def system (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (A B : S) (x : V) : V :=
  (∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x))) +
    b x (pair (A x) (B x))
lemma system_integrable (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (A B : S) {δ C : ℝ} (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) :
    Integrable (fun x => ‖system a b A B x‖^2) := by
  have hcont : Continuous (system a b A B) := by
    apply Continuous.add _ (hbc.clm_apply (pair_continuous A.continuous B.continuous))
    apply continuous_finsetSum
    intro i _
    exact (hac i).clm_apply (pair_continuous (coordinateDeriv i A).continuous
      (coordinateDeriv i B).continuous)
  have hdom := ((gradientEnergy_integrable A B).const_mul (8*δ^2)).add
    (((schwartz_sq_integrable A).add (schwartz_sq_integrable B)).const_mul (2*C^2))
  refine hdom.mono' (hcont.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := norm_add_sq_le
    (∑ i, a i x (pair (coordinateDeriv i A x) (coordinateDeriv i B x)))
    (b x (pair (A x) (B x)))
  have hp := principalError_bound a A B x (ha x)
  have hl := lowerError_bound b A B x (hb x)
  dsimp only [system,Pi.add_apply]
  nlinarith

end TamingCompatibility.MatrixEnergy

end
end

end
end
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

lemma patchPrincipal_continuous {U : Set V} (hU : IsOpen U)
    (c : Fin 4 → Pair →L[ℝ] V) (a : Fin 4 → V → Pair →L[ℝ] V)
    (ha : ∀ i, ContinuousOn (a i) U) {x₀ : V} (φ : ContDiffBump x₀)
    (hφ : tsupport φ ⊆ U) (i : Fin 4) : Continuous (patchPrincipal c a φ i) :=
  (continuous_cutoff hU ((ha i).sub continuousOn_const) φ hφ).add continuous_const

lemma patchPrincipal_bound {U : Set V} (c : Fin 4 → Pair →L[ℝ] V)
    (a : Fin 4 → V → Pair →L[ℝ] V) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ x ∈ U, ∀ i, ‖a i x-c i‖ ≤ δ) {x₀ : V} (φ : ContDiffBump x₀)
    (hφ : tsupport φ ⊆ U) (x : V) (i : Fin 4) : ‖patchPrincipal c a φ i x-c i‖ ≤ δ := by
  simpa only [patchPrincipal,add_sub_cancel_right] using
    cutoff_bound hδ (fun x hx => ha x hx i) φ hφ x

lemma system_patch_eq (c : Fin 4 → Pair →L[ℝ] V)
    (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    {x₀ : V} (φ : ContDiffBump x₀) (A B : S)
    (hA : tsupport A ⊆ Metric.closedBall x₀ φ.rIn)
    (hB : tsupport B ⊆ Metric.closedBall x₀ φ.rIn) (x : V) :
    system (patchPrincipal c a φ) (patchLower b φ) A B x = system a b A B x := by
  by_cases hx : x ∈ Metric.closedBall x₀ φ.rIn
  · simp only [system,patchPrincipal,patchLower,φ.one_of_mem_closedBall hx,
      one_smul,sub_add_cancel]
  · have ha : x ∉ tsupport A := fun h => hx (hA h)
    have hb : x ∉ tsupport B := fun h => hx (hB h)
    have hAa : A x = 0 := image_eq_zero_of_notMem_tsupport ha
    have hBb : B x = 0 := image_eq_zero_of_notMem_tsupport hb
    have hAd (i : Fin 4) : coordinateDeriv i A x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => ha (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
    have hBd (i : Fin 4) : coordinateDeriv i B x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hb (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
    simp only [system,hAa,hBb,hAd,hBd]
    have hp : pair 0 0 = 0 := by ext i; fin_cases i <;> rfl
    simp only [hp,map_zero,Finset.sum_const_zero,add_zero]

end TamingCompatibility.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_LocalMatrixGarding
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
open _root_.MeasureTheory Filter Topology
open scoped ContDiff SchwartzMap
namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricModel MetricForms MetricHodge ExteriorForms AntiInvariantFrame

lemma supported_operator_eq {U : Set V} (hU : IsOpen U)
    (g : V → Metric V) (F ψ χ : V → MetricForms.Form V 2)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U)
    (A B : S) (hA : tsupport A ⊆ U) (hB : tsupport B ⊆ U) (x : V) :
    oneVector (starThree (g x) (F x)
      (extDeriv (fun y => A y • ψ y + B y • χ y) x)) =
      MatrixEnergy.system (fun i x => principal (g x) (F x) (ψ x) (χ x) i)
        (fun x => lower (g x) (F x) ψ χ x) A B x := by
  by_cases hx : x ∈ U
  · simpa only [MatrixEnergy.system,coordinateDeriv,
      SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      operator_expansion (g x) (F x) (A.differentiableAt) (B.differentiableAt)
        ((hψ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
        ((hχ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
  · have hnA : x ∉ tsupport A := fun h => hx (hA h)
    have hnB : x ∉ tsupport B := fun h => hx (hB h)
    have hAz := image_eq_zero_of_notMem_tsupport hnA
    have hBz := image_eq_zero_of_notMem_tsupport hnB
    have hdA : fderiv ℝ A x = 0 := fderiv_of_notMem_tsupport ℝ hnA
    have hdB : fderiv ℝ B x = 0 := fderiv_of_notMem_tsupport ℝ hnB
    have he : (fun y => A y • ψ y + B y • χ y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnA,
        notMem_tsupport_iff_eventuallyEq.mp hnB] with y hAy hBy
      simp only [hAy,hBy,zero_smul,add_zero,Pi.zero_apply]
    have hd : extDeriv (fun y => A y • ψ y + B y • χ y) x = 0 := by
      unfold extDeriv
      rw [he.fderiv_eq, fderiv_fun_const]
      exact map_zero _
    simp only [hd,starThree_zero,map_zero,MatrixEnergy.system,coordinateDeriv,
      SchwartzMap.lineDerivOp_apply_eq_fderiv,hdA,hdB,zero_apply,
      hAz,hBz,show pair 0 0 = 0 by ext i; fin_cases i <;> rfl,Finset.sum_const_zero,add_zero]

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_UnitaryLocalGarding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped ContDiff SchwartzMap
namespace TamingCompatibility.SmoothMetric
open MetricModel LocalUnitaryFrame
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma exists_unitaryFrame_near (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {x : D} (hx : x ∈ U) :
    ∃ W : Set D, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ b : Fin 4 → D → E, (∀ i, ContDiffOn ℝ ∞ (b i) W) ∧
        (∀ y ∈ W, ∀ i j, (g y).bilinear (b i y) (b j y) = if i = j then 1 else 0) ∧
        (∀ y ∈ W, J y (b 0 y) = b 1 y ∧ J y (b 1 y) = -b 0 y ∧
          J y (b 2 y) = b 3 y ∧ J y (b 3 y) = -b 2 y) ∧
        ∃ B : Module.Basis (Fin 4) ℝ E, ∀ i, b i x = B i := by
  obtain ⟨B,hB,h0,h1,h2,h3⟩ := VolumeNormalization.exists_metric_unitary_basis (g x) (J x)
    (hJs x hx) (hgJ x hx) hdim
  have hu : (g x).bilinear (B 0) (B 0) = 1 := by simpa using hB 0 0
  have hw : (g x).bilinear (B 2) (B 2) = 1 := by simpa using hB 2 2
  have huw : (g x).bilinear (B 0) (B 2) = 0 := by simpa using hB 0 2
  have hjuw : (g x).bilinear (J x (B 0)) (B 2) = 0 := by rw [h0]; simpa using hB 1 2
  obtain ⟨W,hW,hxW,hWU,u,w,hus,hws,hux,hwx,hgram⟩ :=
    exists_smooth_frame_near (B := fun y => (g y).bilinear) x hU hx hg hJ
      (fun y _ => (g y).symm) hJs hgJ (B 0) (B 2) hu hw huw hjuw
  refine ⟨W,hW,hxW,hWU,(fun i y => frame (J y) (u y) (w y) i),?_,hgram,?_,B,?_⟩
  · intro i
    fin_cases i
    · exact hus
    · exact (hJ.mono hWU).clm_apply hus
    · exact hws
    · exact (hJ.mono hWU).clm_apply hws
  · intro y hy
    exact ⟨rfl,hJs y (hWU hy) _,rfl,hJs y (hWU hy) _⟩
  · intro i
    fin_cases i <;> simp [frame,hux,hwx,h0,h2]
end TamingCompatibility.SmoothMetric

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartUnitaryData
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open scoped Manifold ContDiff SchwartzMap
namespace TamingCompatibility.GeometricChart
open ManifoldHodge ManifoldVolume ManifoldForms
open MetricModel MetricForms MetricHodge AntiInvariantFrame EuclideanEnergy LocalMatrixOperator
open _root_.MeasureTheory Set
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

structure Data (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) where
  radius : ℝ
  energyConstant : ℝ
  lowerConstant : ℝ
  radius_pos : 0 < radius
  energy_pos : 0 < energyConstant
  lower_pos : 0 < lowerConstant
  domain : Set Space
  domain_open : IsOpen domain
  ball_subset : Metric.closedBall (extChartAt Model p p) (2*radius) ⊆ domain
  domain_subset : domain ⊆ (extChartAt Model p).target
  frame : Fin 4 → Space → Space
  frame_smooth : ∀ i, ContDiffOn ℝ ∞ (frame i) domain
  frame_gram : ∀ x ∈ domain, ∀ i j,
    (coordinateMetric J α ht p x).bilinear (frame i x) (frame j x) = if i = j then 1 else 0
  frame_complex : ∀ x ∈ domain,
    coordinateJ J p x (frame 0 x) = frame 1 x ∧
    coordinateJ J p x (frame 1 x) = -frame 0 x ∧
    coordinateJ J p x (frame 2 x) = frame 3 x ∧
    coordinateJ J p x (frame 3 x) = -frame 2 x
  garding : ∀ A B : S, tsupport A ⊆ Metric.closedBall (extChartAt Model p p) radius →
    tsupport B ⊆ Metric.closedBall (extChartAt Model p p) radius →
    (∫ x, gradientEnergy A B x) ≤ energyConstant * (∫ x,
      ‖oneVector (starThree (coordinateMetric J α ht p x)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm x)
        (extDeriv (fun y => A y • realPart (coordinateMetric J α ht p y) (fun i => frame i y) +
          B y • imagPart (coordinateMetric J α ht p y) (fun i => frame i y)) x))‖^2) +
      lowerConstant * (∫ x, (A x)^2+(B x)^2)

namespace Data
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : Data J α ht p)
def source : Set X := (extChartAt Model p).source ∩
  (extChartAt Model p) ⁻¹' Metric.ball (extChartAt Model p p) D.radius
lemma source_image_subset : (extChartAt Model p) '' D.source ⊆
    Metric.closedBall (extChartAt Model p p) D.radius := by
  rintro x ⟨y,hy,rfl⟩
  exact Metric.ball_subset_closedBall hy.2
lemma small_ball_subset : Metric.closedBall (extChartAt Model p p) D.radius ⊆ D.domain :=
  (Metric.closedBall_subset_closedBall (by linarith [D.radius_pos])).trans D.ball_subset
end Data

end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge
open Set MetricForms AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateSupport_small (p : A.centers) : coordinateSupport A p ⊆
    Metric.closedBall (extChartAt Model p.val p.val) (D p).radius := by
  rintro x ⟨y,hy,rfl⟩
  exact (D p).source_image_subset ⟨y,hD p hy,rfl⟩
include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateSupport_domain (p : A.centers) : coordinateSupport A p ⊆ (D p).domain :=
  (coordinateSupport_small A J α ht D hD p).trans (D p).small_ball_subset

def scalar (p : A.centers) (a : TwoForm X) (j : Fin 4) : Space → ℝ :=
  (D p).domain.indicator (fun x => localizedFunction A p a x ![(D p).frame 0 x,(D p).frame j x])

omit [T2Space X] [CompactSpace X] in
lemma scalar_zero_off (p : A.centers) (a : TwoForm X) (j : Fin 4)
    {x : Space} (hx : x ∉ coordinateSupport A p) : scalar A J α ht D p a j x = 0 := by
  unfold scalar
  by_cases he : x ∈ (D p).domain
  · rw [indicator_of_mem he,localizedFunction_zero_off A p a hx]
    rfl
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartEnergyIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldLocalization ManifoldHodge ContinuousAlternatingMap
open Set MetricForms AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_anti (p : A.centers) {a : TwoForm X}
    (ha : antiInvariantPart J a = a) {x : Space} (hx : x ∈ (extChartAt Model p.val).target) :
    (localizedFunction A p a x).compContinuousLinearMap (coordinateJ J p.val x) =
      -localizedFunction A p a x := by
  have hj : TamingCompatibility.jAction J a = -a := by
    calc TamingCompatibility.jAction J a = a - (2 : ℝ) • antiInvariantPart J a := by
          unfold antiInvariantPart
          module
         _ = -a := by rw [ha]; module
  have hp := pullback_jAction_chart (⟨J.endomorphism,J.square,J.smooth⟩ :
      SmoothAlmostComplex.AlmostComplexStructure X) a p.val hx
  change ManifoldForms.pullback (TamingCompatibility.jAction J a) (extChartAt Model p.val).symm x =
    (ManifoldForms.pullback a (extChartAt Model p.val).symm x).compContinuousLinearMap
      (coordinateJ J p.val x) at hp
  rw [hj] at hp
  have hn : ManifoldForms.pullback (-a) (extChartAt Model p.val).symm x =
    -ManifoldForms.pullback a (extChartAt Model p.val).symm x := rfl
  rw [hn] at hp
  unfold localizedFunction
  rw [indicator_of_mem hx]
  ext v
  change A.partition p ((extChartAt Model p.val).symm x) *
      ((ManifoldForms.pullback a (extChartAt Model p.val).symm x).compContinuousLinearMap
        (coordinateJ J p.val x)) v = _
  rw [← hp]
  simp only [ContinuousAlternatingMap.neg_apply,ContinuousAlternatingMap.smul_apply,
    smul_eq_mul,mul_neg]

include hD in
omit [T2Space X] [CompactSpace X] in
lemma scalar_expansion (p : A.centers) {a : TwoForm X} (ha : antiInvariantPart J a = a)
    (x : Space) : localizedFunction A p a x =
      scalar A J α ht D p a 2 x • realPart (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x) +
      scalar A J α ht D p a 3 x • imagPart (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x) := by
  by_cases hx : x ∈ (D p).domain
  · simp only [scalar,indicator_of_mem hx]
    obtain ⟨h0,h1,h2,h3⟩ := (D p).frame_complex x hx
    exact expansion (coordinateMetric J α ht p.val x) (by simp [Space])
      (fun i => (D p).frame i x) ((D p).frame_gram x hx)
      (coordinateJ J p.val x) h0 h1 h2 h3 (localizedFunction A p a x)
      (localizedFunction_anti A J p ha ((D p).domain_subset hx))
  · have hK : x ∉ coordinateSupport A p := fun h => hx (coordinateSupport_domain A J α ht D hD p h)
    rw [localizedFunction_zero_off A p a hK,scalar_zero_off A J α ht D p a 2 hK,
      scalar_zero_off A J α ht D p a 3 hK,zero_smul,zero_smul,add_zero]
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FramePairing
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume
open Set MetricForms AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include hD in
lemma localizedPairing_scalars (p : A.centers) {a : TwoForm X} (ha : antiInvariantPart J a = a)
    (z : Space) :
    pairing (coordinateMetric J α ht p.val z) (localizedFunction A p a z) (localizedFunction A p a z) =
      2 * ((scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) := by
  by_cases hz : z ∈ (D p).domain
  · rw [scalar_expansion A J α ht D hD p ha]
    exact pairing_combination _ (by simp [Space]) _ ((D p).frame_gram z hz) _ _
  · have hK : z ∉ coordinateSupport A p := fun h => hz (coordinateSupport_domain A J α ht D hD p h)
    rw [localizedFunction_zero_off A p a hK,scalar_zero_off A J α ht D p a 2 hK,
      scalar_zero_off A J α ht D p a 3 hK]
    simp only [(pairing_self_eq_zero _ _).mpr rfl,zero_pow (by decide : 2≠0),add_zero,mul_zero]
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartMetricBounds
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
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_neg_self (g : Metric E) {k : ℕ} (a : Form E k) : pairing g (-a) (-a) = pairing g a a := by
  rw [← neg_one_smul ℝ a,pairing_smul_left,pairing_smul_right]
  ring
end TamingCompatibility.MetricForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalSymbol
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
open EuclideanEnergy
open scoped RealInnerProductSpace

def normalSymbol (ξ : V) : Pair →L[ℝ] V :=
  combine (WithLp.toLp 2 ![-ξ 2,ξ 3,ξ 0,-ξ 1])
    (WithLp.toLp 2 ![-ξ 3,-ξ 2,ξ 1,ξ 0])

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : Data J α ht p)

def coordinateTest (q : Space → EuclideanEnergy.Pair) : Space → MetricForms.Form Space 2 :=
  frameTest (fun x => realPart (coordinateMetric J α ht p x) (fun i => D.frame i x))
    (fun x => imagPart (coordinateMetric J α ht p x) (fun i => D.frame i x)) q

omit [T2Space X] in
lemma coordinateTest_support (q : Space → EuclideanEnergy.Pair) :
    tsupport (coordinateTest J α ht p D q) ⊆ tsupport q := frameTest_tsupport _ _ _

def manifoldTest (q : Space → EuclideanEnergy.Pair) : TwoForm X :=
  antiInvariantPart J (chartLift p (coordinateTest J α ht p D q))

end TamingCompatibility.GeometricChart

end
end

end
end
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

def normalPrincipal (b : Fin 4 → V) (i : Fin 4) : Pair →L[ℝ] V :=
  normalSymbol (frameCovector b i)

def normalLower (g : Metric V) (F : MetricForms.Form V 2) (ψ χ : V → MetricForms.Form V 2)
    (b : Fin 4 → V) (x : V) : Pair →L[ℝ] V :=
  frameVector b ∘L starThreeCLM g F ∘L combine (extDeriv ψ x) (extDeriv χ x)

end TamingCompatibility.LocalMatrixOperator

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_ChartNormalTest
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def normalA (i : Fin 4) (z : Space) : EuclideanEnergy.Pair →L[ℝ] Space :=
  normalPrincipal (fun j => D.frame j z) i

def normalB (z : Space) : EuclideanEnergy.Pair →L[ℝ] Space :=
  normalLower (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
    (fun y => realPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (fun y => imagPart (coordinateMetric J α ht p y) (fun i => D.frame i y))
    (fun i => D.frame i z) z

end TamingCompatibility.GeometricChart

end
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

def lower (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (ψ φ : Fin 6 → V → MetricForms.Form V 2) (x : V) : W →L[ℝ] Q :=
  left b ∘L starThreeCLM g F ∘L combineThree (fun j => extDeriv (φ j) x) +
    right b ∘L starThreeCLM g F ∘L combineThree (fun j => extDeriv (ψ j) x)

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
open scoped ContDiff RealInnerProductSpace
namespace TamingCompatibility.HodgeGeometricCoefficients
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame HodgeNormalOperator
open HodgeNormalSymbol (W Q)

def starFrame (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (j : Fin 6) (x : V) : MetricForms.Form V 2 :=
  starTwo (g x) (J x) (F x) (frame g b j x)
def lower (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (x : V) : W →L[ℝ] Q :=
  HodgeNormalOperator.lower (g x) (F x) (fun i => b i x) (frame g b) (starFrame g J F b) x

end TamingCompatibility.HodgeGeometricCoefficients

end
end

end
end

end OAI
end


