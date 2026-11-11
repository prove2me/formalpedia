-- Prove2me | Definitions.Def_OAIQ239Tc012
-- name    : OAIQ239Tc012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:20:21.66833+00:00
-- url     : https://prove2.me/theorems/2c1aec42-fac6-415c-a71b-083cd315bdec
-- title:
--   Definitions bundle OAIQ239Tc012 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 84 declarations of OpenAI's Lean: 22 definitions, 1 instance and 61 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.CoordinateOperator.firstOrder`, `OAI.TamingCompatibility.HermitianRadial.logCutoffSourceSupported`, `OAI.TamingCompatibility.HermitianRadial.logErrorSchwartz`, `OAI.TamingCompatibility.HermitianRadial.logErrorSupported`, `OAI.TamingCompatibility.HermitianRadial.sqrtCutoffSourceSupported`, `OAI.TamingCompatibility.HermitianRadial.sqrtErrorSchwartz`, `OAI.TamingCompatibility.HermitianRadial.sqrtErrorSupported`, `OAI.TamingCompatibility.HilbertSobolev.interiorLift`, `OAI.TamingCompatibility.HilbertSobolev.linearH`, `OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace`, `OAI.TamingCompatibility.HilbertSobolev.secondCommutatorH`, `OAI.TamingCompatibility.HodgeFlatEnergy.delta`, `OAI.TamingCompatibility.HodgeFlatEnergy.energy`, `OAI.TamingCompatibility.HodgeFrame.reconstruct`, `OAI.TamingCompatibility.HodgeGeometricCoefficients.baseSymbol`, `OAI.TamingCompatibility.HodgeGeometricCoefficients.field`, `OAI.TamingCompatibility.HodgeMatrixEnergy.derivative`, `OAI.TamingCompatibility.HodgeMatrixEnergy.gradient`, `OAI.TamingCompatibility.HodgeNormalOperator.starCLM`, `OAI.TamingCompatibility.LocalRellich.realize`, `OAI.TamingCompatibility.ManifoldLocalization.localizedSchwartz`, `OAI.TamingCompatibility.UnitaryFrame.selfDualPart`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartLift`, `TamingCompatibility_Charts_FiniteCharts`, `TamingCompatibility_Charts_HermitianCutoffErrors`, `TamingCompatibility_Charts_HermitianCutoffSupported`, `TamingCompatibility_Charts_LocalInverse`, `TamingCompatibility_Charts_LocalSmooth`, `TamingCompatibility_Charts_ManifoldComplexDifferential`, `TamingCompatibility_DifferentialForms_AntiDdcBound`, `TamingCompatibility_DifferentialForms_Bessel`, `TamingCompatibility_DifferentialForms_ClosedGraphLift`, `TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding`, `TamingCompatibility_DifferentialForms_HermitianErrorSources`, `TamingCompatibility_DifferentialForms_QuantitativeInterior`, `TamingCompatibility_DifferentialForms_SymbolMap`, `TamingCompatibility_DifferentialForms_UnitaryFrame`, `TamingCompatibility_Elliptic_CriticalH1Linear`, `TamingCompatibility_Elliptic_NormalSystem`, `TamingCompatibility_Elliptic_SchwartzSobolev`, `TamingCompatibility_Elliptic_SobolevBounded`, `TamingCompatibility_Functional_NormalSymbol`, `TamingCompatibility_Hodge_HodgeFrameDifferential`, `TamingCompatibility_Hodge_HodgeFrameH1`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeFrozenEnergy`, `TamingCompatibility_Hodge_HodgeGeometricCoefficients`, `TamingCompatibility_Hodge_HodgeGeometricGarding`, `TamingCompatibility_Hodge_HodgeMatrixEnergy`, `TamingCompatibility_Hodge_HodgeNormalEnergy`, `TamingCompatibility_Hodge_HodgeScalarSquare`, `TamingCompatibility_Hodge_HodgeSymbol`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc005`, `OAIQ239Tc006`, `OAIQ239Tc007` and `OAIQ239Tc008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc015` and `OAIQ239Tc016`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc005
import Definitions.Def_OAIQ239Tc006
import Definitions.Def_OAIQ239Tc007
import Definitions.Def_OAIQ239Tc008

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

theorem closed_iff_exteriorDerivative_eq_zero {α : Form X k} (hα : Smooth α) :
    Closed α ↔ exteriorDerivative α = 0 := by
  constructor
  · intro h
    funext x
    have hz := h (extChartAt Model x).symm (extChartAt Model x).target
      (isOpen_extChartAt_target x) (contMDiffOn_extChartAt_symm x)
      (extChartAt Model x x) ((extChartAt Model x).map_source (mem_extChartAt_source x))
    rwa [extDerivWithin_eq_of_mem (isOpen_extChartAt_target x)
      ((extChartAt Model x).map_source (mem_extChartAt_source x))] at hz
  · intro h f U hU hf y hy
    rw [← pullback_exteriorDerivative α hα hU hf hy, h]
    ext v
    rfl

theorem exteriorDerivative_square {α : Form X k} (hα : Smooth α) :
    exteriorDerivative (exteriorDerivative α) = 0 := by
  funext x
  let e := extChartAt Model x
  let z := e x
  have hz : z ∈ e.target := e.map_source (mem_extChartAt_source x)
  have heq : pullback (exteriorDerivative α) e.symm =ᶠ[𝓝 z]
      extDeriv (pullback α e.symm) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    rw [pullback_exteriorDerivative α hα (isOpen_extChartAt_target x)
      (contMDiffOn_extChartAt_symm x) hy,
      extDerivWithin_eq_of_mem (isOpen_extChartAt_target x) hy]
  change extDeriv (pullback (exteriorDerivative α) e.symm) z = 0
  rw [heq.extDeriv_eq]
  apply extDeriv_extDeriv_apply
    (((smooth_chart α hα x) z hz).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz))
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

lemma Smooth.closed_exteriorDerivative {α : Form X k} (hα : Smooth α) :
    Closed (ManifoldForms.exteriorDerivative α) :=
  (closed_iff_exteriorDerivative_eq_zero hα.exteriorDerivative).mpr (exteriorDerivative_square hα)

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

omit [IsManifold Model ∞ X] [T2Space X] in
lemma liftSupport_subset (p : X) {β : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    (hβ : tsupport β ⊆ (extChartAt Model p).target) :
    liftSupport p β ⊆ (extChartAt Model p).source := by
  rintro _ ⟨z,hz,rfl⟩
  exact (extChartAt Model p).map_target (hβ hz)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma liftSupport_compact (p : X) {β : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    (hc : HasCompactSupport β) (hβ : tsupport β ⊆ (extChartAt Model p).target) :
    IsCompact (liftSupport p β) :=
  hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hβ)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma chartLift_zero_off (p : X) (β : Space → Space [⋀^Fin k]→L[ℝ] ℝ)
    {x : X} (hx : x ∉ liftSupport p β) : chartLift p β x = 0 := by
  unfold chartLift
  split_ifs with hs
  · have hz : extChartAt Model p x ∉ tsupport β := by
      intro hz
      exact hx ⟨_,hz,(extChartAt Model p).left_inv hs⟩
    rw [image_eq_zero_of_notMem_tsupport hz]
    rfl
  · rfl

lemma chartLift_smooth (p : X) {β : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    (hs : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hβ : tsupport β ⊆ (extChartAt Model p).target) : Smooth (chartLift p β) := by
  intro f U hU hf y hy
  have hfy := (hf y hy).contMDiffAt (hU.mem_nhds hy)
  by_cases hk : f y ∈ liftSupport p β
  · have hsrc := liftSupport_subset p hβ hk
    let g : Space → Space := (extChartAt Model p) ∘ f
    have hgy : ContMDiffAt Model Model ∞ g y :=
      (contMDiffAt_extChartAt' (I := Model) (by simpa only [extChartAt_source] using hsrc)).comp y hfy
    have hg : ContDiffAt ℝ ∞ g y := contMDiffAt_iff_contDiffAt.mp hgy
    have he : pullback (chartLift p β) f =ᶠ[𝓝 y]
        fun z => (β (g z)).compContinuousLinearMap (fderiv ℝ g z) := by
      have hne := hfy.continuousAt.eventually ((isOpen_extChartAt_source p).mem_nhds hsrc)
      filter_upwards [hne,hU.mem_nhds hy] with z hz hzU
      change f z ∈ (extChartAt Model p).source at hz
      have hfz := ((hf z hzU).contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt (by simp)
      have hez := (contMDiffAt_extChartAt' (I := Model) (n := ∞)
        (by simpa only [extChartAt_source] using hz)).mdifferentiableAt (by simp)
      simp only [pullback,chartLift,ite_eq_left hz]
      change (β (g z)).compContinuousLinearMap
        (mfderiv Model Model (extChartAt Model p) (f z) ∘L mfderiv Model Model f z) = _
      erw [← mfderiv_comp z hez hfz,mfderiv_eq_fderiv]
      rfl
    exact (((hs.contDiffAt.comp y hg).compAlternating
      (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).congr_of_eventuallyEq he).contDiffWithinAt
  · have hne := hfy.continuousAt.eventually
      ((liftSupport_compact p hc hβ).isClosed.isOpen_compl.mem_nhds hk)
    have he : pullback (chartLift p β) f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hne] with z hz
      unfold pullback
      rw [chartLift_zero_off p β hz]
      rfl
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

end TamingCompatibility.ManifoldForms

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

omit [T2Space X] in
lemma localizedFunction_smooth_compact {k : ℕ} (p : A.centers)
    (α : ManifoldForms.Form X k) (hα : ManifoldForms.Smooth α) :
    ContDiff ℝ ∞ (localizedFunction A p α) ∧ HasCompactSupport (localizedFunction A p α) := by
  apply smooth_indicator_of_compact (isOpen_extChartAt_target p.val)
    (coordinateSupport_compact A p) (coordinateSupport_subset A p)
  · have hρ : ContDiffOn ℝ ∞
        (fun y => A.partition p ((extChartAt Model p.val).symm y))
        (extChartAt Model p.val).target := by
      exact (A.partition p).contMDiff.comp_contMDiffOn
        (contMDiffOn_extChartAt_symm p.val) |>.contDiffOn
    exact hρ.smul (ManifoldForms.smooth_chart α hα p.val)
  · intro y hy hK
    have hz : (extChartAt Model p.val).symm y ∉ tsupport (A.partition p) := by
      intro h
      apply hK
      exact ⟨(extChartAt Model p.val).symm y,h,(extChartAt Model p.val).right_inv hy⟩
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]

def localizedSchwartz {k : ℕ} (p : A.centers)
    (α : ManifoldForms.Form X k) (hα : ManifoldForms.Smooth α) :
    𝓢(Space,Space [⋀^Fin k]→L[ℝ] ℝ) :=
  (localizedFunction_smooth_compact A p α hα).2.toSchwartzMap
    (localizedFunction_smooth_compact A p α hα).1

end TamingCompatibility.ManifoldLocalization

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

def selfDualPart (a : W) : W := (1 / 2 : ℝ) • (a + star a)

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalSymbol
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
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame Function Set
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

lemma frameTest_compact (ψ χ : V → MetricForms.Form V 2) {q : V → Pair}
    (hq : HasCompactSupport q) : HasCompactSupport (frameTest ψ χ q) :=
  hq.of_isClosed_subset (isClosed_tsupport _) (frameTest_tsupport ψ χ q)

end TamingCompatibility.LocalMatrixOperator

namespace TamingCompatibility.ManifoldForms
open Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma pullback_antiInvariantPart (J : AlmostComplexStructure X) (a : TwoForm X)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    pullback (antiInvariantPart J a) (extChartAt Model p).symm z =
      (1/2:ℝ) • (pullback a (extChartAt Model p).symm z -
        (pullback a (extChartAt Model p).symm z).compContinuousLinearMap
          (ManifoldHodge.coordinateJ J p z)) := by
  have h := pullback_jAction_chart (⟨J.endomorphism,J.square,J.smooth⟩ :
    SmoothAlmostComplex.AlmostComplexStructure X) a p hz
  change pullback (TamingCompatibility.jAction J a) (extChartAt Model p).symm z =
    (pullback a (extChartAt Model p).symm z).compContinuousLinearMap
      (ManifoldHodge.coordinateJ J p z) at h
  rw [← h]
  rfl

end TamingCompatibility.ManifoldForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldComplexDifferential
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

lemma pullback_complexDifferential (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    pullback (complexDifferential J f) (extChartAt Model p).symm z =
      ExteriorForms.dc (coordinateJ J p) (f ∘ (extChartAt Model p).symm) z := by
  have hg := (((contMDiffOn_extChartAt_symm (n := ∞) p) z hz).contMDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).mdifferentiableAt (by simp)
  unfold ExteriorForms.dc
  rw [← mfderiv_eq_fderiv,mfderiv_comp z (hf.mdifferentiable (by simp) _) hg]
  ext v
  have hi := coordinateJ_intertwine J p hz (v 0)
  change (inverseChartEquiv p z hz).toContinuousLinearMap (coordinateJ J p z (v 0)) =
    J.endomorphism _ ((inverseChartEquiv p z hz).toContinuousLinearMap (v 0)) at hi
  rw [inverseChartEquiv_coe] at hi
  change -(mfderiv Model 𝓘(ℝ,ℝ) f _) (J.endomorphism _ (mfderiv Model Model _ z (v 0))) =
    -(mfderiv Model 𝓘(ℝ,ℝ) f _) (mfderiv Model Model _ z (coordinateJ J p z (v 0)))
  exact congrArg (fun w => -(mfderiv Model 𝓘(ℝ,ℝ) f ((extChartAt Model p).symm z)) w) hi.symm

lemma complexDifferential_smooth (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) : Smooth (complexDifferential J f) := by
  apply smooth_of_charts
  intro p
  have hc : ContDiffOn ℝ ∞ (f ∘ (extChartAt Model p).symm) (extChartAt Model p).target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)).contDiffOn
  have hd := hc.fderiv_of_isOpen (isOpen_extChartAt_target p) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := ((ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)).contDiff.comp_contDiffOn
    ((hd.clm_comp (coordinateJ_smooth J p)).neg))
  apply he.congr
  intro z hz
  exact pullback_complexDifferential J hf p hz

end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiDdcBound
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
open ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma ddc_smooth_closed (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    IsSmooth (exteriorDerivative (complexDifferential J f)) ∧
      IsClosed (exteriorDerivative (complexDifferential J f)) :=
  ⟨(complexDifferential_smooth J hf).exteriorDerivative,
    (complexDifferential_smooth J hf).closed_exteriorDerivative⟩

end TamingCompatibility.ManifoldForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]

lemma cutoffLogError_tsupport (W : E → E →L[ℝ] E) (V : E → E) {R : ℝ} (hR : 0 < R) (p : ℝ × E) :
    tsupport (cutoffLogError W V R p) ⊆ closedBall (0:E) (2*R) := by
  apply (tsupport_mul_subset_right.trans ?_).trans (scaledCutoff_tsupport hR)
  exact (firstOrderSource_tsupport (fun z => V (p.2+z)) (scaledCutoff R))

lemma cutoffSqrtError_tsupport (W : E → E →L[ℝ] E) (V : E → E) {R : ℝ} (hR : 0 < R) (p : ℝ × E) :
    tsupport (cutoffSqrtError W V R p) ⊆ closedBall (0:E) (2*R) := by
  apply (tsupport_mul_subset_right.trans ?_).trans (scaledCutoff_tsupport hR)
  exact (firstOrderSource_tsupport (fun z => V (p.2+z)) (scaledCutoff R))

end TamingCompatibility.HermitianRadial

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_NormalSystem
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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

lemma frameVector_apply (b : Fin 4 → V) (a : MetricForms.Form V 1) (i : Fin 4) :
    frameVector b a i = a ![b i] := rfl

lemma frameVector_pairing (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a c : MetricForms.Form V 1) :
    ⟪frameVector b a,frameVector b c⟫ = pairing g a c := by
  rw [pairing_one_eq_sum g (by simp [V]) b hb]
  simp only [PiLp.inner_apply,frameVector_apply,RCLike.inner_apply,conj_trivial,mul_comm]

end TamingCompatibility.LocalMatrixOperator

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

theorem localInverse_compact_of_support [ProperSpace F]
    (K : Set E) (hK : IsCompact K)
    (g : Lp ℂ ∞ (volume : Measure E)) (g₂ : Lp ℂ 2 (volume : Measure E))
    (heq : g₂ =ᵐ[volume] g) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g₂ ξ = 0) :
    IsCompactOperator (localInverse (F := F) K hK.measurableSet g) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (localMeasure (volume : Measure E) K) :=
    finite_localMeasure volume K hK.measurableSet hK.measure_lt_top
  let loc : C(K,E) := ⟨Subtype.val, continuous_subtype_val⟩
  let A := CompactKernel.operator (kernel (F := F) loc g₂ hR hs)
  let B := BoundedContinuousFunction.toLp (E := F) 2 (localMeasure (volume : Measure E) K) ℝ
  have hA : IsCompactOperator (A.restrictScalars ℝ) := compact_inverse_cutoff loc g₂ hR hs
  have hcomp : IsCompactOperator (B ∘L A.restrictScalars ℝ) := hA.clm_comp B
  convert hcomp using 1
  all_goals try with_reducible_and_instances rfl
  ext u
  have hmult : multiply g₂ u =ᵐ[volume] multiplyLp g u := by
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) g₂ u,
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) g u, heq] with ξ h1 h2 h3
    change (g₂ • u : Lp F 1 (volume : Measure E)) ξ =
      (g • u : Lp F 2 (volume : Measure E)) ξ
    rw [h1,h2]
    change g₂ ξ • u ξ = g ξ • u ξ
    rw [h3]
  have hi := inverse_L1_L2 (multiply g₂ u) (multiplyLp g u) hmult
  have hil := (measurePreserving_subtype_coe (μa := (volume : Measure E))
    hK.measurableSet).quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hi)
  filter_upwards [restrict_coe volume K hK.measurableSet
    (𝓕⁻ (g • u : Lp F 2 (volume : Measure E))),
    BoundedContinuousFunction.coeFn_toLp 2 (localMeasure (volume : Measure E) K) ℝ (A u),
    hil] with x h1 h2 h3
  change restrict volume K hK.measurableSet (𝓕⁻ (g • u : Lp F 2 (volume : Measure E))) x = B (A u) x
  rw [h1,h2]
  exact h3.symm.trans (inverse_cutoff_apply loc g₂ hR hs u x).symm

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

theorem localInverse_compact_of_decay [ProperSpace F]
    (K : Set E) (hK : IsCompact K) (g : E →ᵇ ℂ)
    (hd : ∀ ε > 0, ∃ R ≥ 0, ∀ ξ : E, R < ‖ξ‖ → ‖g ξ‖ ≤ ε) :
    IsCompactOperator (localInverse (F := F) K hK.measurableSet (g.memLp_top.toLp g)) := by
  have hc : _root_.IsClosed {f : Lp F 2 (volume : Measure E) →L[ℝ]
      Lp F 2 (localMeasure volume K) | IsCompactOperator f} :=
    isClosed_setOfPred_isCompactOperator
  refine hc.closure_subset ((Metric.mem_closure_iff
    (α := Lp F 2 (volume : Measure E) →L[ℝ] Lp F 2 (localMeasure volume K))
    (s := {f | IsCompactOperator f})).mpr ?_)
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hd (ε/2) (half_pos hε)
  let c := (cutoff_memLp_top g R).toLp (cutoff g R)
  refine ⟨localInverse (F := F) K hK.measurableSet c, ?_, ?_⟩
  · exact localInverse_compact_of_support (F := F) K hK c
      ((cutoff_memLp_two g R).toLp (cutoff g R)) (cutoff_lp_eq g R) hR (cutoff_support g R)
  · have hh : ‖localInverse K hK.measurableSet (g.memLp_top.toLp g) -
        localInverse (F := F) K hK.measurableSet c‖ < ε := by
      apply lt_of_le_of_lt (localInverse_sub_norm_le K hK.measurableSet _ _)
      exact (tail_norm_le (le_of_lt (half_pos hε)) ht).trans_lt (half_lt_self hε)
    have he : dist (localInverse (F := F) K hK.measurableSet (g.memLp_top.toLp g))
        (localInverse K hK.measurableSet c) =
        ‖localInverse K hK.measurableSet (g.memLp_top.toLp g) -
          localInverse (F := F) K hK.measurableSet c‖ := dist_eq_norm
      (localInverse (F := F) K hK.measurableSet (g.memLp_top.toLp g))
      (localInverse (F := F) K hK.measurableSet c)
    rw [he]
    exact hh

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
namespace TamingCompatibility.LocalRellich
open _root_.MeasureTheory HilbertSobolev LocalRestriction
open scoped ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def realize (K : Set E) (hK : MeasurableSet K) {s : ℝ} (hs : 0 ≤ s) :
    H E F s →L[ℝ] Lp F 2 (localMeasure volume K) :=
  restrict volume K hK ∘L (inclusion hs).restrictScalars ℝ

theorem realize_compact [ProperSpace F] (K : Set E) (hK : IsCompact K)
    {s : ℝ} (hs : 0 < s) : IsCompactOperator (realize (F := F) K hK.measurableSet hs.le) := by
  have hc := localInverse_compact_of_decay (F := F) K hK
    (RellichWeight.bessel (E := E) s hs.le) (RellichWeight.bessel_decay s hs)
  have hcomp := hc.comp_clm
    ((Lp.fourierTransformₗᵢ E F).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
  convert hcomp using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  change restrict volume K hK.measurableSet
      ((Lp.fourierTransformₗᵢ E F).symm
        (((weight_memLp_top (E := E) (sub_nonpos.mpr hs.le)).toLp (weight (E := E) (0 - s))) •
          (Lp.fourierTransformₗᵢ E F) u)) =
    restrict volume K hK.measurableSet
      ((Lp.fourierTransformₗᵢ E F).symm
        ((((RellichWeight.bessel (E := E) s hs.le).memLp_top (μ := volume)).toLp (RellichWeight.bessel (E := E) s hs.le)) •
          (Lp.fourierTransformₗᵢ E F) u))
  congr 3
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (weight_memLp_top (E := E) (sub_nonpos.mpr hs.le)),
    MemLp.coeFn_toLp ((RellichWeight.bessel (E := E) s hs.le).memLp_top (μ := volume))] with ξ h1 h2
  rw [h1, h2]
  simp [weight, RellichWeight.bessel]

end TamingCompatibility.LocalRellich

end

end OAI
end

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

def secondCommutatorH (n : ℕ) (g : 𝓢(E,ℂ)) (v w : E) :
    H E F ((n:ℝ)+1) →L[ℂ] H E F n :=
  product n (∂_{v} (∂_{w} g) : 𝓢(E,ℂ)) ∘L inclusion (by linarith : (n:ℝ) ≤ n+1) +
  product n (∂_{w} g : 𝓢(E,ℂ)) ∘L derivative ((n:ℝ)+1) v +
  product n (∂_{v} g : 𝓢(E,ℂ)) ∘L derivative ((n:ℝ)+1) w

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalSmooth
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
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory Set Filter
open scoped SchwartzMap Topology ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma local_all_orders_smooth {U : Set E} {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolevLoc U n u)
    (χ : 𝓢(E,ℂ)) (hc : HasCompactSupport (χ : E → ℂ)) (hχ : tsupport χ ⊆ U) :
    ∃ g : E →ᵇ F, ContDiff ℝ ∞ (g : E → F) ∧
      smulLeftCLM F χ u = EuclideanSobolev.boundedDistribution g := by
  apply EuclideanSobolev.exists_smooth_representative
  intro s
  obtain ⟨n,hn⟩ := exists_nat_gt s
  exact (hu n χ hc hχ).mono (le_of_lt hn)

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory Set Filter
open scoped SchwartzMap Topology ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma smooth_representative_on_cutoff {U V : Set E} {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolevLoc U n u) (ψ : 𝓢(E,ℂ))
    (hψ : HasCompactSupport (ψ : E → ℂ)) (hψU : tsupport ψ ⊆ U)
    (hone : ∀ x ∈ V, ψ x = 1) :
    ∃ g : E →ᵇ F, ContDiff ℝ ∞ (g : E → F) ∧ ∀ χ : 𝓢(E,ℂ),
      HasCompactSupport (χ : E → ℂ) → tsupport χ ⊆ V →
      smulLeftCLM F χ u = smulLeftCLM F χ (EuclideanSobolev.boundedDistribution g) := by
  obtain ⟨g,hg,he⟩ := local_all_orders_smooth (u := u) hu ψ hψ hψU
  refine ⟨g,hg,fun χ _ hχV => ?_⟩
  rw [← he]
  exact (local_cutoff_one ψ χ (fun x hx => hone x (hχV hx)) u).symm

lemma exists_local_smooth_representative {U : Set E} (hU : IsOpen U) {p : E} (hp : p ∈ U)
    {u : 𝓢'(E,F)} (hu : ∀ n : ℕ, MemSobolevLoc U n u) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∃ g : E →ᵇ F,
      ContDiff ℝ ∞ (g : E → F) ∧ ∀ χ : 𝓢(E,ℂ), HasCompactSupport (χ : E → ℂ) →
        tsupport χ ⊆ V → smulLeftCLM F χ u = smulLeftCLM F χ (EuclideanSobolev.boundedDistribution g) := by
  obtain ⟨φ,hφ,hφU,V,hV,hpV,hVU,hφone⟩ := SchwartzCutoff.exists_one_near (E := E) (U := U) (p := p) hU hp
  let ψ : 𝓢(E,ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hψ : HasCompactSupport (ψ : E → ℂ) :=
    hφ.of_isClosed_subset (isClosed_tsupport ψ) (postcomp_real_tsupport φ)
  have hψU : tsupport ψ ⊆ U := (postcomp_real_tsupport φ).trans hφU
  refine ⟨V,hV,hpV,hVU,?_⟩
  apply smooth_representative_on_cutoff hu ψ hψ hψU
  intro x hx
  change (φ x : ℂ) = 1
  rw [hφone x hx,Complex.ofReal_one]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedGraphLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section


namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def localSolutionSpace (U : Set E) (n : ℕ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) :
    Submodule ℂ (H E F 1 × H E F n) :=
  ⨅ (g : 𝓢(E,ℂ)) (_ : HasCompactSupport (g : E → ℂ)) (_ : tsupport g ⊆ U),
    LinearMap.ker ((smulLeftCLM F g).comp
      ((P.comp (toDistribution E F 1)).comp (ContinuousLinearMap.fst ℂ _ _) -
       (toDistribution E F n).comp (ContinuousLinearMap.snd ℂ _ _))).toLinearMap

instance localSolutionSpace_complete (U : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) : CompleteSpace (localSolutionSpace U n P) := by
  have h : _root_.IsClosed (↑(localSolutionSpace U n P) : Set (H E F 1 × H E F n)) := by
    unfold localSolutionSpace
    simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun g => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      ContinuousLinearMap.isClosed_ker _
  exact h.completeSpace_coe

def interiorLift (U : Set E) (n : ℕ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (g : 𝓢(E,ℂ))
    (h : ∀ u : localSolutionSpace U n P,
      MemSobolev ((n:ℝ)+2) 2 (smulLeftCLM F g (toDistribution E F 1 u.val.1))) :
    localSolutionSpace U n P →L[ℂ] H E F ((n:ℝ)+2) := by
  let j : localSolutionSpace U n P →L[ℂ] 𝓢'(E,F) := (smulLeftCLM F g).comp ((toDistribution E F 1).comp
    ((ContinuousLinearMap.fst ℂ _ _).comp (localSolutionSpace U n P).subtypeL))
  refine InjectiveLinearLift.continuousLift (toDistribution E F ((n:ℝ)+2))
    (toDistribution_injective ((n:ℝ)+2)) j (fun u => ?_)
  change j u ∈ Set.range (toDistribution E F ((n:ℝ)+2))
  rw [range_toDistribution]
  exact h u

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SchwartzSobolev
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete
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

lemma schwartzToH_spec (s : ℝ) (f : 𝓢(E,F)) :
    toDistribution E F s (schwartzToH s f) = (f : 𝓢'(E,F)) := by
  rw [toDistribution,ContinuousLinearMap.comp_apply,schwartzToH,
    ContinuousLinearMap.comp_apply,SchwartzMap.toLpCLM_apply,
    Lp.toTemperedDistributionCLM_apply]
  rw [besselPotential_neg_apply_eq_iff]
  rw [besselPotential,Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]

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

lemma schwartzToH_derivative (s : ℝ) (v : E) (f : 𝓢(E,F)) :
    schwartzToH (s-1) (∂_{v} f) = derivative s v (schwartzToH s f) := by
  apply toDistribution_injective (s-1)
  rw [schwartzToH_spec,toDistribution_derivative,schwartzToH_spec]
  exact (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq f v).symm

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalH1Linear
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
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance localInst_r804955_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
def linearH (n : ℕ) (L : E ≃L[ℝ] E) : H E F n →L[ℂ] H E F n :=
  liftOperator (linearDistribution L) (fun _ h => memSobolev_nat_linear n L h)

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianErrorSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [ProperSpace E] in
lemma shiftedLogError_support (W : E → E →L[ℝ] E) (V : E → E) {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (shiftedLogError W V R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffLogError_tsupport W V hR (s,b))
omit [ProperSpace E] in
lemma shiftedSqrtError_support (W : E → E →L[ℝ] E) (V : E → E) {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (shiftedSqrtError W V R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffSqrtError_tsupport W V hR (s,b))

variable (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) {R : ℝ} (hR : 0 < R)

def logErrorSchwartz (s : ℝ) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogError W V R s b) :=
    (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogError_support W V hR s b)
  exact hc.toSchwartzMap (shiftedLogError_smooth W V hW hV hR s b)
def sqrtErrorSchwartz (s : ℝ) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtError W V R s b) :=
    (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtError_support W V hR s b)
  exact hc.toSchwartzMap (shiftedSqrtError_smooth W V hW hV hR s b)

def logErrorSupported (K : Set E) (s : ℝ) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K :=
  ⟨logErrorSchwartz W V hW hV hR s b,(shiftedLogError_support W V hR s b).trans hb⟩
def sqrtErrorSupported (K : Set E) (s : ℝ) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtErrorSchwartz W V hW hV hR s b,(shiftedSqrtError_support W V hR s b).trans hb⟩

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_HermitianCutoffSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E)

variable (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)

def logCutoffSourceSupported (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K := by
  let f := firstOrderSource V (translatedCutoffLog W R s b)
  have hf : ContDiff ℝ ∞ f := firstOrderSource_smooth V hV _ (translatedCutoffLog_smooth W R hs b)
  have hc : HasCompactSupport f := (translatedCutoffLog_compact W hR s b).of_isClosed_subset
    (isClosed_tsupport _) (firstOrderSource_tsupport _ _)
  exact ⟨hc.toSchwartzMap hf, ((firstOrderSource_tsupport _ _).trans
    (translatedCutoffLog_support W hR s b)).trans hb⟩
def sqrtCutoffSourceSupported (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K := by
  let f := firstOrderSource V (translatedCutoffSqrt W R s b)
  have hf : ContDiff ℝ ∞ f := firstOrderSource_smooth V hV _ (translatedCutoffSqrt_smooth W R hs b)
  have hc : HasCompactSupport f := (translatedCutoffSqrt_compact W hR s b).of_isClosed_subset
    (isClosed_tsupport _) (firstOrderSource_tsupport _ _)
  exact ⟨hc.toSchwartzMap hf, ((firstOrderSource_tsupport _ _).trans
    (translatedCutoffSqrt_support W hR s b)).trans hb⟩

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMatrixEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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
def derivative (f : Field) (i : Fin 4) (x : V) : W :=
  value (fun j => coordinateDeriv i (f j)) x
def gradient (f : Field) (x : V) : ℝ := ∑ i : Fin 4, ‖derivative f i x‖^2

lemma value_integrable (f : Field) : Integrable (fun x => ‖value f x‖^2) := by
  simp_rw [value_norm]
  exact integrable_finsetSum _ (fun j _ => schwartz_sq_integrable (f j))
lemma gradient_integrable (f : Field) : Integrable (gradient f) :=
  integrable_finsetSum _ (fun i _ => value_integrable (fun j => coordinateDeriv i (f j)))
lemma gradient_nonneg (f : Field) (x : V) : 0 ≤ gradient f x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end TamingCompatibility.HodgeMatrixEnergy

end
end

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy

lemma normalSymbol_polarized (ξ η : V) (a b : W) :
    ⟪normalSymbol ξ a,normalSymbol η b⟫ + ⟪normalSymbol η a,normalSymbol ξ b⟫ =
      2*⟪ξ,η⟫*⟪a,b⟫ := by
  simp only [PiLp.inner_apply]
  simp [normalSymbol_apply,symbol,UnitaryFrame.interior,UnitaryFrame.star,Fin.sum_univ_succ]
  ring

end TamingCompatibility.HodgeNormalSymbol

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSymbol
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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
namespace TamingCompatibility.UnitaryFrame

theorem hodge_symbol_energy (ξ : V) (a : W) :
    ‖interior ξ a‖^2 + ‖interior ξ (star a)‖^2 = ‖ξ‖^2*‖a‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  simp [interior,star,Fin.sum_univ_succ]
  ring
end TamingCompatibility.UnitaryFrame

end
end

section
noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace
namespace TamingCompatibility.HodgeFlatEnergy
open EuclideanEnergy
open DirectionalEnergy (directionDeriv)

def delta (b : Fin 4 → V) (a : Fin 6 → S) : Fin 4 → S :=
  ![-directionDeriv b 1 (a 0)-directionDeriv b 2 (a 1)-directionDeriv b 3 (a 2),
    directionDeriv b 0 (a 0)-directionDeriv b 2 (a 3)-directionDeriv b 3 (a 4),
    directionDeriv b 0 (a 1)+directionDeriv b 1 (a 3)-directionDeriv b 3 (a 5),
    directionDeriv b 0 (a 2)+directionDeriv b 1 (a 4)+directionDeriv b 2 (a 5)]

def energy (b : Fin 4 → V) (a : Fin 6 → S) : ℝ :=
  (∑ i, pairing (delta b a i) (delta b a i)) + ∑ i, pairing (delta b (star a) i) (delta b (star a) i)
end TamingCompatibility.HodgeFlatEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrozenEnergy
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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

lemma basisForm_apply (g : Metric E) (b : Fin 4 → E) (j : Fin 6) (u v : E) :
    basisForm g b j ![u,v] = g.bilinear (b (pairLeft j)) u * g.bilinear (b (pairRight j)) v -
      g.bilinear (b (pairLeft j)) v * g.bilinear (b (pairRight j)) u :=
  AntiInvariantFrame.covectorWedge_apply _ _ _ _

def reconstruct (g : Metric E) (b : Fin 4 → E) : W →L[ℝ] MetricForms.Form E 2 :=
  ∑ i, (EuclideanSpace.proj i).smulRight (basisForm g b i)
lemma reconstruct_apply (g : Metric E) (b : Fin 4 → E) (a : W) :
    reconstruct g b a = ∑ i, a i • basisForm g b i := by
  simp only [reconstruct,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

lemma coordinates_basisForm (g : Metric E) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (i j : Fin 6) :
    coordinates b (basisForm g b j) i = if i=j then 1 else 0 := by
  rw [coordinates_apply,basisForm_apply]
  simp only [hb]
  fin_cases i <;> fin_cases j <;> (first | (simp [pairLeft,pairRight,Fin.ext_iff]; all_goals first | (norm_num [pairLeft,pairRight,Fin.ext_iff]; done) | rfl | decide) | (norm_num [pairLeft,pairRight,Fin.ext_iff]; done) | norm_num [pairLeft,pairRight,Fin.ext_iff])

lemma coordinates_reconstruct (g : Metric E) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a : W) :
    coordinates b (reconstruct g b a) = a := by
  ext i
  rw [reconstruct_apply]
  simp only [coordinates_apply,ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  simp_rw [← coordinates_apply,coordinates_basisForm g b hb]
  simp

variable [FiniteDimensional ℝ E]

lemma reconstruct_coordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a : MetricForms.Form E 2) :
    reconstruct g b (coordinates b a) = a := by
  apply coordinates_injective g hdim b hb
  exact coordinates_reconstruct g b hb _

lemma basisForm_smooth {g : D → Metric E} {b : Fin 4 → D → E} {U : Set D}
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (j : Fin 6) :
    ContDiffOn ℝ ∞ (fun x => basisForm (g x) (fun i => b i x) j) U := by
  apply FormSmooth.contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have hv : (fun i => Module.finBasis ℝ E (a i)) =
      ![Module.finBasis ℝ E (a 0),Module.finBasis ℝ E (a 1)] := by ext i; fin_cases i <;> rfl
  simp only [hv,basisForm_apply]
  exact (((hg.clm_apply (hb (pairLeft j))).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb (pairRight j))).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb (pairLeft j))).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb (pairRight j))).clm_apply contDiffOn_const))

lemma coordinates_model (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a : MetricForms.Form E 2) :
    coordinates b a = GeometricSymbol.coords (basisOfFrame g hdim b hb) (formEquiv g 2 a) := by
  ext i
  fin_cases i <;> simp [coordinates_apply,GeometricSymbol.coords,pairLeft,pairRight,
    formEquiv_apply] <;> rfl

end TamingCompatibility.HodgeFrame

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameDifferential
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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

lemma combineThree_apply (a : Fin 6 → MetricForms.Form V 3) (u : W) :
    combineThree a u = ∑ j, u j • a j := by
  simp only [combineThree,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

lemma extDeriv_frame (f : Fin 6 → V → ℝ) (a : Fin 6 → V → MetricForms.Form V 2)
    {x : V} (hf : ∀ j, DifferentiableAt ℝ (f j) x)
    (ha : ∀ j, DifferentiableAt ℝ (a j) x) :
    extDeriv (fun y => ∑ j, f j y • a j y) x =
      (∑ j, f j x • extDeriv (a j) x) +
      ∑ i : Fin 4, wedgeOne (EuclideanSpace.proj i)
        (∑ j : Fin 6, (fderiv ℝ (f j) x (e i)) • a j x) := by
  rw [extDeriv_sum (f := fun j y => f j y • a j y) (fun j => (hf j).smul (ha j))]
  simp_rw [extDeriv_variable_smul (hf _) (ha _)]
  rw [Finset.sum_add_distrib]
  congr 1
  have he (j : Fin 6) : wedgeOne (fderiv ℝ (f j) x) (a j x) =
      ∑ i : Fin 4, (fderiv ℝ (f j) x (e i)) • wedgeOne (EuclideanSpace.proj i) (a j x) := by
    conv_lhs => rw [LocalMatrixOperator.covector_expansion (fderiv ℝ (f j) x)]
    change (wedgeOneRight (a j x)) (∑ i, (fderiv ℝ (f j) x (e i)) • EuclideanSpace.proj i) = _
    simp only [_root_.map_sum,_root_.map_smul,wedgeOneRight_apply]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change _ = wedgeBy (EuclideanSpace.proj i) (∑ j, (fderiv ℝ (f j) x (e i)) • a j x)
  simp only [_root_.map_sum,_root_.map_smul,wedgeBy_apply]

end TamingCompatibility.HodgeFrame

end
end

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open HodgeNormalSymbol (W)
open FormMetric (pairLeft pairRight)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (J : E →L[ℝ] E) (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hb h0 h1 h2 h3 hF hdim horth

omit horth in
lemma star_wedge_coordinate (ξ : E →L[ℝ] ℝ) (a : MetricForms.Form E 2) (i : Fin 4) :
    starThree g F (wedgeOne ξ a) ![b i] =
      UnitaryFrame.interior (WithLp.toLp 2 (fun j => ξ (b j))) (UnitaryFrame.star (coordinates b a)) i := by
  rw [AntiInvariantFrame.starThree_on_frame g hdim b hb J h0 h1 h2 h3 F hF]
  have ht : (fun l => b (FormMetric.tripleIndices i l)) =
      ![b (FormMetric.tripleIndices i 0),b (FormMetric.tripleIndices i 1),b (FormMetric.tripleIndices i 2)] := by
    ext l; fin_cases l <;> rfl
  rw [ht,wedgeOne_apply_three]
  fin_cases i <;>
    simp [UnitaryFrame.interior,UnitaryFrame.star,coordinates_apply,
      FormMetric.tripleIndices,pairLeft,pairRight] <;> ring

end TamingCompatibility.HodgeFrame

end
end

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame
open HodgeNormalSymbol (W Q)

lemma left_apply (b : Fin 4 → V) (a : MetricForms.Form V 1) :
    left b a = join (LocalMatrixOperator.frameVector b a) 0 := rfl
lemma right_apply (b : Fin 4 → V) (a : MetricForms.Form V 1) :
    right b a = join 0 (LocalMatrixOperator.frameVector b a) := rfl
lemma join_norm_sq (u v : V) : ‖join u v‖^2 = ‖u‖^2+‖v‖^2 := by
  simp [join,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  ring
lemma left_add_right (b : Fin 4 → V) (a c : MetricForms.Form V 1) :
    left b a + right b c = join (LocalMatrixOperator.frameVector b a) (LocalMatrixOperator.frameVector b c) := by
  ext i; fin_cases i <;> simp [left_apply,right_apply,join]
lemma output_norm (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a c : MetricForms.Form V 1) :
    ‖left b a+right b c‖^2 = pairing g a a+pairing g c c := by
  rw [left_add_right,join_norm_sq,← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq,LocalMatrixOperator.frameVector_pairing g b hb,
    LocalMatrixOperator.frameVector_pairing g b hb]

lemma combine_basis (g : Metric V) (b : Fin 4 → V) (u : W) :
    combine (basisForm g b) u = reconstruct g b u := rfl
def starCLM (g : Metric V) (J : V →L[ℝ] V) (F : MetricForms.Form V 2) :
    MetricForms.Form V 2 →L[ℝ] MetricForms.Form V 2 :=
  ((MetricForms.pairingCLM g 2).flip F).smulRight F - compContinuousLinearMapCLM J
lemma starCLM_apply (g : Metric V) (J : V →L[ℝ] V) (F a : MetricForms.Form V 2) :
    starCLM g J F a = starTwo g J F a := rfl

lemma combine_star_basis (g : Metric V) (J : V →L[ℝ] V) (F : MetricForms.Form V 2)
    (b : Fin 4 → V) (u : W) :
    combine (fun j => starTwo g J F (basisForm g b j)) u = starTwo g J F (reconstruct g b u) := by
  rw [combine_apply,reconstruct_apply]
  change _ = starCLM g J F (∑ j, u j • basisForm g b j)
  simp only [_root_.map_sum,_root_.map_smul,starCLM_apply]

end TamingCompatibility.HodgeNormalOperator

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricCoefficients
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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

def baseSymbol (u : W) : V →L[ℝ] Q := LinearMap.toContinuousLinearMap {
  toFun := fun ξ => HodgeNormalSymbol.symbol ξ u
  map_add' := by
    intro a b; ext i; fin_cases i <;>
      simp [HodgeNormalSymbol.symbol,UnitaryFrame.interior] <;> ring
  map_smul' := by
    intro c a; ext i; fin_cases i <;>
      simp [HodgeNormalSymbol.symbol,UnitaryFrame.interior] <;> ring }

lemma principal_smooth {b : Fin 4 → V → V} {U : Set V}
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (i : Fin 4) :
    ContDiffOn ℝ ∞ (principal b i) U := by
  apply contDiffOn_clm_apply.mpr
  intro u
  change ContDiffOn ℝ ∞ (fun x => baseSymbol u (WithLp.toLp 2 (fun j => b j x i))) U
  apply (baseSymbol u).contDiff.comp_contDiffOn
  apply (contDiffOn_piLp 2).mpr
  intro j
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn (hb j)

lemma frame_smooth {g : V → Metric V} {b : Fin 4 → V → V} {U : Set V}
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (j : Fin 6) :
    ContDiffOn ℝ ∞ (frame g b j) U := basisForm_smooth hg hb j

lemma frameVector_smooth {b : Fin 4 → V → V} {a : V → MetricForms.Form V 1} {U : Set V}
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (fun x => LocalMatrixOperator.frameVector (fun i => b i x) (a x)) U := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  apply FormSmooth.contDiffOn_apply ha
  intro k
  fin_cases k
  exact hb i

end TamingCompatibility.HodgeGeometricCoefficients

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
open EuclideanEnergy HodgeFrame HodgeNormalOperator
open HodgeNormalSymbol (W Q)
open HodgeMatrixEnergy (Field)

def field (g : V → Metric V) (b : Fin 4 → V → V) (f : Field) (x : V) : MetricForms.Form V 2 :=
  ∑ j, f j x • frame g b j x
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
lemma reconstruct_function (g : V → Metric V) (b : Fin 4 → V → V) (q : V → W) :
    (fun y => ∑ j, q y j • HodgeGeometricCoefficients.frame g b j y) =
    fun y => reconstruct (g y) (fun i => b i y) (q y) := rfl
end TamingCompatibility.HodgeNormalOperator

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.CoordinateOperator
open HodgeNormalSymbol EuclideanEnergy
open scoped RealInnerProductSpace ContDiff
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def firstOrder (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (u : V → W) (x : V) : Q :=
  (∑ i, a i x (fderiv ℝ u x (e i))) + b x (u x)

end TamingCompatibility.GeometricHilbert.CoordinateOperator


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameH1
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
open _root_.MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff
namespace TamingCompatibility.HodgeMatrixEnergy
open EuclideanEnergy
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma value_fderiv (f : Field) (x : V) (i : Fin 4) :
    fderiv ℝ (value f) x (e i) = derivative f i x := by
  ext j
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x
    ((value_smooth f).differentiable (by simp) x).hasFDerivAt
  have he := congrArg (fun L : V →L[ℝ] ℝ => L (e i)) hp.fderiv
  change fderiv ℝ (f j) x (e i) = _ at he
  exact he.symm

lemma frame_deriv_bound {P : V → W →L[ℝ] F} {u : V → F} (f : Field)
    (he : u = fun x => P x (value f x)) {x : V} (hP : DifferentiableAt ℝ P x)
    {C : ℝ} (hbP : ‖P x‖ ≤ C) (hdP : ‖fderiv ℝ P x‖ ≤ C) (i : Fin 4) :
    ‖fderiv ℝ u x (e i)‖^2 ≤ 2*C^2*(gradient f x + ‖value f x‖^2) := by
  have hder : fderiv ℝ u x (e i) = fderiv ℝ P x (e i) (value f x) + P x (derivative f i x) := by
    rw [he, fderiv_clm_apply hP ((value_smooth f).differentiable (by simp) x)]
    simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,value_fderiv,add_comm]
  have hdp : ‖fderiv ℝ P x (e i)‖ ≤ C := by
    have h := (fderiv ℝ P x).le_opNorm (e i)
    simpa only [show ‖e i‖ = 1 by simp [e],mul_one] using
      h.trans (mul_le_mul_of_nonneg_right hdP (norm_nonneg (e i)))
  have h1 := (fderiv ℝ P x (e i)).le_opNorm (value f x) |>.trans
    (mul_le_mul_of_nonneg_right hdp (norm_nonneg _))
  have h2 := (P x).le_opNorm (derivative f i x) |>.trans
    (mul_le_mul_of_nonneg_right hbP (norm_nonneg _))
  have hs1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hg : ‖derivative f i x‖^2 ≤ gradient f x := by
    unfold gradient
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖derivative f j x‖) (Finset.mem_univ i)
  have hg' := mul_le_mul_of_nonneg_left hg (sq_nonneg C)
  rw [hder]
  have hn := norm_add_sq_bound (fderiv ℝ P x (e i) (value f x)) (P x (derivative f i x))
  simp only [mul_pow] at hs1 hs2
  nlinarith

theorem frame_h1_bound {U K : Set V} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (P : V → W →L[ℝ] F) (hP : ContDiffOn ℝ ∞ P U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Field) (u : 𝓢(V,F)), tsupport u ⊆ K →
      (⇑u = fun x => P x (value f x)) →
      ((∫ x, ‖u x‖^2) ≤ C*((∫ x, gradient f x)+(∫ x, ‖value f x‖^2))) ∧
      (∀ i : Fin 4, (∫ x, ‖(∂_{e i} u) x‖^2) ≤
        C*((∫ x, gradient f x)+(∫ x, ‖value f x‖^2))) := by
  have hdP : ContinuousOn (fderiv ℝ P) K := fun x hx =>
    ((hP.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousWithinAt
  obtain ⟨B₁,h₁⟩ := hK.exists_bound_of_continuousOn (hP.continuousOn.mono hKU)
  obtain ⟨B₂,h₂⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ P) hdP
  let B := max 1 (max B₁ B₂)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb₁ : B₁ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hb₂ : B₂ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨2*B^2,by positivity,?_⟩
  intro f u hsu he
  have hint : Integrable (fun x => 2*B^2*(gradient f x+‖value f x‖^2)) :=
    ((gradient_integrable f).add (value_integrable f)).const_mul _
  have hformula : (∫ x, 2*B^2*(gradient f x+‖value f x‖^2)) =
      2*B^2*((∫ x, gradient f x)+(∫ x, ‖value f x‖^2)) := by
    rw [integral_const_mul,integral_add (gradient_integrable f) (value_integrable f)]
  constructor
  · refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint
      (Filter.Eventually.of_forall (fun x => ?_))).trans_eq hformula
    by_cases hx : x ∈ K
    · have hb := lowerError_bound P f x ((h₁ x hx).trans hb₁)
      rw [he]
      have hn := mul_nonneg (sq_nonneg B) (gradient_nonneg f x)
      have hn' := mul_nonneg (sq_nonneg B) (sq_nonneg ‖value f x‖)
      nlinarith
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsu h)),norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (by positivity) (add_nonneg (gradient_nonneg f x) (sq_nonneg _))
  · intro i
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint
      (Filter.Eventually.of_forall (fun x => ?_))).trans_eq hformula
    by_cases hx : x ∈ K
    · rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact frame_deriv_bound f he
        ((hP.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        ((h₁ x hx).trans hb₁) ((h₂ x hx).trans hb₂) i
    · rw [image_eq_zero_of_notMem_tsupport
        (fun h => hx (hsu (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))),norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (by positivity) (add_nonneg (gradient_nonneg f x) (sq_nonneg _))
end TamingCompatibility.HodgeMatrixEnergy

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalEnergy
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
namespace TamingCompatibility.HodgeNormalOperator
open scoped RealInnerProductSpace
open EuclideanEnergy
lemma join_inner (u v a b : V) : ⟪join u v,join a b⟫ = ⟪u,a⟫+⟪v,b⟫ := by
  simp [join,PiLp.inner_apply,Fin.sum_univ_succ]
  ring
lemma output_inner (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a c d f : MetricForms.Form V 1) :
    ⟪left b a+right b c,left b d+right b f⟫ =
      MetricForms.pairing g a d+MetricForms.pairing g c f := by
  rw [left_add_right,left_add_right,join_inner,
    LocalMatrixOperator.frameVector_pairing g b hb,LocalMatrixOperator.frameVector_pairing g b hb]
end TamingCompatibility.HodgeNormalOperator

namespace TamingCompatibility.MetricHodge
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma full_starTwo_zero (g : MetricModel.Metric E) (J : E →L[ℝ] E) (F : MetricForms.Form E 2) :
    starTwo g J F 0 = 0 := by
  simp only [starTwo,MetricForms.pairing_zero_left,zero_smul]
  ext v
  simp
end TamingCompatibility.MetricHodge

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section

namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy
open scoped RealInnerProductSpace
lemma normalSymbol_weighted_polarized (ρ c : ℝ) (ξ η : V) :
    (ρ • (c • normalSymbol ξ)).adjoint ∘L (c • normalSymbol η) +
      (ρ • (c • normalSymbol η)).adjoint ∘L (c • normalSymbol ξ) =
        (2 * (ρ*c*c*⟪ξ,η⟫)) • ContinuousLinearMap.id ℝ W := by
  apply ContinuousLinearMap.ext
  intro q
  apply ext_inner_left ℝ
  intro r
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,inner_add_right,
    ContinuousLinearMap.adjoint_inner_right,_root_.smul_apply,real_inner_smul_left,
    real_inner_smul_right,ContinuousLinearMap.id_apply]
  calc
    _ = (ρ*c*c) * (⟪normalSymbol ξ r,normalSymbol η q⟫ +
        ⟪normalSymbol η r,normalSymbol ξ q⟫) := by ring
    _ = _ := by rw [normalSymbol_polarized]; ring
end TamingCompatibility.HodgeNormalSymbol

end
end

end
end

end OAI
end


