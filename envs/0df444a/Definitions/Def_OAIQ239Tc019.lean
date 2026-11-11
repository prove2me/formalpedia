-- Prove2me | Definitions.Def_OAIQ239Tc019
-- name    : OAIQ239Tc019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:09.085193+00:00
-- url     : https://prove2.me/theorems/b31cd302-4f02-4676-87db-d96990a4fbff
-- title:
--   Definitions bundle OAIQ239Tc019 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 26 definitions, 1 inductive type or structure, 1 instance and 32 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixResidualMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixResidualMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedAddCommGroupMetricTensorV_1`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedSpaceRealMetricTensorV_1`, `OAI.TamingCompatibility.GeometricHilbert.SquareData`, `OAI.TamingCompatibility.GeometricHilbert.antiRdd`, `OAI.TamingCompatibility.GeometricHilbert.antiToH1`, `OAI.TamingCompatibility.GeometricHilbert.chartToMetric`, `OAI.TamingCompatibility.GeometricHilbert.coordinateTwoJet`, `OAI.TamingCompatibility.GeometricHilbert.densityTest`, `OAI.TamingCompatibility.GeometricHilbert.hodgeEnergyToH1`, `OAI.TamingCompatibility.GeometricHilbert.hodgeToH1`, `OAI.TamingCompatibility.GeometricHilbert.scalarToJet`, `OAI.TamingCompatibility.GeometricHilbert.smoothToChart`, `OAI.TamingCompatibility.HodgeChart.energyPairing`, `OAI.TamingCompatibility.HodgeChart.normalOperator`, `OAI.TamingCompatibility.HodgeChart.patchA`, `OAI.TamingCompatibility.HodgeChart.patchB`, `OAI.TamingCompatibility.HodgeScalar.Jet`, `OAI.TamingCompatibility.HodgeScalar.jet`, `OAI.TamingCompatibility.HodgeScalar.jetComponent`, `OAI.TamingCompatibility.HodgeScalar.jetDistribution`, `OAI.TamingCompatibility.HodgeScalar.make`, `OAI.TamingCompatibility.ScalarPair.Jet`, `OAI.TamingCompatibility.ScalarPair.jet`, `OAI.TamingCompatibility.ScalarPair.jetComponent`, `OAI.TamingCompatibility.ScalarPair.jetDistribution`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartComponent`, `TamingCompatibility_Concentration_HodgeParametrixResidual`, `TamingCompatibility_DifferentialForms_FirstMatrixJoint`, `TamingCompatibility_DifferentialForms_MetricSquareEstimate`, `TamingCompatibility_DifferentialForms_RawJetEstimate`, `TamingCompatibility_DifferentialForms_RawRepresentative`, `TamingCompatibility_DifferentialForms_ScalarJet`, `TamingCompatibility_DifferentialForms_SmoothGeometricInverse`, `TamingCompatibility_DifferentialForms_WeightedRawPairing`, `TamingCompatibility_Elliptic_AntiChartH1`, `TamingCompatibility_Functional_GeometricCompact`, `TamingCompatibility_Functional_WeakNormalEquation`, `TamingCompatibility_Hodge_HodgeCutoffIntegral`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeGeometricCoefficients`, `TamingCompatibility_Hodge_HodgeH1`, `TamingCompatibility_Hodge_HodgeLocalCodifferential`, `TamingCompatibility_Hodge_HodgeNormalDistribution`, `TamingCompatibility_Hodge_HodgeNormalEnergy`, `TamingCompatibility_Hodge_HodgeScalarJet`, `TamingCompatibility_Hodge_HodgeScalarRaw`, `TamingCompatibility_Hodge_HodgeScalarSquare`, `TamingCompatibility_Hodge_HodgeWedgeEnergy`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc014` and `OAIQ239Tc015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc022`, `OAIQ239Tc023` and `OAIQ239Tc024`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_joint`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledB_joint`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_smooth`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc014
import Definitions.Def_OAIQ239Tc015

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartComponent
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open _root_.MeasureTheory TemperedDistribution Set Function HilbertSobolev
open scoped Topology Manifold ContDiff SchwartzMap LineDeriv Laplacian RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

omit [T2Space X] in
lemma h1ToL2_compact : IsCompactOperator (h1ToL2 A k) := by
  let f := ContinuousLinearMap.pi (fun p : A.centers => chartComponent A k none p)
  have hf : IsCompactOperator f :=
    CompactPi.pi_compact _ (chartComponent_compact A k)
  have h := hf.clm_comp (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : A.centers => Lp (CoordinateFiber k) 2 (volume : Measure Space))).symm.toContinuousLinearMap
  have he : (zeroth A k).comp (globalH1 A k).subtypeL =
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : A.centers => Lp (CoordinateFiber k) 2 (volume : Measure Space))).symm.toContinuousLinearMap.comp f := by
    ext u p
    rfl
  have hg : IsCompactOperator ((zeroth A k).comp (globalH1 A k).subtypeL) := by
    rw [he]
    exact h
  exact hg.codRestrict (zeroth_mem_globalL2 A k)
    (LinearMap.range (localizeL2 A k)).isClosed_topologicalClosure

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricCoefficients
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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

variable (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
  (b : Fin 4 → V → V) {U : Set V} (hU : IsOpen U)
  (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
  (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
  (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
  (hF : ContDiffOn ℝ ∞ F U) (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
include hU hg hJ hJs hgJ hF hb

lemma lower_smooth : ContDiffOn ℝ ∞ (lower g J F b) U := by
  have hstar := SmoothHodge.starThreeCLM_contDiffOn g J (by simp [V]) hU hg hJ hJs hgJ hF
  have hψ (j : Fin 6) := derivative_smooth hU (frame_smooth hg hb j)
  have hφ (j : Fin 6) := derivative_smooth hU (starFrame_smooth g J F b hU hg hJ hJs hgJ hF hb j)
  apply contDiffOn_clm_apply.mpr
  intro q
  have he (x : V) : lower g J F b x q = join
      (LocalMatrixOperator.frameVector (fun i => b i x)
        (starThreeCLM (g x) (F x) (∑ j, q j • extDeriv (starFrame g J F b j) x)))
      (LocalMatrixOperator.frameVector (fun i => b i x)
        (starThreeCLM (g x) (F x) (∑ j, q j • extDeriv (frame g b j) x))) := by
    simp only [lower,HodgeNormalOperator.lower,_root_.add_apply,ContinuousLinearMap.comp_apply,
      combineThree_apply,left_add_right]
  simp_rw [he]
  change ContDiffOn ℝ ∞ (fun x => joinCLM (_, _)) U
  apply joinCLM.contDiff.comp_contDiffOn
  apply ContDiffOn.prodMk
  · apply frameVector_smooth hb
    apply hstar.clm_apply
    exact ContDiffOn.sum (fun j _ => (hφ j).const_smul (q j))
  · apply frameVector_smooth hb
    apply hstar.clm_apply
    exact ContDiffOn.sum (fun j _ => (hψ j).const_smul (q j))
end TamingCompatibility.HodgeGeometricCoefficients

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility
open ManifoldForms ManifoldHodge GeometricAdjoint
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

local instance instNormedAddCommGroupTangentSpaceRealSpaceModel_1_re397b7_1 (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance instNormedSpaceRealTangentSpaceSpaceModel_1_re397b7_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel_1_re397b7_1 (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)
lemma hodgeStar_fun_smul (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (f : X → ℝ) (a : TwoForm X) :
    starTwo J α ht (fun x => f x • a x) = fun x => f x • starTwo J α ht a x := by
  funext x
  exact congrFun (hodgeStar_smul J α ht (f x) a) x

lemma codifferential_fun_smul (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : Smooth a)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    codifferential J α ht (fun x => f x • a x) =
      (fun x => f x • codifferential J α ht a x) -
        starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) (starTwo J α ht a)) := by
  unfold codifferential
  rw [hodgeStar_fun_smul,exteriorDerivative_fun_smul hf (starTwo_smooth J α hs ht ha),
    ManifoldHodge.starThree_add]
  funext x
  let d : MetricForms.Form Space 3 := exteriorDerivative (starTwo J α ht a) x
  let t : MetricForms.Form Space 1 := starThree J α ht
    (ManifoldForms.wedgeOne (scalarDifferential f) (starTwo J α ht a)) x
  let F : MetricForms.Form Space 2 := invariantPart J α x
  let g := pointMetric J α ht x
  change -(MetricHodge.starThree g F (f x • d) + t) =
    f x • (-MetricHodge.starThree g F d) - t
  rw [MetricHodge.starThree_smul]
  module

lemma full_pairing_star_wedge (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a : TwoForm X) (ξ : ManifoldForms.Form X 1) (x : X) :
    pairing J α ht (starThree J α ht (ManifoldForms.wedgeOne ξ (starTwo J α ht a)))
      (starThree J α ht (ManifoldForms.wedgeOne ξ (starTwo J α ht a))) x +
    pairing J α ht (starThree J α ht (ManifoldForms.wedgeOne ξ a))
      (starThree J α ht (ManifoldForms.wedgeOne ξ a)) x =
      pairing J α ht ξ ξ x * pairing J α ht a a x := by
  have he := MetricHodge.full_wedge_energy (pointMetric J α ht x)
    (J.endomorphism x : Space →L[ℝ] Space) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x) (by simp [Space])
    (invariantPart J α x) (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm)
    (ExteriorForms.oneLinear (E := Space) (ξ x)) (a x)
  have hx : ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)
      (ExteriorForms.oneLinear (E := Space) (ξ x)) = ξ x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).apply_symm_apply _
  rw [hx] at he
  exact he

lemma full_cutoff_delta_pointwise (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : Smooth a)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (x : X) :
    pairing J α ht (codifferential J α ht (fun x => f x • a x))
      (codifferential J α ht (fun x => f x • a x)) x +
    pairing J α ht (codifferential J α ht (starTwo J α ht (fun x => f x • a x)))
      (codifferential J α ht (starTwo J α ht (fun x => f x • a x))) x ≤
      2*(f x)^2*(pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
        pairing J α ht (codifferential J α ht (starTwo J α ht a))
          (codifferential J α ht (starTwo J α ht a)) x) +
      2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x * pairing J α ht a a x := by
  rw [hodgeStar_fun_smul,codifferential_fun_smul J α hs ht ha hf,
    codifferential_fun_smul J α hs ht (starTwo_smooth J α hs ht ha) hf,starTwo_square]
  let d : MetricForms.Form Space 1 := codifferential J α ht a x
  let ds : MetricForms.Form Space 1 := codifferential J α ht (starTwo J α ht a) x
  let t : MetricForms.Form Space 1 :=
    starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) (starTwo J α ht a)) x
  let u : MetricForms.Form Space 1 :=
    starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) a) x
  have h₁ := MetricForms.pairing_sub_self_le (pointMetric J α ht x) (f x • d) t
  have h₂ := MetricForms.pairing_sub_self_le (pointMetric J α ht x) (f x • ds) u
  rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right] at h₁ h₂
  have he := full_pairing_star_wedge J α ht a (scalarDifferential f) x
  let g := pointMetric J α ht x
  change MetricForms.pairing g t t + MetricForms.pairing g u u = _ at he
  change MetricForms.pairing g (f x • d - t) (f x • d - t) +
    MetricForms.pairing g (f x • ds - u) (f x • ds - u) ≤
      2*(f x)^2*(MetricForms.pairing g d d+MetricForms.pairing g ds ds) +
        2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x * pairing J α ht a a x
  calc
    _ ≤ (2*(f x*(f x*MetricForms.pairing g d d)) + 2*MetricForms.pairing g t t) +
        (2*(f x*(f x*MetricForms.pairing g ds ds)) + 2*MetricForms.pairing g u u) :=
      add_le_add h₁ h₂
    _ = 2*(f x)^2*(MetricForms.pairing g d d+MetricForms.pairing g ds ds) +
        2*(MetricForms.pairing g t t+MetricForms.pairing g u u) := by ring
    _ = _ := by rw [he]; ring
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalCodifferential
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldForms ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_codifferential (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z =
      -MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (ManifoldForms.pullback (starTwo J α ht a) (extChartAt Model p).symm) z) := by
  have hneg (b : ManifoldForms.Form X 1) :
      ManifoldForms.pullback (-b) (extChartAt Model p).symm z =
        -ManifoldForms.pullback b (extChartAt Model p).symm z := by ext v; rfl
  change ManifoldForms.pullback (-(starThree J α ht (exteriorDerivative (starTwo J α ht a))))
    (extChartAt Model p).symm z = _
  rw [hneg,pullback_starThree J α ht _ p hz,
    pullback_exteriorDerivative _ (starTwo_smooth J α hs ht ha)
      (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hz]
  congr 2
  exact extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz

lemma pullback_codifferential_star (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (codifferential J α ht (starTwo J α ht a)) (extChartAt Model p).symm z =
      -MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (ManifoldForms.pullback a (extChartAt Model p).symm) z) := by
  rw [pullback_codifferential J α hs ht (starTwo_smooth J α hs ht ha) p hz,starTwo_square]
end TamingCompatibility.ManifoldHodge

namespace TamingCompatibility.HodgeChart
open GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume ContinuousAlternatingMap
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

lemma cutoffDelta_zero_off (p : A.centers) (a : TwoForm X)
    {x : X} (hx : x ∉ tsupport (A.partition p)) :
    codifferential J α ht (cutoffForm A p a) x = 0 := by
  unfold codifferential
  change -(starThree J α ht (exteriorDerivative (starTwo J α ht (fun y => A.partition p y • a y))) x) = 0
  rw [hodgeStar_fun_smul]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) (invariantPart J α x)
    (exteriorDerivative (fun y => A.partition p y • starTwo J α ht a y) x) = 0
  rw [exteriorDerivative_fun_smul_vanishes _ hx]
  let F : MetricForms.Form Space 2 := invariantPart J α x
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) F (0 : MetricForms.Form Space 3) = 0
  rw [MetricHodge.starThree_zero,neg_zero]

lemma cutoffDelta_pairing_tsupport (p : A.centers) (a : TwoForm X) :
    tsupport (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
      (codifferential J α ht (cutoffForm A p a))) ⊆ tsupport (A.partition p) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  apply hx
  change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (codifferential J α ht (cutoffForm A p a) x) (codifferential J α ht (cutoffForm A p a) x) = 0
  rw [cutoffDelta_zero_off A J α ht p a hn]
  exact (MetricForms.pairing_self_eq_zero _ _).mpr rfl

variable [CompactSpace X] (hs : IsSmooth α)
include hs in
lemma localDelta_density_integrable (p : A.centers) {a : TwoForm X} (ha : Smooth a) :
    Integrable (coordinateIntegrand J α p.val
      (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a)))) := by
  apply coordinateIntegrand_integrable J α hs ht p.val
  · have hd := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
    exact (GeometricAdjoint.pairing_one_smooth J α hs ht hd hd).continuous
  · exact (cutoffDelta_pairing_tsupport A J α ht p a).trans (A.subordinate p)

variable [MeasurableSpace X] [BorelSpace X]
include hs in
lemma integral_localDelta_density (p : A.centers) {a : TwoForm X} (ha : Smooth a) :
    (∫ z, coordinateIntegrand J α p.val
      (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a))) z) =
    ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a)) x ∂geometricVolume A J α := by
  have hd := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
  rw [integral_geometricVolume_coordinate A J α hs ht p.val _
    (GeometricAdjoint.pairing_one_smooth J α hs ht hd hd).continuous
    ((cutoffDelta_pairing_tsupport A J α ht p a).trans (A.subordinate p)),
    ← integral_indicator (isOpen_extChartAt_target p.val).measurableSet]
  rfl
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame HodgeGeometricCoefficients GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

def normalOperator (q : Space → HodgeNormalSymbol.W) (z : Space) : HodgeNormalSymbol.Q :=
  (∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
    normalB J α ht p D z (q z)

lemma normalA_smooth (i : Fin 4) : ContDiffOn ℝ ∞ (normalA J α ht p D i) D.domain :=
  HodgeGeometricCoefficients.principal_smooth D.frame_smooth i
include hs in
lemma normalB_smooth : ContDiffOn ℝ ∞ (normalB J α ht p D) D.domain :=
  HodgeGeometricCoefficients.lower_smooth _ _ _ _ D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset)
    ((coordinateJ_smooth J p).mono D.domain_subset)
    (fun _x hx => coordinateJ_square J p (D.domain_subset hx))
    (fun _x hx => coordinateMetric_hermitian J α ht p (D.domain_subset hx))
    ((smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset) D.frame_smooth

lemma normalOperator_zero_off (q : Space → HodgeNormalSymbol.W) {z : Space} (hz : z ∉ tsupport q) :
    normalOperator J α ht p D q z = 0 := by
  have he : q =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport q).isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  simp [normalOperator,he.fderiv_eq,image_eq_zero_of_notMem_tsupport hz]
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupMetricTensorV_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorV_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeParametrixResidual
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixResidualMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixResidualMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_AntiChartH1
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def antiToH1 : antiPre A J α hs ht →ₗ[ℝ] globalH1 A 2 :=
  (ClosureLinear.toClosure (localizeH1 A 2)).comp (antiPre A J α hs ht).subtype

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricCompact
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def smoothToChart : PreL2 A J α hs ht true →ₗ[ℝ] globalL2 A 2 :=
  ClosureLinear.toClosure (localizeL2 A 2)

omit [MeasurableSpace X] [BorelSpace X] in
lemma smoothToChart_dense : DenseRange (smoothToChart A J α hs ht) :=
  ClosureLinear.toClosure_dense (localizeL2 A 2)

def chartToMetric : globalL2 A 2 →L[ℝ] L2 A J α hs ht true :=
  (smoothL2 A J α hs ht true).toLinearMap.extendOfNorm (smoothToChart A J α hs ht)

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarJet
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ScalarPair
open _root_.MeasureTheory LineDeriv EuclideanEnergy ManifoldLocalization
open scoped SchwartzMap LineDeriv

abbrev Jet := PiLp 2 (fun _ : DerivativeIndex => Lp F 2 (volume : Measure Space))

def jetComponent (j : DerivativeIndex) : 𝓢(Space,F) →L[ℝ] 𝓢(Space,F) :=
  match j with
  | none => ContinuousLinearMap.id ℝ _
  | some i => lineDerivOpCLM ℝ 𝓢(Space,F) (stdOrthonormalBasis ℝ Space i)

def jet : 𝓢(Space,F) →L[ℝ] Jet :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeIndex => Lp F 2 (volume : Measure Space))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun j => SchwartzMap.toLpCLM ℝ F 2 (volume : Measure Space) ∘L jetComponent j)

def jetDistribution (j : DerivativeIndex) : Jet →L[ℝ] 𝓢'(Space,F) :=
  (Lp.toTemperedDistributionCLM F (volume : Measure Space) 2).restrictScalars ℝ ∘L PiLp.proj 2 _ j

lemma jetDistribution_jet (u : 𝓢(Space,F)) (j : DerivativeIndex) :
    jetDistribution j (jet u) = SchwartzMap.toTemperedDistributionCLM Space F volume (jetComponent j u) :=
  Lp.toTemperedDistribution_toLp_eq _

lemma jet_derivative (u : 𝓢(Space,F)) (i : Fin (Module.finrank ℝ Space)) :
    lineDerivOpCLM ℝ 𝓢'(Space,F) (stdOrthonormalBasis ℝ Space i) (jetDistribution none (jet u)) =
      jetDistribution (some i) (jet u) := by
  rw [jetDistribution_jet,jetDistribution_jet]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq _ _
end TamingCompatibility.ScalarPair

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def scalarToJet (p : A.centers) : antiPre A J α hs ht →ₗ[ℝ] ScalarPair.Jet :=
  ScalarPair.jet.toLinearMap ∘ₗ pairLinear A J α ht D hD p ∘ₗ (antiPre A J α hs ht).subtype

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_WeakNormalEquation
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma componentTest_support (j : Fin 2) (φ : 𝓢(Space,ℝ)) :
    tsupport (componentTest j φ) ⊆ tsupport φ := by
  exact tsupport_smul_subset_left (φ : Space → ℝ)
    (fun _ : Space => EuclideanSpace.single j (1:ℝ))

lemma componentTest_compact (j : Fin 2) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) : HasCompactSupport (componentTest j φ : Space → _) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (componentTest_support j φ)

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_WeightedRawPairing
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def densityTest (p : A.centers) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain) : 𝓢(Space,ℝ) :=
  SchwartzCutoff.schwartz (D p).domain_open
    ((contDiffOn_const (c := (2:ℝ))).mul ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset))
    (φ.smooth ⊤) hc hφD

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawRepresentative
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_nonzero_weight_chart (x : X) :
    ∃ p : A.centers, A.partition p x ≠ 0 ∧ (extChartAt Model p.val) x ∈ (D p).domain := by
  classical
  have hp : ∃ p : A.centers, A.partition p x ≠ 0 := by
    by_contra hn
    push Not at hn
    have hsum := partition_sum A x
    simp only [hn,Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨p,hp⟩ := hp
  have hx := hD p (subset_closure hp)
  refine ⟨p,hp,(D p).small_ball_subset ?_⟩
  exact Metric.ball_subset_closedBall hx.2

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothGeometricInverse
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricAdjoint Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def antiRdd (a : antiPre A J α hs ht) : antiPre A J α hs ht :=
  ⟨⟨rdd J α ht a.val.val,rdd_smooth J α hs ht a.val.property⟩,
    antiInvariantPart_idempotent J _⟩

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricSquareEstimate
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

structure SquareData (p : A.centers) (U : Set Space) (q : Space) where
  W : Set Space
  openW : IsOpen W
  qW : q ∈ W
  WU : W ⊆ U
  a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)
  b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)
  ρ : 𝓢(Space,ℝ)
  g : Fin 4 → Fin 4 → Space → ℝ
  agreeA : ∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p) i z
  agreeB : ∀ z ∈ W, b z = normalB J α ht p.val (D p) z
  agreeρ : ∀ z ∈ W, ρ z = chartDensity J α p.val z
  polarized : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
    (2*g i j x) • ContinuousLinearMap.id ℝ EuclideanEnergy.Pair
  center : ∀ i j, g i j q = chartDensity J α p.val q * ∑ t, (D p).frame t q i * (D p).frame t q j

end TamingCompatibility.GeometricHilbert

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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def coordinateTwoJet (u : 𝓢(Space,C 2)) (x : Space) : ℝ :=
  ‖u x‖ + ∑ i : Fin 4, ‖(∂_{EuclideanEnergy.e i} u) x‖ +
    ∑ i : Fin 4, ∑ j : Fin 4, ‖(∂_{EuclideanEnergy.e j} (∂_{EuclideanEnergy.e i} u)) x‖

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth
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
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization GeometricAdjoint
open _root_.MeasureTheory Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

include hs in
lemma full_cutoff_energy_bound {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a →
      (∫ x, pairing J α ht (fun y => f y • a y) (fun y => f y • a y) x ∂geometricVolume A J α) +
      (∫ x, pairing J α ht (codifferential J α ht (fun y => f y • a y))
        (codifferential J α ht (fun y => f y • a y)) x +
        pairing J α ht (codifferential J α ht (starTwo J α ht (fun y => f y • a y)))
          (codifferential J α ht (starTwo J α ht (fun y => f y • a y))) x ∂geometricVolume A J α) ≤
      C * ((∫ x, pairing J α ht a a x ∂geometricVolume A J α) +
        (∫ x, pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
          pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x ∂geometricVolume A J α)) := by
  let := geometricVolume_finite A J α hs ht
  have hdf := scalarDifferential_smooth hf
  have hc := (pairing_one_smooth J α hs ht hdf hdf).continuous
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => (f x)^2 + 2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x)
    ((hf.continuous.pow 2).add (hc.const_mul 2)).continuousOn
  obtain ⟨D,hD⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => 2*(f x)^2) ((hf.continuous.pow 2).const_mul 2).continuousOn
  let C := max 1 (max B D)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro a ha
  have hb₁ (x : X) : (f x)^2 + 2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x ≤ C :=
    (le_abs_self _).trans ((hB x (mem_univ x)).trans ((le_max_left B D).trans (le_max_right 1 (max B D))))
  have hb₂ (x : X) : 2*(f x)^2 ≤ C :=
    (le_abs_self _).trans ((hD x (mem_univ x)).trans ((le_max_right B D).trans (le_max_right 1 (max B D))))
  have hi₁ (b : TwoForm X) (hb : Smooth b) :
      Integrable (fun x => pairing J α ht b b x) (geometricVolume A J α) :=
    (pairing_two_smooth J α hs ht hb hb).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi₂ (b : TwoForm X) (hb : Smooth b) :
      Integrable (fun x => pairing J α ht (codifferential J α ht b) (codifferential J α ht b) x +
        pairing J α ht (codifferential J α ht (starTwo J α ht b))
          (codifferential J α ht (starTwo J α ht b)) x) (geometricVolume A J α) := by
    have hd := codifferential_smooth J α hs ht hb
    have hds := codifferential_smooth J α hs ht (starTwo_smooth J α hs ht hb)
    exact ((pairing_one_smooth J α hs ht hd hd).continuous.add
      (pairing_one_smooth J α hs ht hds hds).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hfa := Smooth.fun_smul hf ha
  rw [← integral_add (hi₁ _ hfa) (hi₂ _ hfa),← integral_add (hi₁ _ ha) (hi₂ _ ha),← integral_const_mul]
  apply integral_mono ((hi₁ _ hfa).add (hi₂ _ hfa)) (((hi₁ _ ha).add (hi₂ _ ha)).const_mul C)
  intro x
  have hx := full_cutoff_delta_pointwise J α hs ht ha hf x
  have he : pairing J α ht (fun y => f y • a y) (fun y => f y • a y) x =
      (f x)^2 * pairing J α ht a a x := by
    let v : MetricForms.Form Space 2 := a x
    change MetricForms.pairing (pointMetric J α ht x) (f x • v) (f x • v) = _
    rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right]
    change f x * (f x * MetricForms.pairing (pointMetric J α ht x) (a x) (a x)) = _
    dsimp [pairing]
    ring
  have h₁ := mul_le_mul_of_nonneg_right (hb₁ x) (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (a x))
  have h₂ := mul_le_mul_of_nonneg_right (hb₂ x)
    (add_nonneg (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (codifferential J α ht a x))
      (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (codifferential J α ht (starTwo J α ht a) x)))
  simp only [Pi.add_apply]
  rw [he]
  change ((f x)^2 + 2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x) *
    pairing J α ht a a x ≤ C * pairing J α ht a a x at h₁
  change 2*(f x)^2 * (pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
    pairing J α ht (codifferential J α ht (starTwo J α ht a))
      (codifferential J α ht (starTwo J α ht a)) x) ≤ _ at h₂
  calc
    _ ≤ (f x)^2 * pairing J α ht a a x +
        (2*(f x)^2 * (pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
          pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x) +
         2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x * pairing J α ht a a x) :=
      add_le_add (le_refl _) hx
    _ = ((f x)^2+2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x)*pairing J α ht a a x +
        2*(f x)^2 * (pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
          pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x) := by ring
    _ ≤ C*pairing J α ht a a x + C*(pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
          pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x) := add_le_add h₁ h₂
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ManifoldLocalization ManifoldVolume
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
def energyPairing (a b : TwoForm X) (x : X) : ℝ :=
  GeometricAdjoint.pairing J α ht (codifferential J α ht a) (codifferential J α ht b) x +
  GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a))
    (codifferential J α ht (starTwo J α ht b)) x
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalDistribution
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

instance hodgeEnergy_complete : CompleteSpace (hodgeEnergy A J α hs ht) :=
  ((LinearMap.range (hodgeGraph A J α hs ht)).isClosed_topologicalClosure).completeSpace_coe

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarSquare
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge LocalMatrixOperator Set Filter LocalFormalAdjoint LineDeriv
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def patchA (i : Fin 4) : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q) :=
  SchwartzCutoff.schwartz D.domain_open (normalA_smooth J α ht p D i) hφ hc hφD

def patchB : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q) :=
  SchwartzCutoff.schwartz D.domain_open (normalB_smooth J α hs ht p D) hφ hc hφD

end TamingCompatibility.HodgeChart

namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge LocalMatrixOperator ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

lemma patchA_polarized (ρ : 𝓢(Space,ℝ)) (i j : Fin 4) (z : Space) :
    (ρ z • patchA J α ht p D hφ hc hφD i z).adjoint ∘L patchA J α ht p D hφ hc hφD j z +
      (ρ z • patchA J α ht p D hφ hc hφD j z).adjoint ∘L patchA J α ht p D hφ hc hφD i z =
    (2*(ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p D i j z)) • ContinuousLinearMap.id ℝ HodgeNormalSymbol.W :=
  HodgeNormalSymbol.normalSymbol_weighted_polarized (ρ z) (φ z) _ _

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeH1
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeGraph_norm_sq (a : PreL2 A J α hs ht true) :
    ‖hodgeGraph A J α hs ht a‖^2 =
      (∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂ManifoldVolume.geometricVolume A J α) +
      (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
        (codifferential J α ht a.val) x +
        GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a.val))
          (codifferential J α ht (starTwo J α ht a.val)) x ∂ManifoldVolume.geometricVolume A J α) := by
  rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
  change ‖smoothL2 A J α hs ht true a‖^2 +
    (‖smoothL2 A J α hs ht false (hodgeDelta A J α hs ht a)‖^2 +
      ‖smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht a))‖^2) = _
  rw [(smoothL2 A J α hs ht true).norm_map,(smoothL2 A J α hs ht false).norm_map,
    (smoothL2 A J α hs ht false).norm_map,preL2_norm_sq,preL2_norm_sq,preL2_norm_sq]
  let := ManifoldVolume.geometricVolume_finite A J α hs ht
  have h₁ := GeometricAdjoint.codifferential_smooth J α hs ht a.property
  have h₂ := GeometricAdjoint.codifferential_smooth J α hs ht
    (starTwo_smooth J α hs ht a.property)
  rw [integral_add
    ((GeometricAdjoint.pairing_one_smooth J α hs ht h₁ h₁).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((GeometricAdjoint.pairing_one_smooth J α hs ht h₂ h₂).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  rfl

lemma hodgeSmooth_dense : DenseRange (hodgeSmooth A J α hs ht) :=
  ClosureLinear.toClosure_dense (hodgeGraph A J α hs ht)

def hodgeToH1 : PreL2 A J α hs ht true →ₗ[ℝ] globalH1 A 2 :=
  ClosureLinear.toClosure (localizeH1 A 2)

def hodgeEnergyToH1 : hodgeEnergy A J α hs ht →L[ℝ] globalH1 A 2 :=
  (hodgeToH1 A J α hs ht).extendOfNorm (hodgeSmooth A J α hs ht)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarJet
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeScalar
open _root_.MeasureTheory LineDeriv EuclideanEnergy ManifoldLocalization
open scoped SchwartzMap LineDeriv ContDiff
def make (f : Fin 6 → 𝓢(Space,ℝ)) : 𝓢(Space,F) := ∑ j, SchwartzMap.postcompCLM (inject j) (f j)
lemma make_apply (f : Fin 6 → 𝓢(Space,ℝ)) (x : Space) (i : Fin 6) : make f x i = (f i x : ℂ) := by
  simp [make,inject_apply]
lemma make_norm_sq (f : Fin 6 → 𝓢(Space,ℝ)) (x : Space) :
    ‖make f x‖^2 = ‖HodgeMatrixEnergy.value f x‖^2 := by
  simp [PiLp.norm_sq_eq_of_L2,make_apply,HodgeMatrixEnergy.value,Complex.norm_real]
lemma make_derivative (f : Fin 6 → 𝓢(Space,ℝ)) (v : Space) :
    ∂_{v} (make f) = make (fun j => ∂_{v} (f j)) := by
  simp only [make,lineDerivOp_sum,ScalarPair.postcomp_derivative]
abbrev Jet := PiLp 2 (fun _ : DerivativeIndex => Lp F 2 (volume : Measure Space))
def jetComponent (j : DerivativeIndex) : 𝓢(Space,F) →L[ℝ] 𝓢(Space,F) :=
  match j with
  | none => ContinuousLinearMap.id ℝ _
  | some i => lineDerivOpCLM ℝ 𝓢(Space,F) (stdOrthonormalBasis ℝ Space i)
def jet : 𝓢(Space,F) →L[ℝ] Jet :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeIndex => Lp F 2 (volume : Measure Space))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun j => SchwartzMap.toLpCLM ℝ F 2 (volume : Measure Space) ∘L jetComponent j)

def jetDistribution (j : DerivativeIndex) : Jet →L[ℝ] 𝓢'(Space,F) :=
  (Lp.toTemperedDistributionCLM F (volume : Measure Space) 2).restrictScalars ℝ ∘L PiLp.proj 2 _ j
lemma jetDistribution_jet (u : 𝓢(Space,F)) (j : DerivativeIndex) :
    jetDistribution j (jet u) = SchwartzMap.toTemperedDistributionCLM Space F volume (jetComponent j u) :=
  Lp.toTemperedDistribution_toLp_eq _
lemma jet_derivative (u : 𝓢(Space,F)) (i : Fin (Module.finrank ℝ Space)) :
    lineDerivOpCLM ℝ 𝓢'(Space,F) (stdOrthonormalBasis ℝ Space i) (jetDistribution none (jet u)) =
      jetDistribution (some i) (jet u) := by
  rw [jetDistribution_jet,jetDistribution_jet]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq _ _
end TamingCompatibility.HodgeScalar

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarRaw
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
lemma full_componentTest_support (j : Fin 6) (φ : 𝓢(Space,ℝ)) :
    tsupport (componentTest j φ) ⊆ tsupport φ :=
  tsupport_smul_subset_left (φ : Space → ℝ) (fun _ : Space => EuclideanSpace.single j (1:ℝ))
lemma full_componentTest_compact (j : Fin 6) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) : HasCompactSupport (componentTest j φ : Space → _) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (full_componentTest_support j φ)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


