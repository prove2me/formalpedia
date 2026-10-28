-- Prove2me | Definitions.Def_OAIQ3Ho003
-- name    : OAIQ3Ho003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T05:07:02.69679+00:00
-- url     : https://prove2.me/theorems/006293b5-8137-41fc-8683-f21a7e2c14f7
-- title:
--   Definitions bundle OAIQ3Ho003 of the split of OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 166 declarations of OpenAI's Lean: 84 definitions, 6 instances and 76 theorems. The definitions and types are `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multiplierTrace`, `OAI.StrictHotSpots.Conformal.planeChart`, `OAI.StrictHotSpots.Conformal.transportTest`, `OAI.StrictHotSpots.DiskCompact.coordinates`, `OAI.StrictHotSpots.DiskCompact.operator`, `OAI.StrictHotSpots.DiskCompact.regularized`, `OAI.StrictHotSpots.Douglas.boundaryRealCross`, `OAI.StrictHotSpots.Douglas.poissonRealEnergy`, `OAI.StrictHotSpots.H1.corrected`, `OAI.StrictHotSpots.H1.form`, `OAI.StrictHotSpots.H10.dilateTest`, `OAI.StrictHotSpots.H10.zeroGrad`, `OAI.StrictHotSpots.H10.zeroValue`, `OAI.StrictHotSpots.Helmholtz.complexExtension`, `OAI.StrictHotSpots.Helmholtz.coord`, `OAI.StrictHotSpots.Hodge.NeumannEuler`, `OAI.StrictHotSpots.Hodge.V2`, `OAI.StrictHotSpots.Hodge.WeakDivZero`, `OAI.StrictHotSpots.Hodge.WeakNormalDiv`, `OAI.StrictHotSpots.Hodge.cartesianEnergy`, `OAI.StrictHotSpots.Hodge.cartesianForm`, `OAI.StrictHotSpots.Hodge.nFunctional`, `OAI.StrictHotSpots.InInteriorNeumannEigenspace`, `OAI.StrictHotSpots.N1.value`, `OAI.StrictHotSpots.PhysicalHelmholtz.instInnerProductSpaceRealSubtypeH1AmbientMemSubmoduleH1H10`, `OAI.StrictHotSpots.PhysicalHelmholtz.instNormedSpaceRealSubtypeH1AmbientMemSubmoduleH1`, `OAI.StrictHotSpots.PhysicalHelmholtz.instNormedSpaceRealSubtypeH1AmbientMemSubmoduleH1H10`, `OAI.StrictHotSpots.PhysicalHelmholtz.pair`, `OAI.StrictHotSpots.PlaneGreen.boundaryClosedPoisson`, `OAI.StrictHotSpots.PlaneGreen.boundaryClosedSolution`, `OAI.StrictHotSpots.PlaneGreen.boundaryForm`, `OAI.StrictHotSpots.PlaneGreen.boundaryInteraction`, `OAI.StrictHotSpots.PlaneGreen.boundaryK`, `OAI.StrictHotSpots.PlaneGreen.boundaryMeasure`, `OAI.StrictHotSpots.PlaneGreen.boundaryN`, `OAI.StrictHotSpots.PlaneGreen.boundarySolutionValue`, `OAI.StrictHotSpots.PlaneGreen.boundedKernel`, `OAI.StrictHotSpots.PlaneGreen.closedRow`, `OAI.StrictHotSpots.PlaneGreen.compactRow`, `OAI.StrictHotSpots.PlaneGreen.cutoffK` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/HotSpots, in whole or in part: `HotSpots_BoundaryEnergy`, `HotSpots_BoundaryKernel`, `HotSpots_Cauchy`, `HotSpots_ClosedSolution`, `HotSpots_Conformal`, `HotSpots_Dirichlet`, `HotSpots_DouglasEnergy`, `HotSpots_Eigenfunction`, `HotSpots_Green`, `HotSpots_GreenOperator`, `HotSpots_GreenSolution`, `HotSpots_Helmholtz`, `HotSpots_Hodge`, `HotSpots_KernelLimit`, `HotSpots_Multiplicity`, `HotSpots_Multiplier`, `HotSpots_Poisson`, `HotSpots_Potentials`, `HotSpots_Sobolev`, `HotSpots_Variational`, `HotSpots_VectorEnergy`.
--
--   **Imports.** It imports the published bundle `Def_HotSpots`; the bundles `OAIQ3Ho000` and `OAIQ3Ho001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Ho004`; the statements `OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient`, `OAI_StrictHotSpots_Conformal_ClosedDiskChart_lipschitzMultipliedGradient_null`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.operator_norm_lt_one`, `OAI.StrictHotSpots.Helmholtz.plane_representative`, `OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg`, `OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_pos`, `OAI.StrictHotSpots.PlaneGreen.boundarySolution_energy`, `OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm`, `OAI.StrictHotSpots.PlaneGreen.full_boundary_hilbert_embedding`, `OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum`, `OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support` and `OAI_StrictHotSpots_weak_eigenfunction_representative`; the proofs of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient`, `OAI_StrictHotSpots_Conformal_ClosedDiskChart_lipschitzMultipliedGradient_null`, `OAI.StrictHotSpots.H10.subcritical`, `OAI.StrictHotSpots.Helmholtz.plane_representative`, `OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg`, `OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_pos`, `OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum`, `OAI.StrictHotSpots.main_theorem` and `OAI_StrictHotSpots_weak_eigenfunction_representative`.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HotSpots at commit adc7f12

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho000
import Definitions.Def_OAIQ3Ho001

section
-- module Solutions.OAIQ3_Hot.HotSpots_Sobolev
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer



open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal




open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff

namespace StrictHotSpots

namespace DiskH10
open DiskCutoff

lemma smooth_memH1 {f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R)) :
    HasH1Gradient disk f (gradient f) := by
  have hs : Metric.closedBall (0 : Plane) 1 ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hR
  let : IsFiniteMeasure (volume.restrict disk) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hfc := hf.continuousOn
  have hgc : ContinuousOn (gradient f) (Metric.ball 0 R) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp))
  have hb {F : Type} [NormedAddCommGroup F] {g : Plane → F}
      (hg : ContinuousOn g (Metric.ball 0 R)) : MemLp g 2 (volume.restrict disk) := by
    obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Plane) 1).exists_bound_of_continuousOn (hg.mono hs)
    have hm : AEStronglyMeasurable g (volume.restrict disk) :=
      (hg.mono ((Metric.ball_subset_closedBall).trans hs)).aestronglyMeasurable Metric.isOpen_ball.measurableSet
    apply MemLp.of_bound hm C
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hC x (Metric.ball_subset_closedBall hx)
  exact HasH1Gradient.of_contDiffOn Metric.isOpen_ball
    (hf.mono ((Metric.ball_subset_closedBall).trans hs)) (hb hfc) (hb hgc)



end DiskH10
end StrictHotSpots

open scoped Laplacian







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Green
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian

open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace

open scoped Convolution



open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian




open InnerProductSpace
open scoped Laplacian ContDiff


namespace StrictHotSpots.PlaneGreen
open GreenPotential DiskH10

def source (f : Plane → ℝ) (z : ℂ) : ℝ := f (complexIso z)

def potential (f : Plane → ℝ) (x : Plane) : ℝ :=
  GreenPotential.potential (source f) (complexIso.symm x)

end StrictHotSpots.PlaneGreen







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology







open scoped InnerProductSpace


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

def kernel (x y : Plane) : ℝ := DiskFormula.green (complexIso.symm x) (complexIso.symm y)

lemma kernel_memLp (x : Plane) (hx : x ∈ disk) :
    MemLp (kernel x) 2 (volume.restrict disk) := by
  have hx' : ‖complexIso.symm x‖ < 1 := by simpa [disk] using hx
  exact (DiskFormula.green_memLp_two _ hx').comp_measurePreserving complexIso_disk_preserving

lemma measurable_kernel : Measurable (fun p : Plane × Plane => kernel p.1 p.2) := by
  unfold kernel DiskFormula.green
  fun_prop

lemma kernel_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ disk,
    (eLpNorm (kernel x) 2 (volume.restrict disk)).toReal ≤ B := by
  obtain ⟨B,hB,h⟩ := DiskFormula.green_uniform_L2_bound
  refine ⟨B,hB,fun x hx => ?_⟩
  have hx' : ‖complexIso.symm x‖ < 1 := by simpa [disk] using hx
  have he := eLpNorm_comp_measurePreserving (p := 2)
    (DiskFormula.green_memLp_two _ hx').aestronglyMeasurable complexIso_disk_preserving
  change (eLpNorm (DiskFormula.green (complexIso.symm x) ∘ complexIso.symm) 2
    (volume.restrict disk)).toReal ≤ B
  rw [he]
  exact h _ hx'

lemma kernel_rows : ∀ᵐ x ∂volume.restrict disk, MemLp (kernel x) 2 (volume.restrict disk) := by
  filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
  exact kernel_memLp x hx

def integralOperator : Lp ℝ 2 (volume.restrict disk) →L[ℝ] Lp ℝ 2 (volume.restrict disk) :=
  MeasurableL2Kernel.operator (fun p => kernel p.1 p.2) measurable_kernel.aestronglyMeasurable
    kernel_rows kernel_bound.choose_spec.1
    (by filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
        exact kernel_bound.choose_spec.2 x hx)

end StrictHotSpots.PlaneGreen


open MeasureTheory
open scoped InnerProductSpace ENNReal


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

def inclusion : Lp ℝ 2 (volume.restrict disk) →L[ℝ] Lp ℝ 2 ν :=
  Lp.LpToLpOfMeasureLeSMul hC hν

include hC hν in
lemma kernel_memLp_weighted (x : Plane) (hx : x ∈ disk) : MemLp (kernel x) 2 ν :=
  ((kernel_memLp x hx).smul_measure hC).mono_measure hν



def weightedIntegralOperator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  ((inclusion hC hν).comp integralOperator).comp (inclusion hC hν).adjoint

end StrictHotSpots.PlaneGreen

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryKernel
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section DiskCompactLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
lemma kernel_symm (x y : Plane) : kernel x y = kernel y x := by
  simp only [kernel, DiskFormula.green, norm_sub_rev, mul_comm]
end StrictHotSpots.PlaneGreen

namespace StrictHotSpots.DiskCompact
open PlaneGreen DiskH10
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (ν : Measure X) [IsFiniteMeasure ν]
  (e : X → Plane) (he : Continuous e) (hd : ∀ x, e x ∈ disk)

def coordinates (x : X) : DiskKernel.Disk :=
  ⟨complexIso.symm (e x), by simpa [disk] using hd x⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
include he in
lemma coordinates_continuous : Continuous (coordinates e hd) :=
  ((complexIso.symm.continuous.comp he)).subtype_mk _

def regularized (n : ℕ) : C(X × X, ℝ) where
  toFun p := DiskKernel.regularized (regularizationParameter n) (coordinates e hd p.1)
    (coordinates e hd p.2)
  continuous_toFun := by
    have hfirst : Continuous (fun p : X × X => coordinates e hd p.1) :=
      (coordinates_continuous e he hd).comp continuous_fst
    have hsecond : Continuous (fun p : X × X => coordinates e hd p.2) :=
      (coordinates_continuous e he hd).comp continuous_snd
    have hr : Continuous (fun p : DiskKernel.Disk × DiskKernel.Disk =>
        DiskKernel.regularized (regularizationParameter n) p.1 p.2) :=
      DiskKernel.regularized_continuous (parameter_pos n) (parameter_le_one n)
    have hm : Continuous (fun p : X × X => (coordinates e hd p.1, coordinates e hd p.2)) :=
      hfirst.prodMk hsecond
    have hc := hr.comp hm
    simpa only [Function.comp_def] using hc

omit [CompactSpace X] [IsFiniteMeasure ν] in
include he in
lemma preserving : MeasurePreserving e ν (Measure.map e ν) := ⟨he.measurable,rfl⟩

variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : Measure.map e ν ≤ C • volume.restrict disk)

omit [CompactSpace X] [IsFiniteMeasure ν] in
include he hd hC hν in
lemma kernel_memLp (x : X) : MemLp (fun z => kernel (e z) (e x)) 2 ν := by
  have h := (kernel_memLp_weighted hC hν (e x) (hd x)).comp_measurePreserving (preserving ν e he)
  simpa only [Function.comp_def, kernel_symm] using h

def operator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  MeasureKernelTransfer.operator e (preserving ν e he) (weightedIntegralOperator hC hν)

end StrictHotSpots.DiskCompact
end
end DiskCompactLayer

section PlaneResolvedLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma column_memLp (x : disk) : MemLp (fun z => kernel z x) 2 ν := by
  convert kernel_memLp_weighted hC hν x x.property using 1
  ext z
  exact kernel_symm z x

def row (x : disk) : Lp ℝ 2 ν := (column_memLp hC hν x).toLp (fun z => kernel z x)

def resolved (x y : disk) : ℝ := kernel x y + inner ℝ (row hC hν x)
  (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (row hC hν y))

end StrictHotSpots.PlaneGreen
end
end PlaneResolvedLayer

section KernelPositivityLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace StrictHotSpots.PlaneGreen
open DiskH10
lemma kernel_nonneg {x y : Plane} (hx : x ∈ disk) (hy : y ∈ disk) : 0 ≤ kernel x y := by
  by_cases he : x = y
  · subst y
    simp [kernel, DiskFormula.green]
  · exact (DiskFormula.green_pos (by simpa [disk] using hx)
      (by simpa [disk] using hy) (fun h => he (complexIso.symm.injective h))).le

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hν in
lemma ae_mem_disk : ∀ᵐ x ∂ν, x ∈ disk :=
  (ae_restrict_mem diskOpen.measurableSet).filter_mono
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le

end StrictHotSpots.PlaneGreen
end
end KernelPositivityLayer

section PlaneBoundaryLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

def poisson (s : Boundary) (x : Plane) : ℝ :=
  DiskFormula.poisson (complexIso.symm s) (complexIso.symm x)

def boundaryInteraction (s t : Boundary) : ℝ :=
  DiskFormula.boundaryInteraction (complexIso.symm s) (complexIso.symm t)

def radial (s : Boundary) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : disk :=
  ⟨r • (s : Plane), by simpa [disk, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0,
    s.property] using hr1⟩

lemma poisson_nonneg (s : Boundary) (x : disk) : 0 ≤ poisson s x :=
  DiskFormula.poisson_nonneg _ _ (by simpa [disk] using x.property)

variable {ν : Measure Plane} [IsFiniteMeasure ν] {R : ℝ}
  (hR : ∀ᵐ x ∂ν, ‖x‖ ≤ R) (hR1 : R < 1)

include hR hR1 in
lemma poisson_memLp (s : Boundary) : MemLp (poisson s) 2 ν := by
  exact DiskFormula.poisson_memLp_ae ν (complexIso.symm s) (by simpa using s.property) complexIso.symm
    complexIso.symm.continuous.measurable (by simpa using hR) hR1

def poissonRow (s : Boundary) : Lp ℝ 2 ν := (poisson_memLp hR hR1 s).toLp (poisson s)

variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

def boundaryK (p : disk) (s : Boundary) : ℝ := poisson s p +
  inner ℝ (row hC hν p) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
    (poissonRow hR hR1 s))

def boundaryN (s t : Boundary) : ℝ := boundaryInteraction s t +
  inner ℝ (poissonRow hR hR1 s) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
    (poissonRow hR hR1 t))

end StrictHotSpots.PlaneGreen
end
end PlaneBoundaryLayer

section FullBoundarySmoothingLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma kernel_memLp_three (x : Plane) (hx : x ∈ disk) :
    MemLp (kernel x) 3 (volume.restrict disk) := by
  exact (DiskFormula.green_memLp_three _ (by simpa [disk] using hx)).comp_measurePreserving
    complexIso_disk_preserving

lemma poisson_memLp_three_halves (s : Boundary) :
    MemLp (poisson s) (3/2) (volume.restrict disk) :=
  (DiskFormula.poisson_memLp_three_halves _ (by simpa using s.property)).comp_measurePreserving
    complexIso_disk_preserving

lemma kernel_uniform_three_bound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x ∈ disk,
    eLpNorm (kernel x) 3 (volume.restrict disk) ≤ B := by
  obtain ⟨B,hB,h⟩ := DiskFormula.green_uniform_L3_bound
  refine ⟨B,hB,fun x hx => ?_⟩
  change eLpNorm (DiskFormula.green (complexIso.symm x) ∘ complexIso.symm) 3 _ ≤ B
  rw [eLpNorm_comp_measurePreserving
    (DiskFormula.green_memLp_three _ (by simpa [disk] using hx)).aestronglyMeasurable
      complexIso_disk_preserving]
  exact h _ (by simpa [disk] using hx)

lemma poisson_uniform_three_halves_bound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ s : Boundary,
    eLpNorm (poisson s) (3/2) (volume.restrict disk) ≤ B := by
  obtain ⟨B,hB,h⟩ := DiskFormula.poisson_uniform_L32_bound
  refine ⟨B,hB,fun s => ?_⟩
  change eLpNorm (DiskFormula.poisson (complexIso.symm s) ∘ complexIso.symm) (3/2) _ ≤ B
  rw [eLpNorm_comp_measurePreserving
    (DiskFormula.poisson_memLp_three_halves _ (by simpa using s.property)).aestronglyMeasurable
      complexIso_disk_preserving]
  exact h _ (by simpa using s.property)

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma kernel_memLp_three_weighted (x : Plane) (hx : x ∈ disk) : MemLp (kernel x) 3 ν :=
  (kernel_memLp_three x hx).of_measure_le_smul hC hν

include hC hν in
lemma poisson_memLp_three_halves_weighted (s : Boundary) : MemLp (poisson s) (3/2) ν :=
  (poisson_memLp_three_halves s).of_measure_le_smul hC hν

attribute [local instance] OAI.StrictHotSpots.PlaneGreen.holder_three_three_halves
include hC hν in
lemma product_green_poisson_integrable (x : Plane) (hx : x ∈ disk) (s : Boundary) :
    Integrable (fun y => kernel x y * poisson s y) ν :=
  (kernel_memLp_three_weighted hC hν x hx).integrable_mul
    (poisson_memLp_three_halves_weighted hC hν s)

include hC hν in
lemma kernel_uniform_three_bound_weighted : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x ∈ disk,
    eLpNorm (kernel x) 3 ν ≤ B := by
  obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound
  refine ⟨C ^ (1/(3:ℝ≥0∞)).toReal * B, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC) hB,
    fun x hx => ?_⟩
  exact (eLpNorm_le_of_measure_le_smul hν).trans (mul_le_mul' le_rfl (h x hx))

include hC hν in
lemma poisson_uniform_three_halves_bound_weighted : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ s : Boundary,
    eLpNorm (poisson s) (3/2) ν ≤ B := by
  obtain ⟨B,hB,h⟩ := poisson_uniform_three_halves_bound
  refine ⟨C ^ (1/(3/2:ℝ≥0∞)).toReal * B, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC) hB,
    fun s => ?_⟩
  exact (eLpNorm_le_of_measure_le_smul hν).trans (mul_le_mul' le_rfl (h s))

include hC hν in
lemma green_poisson_uniform_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ disk, ∀ s : Boundary,
    ‖∫ y, kernel x y * poisson s y ∂ν‖ ≤ B := by
  obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound_weighted hC hν
  obtain ⟨D,hD,hp⟩ := poisson_uniform_three_halves_bound_weighted hC hν
  refine ⟨(B*D).toReal, ENNReal.toReal_nonneg, fun x hx s => ?_⟩
  have hg := kernel_memLp_three_weighted hC hν x hx
  have hs := poisson_memLp_three_halves_weighted hC hν s
  have he : eLpNorm (fun y => kernel x y * poisson s y) 1 ν ≤ B*D := by
    exact (eLpNorm_smul_le_mul_eLpNorm hs.aestronglyMeasurable hg.aestronglyMeasurable).trans
      (mul_le_mul' (h x hx) (hp s))
  have hh := (enorm_integral_le_lintegral_enorm (fun y => kernel x y * poisson s y)).trans
    (((eLpNorm_one_eq_lintegral_enorm).symm.le).trans he)
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hB hD) hh
  simpa only [enorm, ENNReal.coe_toReal, coe_nnnorm] using ht



def smoothedPoisson (s : Boundary) (x : Plane) : ℝ :=
  ∫ y, kernel x y * poisson s y ∂ν

omit hC hν in
lemma smoothedPoisson_measurable [SFinite ν] (s : Boundary) : Measurable (smoothedPoisson (ν := ν) s) := by
  have hm : Measurable (fun z : Plane × Plane => kernel z.1 z.2 * poisson s z.2) :=
    measurable_kernel.mul (by unfold poisson DiskFormula.poisson; fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

include hC hν in
lemma smoothedPoisson_memLp [IsFiniteMeasure ν] (s : Boundary) :
    MemLp (smoothedPoisson (ν := ν) s) 2 ν := by
  obtain ⟨B,_,hB⟩ := green_poisson_uniform_bound hC hν
  apply MemLp.of_bound (smoothedPoisson_measurable s).aestronglyMeasurable B
  filter_upwards [ae_mem_disk hν] with x hx
  exact hB x hx s

end StrictHotSpots.PlaneGreen
end
end FullBoundarySmoothingLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section MainVariationalCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff
namespace StrictHotSpots






lemma rayleighValues_nonneg {Ω : Set Plane} {r : ℝ} (hr : r ∈ rayleighValues Ω) :
    0 ≤ r := by
  obtain ⟨v, g, _, _, hm, rfl⟩ := hr
  exact div_nonneg (integral_nonneg fun x => sq_nonneg ‖g x‖) hm.le

lemma firstPositiveNeumannValue_nonneg (Ω : Set Plane) :
    0 ≤ firstPositiveNeumannValue Ω :=
  Real.sInf_nonneg fun _ hr => rayleighValues_nonneg hr


lemma eigenfunction_energy_identity {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InFirstNeumannEigenspace Ω u) :
    (∫ x in Ω, ‖gradient u x‖ ^ 2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (u x) ^ 2) := by
  simpa only [real_inner_self_eq_norm_sq, pow_two] using hu.2.2.2 u (gradient u) hu.2.1



lemma eigenfunction_gradient_continuous {Ω : Set Plane} {u : Plane → ℝ}
    (hopen : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u) :
    ContinuousOn (gradient u) Ω := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    ((hu.1.mono subset_closure).continuousOn_fderiv_of_isOpen hopen (by simp))


lemma firstPositiveNeumannValue_pos_of_eigenfunction {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : 0 < firstPositiveNeumannValue Ω := by
  have hμ := firstPositiveNeumannValue_nonneg Ω
  by_contra hp
  have hz : firstPositiveNeumannValue Ω = 0 := le_antisymm (le_of_not_gt hp) hμ
  have he : (∫ x in Ω, ‖gradient u x‖ ^ 2) = 0 := by
    rw [eigenfunction_energy_identity hu, hz, zero_mul]
  have hi : Integrable (fun x => ‖gradient u x‖ ^ 2) (volume.restrict Ω) :=
    hu.2.1.2.1.integrable_norm_pow (by norm_num)
  have hg2 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖gradient u x‖) hi).mp he
  have hg : gradient u =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hg2] with x hx
    simpa using (eq_zero_of_pow_eq_zero hx : ‖gradient u x‖ = 0)
  have hg0 := Measure.eqOn_open_of_ae_eq hg hΩ.2.1
    (eigenfunction_gradient_continuous hΩ.2.1 hu) continuousOn_const
  have hd0 : Ω.EqOn (fderiv ℝ u) 0 := by
    intro x hx
    have hh := hg0 hx
    change (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ u x) = 0 at hh
    simpa using congrArg (InnerProductSpace.toDual ℝ Plane) hh
  obtain ⟨x, hx, hux⟩ := hne
  have hc : Ω.EqOn u (fun _ => u x) := fun y hy =>
    hΩ.2.1.is_const_of_fderiv_eq_zero
      hΩ.2.2.2.1.isPathConnected.isConnected.isPreconnected
      ((hu.1.mono subset_closure).differentiableOn (by simp)) hd0 hy hx
  have hmean : (∫ y in Ω, u x) = 0 :=
    (setIntegral_congr_fun hΩ.2.1.measurableSet hc).symm.trans hu.2.2.1
  have hv : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos (ne_of_gt (hΩ.2.1.measure_pos volume hΩ.1))
      hΩ.2.2.1.measure_lt_top.ne
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hmean
  exact hux ((mul_eq_zero.mp hmean).resolve_left hv.ne')

lemma integrable_inner_of_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Plane} {f g : Plane → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  exact (hf.norm.integrable_mul hg.norm).mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => norm_inner_le_norm _ _)


end StrictHotSpots
end MainVariationalCombinedLayer

section PlaneWavesCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff Laplacian
namespace StrictHotSpots.PlaneWaves

def cosine (k : Plane) (x : Plane) : ℝ := Real.cos (inner ℝ k x)
def sine (k : Plane) (x : Plane) : ℝ := Real.sin (inner ℝ k x)

lemma cosine_smooth (k : Plane) : ContDiff ℝ ∞ (cosine k) :=
  (innerSL ℝ k).contDiff.cos
lemma sine_smooth (k : Plane) : ContDiff ℝ ∞ (sine k) :=
  (innerSL ℝ k).contDiff.sin

lemma fderiv_cosine (k x : Plane) :
    fderiv ℝ (cosine k) x = (-sine k x) • innerSL ℝ k := by
  exact ((innerSL ℝ k).hasFDerivAt.cos).fderiv
lemma fderiv_sine (k x : Plane) :
    fderiv ℝ (sine k) x = cosine k x • innerSL ℝ k := by
  exact ((innerSL ℝ k).hasFDerivAt.sin).fderiv

lemma gradient_cosine (k x : Plane) : gradient (cosine k) x = (-sine k x) • k := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,fderiv_cosine]
  rfl
lemma gradient_sine (k x : Plane) : gradient (sine k) x = cosine k x • k := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,fderiv_sine]
  rfl

lemma cosine_memLp {Ω : Set Plane} (hb : Bornology.IsBounded Ω) (k : Plane) :
    MemLp (cosine k) 2 (volume.restrict Ω) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact MemLp.of_bound (cosine_smooth k).continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x => Real.norm_eq_abs _ ▸ Real.abs_cos_le_one _)
lemma sine_memLp {Ω : Set Plane} (hb : Bornology.IsBounded Ω) (k : Plane) :
    MemLp (sine k) 2 (volume.restrict Ω) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact MemLp.of_bound (sine_smooth k).continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x => Real.norm_eq_abs _ ▸ Real.abs_sin_le_one _)

lemma cosine_h1 {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (k : Plane) :
    HasH1Gradient Ω (cosine k) (fun x => (-sine k x) • k) := by
  have he : gradient (cosine k) = fun x => (-sine k x) • k := funext (gradient_cosine k)
  rw [← he]
  apply HasH1Gradient.of_contDiffOn hΩ (cosine_smooth k).contDiffOn (cosine_memLp hb k)
  rw [he]
  exact (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) k).comp_memLp' (sine_memLp hb k).neg
lemma sine_h1 {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (k : Plane) :
    HasH1Gradient Ω (sine k) (fun x => cosine k x • k) := by
  have he : gradient (sine k) = fun x => cosine k x • k := funext (gradient_sine k)
  rw [← he]
  apply HasH1Gradient.of_contDiffOn hΩ (sine_smooth k).contDiffOn (sine_memLp hb k)
  rw [he]
  exact (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) k).comp_memLp' (cosine_memLp hb k)

end StrictHotSpots.PlaneWaves
end PlaneWavesCombinedLayer

section H1RayleighFormCombinedLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace StrictHotSpots.H1
variable {Ω : Set Plane}
def form (lam : ℝ) (u v : H1 Ω) : ℝ :=
  inner ℝ (grad u) (grad v) - lam * inner ℝ (value u) (value v)

end StrictHotSpots.H1
end H1RayleighFormCombinedLayer

section DiskCompactEmbeddingCombinedLayer
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

def boundedKernel (p : Plane × Plane) : ℝ := by
  classical
  exact if p.1 ∈ disk then kernel p.1 p.2 else 0

lemma boundedKernel_memLp (x : Plane) :
    MemLp (fun y => boundedKernel (x,y)) 2 (volume.restrict disk) := by
  by_cases hx : x ∈ disk
  · simpa only [boundedKernel, ite_eq_left hx] using kernel_memLp x hx
  · simp only [boundedKernel, ite_eq_right hx]
    exact MemLp.zero

def compactRow (x : Plane) : Lp ℝ 2 (volume.restrict disk) :=
  (boundedKernel_memLp x).toLp (fun y => boundedKernel (x,y))

end StrictHotSpots.PlaneGreen
end DiskCompactEmbeddingCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Helmholtz
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section PlaneWaveFormsCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology Laplacian
namespace StrictHotSpots.PlaneWaves
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
include hΩ hb

lemma cosine_h1_gradient (k : Plane) : HasH1Gradient Ω (cosine k) (gradient (cosine k)) :=
  (cosine_h1 hΩ hb k).congr (EventuallyEq.refl _ _) (Eventually.of_forall fun x => (gradient_cosine k x).symm)
lemma sine_h1_gradient (k : Plane) : HasH1Gradient Ω (sine k) (gradient (sine k)) :=
  (sine_h1 hΩ hb k).congr (EventuallyEq.refl _ _) (Eventually.of_forall fun x => (gradient_sine k x).symm)

def cosH1 (k : Plane) : H1 Ω := (cosine_h1_gradient hΩ hb k).toH1
def sinH1 (k : Plane) : H1 Ω := (sine_h1_gradient hΩ hb k).toH1

end StrictHotSpots.PlaneWaves
end PlaneWaveFormsCombinedLayer

section H10ZeroExtensionCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.H10

variable {Ω : Set Plane} (hΩ : IsOpen Ω)

def zeroValue : H10 hΩ →L[ℝ] Lp ℝ 2 (volume : Measure Plane) :=
  (LpZeroExtension.linearIsometry hΩ.measurableSet).toContinuousLinearMap.comp (value hΩ)

def zeroGrad : H10 hΩ →L[ℝ] Lp Plane 2 (volume : Measure Plane) :=
  (LpZeroExtension.linearIsometry hΩ.measurableSet).toContinuousLinearMap.comp (grad hΩ)

end StrictHotSpots.H10
end H10ZeroExtensionCombinedLayer

section GapWeakPDECombinedLayer
open scoped Laplacian ContDiff InnerProductSpace
open Set MeasureTheory Filter
namespace StrictHotSpots
open Laplacian

def directionalDerivative (f : Plane → ℝ) (e : Plane) : Plane → ℝ :=
  fun x => (fderiv ℝ f x) e


end StrictHotSpots

section


open Set MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian
namespace StrictHotSpots


def PlaneWeakEquation (Ω : Set Plane) (μ : ℝ) (u : Plane → ℝ) : Prop :=
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x in Ω, u x * Δ φ x) = -μ * (∫ x in Ω, u x * φ x)

end StrictHotSpots
end

section


open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology
namespace StrictHotSpots

def coord : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

def complexExtension (Ω : Set Plane) (u : Plane → ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal (Ω.indicator u (coord z))

end StrictHotSpots
end
end GapWeakPDECombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Dirichlet
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section H10DilationCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots
open DiskH10

namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) {R : ℝ} (hR : 1 ≤ R)
  (hb : Ω ⊆ Metric.ball 0 R)

def dilateTest : smoothTestSpace Ω →ₗ[ℝ] smoothTestSpace disk where
  toFun f := ⟨fun x => (f : Plane → ℝ) (R • x), f.property.1.comp (contDiff_id.const_smul R),
    f.property.2.1.comp_homeomorph (Homeomorph.smul (Units.mk0 R (radius_pos hR).ne')),
    by
      intro x hx
      have hh : R • x ∈ Ω := f.property.2.2 (tsupport_comp_subset_preimage _ (continuous_id.const_smul R) hx)
      have ht := hb hh
      simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (radius_pos hR)] at ht
      change ‖x - 0‖ < 1
      rw [sub_zero]
      nlinarith [radius_pos hR]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end H10
end StrictHotSpots
end H10DilationCombinedLayer

section StrictGapAlgebraCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace StrictHotSpots
namespace H1
variable {Ω : Set Plane} (hb : Bornology.IsBounded Ω)

def corrected (φ v : H1 Ω) : H1 Ω := v - ((mean hb v) / (mean hb φ)) • φ
end H1
end StrictHotSpots
end StrictGapAlgebraCombinedLayer

section NearbyFrequenciesCombinedLayer
open Set MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace Topology
namespace StrictHotSpots.PlaneWaves

def frequency (r θ : ℝ) : Plane := WithLp.toLp 2 ![r * Real.cos θ, r * Real.sin θ]
end StrictHotSpots.PlaneWaves
end NearbyFrequenciesCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Poisson
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section SubcriticalExtensionCombinedLayer
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict Ω)

def Harmonic (A : H1 Ω) : Prop :=
  ∀ v : H10 ho, inner ℝ (H1.grad A) (H10.grad ho v) = 0

end StrictHotSpots.SubcriticalExtension
end SubcriticalExtensionCombinedLayer

end
end DouglasLipschitzBase


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_DouglasEnergy
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PoissonComponents

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace Convolution
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local notation "τ" => (2*Real.pi)


def poissonRealEnergy (f : C(AddCircle τ,ℂ)) : ℝ :=
  ∫ x : Plane in disk, ‖gradient (planePoisson f) x‖^2

end StrictHotSpots.Douglas
end
end PoissonComponents

section DouglasLipschitzBilinear

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local notation "τ" => (2*Real.pi)

attribute [local instance] OAI.StrictHotSpots.Douglas.instFactLtRealOfNatHMulPi_solutions_18
def boundaryRealCross (f g : AddCircle τ → ℂ) : ℝ :=
  ∫ p : AddCircle τ × AddCircle τ, inner ℝ (boundaryDifference f p) (boundaryDifference g p)

end StrictHotSpots.Douglas
end
end DouglasLipschitzBilinear

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_KernelLimit
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section CutoffOperatorsLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk) (s : Set Plane)

include hν in
lemma restrictDensity : ν.restrict s ≤ C • volume.restrict disk :=
  Measure.restrict_le_self.trans hν

end StrictHotSpots.PlaneGreen
end
end CutoffOperatorsLayer

section DiskCutoffLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

def cutoffSet (n : ℕ) : Set Plane := closedBall 0 (cutoffRadius n)

lemma cutoffSet_measurable (n : ℕ) : MeasurableSet (cutoffSet n) := measurableSet_closedBall

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hν in
lemma smoothedPoisson_nonneg (s : Boundary) {x : Plane} (hx : x ∈ disk) :
    0 ≤ smoothedPoisson (ν := ν) s x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_disk hν] with y hy
  exact mul_nonneg (kernel_nonneg hx hy) (poisson_nonneg s ⟨y,hy⟩)

include hC hν in
lemma smoothedPoisson_restrict_le (s : Boundary) (E : Set Plane) {x : Plane} (hx : x ∈ disk) :
    smoothedPoisson (ν := ν.restrict E) s x ≤ smoothedPoisson (ν := ν) s x := by
  apply setIntegral_le_integral (product_green_poisson_integrable hC hν x hx s)
  filter_upwards [ae_mem_disk hν] with y hy
  exact mul_nonneg (kernel_nonneg hx hy) (poisson_nonneg s ⟨y,hy⟩)

include hC hν in
lemma smoothedPoisson_full_memLp [IsFiniteMeasure ν] (s : Boundary) (E : Set Plane) :
    MemLp (smoothedPoisson (ν := ν.restrict E) s) 2 ν := by
  obtain ⟨B,_,hB⟩ := green_poisson_uniform_bound hC hν
  apply MemLp.of_bound (smoothedPoisson_measurable s).aestronglyMeasurable B
  filter_upwards [ae_mem_disk hν] with x hx
  rw [Real.norm_of_nonneg (smoothedPoisson_nonneg (restrictDensity hν E) s hx)]
  exact (smoothedPoisson_restrict_le hC hν s E hx).trans
    (le_abs_self _ |>.trans (hB x hx s))

end StrictHotSpots.PlaneGreen
end
end DiskCutoffLayer

section FullBoundaryKernelLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

def smoothedRow (s : Boundary) : Lp ℝ 2 ν :=
  (smoothedPoisson_memLp hC hν s).toLp (smoothedPoisson (ν := ν) s)

def cutoffSmoothedRow (n : ℕ) (s : Boundary) : Lp ℝ 2 ν :=
  (smoothedPoisson_full_memLp hC hν s (cutoffSet n)).toLp
    (smoothedPoisson (ν := ν.restrict (cutoffSet n)) s)

omit [IsFiniteMeasure ν] in
lemma cutoff_ae_norm (n : ℕ) : ∀ᵐ x ∂ν.restrict (cutoffSet n), ‖x‖ ≤ cutoffRadius n := by
  filter_upwards [ae_restrict_mem (cutoffSet_measurable n)] with x hx
  simpa [cutoffSet] using hx



def fullBoundaryK (p : disk) (s : Boundary) : ℝ := poisson s p + smoothedPoisson (ν := ν) s p +
  inner ℝ (row hC hν p) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
    (smoothedRow hC hν s))



def fullBoundaryN (s t : Boundary) : ℝ := boundaryInteraction s t +
  (∫ x, poisson s x * poisson t x ∂ν) +
  (∫ x, poisson s x * smoothedPoisson (ν := ν) t x ∂ν) +
  inner ℝ (smoothedRow hC hν s) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
    (smoothedRow hC hν t))

end StrictHotSpots.PlaneGreen
end
end FullBoundaryKernelLayer

section CutoffBoundaryLimitsLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

abbrev cutoffOperator (n : ℕ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  L2Cutoff.compressedOperator (cutoffSet n) (cutoffSet_measurable n) (weightedIntegralOperator hC hν)

abbrev cutoffK (n : ℕ) (p : disk) (s : Boundary) : ℝ :=
  boundaryK (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) hC
    (restrictDensity hν (cutoffSet n)) p s

abbrev cutoffN (n : ℕ) (s t : Boundary) : ℝ :=
  boundaryN (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) hC
    (restrictDensity hν (cutoffSet n)) s t

end StrictHotSpots.PlaneGreen
end
end CutoffBoundaryLimitsLayer

section FullBoundaryReciprocalLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)



def fullDistanceKernel (p : disk) (s t : Boundary) : ℝ :=
  if s = t then 0 else fullBoundaryK hC hν p s * fullBoundaryK hC hν p t /
    fullBoundaryN hC hν s t



end StrictHotSpots.PlaneGreen
end
end FullBoundaryReciprocalLayer



end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryEnergy
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section BoundaryMeasureScalarSupportLayer

section BoundaryMeasureLayer
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10


attribute [local instance] OAI.StrictHotSpots.PlaneGreen.twoPiPos
def boundaryMeasure : Measure Boundary := Measure.map angleBoundary volume

instance boundaryMeasure_finite : IsFiniteMeasure boundaryMeasure := by
  unfold boundaryMeasure
  infer_instance

instance boundaryMeasure_nullSingleton : NullSingletonClass boundaryMeasure := by
  constructor
  intro s
  rw [boundaryMeasure, Measure.map_apply angleBoundary.continuous.measurable (measurableSet_singleton s)]
  rw [show angleBoundary ⁻¹' {s} = {angleBoundary.symm s} by ext x; exact angleBoundary.toEquiv.eq_symm_apply.symm]
  simpa only [closedBall_zero, mul_zero, min_eq_right Real.two_pi_pos.le, ENNReal.ofReal_zero] using
    (AddCircle.volume_closedBall (2 * Real.pi) (x := angleBoundary.symm s) 0)

instance boundaryMeasure_openPos : boundaryMeasure.IsOpenPosMeasure :=
  angleBoundary.continuous.isOpenPosMeasure_map angleBoundary.surjective

lemma integral_boundary_angles {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Boundary → E) :
    ∫ s, f s ∂boundaryMeasure = ∫ θ in 0..2*Real.pi,
      f (circleBoundary (Circle.exp θ)) := by
  change ∫ s, f s ∂Measure.map angleBoundary.toMeasurableEquiv volume = _
  rw [integral_map_equiv]
  change (∫ x : AddCircle (2 * Real.pi), f (angleBoundary x)) = _
  rw [← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 (fun s => f (angleBoundary s))]
  simp only [zero_add]
  rfl

lemma poisson_eq_standard (s : Boundary) (x : Plane) :
    poisson s x = (2*Real.pi)⁻¹ *
      _root_.poissonKernel 0 (complexIso.symm x) (complexIso.symm (s : Plane)) := by
  simp only [poisson, DiskFormula.poisson, _root_.poissonKernel_def, sub_zero,
    LinearIsometryEquiv.norm_map, s.property, one_pow]
  ring

lemma integral_poisson (x : disk) : ∫ s, poisson s x ∂boundaryMeasure = 1 := by
  have hx : complexIso.symm (x : Plane) ∈ ball (0:ℂ) 1 := by
    simpa [disk, mem_ball_zero_iff] using x.property
  have hc : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => (1:ℝ)) (closedBall 0 1) := by
    intro z _
    exact InnerProductSpace.harmonicAt_const (1:ℝ)
  have he := hc.circleAverage_poissonKernel_smul hx
  rw [integral_boundary_angles]
  simp_rw [poisson_eq_standard]
  rw [intervalIntegral.integral_const_mul]
  convert he using 1
  unfold Real.circleAverage
  congr 2
  funext θ
  change poissonKernel 0 (complexIso.symm (x : Plane))
      (complexIso.symm (complexIso (Circle.exp θ : ℂ))) =
    (poissonKernel 0 (complexIso.symm (x : Plane)) • (fun _ : ℂ => (1 : ℝ)))
      (circleMap 0 1 θ)
  simp [circleMap, Circle.coe_exp]

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasureLayer
end BoundaryMeasureScalarSupportLayer

section BoundaryMeasurabilityScalarSupportLayer

section BoundaryMeasurabilityLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma poisson_continuous_boundary (x : disk) : Continuous (fun s : Boundary => poisson s x) := by
  have hn (s : Boundary) : complexIso.symm (s : Plane) - complexIso.symm (x : Plane) ≠ 0 := by
    intro he
    have hx : ‖(x : Plane)‖ < 1 := by simpa [disk] using x.property
    have he' := complexIso.symm.injective (sub_eq_zero.mp he)
    rw [← he', s.property] at hx
    exact (lt_irrefl _ hx)
  unfold poisson DiskFormula.poisson
  apply Continuous.div continuous_const
  · fun_prop
  · intro s
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hn s)))

lemma poisson_joint_measurable : Measurable (fun z : Boundary × Plane => poisson z.1 z.2) := by
  unfold poisson DiskFormula.poisson
  fun_prop

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasurabilityLayer
end BoundaryMeasurabilityScalarSupportLayer

section BoundaryPoissonIntegralsScalarSupportLayer

section BoundaryPoissonIntegralsLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

instance boundary_compactSpace : CompactSpace Boundary := circleBoundary.compactSpace

lemma poisson_boundary_integrable (x : disk) :
    Integrable (fun s : Boundary => poisson s x) boundaryMeasure :=
  (poisson_continuous_boundary x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)


def poissonExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Boundary → E) (x : Plane) : E := ∫ s, poisson s x • f s ∂boundaryMeasure

lemma poissonExtension_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Boundary → E} {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    ‖poissonExtension f x‖ ≤ B := by
  unfold poissonExtension
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ s, poisson s x * B ∂boundaryMeasure := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun _ => norm_nonneg _
      · exact (poisson_boundary_integrable x).mul_const B
      · filter_upwards [] with s
        rw [norm_smul, Real.norm_of_nonneg (poisson_nonneg s x)]
        exact mul_le_mul_of_nonneg_left (hB s) (poisson_nonneg s x)
    _ = B := by rw [integral_mul_const, integral_poisson, one_mul]

end StrictHotSpots.PlaneGreen
end
end BoundaryPoissonIntegralsLayer
end BoundaryPoissonIntegralsScalarSupportLayer

section BoundaryExtensionScalarSupportLayer

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma poissonExtension_measurable {f : Boundary → ℝ} (hf : Measurable f) :
    Measurable (poissonExtension f) := by
  have hm : Measurable (fun z : Boundary × Plane => poisson z.1 z.2 * f z.1) :=
    poisson_joint_measurable.mul (hf.comp measurable_fst)
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

include hν in
lemma poissonExtension_memLp {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) : MemLp (poissonExtension f) 2 ν := by
  apply MemLp.of_bound (poissonExtension_measurable hf).aestronglyMeasurable B
  filter_upwards [ae_mem_disk hν] with x hx
  exact poissonExtension_norm_le hB ⟨x,hx⟩



def poissonL2 {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) : Lp ℝ 2 ν :=
  (poissonExtension_memLp hν hf hB).toLp (poissonExtension f)

end StrictHotSpots.PlaneGreen
end BoundaryExtensionScalarSupportLayer

section BoundaryKRepresentationScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)


def fullExtension {f : Boundary → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B)
    (p : disk) : ℝ := poissonExtension f p + inner ℝ (row hC hν p)
      (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (poissonL2 hν hf hB))

end StrictHotSpots.PlaneGreen
end BoundaryKRepresentationScalarSupportLayer

section BoundaryInteractionPartsScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

def firstInteraction (s t : Boundary) : ℝ := ∫ x, poisson s x * poisson t x ∂ν

def secondInteraction (s t : Boundary) : ℝ := ∫ x, poisson s x * smoothedPoisson (ν := ν) t x ∂ν

def tailInteraction (s t : Boundary) : ℝ := inner ℝ (smoothedRow hC hν s)
  (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (smoothedRow hC hν t))

def fullBoundaryR (s t : Boundary) : ℝ := firstInteraction (ν := ν) s t +
  secondInteraction (ν := ν) s t + tailInteraction hC hν s t

end StrictHotSpots.PlaneGreen
end BoundaryInteractionPartsScalarSupportLayer

section BoundaryFormScalarSupportLayer



open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def boundaryForm (R : Boundary → Boundary → ℝ) (c : Boundary → ℝ) (h k : Boundary → E) : ℝ :=
  (1/2:ℝ) * (∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
      inner ℝ (h z.1-h z.2) (k z.1-k z.2) ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ z : Boundary × Boundary, R z.1 z.2 * inner ℝ (h z.1) (k z.2) ∂boundaryMeasure.prod boundaryMeasure) +
    ∫ s, c s * inner ℝ (h s) (k s) ∂boundaryMeasure

end StrictHotSpots.PlaneGreen
end BoundaryFormScalarSupportLayer
end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Potentials
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport

noncomputable section


section PlaneWeakWeylInteriorSupportLayer


open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology
namespace StrictHotSpots.Weyl

def coord : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

def complexExtension (Ω : Set Plane) (u : Plane → ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal (Ω.indicator u (coord z))

end StrictHotSpots.Weyl

end PlaneWeakWeylInteriorSupportLayer


section WeakHodgeRegularityInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge

def WeakDivZero (Ω : Set Plane) (Z : Plane → Plane) : Prop :=
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x in Ω, inner ℝ (Z x) (gradient φ x)) = 0

end StrictHotSpots.Hodge

end WeakHodgeRegularityInteriorSupportLayer



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Hodge
attribute [-instance] _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section
section ActualNeumannHilbertLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots

instance N1.normedAddCommGroup {Ω : Set Plane} (hb : Bornology.IsBounded Ω) :
    NormedAddCommGroup (N1 hb) := (meanZeroSubmodule hb).normedAddCommGroup

instance N1.completeSpace {Ω : Set Plane} (hb : Bornology.IsBounded Ω) :
    CompleteSpace (N1 hb) := (H1.mean hb).isClosed_ker.completeSpace_coe

namespace N1
variable {Ω : Set Plane} (hb : Bornology.IsBounded Ω)

def value : N1 hb →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  H1.value.comp (meanZeroSubmodule hb).subtypeL

end N1
end StrictHotSpots

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
end ActualNeumannHilbertLayer

section HodgeOrthogonalityInteriorSupportLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots
namespace Hodge

abbrev V2 (Ω : Set Plane) : Type := Lp Plane 2 (volume.restrict Ω)

end Hodge
end StrictHotSpots

end HodgeOrthogonalityInteriorSupportLayer


section HodgeProjectionInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

def nFunctional {Ω : Set Plane} (hb : Bornology.IsBounded Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    N1 hb →L[ℝ] ℝ := (innerSL ℝ X).comp (N1.grad hb)
end StrictHotSpots.Hodge

end HodgeProjectionInteriorSupportLayer


section HodgeVectorEnergyInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge



def WeakNormalDiv {Ω : Set Plane} (X : Lp Plane 2 (volume.restrict Ω)) (F : Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  ∀ u : H1 Ω, inner ℝ X (H1.grad u) = -inner ℝ F (H1.value u)

end StrictHotSpots.Hodge

end HodgeVectorEnergyInteriorSupportLayer


end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Conformal
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalCoordinates


noncomputable section
open Set MeasureTheory _root_.Complex ComplexConjugate InnerProductSpace
open scoped InnerProductSpace Topology ContDiff
namespace StrictHotSpots.Conformal

lemma planeMul_det (a : ℂ) : (planeMul a).det = ‖a‖^2 := by
  have hh := LinearMap.det_conj
    (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).toLinearMap) coordinate.toLinearEquiv
  change LinearMap.det _ = _
  have he : (planeMul a).toLinearMap =
      (coordinate.toLinearEquiv : ℂ →ₗ[ℝ] CoordinatePlane) ∘ₗ
        ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).toLinearMap ∘ₗ
        (coordinate.toLinearEquiv.symm : CoordinatePlane →ₗ[ℝ] ℂ) := by
    ext z
    rfl
  rw [he,hh]
  simp [LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]


def planeChart (e : OpenPartialHomeomorph ℂ ℂ) :
    OpenPartialHomeomorph CoordinatePlane CoordinatePlane :=
  coordinate.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (e.trans coordinate.toHomeomorph.toOpenPartialHomeomorph)

end StrictHotSpots.Conformal
end
end ConformalCoordinates

section ConformalH10Tests


noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)

def transportTest : smoothTestSpace e.source →ₗ[ℝ] smoothTestSpace e.target where
  toFun f := ⟨CompactChart.transport e f,
    CompactChart.contDiff_transport e f.property.1 f.property.2.1 f.property.2.2 he,
    CompactChart.hasCompactSupport_transport e f.property.2.1 f.property.2.2,
    CompactChart.transport_support_target e f.property.2.1 f.property.2.2⟩
  map_add' f g := Subtype.ext (CompactChart.transport_add e f g)
  map_smul' c f := Subtype.ext (CompactChart.transport_smul e c f)

end StrictHotSpots.Conformal
end
end ConformalH10Tests

section ConformalMeasure




noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane) (d : CoordinatePlane → ℂ)

lemma map_chartMeasure
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) :
    (chartMeasure e d).map e = volume.restrict e.target := by
  have hh := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure CoordinatePlane)
    e.open_source.measurableSet.nullMeasurableSet
    (fun x hx => (hd x hx).hasFDerivWithinAt) e.injOn
  simpa only [chartMeasure, planeMul_det,abs_sq,OpenPartialHomeomorph.image_source_eq_target] using hh



end StrictHotSpots.Conformal
end
end ConformalMeasure


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenSolution
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section GreenRowContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma kernel_plane_formula (x y : Plane) : kernel x y =
    Real.log (1+(1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2)/(4*Real.pi) := by
  simp only [kernel,DiskFormula.green,← map_sub,LinearIsometryEquiv.norm_map]

end StrictHotSpots.PlaneGreen
end
end GreenRowContinuous

section GreenSolveContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)



def boundarySolutionValue [IsFiniteMeasure ν] (f : C(Boundary,ℝ)) {B : ℝ}
    (hB : ∀ s, ‖f s‖ ≤ B) (x : Plane) : ℝ :=
  poissonExtension f x + ∫ y, kernel x y *
    (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
      (poissonL2 hν f.continuous.measurable hB)) y ∂ν

end StrictHotSpots.PlaneGreen
end
end GreenSolveContinuous

section ActualBoundaryDatum

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma pullDatum_comp_H1 (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    HasH1Gradient disk (w ∘ c.diskMap) (gradient (w ∘ c.diskMap)) := by
  apply (c.pullDatum_H1 hb hs hw).congr
  · filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
    exact c.pullDatum_eq_inner hx
  · filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
    have he : c.pullDatum w =ᶠ[nhds x] w ∘ c.diskMap :=
      eventually_of_mem (diskOpen.mem_nhds hx) (fun _ hy => c.pullDatum_eq_inner hy)
    exact congrArg (InnerProductSpace.toDual ℝ Plane).symm he.fderiv_eq

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualBoundaryDatum


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section

section VectorDefectEnergyActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

def cartesianEnergy (X Y : Fin 2 → H1 Ω) : ℝ :=
  inner ℝ (H1.grad (X 0)) (H1.grad (Y 0))+inner ℝ (H1.grad (X 1)) (H1.grad (Y 1))

def cartesianForm (μ : ℝ) (X Y : Fin 2 → H1 Ω) : ℝ :=
  cartesianEnergy X Y-μ*(inner ℝ (H1.value (X 0)) (H1.value (Y 0))+
    inner ℝ (H1.value (X 1)) (H1.value (Y 1)))

end StrictHotSpots.Hodge
end VectorDefectEnergyActualCompatibleLayer

section GradientVectorEnergyActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal Topology
namespace StrictHotSpots
namespace Hodge
variable {Ω : Set Plane}


def NeumannEuler (μ : ℝ) (u : H1 Ω) : Prop := ∀ w : H1 Ω,
  inner ℝ (H1.grad u) (H1.grad w)=μ*inner ℝ (H1.value u) (H1.value w)

end Hodge
end StrictHotSpots
end GradientVectorEnergyActualCompatibleLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
end
end ActualVectorSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PhysicalHelmholtz

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PhysicalHelmholtz
variable {Ω : Set Plane} (ho : IsOpen Ω)
local instance instInnerProductSpaceRealSubtypeH1AmbientMemSubmoduleH1H10 : InnerProductSpace ℝ (H10 ho) := H10.innerProductSpace ho
local instance instNormedSpaceRealSubtypeH1AmbientMemSubmoduleH1H10 : NormedSpace ℝ (H10 ho) := (H10.innerProductSpace ho).toNormedSpace
local instance instNormedSpaceRealSubtypeH1AmbientMemSubmoduleH1 : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace

def pair (μ : ℝ) : H1 Ω →L[ℝ] H1 Ω →L[ℝ] ℝ :=
  ((innerSL ℝ).comp H1.grad).flip.comp H1.grad -
    μ • ((innerSL ℝ).comp H1.value).flip.comp H1.value

end StrictHotSpots.PhysicalHelmholtz
end
end PhysicalHelmholtz

section LipschitzMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

lemma physical_boundary_lipschitz {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) : LipschitzWith ((B*c.Lip)*1)
      (fun s : Boundary => b (c.F s)) :=
  (hb.comp c.lipschitz).comp (LipschitzWith.subtype_val _)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end LipschitzMultiplierKernel


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedSolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section GreenClosedContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma norm_le_of_mem_closure_disk {x : Plane} (hx : x ∈ closure disk) : ‖x‖ ≤ 1 := by
  simpa only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
    mem_closedBall_zero_iff] using hx

lemma mem_disk_of_norm_lt {x : Plane} (hx : ‖x‖ < 1) : x ∈ disk := by
  simpa only [disk,mem_ball_zero_iff] using hx

lemma kernel_zero_left {x : Plane} (hx : ‖x‖ = 1) (y : Plane) : kernel x y = 0 := by
  simp [kernel_plane_formula,hx]

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma kernel_memLp_closed (x : Plane) (hx : x ∈ closure disk) : MemLp (kernel x) 2 ν := by
  by_cases hi : ‖x‖ < 1
  · exact kernel_memLp_weighted hC hν x (mem_disk_of_norm_lt hi)
  · have hn : ‖x‖ = 1 := le_antisymm (norm_le_of_mem_closure_disk hx) (not_lt.mp hi)
    have he : kernel x = 0 := funext (kernel_zero_left hn)
    rw [he]
    exact MemLp.zero


def closedRow (x : closure disk) : Lp ℝ 2 ν :=
  (kernel_memLp_closed hC hν x x.property).toLp (kernel x)

end StrictHotSpots.PlaneGreen
end
end GreenClosedContinuous

section BoundaryClosedSolution

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

def boundaryClosedPoisson (f : C(Boundary,ℝ)) : Plane → ℝ :=
  Douglas.closedPlanePoisson (boundaryAngleData f)

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)



def boundaryClosedSolution (f : C(Boundary,ℝ)) {B : ℝ}
    (hB : ∀ s, ‖f s‖ ≤ B) (x : Plane) : ℝ :=
  boundaryClosedPoisson f x + ∫ y, kernel x y *
    (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
      (poissonL2 hν f.continuous.measurable hB)) y ∂ν

end StrictHotSpots.PlaneGreen
end
end BoundaryClosedSolution

section PhysicalMultiplierClosed

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

def multiplierTrace {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b)
    (w : Plane → ℝ) (hw : ContinuousOn w (closure Ω)) : C(Boundary,ℝ) where
  toFun s := b (c.F s)*w (c.F s)
  continuous_toFun := (c.physical_boundary_lipschitz hb).continuous.mul (c.datumTrace w hw).continuous

end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalMultiplierClosed


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualInteriorEigenSupport



noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology
namespace StrictHotSpots.Helmholtz

def coord : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

def complexExtension (Ω : Set Plane) (u : Plane → ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal (Ω.indicator u (coord z))

end StrictHotSpots.Helmholtz


section WeakEigenRegularityActualInteriorLayer
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace StrictHotSpots




def InInteriorNeumannEigenspace (Ω : Set Plane) (u : Plane → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u Ω ∧ HasH1Gradient Ω u (gradient u) ∧
    (∫ x in Ω, u x) = 0 ∧
    ∀ (v : Plane → ℝ) (g : Plane → Plane), HasH1Gradient Ω v g →
      (∫ x in Ω, inner ℝ (gradient u x) (g x)) =
        firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x)

end StrictHotSpots
end
end WeakEigenRegularityActualInteriorLayer


end
end ActualInteriorEigenSupport

section ClosedEigenAlgebra

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace StrictHotSpots

lemma InInteriorNeumannEigenspace.differentiableAt {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) (ho : IsOpen Ω) {x : Plane} (hx : x ∈ Ω) :
    DifferentiableAt ℝ u x :=
  ((hu.1 x hx).contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)

lemma gradient_add_at {u v : Plane → ℝ} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    gradient (u+v) x = gradient u x + gradient v x := by
  simp only [gradient,(hu.hasFDerivAt.add hv.hasFDerivAt).fderiv,map_add]

lemma gradient_smul_at {u : Plane → ℝ} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (a : ℝ) : gradient (a • u) x = a • gradient u x := by
  simp only [gradient,(hu.hasFDerivAt.const_smul a).fderiv,map_smul]

lemma InInteriorNeumannEigenspace.add {Ω : Set Plane} {u v : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) (hv : InInteriorNeumannEigenspace Ω v)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) : InInteriorNeumannEigenspace Ω (u+v) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hgrad : (gradient u+gradient v) =ᵐ[volume.restrict Ω] gradient (u+v) :=
    (ae_restrict_iff' ho.measurableSet).mpr (Eventually.of_forall fun x hx =>
      (gradient_add_at (hu.differentiableAt ho hx) (hv.differentiableAt ho hx)).symm)
  refine ⟨hu.1.add hv.1,(hu.2.1.add hv.2.1).congr (EventuallyEq.refl _ _) hgrad,?_,?_⟩
  · simp only [Pi.add_apply]
    rw [integral_add]
    · rw [hu.2.2.1,hv.2.2.1,add_zero]
    · exact hu.2.1.1.integrable (by norm_num)
    · exact hv.2.1.1.integrable (by norm_num)
  · intro w g hw
    calc
      (∫ x in Ω, inner ℝ (gradient (u+v) x) (g x)) =
          ∫ x in Ω, inner ℝ (gradient u x + gradient v x) (g x) := by
        apply integral_congr_ae
        filter_upwards [hgrad] with x hx
        rw [← hx]
        rfl
      _ = (∫ x in Ω, inner ℝ (gradient u x) (g x)) +
          (∫ x in Ω, inner ℝ (gradient v x) (g x)) := by
        simp only [inner_add_left]
        exact integral_add (integrable_inner_of_memLp hu.2.1.2.1 hw.2.1)
          (integrable_inner_of_memLp hv.2.1.2.1 hw.2.1)
      _ = firstPositiveNeumannValue Ω * (∫ x in Ω, u x*w x) +
          firstPositiveNeumannValue Ω * (∫ x in Ω, v x*w x) := by
        rw [hu.2.2.2 w g hw,hv.2.2.2 w g hw]
      _ = firstPositiveNeumannValue Ω * (∫ x in Ω, (u+v) x*w x) := by
        simp only [Pi.add_apply,add_mul]
        have hiu : Integrable (fun x => u x*w x) (volume.restrict Ω) := hu.2.1.1.integrable_mul hw.1
        have hiv : Integrable (fun x => v x*w x) (volume.restrict Ω) := hv.2.1.1.integrable_mul hw.1
        rw [integral_add hiu hiv,mul_add]

lemma InInteriorNeumannEigenspace.smul {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) (ho : IsOpen Ω) (a : ℝ) :
    InInteriorNeumannEigenspace Ω (a • u) := by
  have hgrad : (a • gradient u) =ᵐ[volume.restrict Ω] gradient (a • u) :=
    (ae_restrict_iff' ho.measurableSet).mpr (Eventually.of_forall fun x hx =>
      (gradient_smul_at (hu.differentiableAt ho hx) a).symm)
  refine ⟨hu.1.const_smul a,(hu.2.1.smul a).congr (EventuallyEq.refl _ _) hgrad,?_,?_⟩
  · simp only [Pi.smul_apply,smul_eq_mul,integral_const_mul,hu.2.2.1,mul_zero]
  · intro w g hw
    calc
      (∫ x in Ω, inner ℝ (gradient (a • u) x) (g x)) =
          ∫ x in Ω, inner ℝ (a • gradient u x) (g x) := by
        apply integral_congr_ae
        filter_upwards [hgrad] with x hx
        rw [← hx]
        rfl
      _ = a * (∫ x in Ω, inner ℝ (gradient u x) (g x)) := by
        simp only [real_inner_smul_left,integral_const_mul]
      _ = firstPositiveNeumannValue Ω * (∫ x in Ω, (a • u) x*w x) := by
        rw [hu.2.2.2 w g hw]
        simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
        ring

lemma InInteriorNeumannEigenspace.zero (Ω : Set Plane) : InInteriorNeumannEigenspace Ω 0 := by
  have hg : gradient (0 : Plane → ℝ) = 0 := by
    ext x
    simp [gradient]
  refine ⟨contDiffOn_const,?_,by simp,?_⟩
  · rw [hg]
    refine ⟨MemLp.zero,MemLp.zero,?_⟩
    intro φ _ _ _ e
    simp
  · intro w g hw
    simp only [hg,Pi.zero_apply,inner_zero_left,zero_mul,integral_zero,mul_zero]




def closedEigenJet (Ω : Set Plane) (v : Plane → ℝ) (Y : Plane → Plane) : ClosedEigenJet Ω :=
  (fun x => v x, fun x => Y x)




def closedEigenSpace (Ω : Set Plane) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    Submodule ℝ (ClosedEigenJet Ω) where
  carrier := {J | ∃ v Y, InInteriorNeumannEigenspace Ω v ∧ ContinuousOn v (closure Ω) ∧
    ContinuousOn Y (closure Ω) ∧ EqOn (gradient v) Y Ω ∧ closedEigenJet Ω v Y = J}
  zero_mem' := by
    refine ⟨0,0,InInteriorNeumannEigenspace.zero Ω,continuousOn_const,continuousOn_const,?_,rfl⟩
    intro x hx
    simp [gradient]
  add_mem' := by
    rintro J K ⟨u,Y,hu,huc,hY,huY,rfl⟩ ⟨v,Z,hv,hvc,hZ,hvZ,rfl⟩
    refine ⟨u+v,Y+Z,hu.add hv ho hb,huc.add hvc,hY.add hZ,?_,rfl⟩
    intro x hx
    rw [gradient_add_at (hu.differentiableAt ho hx) (hv.differentiableAt ho hx),huY hx,hvZ hx]
    rfl
  smul_mem' := by
    rintro a J ⟨u,Y,hu,huc,hY,huY,rfl⟩
    refine ⟨a • u,a • Y,hu.smul ho a,huc.const_smul a,hY.const_smul a,?_,rfl⟩
    intro x hx
    rw [gradient_smul_at (hu.differentiableAt ho hx) a,huY hx]
    rfl

end StrictHotSpots
end
end ClosedEigenAlgebra

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedEigenMultiplicity

noncomputable section
open Set Metric Function Module
open scoped Topology InnerProductSpace
namespace StrictHotSpots
open PlaneGreen DiskH10


def closedScalarEval {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (x : closure Ω) : closedEigenSpace Ω ho hb →ₗ[ℝ] ℝ where
  toFun J := J.val.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl




end StrictHotSpots
end
end ClosedEigenMultiplicity


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Cauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedEigenLocalRank

noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots


def closedPatchEigenSpace (Ω O : Set Plane) (hΩ : AdmissibleDomain Ω) :
    Submodule ℝ (ClosedEigenJet Ω) where
  carrier := {J | J ∈ closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 ∧
    ∀ x : closure Ω, (x : Plane) ∈ O ∩ frontier Ω → J.2 x = 0}
  zero_mem' := ⟨(closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1).zero_mem,by simp⟩
  add_mem' := by
    intro J K hJ hK
    refine ⟨(closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1).add_mem hJ.1 hK.1,?_⟩
    intro x hx
    change J.2 x + K.2 x = 0
    rw [hJ.2 x hx,hK.2 x hx,add_zero]
  smul_mem' := by
    intro a J hJ
    refine ⟨(closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1).smul_mem a hJ.1,?_⟩
    intro x hx
    change a • J.2 x = 0
    rw [hJ.2 x hx,smul_zero]

def closedPatchEval {Ω O : Set Plane} (hΩ : AdmissibleDomain Ω) {p : Plane}
    (hp : p ∈ frontier Ω) : closedPatchEigenSpace Ω O hΩ →ₗ[ℝ] ℝ where
  toFun J := J.val.1 ⟨p,hp.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end StrictHotSpots
end
end ClosedEigenLocalRank



end OAI
end


