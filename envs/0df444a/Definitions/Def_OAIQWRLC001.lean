-- Prove2me | Definitions.Def_OAIQWRLC001
-- name    : OAIQWRLC001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T02:01:07.332215+00:00
-- url     : https://prove2.me/theorems/2f1b6def-85e8-48f4-99de-acdcb05dfb49
-- title:
--   Definitions bundle OAIQWRLC001 of the split of OpenAI, Localization costs and information growth for exact Gaussian observations
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KernelPotential.actual_row_drift`, `OAI.KernelPotential.kernel_coercivity` and `OAI.AllScaleInverseVolume.inverse_volume_without_support`, carved from OpenAI's openai/math development (OpenAI, *Localization costs and information growth for exact Gaussian observations*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to this platform's Lean and Mathlib. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 93 declarations of OpenAI's Lean: 89 definitions, 2 inductive types or structures, 1 instance and 1 theorem. The definitions and types are `OAI.AllScaleInverseVolume.BinEvent`, `OAI.AllScaleInverseVolume.Greedy`, `OAI.AllScaleInverseVolume.GreedyEvent`, `OAI.AllScaleInverseVolume.InBins`, `OAI.AllScaleInverseVolume.StageEvent`, `OAI.AllScaleInverseVolume.Suborthonormal`, `OAI.AllScaleInverseVolume.baseExponent`, `OAI.AllScaleInverseVolume.binGap`, `OAI.AllScaleInverseVolume.binInverseExponent`, `OAI.AllScaleInverseVolume.clippedInverse`, `OAI.AllScaleInverseVolume.clippedLength`, `OAI.AllScaleInverseVolume.coordinates`, `OAI.AllScaleInverseVolume.diagonalMap`, `OAI.AllScaleInverseVolume.dyadicRadius`, `OAI.AllScaleInverseVolume.gramTriangular`, `OAI.AllScaleInverseVolume.groupedTube`, `OAI.AllScaleInverseVolume.integerWeight`, `OAI.AllScaleInverseVolume.negativeSum`, `OAI.AllScaleInverseVolume.orthoResidual`, `OAI.AllScaleInverseVolume.positiveSum`, `OAI.AllScaleInverseVolume.prefixAxes`, `OAI.AllScaleInverseVolume.prefixResidual`, `OAI.AllScaleInverseVolume.rawInverse`, `OAI.AllScaleInverseVolume.residual`, `OAI.AllScaleInverseVolume.residualScore`, `OAI.AllScaleInverseVolume.stageExponent`, `OAI.AllScaleInverseVolume.synth`, `OAI.AllScaleInverseVolume.totalExponent`, `OAI.AllScaleInverseVolume.translated`, `OAI.GaussianTools.labelDensity`, `OAI.GaussianTools.scalarRow`, `OAI.KernelPotential.Bayes.clippedJ`, `OAI.KernelPotential.Bayes.mass`, `OAI.KernelPotential.Bayes.post`, `OAI.KernelPotential.Bayes.referenceWeight`, `OAI.KernelPotential.Coercivity.sphereMoment`, `OAI.KernelPotential.Continuity.densityLaw`, `OAI.KernelPotential.DriftCutoff.level`, `OAI.KernelPotential.DriftTools.FiniteReference.C`, `OAI.KernelPotential.DriftTools.FiniteReference.joint` and 51 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/GaussianInformation, in whole or in part: `GaussianInformation_Inverse_ClippedMoments`, `GaussianInformation_Inverse_DyadicBins`, `GaussianInformation_Inverse_Ellipsoids`, `GaussianInformation_Inverse_ExponentBounds`, `GaussianInformation_Inverse_GramVolume`, `GaussianInformation_Inverse_GreedyOrder`, `GaussianInformation_Inverse_InverseMoments`, `GaussianInformation_Inverse_Orthogonal`, `GaussianInformation_Inverse_StageEvents`, `GaussianInformation_Inverse_Tubes`, `GaussianInformation_Kernel_Bayes`, `GaussianInformation_Kernel_BoxKernels`, `GaussianInformation_Kernel_Coercivity`, `GaussianInformation_Kernel_DriftCutoff`, `GaussianInformation_Kernel_Entropy`, `GaussianInformation_Kernel_GaussianImages`, `GaussianInformation_Kernel_GaussianReference`, `GaussianInformation_Kernel_GaussianRows`, `GaussianInformation_Kernel_GramVolume`, `GaussianInformation_Kernel_JointCompensation`, `GaussianInformation_Kernel_JointRules`, `GaussianInformation_Kernel_LocalRules`, `GaussianInformation_Kernel_MassPotential`, `GaussianInformation_Kernel_MixedProjection`, `GaussianInformation_Kernel_NoiseContinuity`, `GaussianInformation_Kernel_NoiseLaw`, `GaussianInformation_Kernel_NoisyProjection`, `GaussianInformation_Kernel_OutgoingLaws`, `GaussianInformation_Kernel_PairReference`, `GaussianInformation_Kernel_PositiveRules`, `GaussianInformation_Kernel_PotentialContinuity`, `GaussianInformation_Kernel_ProjectionMoments`, `GaussianInformation_Kernel_ReferenceBounds`, `GaussianInformation_Kernel_ReferenceMarginals`, `GaussianInformation_Kernel_ReplicaMoments`, `GaussianInformation_Kernel_Reweighting`, `GaussianInformation_Kernel_RowConcatenation`, `GaussianInformation_Kernel_SampleEquivalence`, `GaussianInformation_Kernel_SampleLaw`, `GaussianInformation_Kernel_Scaling`, `GaussianInformation_Kernel_SimplexApproximation`, `GaussianInformation_Kernel_Sphere`.
--
--   **Imports.** It imports the published bundles `Def_GaussianInformation_002` and `Def_GaussianInformation_003`.
--
--   **Imported by** (directly, in this split): the statements `OAI.KernelPotential.MassPotential.local_energy_bound`, `OAI.KernelPotential.Noise.weighted_centered_projection` and `OAI.KernelPotential.NoisyDrift.positive_noisy_comparison`; the proofs of `OAI.AllScaleInverseVolume.inverse_volume_without_support`, `OAI.KernelPotential.MassPotential.local_energy_bound`, `OAI.KernelPotential.Noise.weighted_centered_projection`, `OAI.KernelPotential.NoisyDrift.positive_noisy_comparison`, `OAI.KernelPotential.actual_row_drift` and `OAI.KernelPotential.kernel_coercivity`.
-- source:
--   OpenAI, Localization costs and information growth for exact Gaussian observations, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/GaussianInformation at commit adc7f12

import Mathlib
import Definitions.Def_GaussianInformation_002
import Definitions.Def_GaussianInformation_003

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_Ellipsoids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
noncomputable def diagonalMap {q : ℕ} (c : Fin q → ℝ) : Ambient q →ₗ[ℝ] Ambient q :=
  Matrix.toEuclideanLin (Matrix.diagonal c)

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_Tubes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
noncomputable def synth {q d : ℕ} (e : Fin q → Ambient d) (x : Ambient q) : Ambient d :=
  ∑ j,x j • e j
noncomputable def coordinates {q d : ℕ} (e : Fin q → Ambient d) (x : Ambient d) : Ambient q :=
  WithLp.toLp 2 (fun j => inner ℝ (e j) x)
noncomputable def residual {q d : ℕ} (e : Fin q → Ambient d) (x : Ambient d) : Ambient d :=
  x-synth e (coordinates e x)

def groupedTube {q d : ℕ} (e : Fin q → Ambient d) (g : Fin q → ℕ) (r : ℝ) : Set (Ambient d) :=
  {x | ‖residual e x‖ ≤ r ∧ ∀ h : ℕ,
    ∑ j ∈ Finset.univ.filter (fun j => g j=h),(inner ℝ (e j) x)^2 ≤ r^2*(4:ℝ)^h}

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_Orthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace

def Suborthonormal {d k : ℕ} (e : Fin k → Ambient d) : Prop :=
  Pairwise (fun i j => inner ℝ (e i) (e j)=0) ∧ ∀ j,e j=0 ∨ ‖e j‖=1

noncomputable def orthoResidual {d k : ℕ} (e : Fin k → Ambient d) (s : Finset (Fin k))
    (x : Ambient d) : Ambient d := x-∑ j ∈ s,(inner ℝ (e j) x) • e j

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_GramVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gramTriangular {q : ℕ} (f : Fin q → E) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (if i = j then 1 else 0) +
    (if i < j then ⟪gramSchmidt ℝ f i, f j⟫ / ‖gramSchmidt ℝ f i‖ ^ 2 else 0)

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_GreedyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def Greedy {α : Type*} {k : ℕ} (D : (Fin k → α) → Fin k → α → ℝ) (f : Fin k → α) : Prop :=
  ∀ i j : Fin k,i ≤ j → D f i (f j) ≤ D f i (f i)

noncomputable def prefixResidual {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k)
    (x : Ambient d) : Ambient d := orthoResidual (gramSchmidtNormed ℝ f) (Finset.Iio i) x
noncomputable def prefixAxes {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) : Fin k → Ambient d :=
  fun j => if j < i then gramSchmidtNormed ℝ f j else 0

noncomputable def residualScore {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) (x : Ambient d) : ℝ :=
  ‖prefixResidual f i x‖

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_DyadicBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def dyadicRadius (l : ℤ) : ℝ := (2:ℝ)^(-l)

noncomputable def clippedLength {d k : ℕ} (ε : ℝ) (f : Fin k → Ambient d) (i : Fin k) :=
  max ‖gramSchmidt ℝ f i‖ ε

def InBins {d k : ℕ} (ε : ℝ) (f : Fin k → Ambient d) (l : Fin k → ℤ) : Prop :=
  ∀ i,dyadicRadius (l i+1)<clippedLength ε f i ∧ clippedLength ε f i≤dyadicRadius (l i)

noncomputable def binGap {k : ℕ} (l : Fin k → ℤ) (i j : Fin k) : ℕ :=
  if j < i then (l i-l j).toNat else 0

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_StageEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def translated {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d) : Fin k → Ambient d :=
  fun i => z i-u

noncomputable def StageEvent {d k : ℕ} (u : Ambient d) (l : Fin k → ℤ) (i : Fin k)
    (z : Fin k → Ambient d) : Prop :=
  0 ≤ l i → z i-u∈groupedTube (prefixAxes (translated u z) i) (binGap l i) (dyadicRadius (l i))

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_ExponentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def positiveSum {k : ℕ} (l : Fin k → ℤ) : ℝ := ∑ i,max (l i:ℝ) 0
noncomputable def negativeSum {k : ℕ} (l : Fin k → ℤ) : ℝ := ∑ i,max (-(l i:ℝ)) 0

noncomputable def stageExponent {d k : ℕ} (l : Fin k → ℤ) (i : Fin k) : ℝ :=
  k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3+
    Real.log 2*((2*k-(((d:ℝ)-1)/2))*max (l i:ℝ) 0+2*negativeSum l)
noncomputable def totalExponent {d k : ℕ} (l : Fin k → ℤ) : ℝ :=
  k*(k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3)+
    Real.log 2*((2*k-(((d:ℝ)-1)/2))*positiveSum l+2*k*negativeSum l)

noncomputable def BinEvent {d k : ℕ} (ε : ℝ) (u : Ambient d) (l : Fin k → ℤ) : Set (Fin k → Ambient d) :=
  {z | Greedy residualScore (translated u z) ∧ InBins ε (translated u z) l}

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_ClippedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def integerWeight (l : ℤ) : ℝ≥0∞ := (1/2:ℝ≥0∞)^l.natAbs
noncomputable def clippedInverse {d k : ℕ} (ε : ℝ) (f : Fin k → Ambient d) : ℝ≥0∞ :=
  ∏ i,((ENNReal.ofReal (clippedLength ε f i))⁻¹)^k
noncomputable def binInverseExponent {k : ℕ} (l : Fin k → ℤ) : ℝ :=
  Real.log 2*(k*k+k*(positiveSum l-negativeSum l))
noncomputable def baseExponent (d k : ℕ) : ℝ :=
  k*(k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3)+Real.log 2*k*k

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def GreedyEvent {d k : ℕ} (u : Ambient d) : Set (Fin k → Ambient d) :=
  {z | Greedy residualScore (translated u z)}

noncomputable def rawInverse {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d) : ℝ≥0∞ :=
  ((ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ (translated u z)).det))⁻¹)^k

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GaussianRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaussianTools
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def scalarRow (d : ℕ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

noncomputable def labelDensity {p : ℕ} (r : ℝ) (y : Fin p → ℝ) : ℝ :=
  ∏ i,gaussianPDFReal 0 (NNReal.mk (r^2) (sq_nonneg r)) (y i)

end GaussianTools

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Sphere

noncomputable def unitVolume (d : ℕ) : Measure (Ambient d) :=
  (volume (ball (0 : Ambient d) 1))⁻¹ • volume

end Sphere

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace EntropySupport
noncomputable def xlog (x : ℝ) : ℝ := x * Real.log x

end EntropySupport

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Coercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Coercivity
open Sphere

open EntropySupport

noncomputable def sphereMoment (d : ℕ) : ℝ := 1+(9*3^d:ℝ)*2^((d-1)+4*(d/16)+1)

end Coercivity
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_BoxKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Support

noncomputable def closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) : Set (Fin k → ℝ) :=
  {u | ∀ i, |u i-c i| ≤ η}

noncomputable def boxScale (k : ℕ) (η : ℝ) : ℝ≥0∞ := (ENNReal.ofReal ((2*η)^k))⁻¹

noncomputable def boxKernel {k : ℕ} (η : ℝ) (c u : Fin k → ℝ) : ℝ≥0∞ :=
  (closedBox c η).indicator (fun _ => boxScale k η) u

end Support

open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GramVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Support

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gramTriangular {q : ℕ} (f : Fin q → E) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (if i = j then 1 else 0) +
    (if i < j then ⟪gramSchmidt ℝ f i, f j⟫ / ‖gramSchmidt ℝ f i‖ ^ 2 else 0)

end Support

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReplicaMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Support
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def replicaPlane {q : ℕ} (b : E) (f : Fin q → E) : AffineSubspace ℝ E :=
  AffineSubspace.mk' b (Submodule.span ℝ (range f))

noncomputable def gramInverseProduct {q : ℕ} (k : ℕ) (f : Fin q → E) : ℝ≥0∞ :=
  ∏ i, (ENNReal.ofReal ‖gramSchmidt ℝ f i‖)⁻¹ ^ k

end Support

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GaussianImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Support
open Matrix WithLp
open scoped MatrixOrder RealInnerProductSpace

noncomputable def rowMatrix {q d : ℕ} (f : Fin q → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin q) (Fin d) ℝ := fun i j => f i j

end Support

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ProjectionMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Support
open Metric Matrix WithLp

noncomputable def gaussianRows (k d : ℕ) : Measure (Fin k → Fin d → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 1))

noncomputable def projectVector {k d : ℕ} (X : Fin k → Fin d → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Fin k → ℝ := fun r => ∑ j, X r j * v j

lemma continuous_projectVector {k d : ℕ} :
    Continuous (fun p : (Fin k → Fin d → ℝ) × EuclideanSpace ℝ (Fin d) => projectVector p.1 p.2) := by
  unfold projectVector
  fun_prop

end Support

open Support

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_MixedProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open Support

noncomputable def mixedCubeAverage {k d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (η : ℝ) (X Z : Fin k → Fin d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, boxKernel η (projectVector X x) 0 * boxKernel η (projectVector Z x) 0 ∂μ

end Projection

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Reweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Reweight
open Coercivity Sphere
noncomputable def rho {d : ℕ} (ν : Measure (Ambient d)) : Measure (Ambient d) :=
  ν.withDensity (fun s => (J ν s)⁻¹)

noncomputable def centeredRho {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : Measure (Ambient d) :=
  (rho ν).map (fun u => u-s)

end Reweight
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoiseLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight

noncomputable def noiseLaw (k : ℕ) (η : ℝ) : Measure (Fin k → ℝ) :=
  volume.withDensity (boxKernel η 0)

noncomputable def projectedReference {k d : ℕ} (ν : Measure (Ambient d)) (η : ℝ)
    (X Z : Fin k → Fin d → ℝ) (y z : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ u,boxKernel η (projectVector X u) y*boxKernel η (projectVector Z u) z ∂rho ν

end KernelPotential.Noise

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight EntropySupport Sphere

noncomputable def momentConstant (d L : ℕ) : ℝ :=
  (9^(d/16-1)*3^(d-1)*2^((d-1)+4*(d/16)+2):ℝ)*((L:ℝ)+2)

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential

namespace Scale
open Sphere Coercivity

noncomputable def radius (j : ℕ) : ℝ := 2*(1/2:ℝ)^j

end Scale

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GaussianReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open GaussianTools

abbrev Mat (p d : ℕ) := Fin p → Fin d → ℝ
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
noncomputable def applyRows {p d : ℕ} (X : Mat p d) (s : Vec d) : Fin p → ℝ :=
  fun i => ∑ j,X i j*s j

noncomputable def atDensity {p d : ℕ} (r : ℝ) (X : Mat p d) (y : Fin p → ℝ) (u : Vec d) : ℝ :=
  labelDensity r (y-applyRows X u)

noncomputable def densityBound (p : ℕ) (r : ℝ) : ℝ := (Real.sqrt (2*Real.pi*r^2))⁻¹^p

noncomputable def mixture {p d L : ℕ} (ν : Measure (Vec d)) (r : Fin L → ℝ)
    (X : Mat p d) (y : Fin p → ℝ) : ℝ :=
  (L:ℝ)⁻¹*∑ j,∫ u,atDensity (r j) X y u ∂ν

end ReferenceGaussian

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open GaussianTools

noncomputable def energy {p d : ℕ} (X : Mat p d) (v : Vec d) (e : Fin p → ℝ) : ℝ :=
  ∑ i,(applyRows X v i+e i)^2
noncomputable def matEnergy {p d : ℕ} (X : Mat p d) : ℝ := ∑ i,∑ j,(X i j)^2

end ReferenceGaussian

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_RowConcatenation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace RowConcat
abbrev index (k : ℕ) : Fin k ⊕ Fin k ≃ Fin (2*k) :=
  finSumFinEquiv.trans (finCongr (by omega))
noncomputable def join {E : Type*} [MeasurableSpace E] (k : ℕ) :
    ((Fin k → E) × (Fin k → E)) ≃ᵐ (Fin (2*k) → E) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => E)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (2*k) => E) (index k))

end RowConcat

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_PairReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.PairReference
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Sphere Coercivity Scale ReferenceGaussian GaussianTools RowConcat
noncomputable def density {k d L : ℕ} (ν : Measure (Ambient d)) (r : Fin L → ℝ)
    (X Z : Mat k d) (y z : Fin k → ℝ) : ℝ :=
  mixture ν r (join k (X,Z)) (join k (y,z))

end KernelPotential.PairReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SampleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight

abbrev Observation (k d : ℕ) :=
  ((Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ))
noncomputable def observationBase (k d : ℕ) : Measure (Observation k d) :=
  ((gaussianRows k d).prod (gaussianRows k d)).prod
    ((volume : Measure (Fin k → ℝ)).prod volume)
noncomputable def observationKernel {k d : ℕ} (η : ℝ) (z : Observation k d) (s : Ambient d) : ℝ≥0∞ :=
  boxKernel η (projectVector z.1.1 s) z.2.1*boxKernel η (projectVector z.1.2 s) z.2.2

instance observationBase_sigmaFinite (k d : ℕ) : SigmaFinite (observationBase k d) := by
  unfold observationBase gaussianRows
  infer_instance

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SampleEquivalence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support
noncomputable def samplingLaw (k d : ℕ) (η : ℝ) : Measure (Observation k d) :=
  ((gaussianRows k d).prod (gaussianRows k d)).prod ((noiseLaw k η).prod (noiseLaw k η))

noncomputable def sampleEquiv {k d : ℕ} (s : Ambient d) : Observation k d ≃ᵐ Observation k d where
  toFun t := (t.1,(projectVector t.1.1 s+t.2.1,projectVector t.1.2 s+t.2.2))
  invFun t := (t.1,(t.2.1-projectVector t.1.1 s,t.2.2-projectVector t.1.2 s))
  left_inv t := by simp
  right_inv t := by simp
  measurable_toFun := by dsimp; have hP := continuous_projectVector (k := k) (d := d); fun_prop
  measurable_invFun := by dsimp; have hP := continuous_projectVector (k := k) (d := d); fun_prop

attribute [local irreducible] sampleEquiv

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Bayes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open EntropySupport Coercivity Sphere

noncomputable def mass {α : Type*} [MeasurableSpace α] (ν : Measure α) (r : α → ℝ) : ℝ := ∫ s,r s ∂ν
noncomputable def post {α : Type*} [MeasurableSpace α] (ν : Measure α) (r : α → ℝ) : Measure α :=
  ν.withDensity (fun s => ENNReal.ofReal (r s/mass ν r))

noncomputable def clippedJ {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : ℝ :=
  max ((1/2:ℝ)^(2*(d/16))) (J ν s).toReal

noncomputable def referenceWeight {d : ℕ} (ν : Measure (Ambient d)) (r : Ambient d → ℝ)
    (s : Ambient d) : ℝ := r s/(mass ν r*clippedJ (post ν r) s)

end KernelPotential.Bayes

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_JointCompensation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.DriftTools

namespace FiniteReference
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def joint (ν : Measure α) (Λ : Measure β)
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞) : Measure (α × β × ι) :=
  (ν.prod (Λ.prod Measure.count)).withDensity (fun x => K x.2.1 x.1 * κ x.2.1 x.2.2)

noncomputable def C (ν : Measure α) (K : β → α → ℝ≥0∞) (x : ι → α → ℝ≥0∞)
    (z : β) (w : ι) : ℝ≥0∞ := ∫⁻ s,K z s*x w s ∂ν

end FiniteReference

end KernelPotential.DriftTools

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def likelihood (Λ : Measure β) (K : β → α → ℝ≥0∞)
    (κ : β → ι → ℝ≥0∞) (s : α) (w : ι) : ℝ := (∫⁻ z,K z s*κ z w ∂Λ).toReal

end KernelPotential.DriftTools.FiniteReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_DriftCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.DriftCutoff

noncomputable def level (d : ℕ) (H : ℝ) : ℕ := ⌈2*Real.log H+20*(d:ℝ)⌉₊+1

end KernelPotential.DriftCutoff

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_PositiveRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference

structure PositiveRule (k d N : ℕ) where
  prob : ((Mat k d) × (Fin k → ℝ)) → Fin N → ℝ
  measurable_prob : Measurable (Function.uncurry prob)
  sum_prob : ∀ t,∑ w,prob t w=1
  lower : ℝ
  lower_pos : 0 < lower
  lower_prob : ∀ t w,lower ≤ prob t w

namespace PositiveRule
variable {k d N : ℕ} (rule : PositiveRule k d N)
noncomputable def kernel (z : Observation k d) (w : Fin N) : ℝ≥0∞ :=
  ENNReal.ofReal (rule.prob (z.1.1,z.2.1) w)
noncomputable def response (η : ℝ) (w : Fin N) (s : Ambient d) : ℝ :=
  likelihood (observationBase k d) (observationKernel η) rule.kernel s w
end PositiveRule
end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoiseContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift.PositiveRule
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference
variable {k d N : ℕ} (rule : PositiveRule k d N)
noncomputable def exactResponse (w : Fin N) (s : Ambient d) : ℝ :=
  ∫ X,rule.prob (X,projectVector X s) w ∂gaussianRows k d
end KernelPotential.NoisyDrift.PositiveRule

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_LocalRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference
structure LocalRule (k d N : ℕ) where
  prob : ((Mat k d) × (Fin k → ℝ)) → Fin N → ℝ
  measurable : ∀ w,Measurable (fun t => prob t w)
  nonneg : ∀ t w,0 ≤ prob t w
  sum : ∀ t,∑ w,prob t w=1
namespace LocalRule
variable {k d N : ℕ} (rule : LocalRule k d N)
noncomputable def response (w : Fin N) (s : Ambient d) : ℝ :=
  ∫ X,rule.prob (X,projectVector X s) w ∂gaussianRows k d
noncomputable def positive (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : PositiveRule k d N where
  prob := fun t w => (1-ε)*rule.prob t w+ε/(N:ℝ)
  measurable_prob := by
    apply measurable_from_prod_countable_left
    intro w
    exact ((rule.measurable w).const_mul _).add_const _
  sum_prob := by
    intro t
    rw [Finset.sum_add_distrib,← Finset.mul_sum,rule.sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    ring
  lower := ε/(N:ℝ)
  lower_pos := div_pos hε (by exact_mod_cast hN)
  lower_prob := fun t w => le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hε1) (rule.nonneg t w))
end LocalRule
end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_OutgoingLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.FiniteMessage
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open NoisyDrift GaussianTools ReferenceGaussian Noise Bayes Projection Projection.Support
variable {d N : ℕ}
def localRule (rule : BlockRule d N) (v : Fin N) : LocalRule (d/16) d N where
  prob := fun t w => rule.prob (v,t) w
  measurable := fun w => (rule.measurable_prob w).comp (measurable_const.prodMk measurable_id)
  nonneg := fun input message => rule.nonneg_prob (v,input) message
  sum := fun input => rule.sum_prob (v,input)
noncomputable def rowSlice (μ : Measure (Ambient d × Fin N)) (rule : BlockRule d N) (w : Fin N) : Measure (Ambient d) :=
  ((μ.prod (rowLaw d)).withDensity (fun x =>
    ENNReal.ofReal (rule.prob (x.1.2,x.2,labels x.2 x.1.1) w))).map (fun x => x.1.1)
end KernelPotential.FiniteMessage

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_MassPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.MassPotential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Sphere
noncomputable def normalized {d : ℕ} (ρ : Measure (Ambient d)) : Measure (Ambient d) := (ρ univ)⁻¹ • ρ
noncomputable def energy {d : ℕ} (ρ : Measure (Ambient d)) : ℝ := (ρ univ).toReal*Phi (normalized ρ)
noncomputable def proper {d : ℕ} (ρ : Measure (Ambient d)) : Measure (Ambient d) :=
  if ρ univ=0 then sphereProbability d else normalized ρ
end KernelPotential.MassPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SimplexApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift.Simplex
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
noncomputable def clip (ε : ℝ) (x : ℝ) : ℝ := max ε (min 1 x)
noncomputable def total {N : ℕ} (ε : ℝ) (x : Fin N → ℝ) : ℝ := ∑ w,clip ε (x w)
noncomputable def normalize {N : ℕ} (ε : ℝ) (x : Fin N → ℝ) (w : Fin N) : ℝ := clip ε (x w)/total ε x
end KernelPotential.NoisyDrift.Simplex

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_JointRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity Sphere
noncomputable def postCharge {d N : ℕ} (ν : Measure (Ambient d))
    (rule : PositiveRule (d/16) d N) (η : ℝ) (z : Observation (d/16) d) (w : Fin N) : ℝ :=
  Real.log (1+(projectedReference (post ν (rule.response η w)) η z.1.1 z.1.2 z.2.1 z.2.2).toReal)

end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_PotentialContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Continuity
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open Coercivity Sphere EntropySupport
noncomputable def densityLaw {d : ℕ} (f : Ambient d → ℝ) : Measure (Ambient d) :=
  (sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))

end KernelPotential.Continuity

end OAI
end


