-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
-- name    : GroundTheory_AutomorphicForms_KernelTrace
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:56.01907+00:00
-- url     : https://prove2.me/theorems/51c484bd-9f95-4575-a098-298b4d24dbeb
-- title:
--   Kernel Trace
-- statement:
--   Definitions and structural lemmas for Kernel Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Theorems.Thm_GroundTheory_Automorphic_measurable_of_continuous_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal
noncomputable section
section Kernel
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]
theorem measurable_of_continuous_compactProd {Y β : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] [PseudoMetricSpace β] [MeasurableSpace β]
    [BorelSpace β] {k : X × Y → β} (hk : Continuous k) : Measurable k := by
  let : UniformSpace X := uniformSpaceOfCompactR1
  let : UniformSpace Y := uniformSpaceOfCompactR1
  exact measurable_of_continuous_prod hk
variable (μ : Measure X) [IsFiniteMeasure μ]
theorem memLp_contKernel (k : C(X × X, ℂ)) : MemLp k 2 (μ.prod μ) :=
  MemLp.of_bound (measurable_of_continuous_compactProd k.continuous).aestronglyMeasurable ‖k‖
    (ae_of_all _ fun z => k.norm_coe_le_norm z)
def contKernelOp (k : C(X × X, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  L2Kernel.kernelOp ((memLp_contKernel μ k).toLp k)
end Kernel
section Averaging
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
namespace MeasurablePartition
variable (p : MeasurablePartition X)
def nonnull : Finset ℕ := (Finset.range p.n).filter fun i => μ (p.E i) ≠ 0
def avgVec (i : p.nonnull μ) : Lp ℂ 2 μ :=
  (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) •
    indicatorConstLp 2 (p.measurableSet i) (measure_ne_top μ _) (1 : ℂ)
def avgProj : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := finProj (p.avgVec μ)
end MeasurablePartition
end Averaging
section Diagonal
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
namespace MeasurablePartition
variable (p : MeasurablePartition X)
end MeasurablePartition
end Diagonal
section PositiveConj
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]
end PositiveConj
section Approx
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
namespace MeasurablePartition
variable (p : MeasurablePartition X)
end MeasurablePartition
end Approx
section Uniform
variable {X : Type*} [UniformSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open MeasurablePartition
end Uniform
section Main
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
end Main
end
end GroundTheory.Automorphic


