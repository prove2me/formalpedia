-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FellerDenseApproximationClean
-- name    : MarkovProcess_V3HRepair_FellerDenseApproximationClean
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T11:34:20.525532+00:00
-- url     : https://prove2.me/theorems/7e9950df-1d66-47ad-b4b2-fffd68d8e291
-- title:
--   Verified MarkovProcess source repair: FellerDenseApproximationClean
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FellerDenseApproximationClean module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FellerDenseApproximationClean source SHA-256 4c8c36d41ead934c02087286f0355eccd0749b339f7f09e51186ba3fbb5a278b. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Definitions.Def_MarkovProcess_V3HRepair_FiniteTimeKernelRestrict
import Definitions.Def_MarkovProcess_V3HRepair_FellerFiniteTimeCompactTestContinuity
import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feller continuity of finite dense approximations

This file proves compact-test convergence of the finite laws obtained by simultaneously
approximating a finite set of nonnegative-real times by dense times. Both the approximating and
limiting kernels are transported through the same ordered-coordinate homeomorphism, after which
the finite-time Feller continuity theorem applies directly.

This is finite-dimensional infrastructure. No path-space Markov property is asserted here; the
Markov and strong Markov statements are in `MarkovProcess/Main.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.SubMarkovKernelSemigroup
private theorem tendsto_finiteDenseApproximationOrderedTimes
    {I : Finset NNReal} (q : ℕ → I ↪o DenseTime)
    (hq : ∀ t, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k t)) atTop
      (nhds (t : NNReal))) (i : Fin I.card) :
    Tendsto (fun k ↦ finiteDenseApproximationOrderedTimes (q k) i) atTop
      (nhds (finiteSetTimes I i)) := by
  change Tendsto
    (fun k ↦ DenseTime.castOrderEmbedding (q k (I.orderIsoOfFin rfl i))) atTop
    (nhds ((I.orderIsoOfFin rfl i : I) : NNReal))
  exact hq (I.orderIsoOfFin rfl i)

end MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feller continuity of finite dense approximations

This file proves compact-test convergence of the finite laws obtained by simultaneously
approximating a finite set of nonnegative-real times by dense times. Both the approximating and
limiting kernels are transported through the same ordered-coordinate homeomorphism, after which
the finite-time Feller continuity theorem applies directly.

This is finite-dimensional infrastructure. No path-space Markov property is asserted here; the
Markov and strong Markov statements are in `MarkovProcess/Main.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]


noncomputable section

private theorem approximation_mem {I : Finset NNReal} (q : I ↪o DenseTime) (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩

private def finiteDenseApproximationOrderEmb {I : Finset NNReal} (q : I ↪o DenseTime) :
    Fin I.card ↪o Fin (finiteDenseApproximationPhysicalSet q).card :=
  (I.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (OrderEmbedding.ofStrictMono
      (fun t : I => (⟨DenseTime.castOrderEmbedding (q t), approximation_mem q t⟩ :
        finiteDenseApproximationPhysicalSet q))
        (fun _ _ h => DenseTime.castOrderEmbedding.strictMono (q.strictMono h))) |>.trans
    ((finiteDenseApproximationPhysicalSet q).orderIsoOfFin rfl).symm.toOrderEmbedding

private theorem finiteSetTimes_restrict_approximationOrderEmb
    {I : Finset NNReal} (q : I ↪o DenseTime) :
    (finiteSetTimes (finiteDenseApproximationPhysicalSet q)).restrict
        (finiteDenseApproximationOrderEmb q) =
      finiteDenseApproximationOrderedTimes q := by
  apply DFunLike.ext _ _
  intro i
  change finiteSetTimes (finiteDenseApproximationPhysicalSet q)
      (finiteDenseApproximationOrderEmb q i) = _
  simp only [finiteSetTimes, finiteDenseApproximationOrderEmb,
    finiteDenseApproximationOrderedTimes, RelEmbedding.trans_apply]
  exact congrArg Subtype.val
    ((finiteDenseApproximationPhysicalSet q).orderIsoOfFin rfl |>.apply_symm_apply
      ⟨DenseTime.castOrderEmbedding (q (I.orderIsoOfFin rfl i)),
        approximation_mem q (I.orderIsoOfFin rfl i)⟩)

private theorem reindex_comp_orderedPathToFiniteSet
    {gamma : Type*} {I : Finset NNReal} (q : I ↪o DenseTime) :
    finiteDenseApproximationReindex (γ := gamma) q ∘
        orderedPathToFiniteSet (finiteDenseApproximationPhysicalSet q) =
      orderedPathToFiniteSet I ∘
        FiniteOrderedTimes.restrictPath (finiteDenseApproximationOrderEmb q) := by
  funext path t
  simp only [Function.comp_apply, finiteDenseApproximationReindex,
    orderedPathToFiniteSet, FiniteOrderedTimes.restrictPath,
    finiteDenseApproximationOrderEmb, RelEmbedding.trans_apply,
    OrderIso.coe_toOrderEmbedding, OrderIso.apply_symm_apply]
  rfl

private theorem finiteDenseApproximation_mem {I : Finset NNReal} (q : I ↪o DenseTime)
    (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩

/-- The approximating-set reindexing map is measurable. -/
private theorem measurable_finiteDenseApproximationReindex
    {γ : Type*} [MeasurableSpace γ] {I : Finset NNReal} (q : I ↪o DenseTime) :
    Measurable (finiteDenseApproximationReindex (γ := γ) q) := by
  rw [measurable_pi_iff]
  intro t
  let s : finiteDenseApproximationPhysicalSet q :=
    ⟨DenseTime.castOrderEmbedding (q t), finiteDenseApproximation_mem q t⟩
  exact measurable_pi_apply s

private theorem finiteDenseApproximationKernel_eq_map_finiteTimeKernel
    {alpha : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {I : Finset NNReal} (q : I ↪o DenseTime) :
    finiteDenseApproximationKernel P q =
      (finiteTimeKernel P (finiteDenseApproximationOrderedTimes q)).map
        (orderedPathToFiniteSet I) := by
  rw [finiteDenseApproximationKernel, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [reindex_comp_orderedPathToFiniteSet q, Kernel.map_comp_right]
    · rw [hP.finiteTimeKernel_map_restrictPath P,
        finiteSetTimes_restrict_approximationOrderEmb q]
    · exact FiniteOrderedTimes.measurable_restrictPath _
    · exact measurable_orderedPathToFiniteSet _
  · exact measurable_orderedPathToFiniteSet _
  · exact measurable_finiteDenseApproximationReindex q

open MarkovProcess.SubMarkovKernelSemigroup in
theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {I : Finset NNReal} (q : ℕ → I ↪o DenseTime)
    (hq : ∀ t, Tendsto
      (fun k ↦ DenseTime.castOrderEmbedding (q k t)) atTop (nhds (t : NNReal)))
    (f : C_c(I → alpha, ℝ)) (x : alpha) :
    Tendsto
      (fun k ↦ ∫ y, f y ∂finiteDenseApproximationKernel P (q k) x)
      atTop (nhds (∫ y, f y ∂finiteSetKernel P I x)) := by
  have htime : ∀ i, Tendsto
      (fun k ↦ finiteDenseApproximationOrderedTimes (q k) i) atTop
        (nhds (finiteSetTimes I i)) :=
    tendsto_finiteDenseApproximationOrderedTimes q hq
  have h := hFeller.tendsto_integral_compactlySupported_finiteTimeKernel
    hP htime (pullbackFiniteSetCompactTest I f) x
  have happrox (k : ℕ) :
      (∫ y, f y ∂finiteDenseApproximationKernel P (q k) x) =
        ∫ path, pullbackFiniteSetCompactTest I f path
          ∂finiteTimeKernel P (finiteDenseApproximationOrderedTimes (q k)) x := by
    rw [finiteDenseApproximationKernel_eq_map_finiteTimeKernel P hP (q k),
      Kernel.map_apply _ (measurable_orderedPathToFiniteSet I)]
    exact integral_map_orderedPathToFiniteSet I f _
  rw [show (fun k ↦ ∫ y, f y ∂finiteDenseApproximationKernel P (q k) x) =
      (fun k ↦ ∫ path, pullbackFiniteSetCompactTest I f path
        ∂finiteTimeKernel P (finiteDenseApproximationOrderedTimes (q k)) x) from
      funext happrox,
    integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest P I f x]
  exact h


