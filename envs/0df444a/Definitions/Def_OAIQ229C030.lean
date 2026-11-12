-- Prove2me | Definitions.Def_OAIQ229C030
-- name    : OAIQ229C030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T12:06:30.571946+00:00
-- url     : https://prove2.me/theorems/93684eba-81f5-404e-a7ef-d76731c957ca
-- title:
--   Definitions bundle OAIQ229C030 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 3 definitions and 11 theorems. The definitions and types are `OAI.CoarseAssembly.Rips.ControlledCycleFamily.included`, `OAI.CoarseAssembly.provedCircleInput`, `OAI.CoarseAssembly.transferRoeHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_AveragingPropagation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/AveragingPropagation.lean), [`CoarseAssembly_BoundaryAssemblyMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/BoundaryAssemblyMaps.lean), [`CoarseAssembly_CircleCoefficient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/CircleCoefficient.lean), [`CoarseAssembly_KazhdanInput`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/KazhdanInput.lean), [`CoarseAssembly_ProjectionBlocks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ProjectionBlocks.lean), [`CoarseAssembly_RipsBoundaryDegeneracy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsBoundaryDegeneracy.lean), [`CoarseAssembly_RipsFamilyInclusion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsFamilyInclusion.lean), [`CoarseAssembly_SpatialAveraging`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SpatialAveraging.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C025`, `OAIQ229C026` and `OAIQ229C027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ229C034`; the statements `OAI_NuclearUltrapower_SOS_basis_good`, `OAI_NuclearUltrapower_SOS_delta_good`, `OAI_NuclearUltrapower_SOS_goodWord_inv` and `OAI_NuclearUltrapower_SOS_goodWord_mul`; the proofs of `OAI_NuclearUltrapower_SOS_delta_good`, `OAI_NuclearUltrapower_SOS_goodWord_inv` and `OAI_NuclearUltrapower_SOS_goodWord_mul`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Bases
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.TransferInstance
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C025
import Definitions.Def_OAIQ229C026
import Definitions.Def_OAIQ229C027

section
-- module Solutions.Q229_CA.CoarseAssembly_ProjectionBlocks
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial block projections

Adjoints commute with uniformly bounded Hilbert direct sums. Under the
explicit flattening equivalence, the sum of constant-fiber projections is
exactly the spatial projection `V V*` used by the Roe transfer.
-/

noncomputable section

namespace CoarseAssembly

open scoped Topology

variable {I : Type*} {E F : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
variable [∀ i, CompleteSpace (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
variable [∀ i, CompleteSpace (F i)]

variable {Q : I → Type*} [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Equality with the actual spatial projection, not merely agreement on
formal constant-fiber symbols. -/
theorem flatten_constantProjection :
    flattenOperator (Q := Q) (H := H) (blockOperator (fun i => constantProjection (H := H) (Q i))
      1 zero_le_one (fun i => constantProjection_norm_le (Q i))) =
      fiberProjection (H := H) Q := by
  rw [block_constantProjection (Q := Q) (H := H),
    flattenOperator_eq_conjugation, operatorConjugation_comp]
  rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SpatialAveraging
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform spatial approximation from the published gap

The gap hypothesis is the norm estimate for the explicitly defined lazy
regular-representation averages. The direct-sum convergence and its
identification with the actual spatial constant-fiber projection are proved
here, as required by the transfer construction.
-/

noncomputable section

namespace CoarseAssembly

open Congruence DiscreteRoe
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spatialAveragingPower_tendsto (S : Finset ArithmeticGroup) (hS : S.Nonempty)
    (hgap : UniformAveragingGap S H) :
    Filter.Tendsto (spatialAveragingPower (H := H) S) Filter.atTop
      (nhds (fiberProjection (H := H) BaseFiber)) := by
  obtain ⟨c, hc, hc1, hgap⟩ := hgap
  let M := fun u : BaseUnion => lazyAverage (H := H) S (discDepth u.1 u.2)
  let P := fun u : BaseUnion => constantProjection (H := H) (BaseFiber u)
  have hM (u : BaseUnion) : ‖M u‖ ≤ 1 := lazyAverage_norm_le S _
  have hP (u : BaseUnion) : ‖P u‖ ≤ 1 := constantProjection_norm_le _
  have hconv := averaging_blocks_tendsto
    (ι := BaseUnion) (E := fun u => lp (fun _ : BaseFiber u => H) 2)
    M P c hc hc1 hM hP
    (fun u => constantProjection_idempotent (H := H) (BaseFiber u))
    (fun u => lazyAverage_projection (H := H) S hS (discDepth u.1 u.2))
    (fun u => projection_lazyAverage (H := H) S hS (discDepth u.1 u.2))
    (fun u => hgap (discDepth u.1 u.2))
  have hflat := flattenOperator_tendsto (Q := BaseFiber) (H := H) _ _ hconv
  rw [flatten_constantProjection (Q := BaseFiber) (H := H)] at hflat
  exact hflat

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AveragingPropagation
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_adjoint_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalFamily_apply _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalMultiplier_apply _root_.OAI.CoarseAssembly.DiscreteRoe.entry_diagonalFamily_same _root_.OAI.CoarseAssembly.DiscreteRoe.familyCoefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.mem_multiplierRoeIdeal _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply _root_.OAI.CoarseAssembly.discHatWeights_apply _root_.OAI.CoarseAssembly.latticeHatWeights_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite propagation of the averaging powers

The left regular generators move at most one graph edge. The global lazy
average therefore has propagation one, and its powers have the expected
linear propagation bound on the actual separated union.
-/

noncomputable section

namespace CoarseAssembly

open Congruence DiscreteRoe

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem leftMove_distance (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (u : Disc j) (q : Quotient (discDepth j u))
    (s : ArithmeticGroup) (hs : s ∈ S) :
    @dist VertexUnion (vertexUnionMetric S t).toDist
      ⟨⟨j, u⟩, reduce (discDepth j u) s * q⟩ ⟨⟨j, u⟩, q⟩ ≤ 1 := by
  rw [vertexUnion_dist_same S t]
  by_cases he : reduce (discDepth j u) s * q = q
  · simp [he]
  · have ha : (fiberedGraph S t j).Adj ⟨u, q⟩ ⟨u, reduce (discDepth j u) s * q⟩ := by
      refine ⟨?_, s, ?_, Or.inl rfl, ?_⟩
      · intro h
        have hc : HEq q (reduce (discDepth j u) s * q) := (Sigma.mk.inj h).2
        exact he (eq_of_heq hc).symm
      · simp [symmetricMoves, hs]
      · intro m hq hr
        simp [fiberCoordinate, fiberCharge, latticeCharge_self, map_mul, quotientMap_reduce]
    have hd := SimpleGraph.dist_le ha.toWalk
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, zero_add] at hd
    rw [SimpleGraph.dist_comm]
    exact_mod_cast hd

theorem spatialLazyAverage_propagation (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    PropagationLE 1 (spatialLazyAverage (H := H) S) := by
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  intro x y hdist
  apply ContinuousLinearMap.ext
  intro v
  rcases x with ⟨u, q⟩
  rcases y with ⟨w, r⟩
  change spatialLazyAverage S (lp.single 2 ⟨w, r⟩ v) ⟨u, q⟩ = 0
  by_cases huw : u = w
  · subst w
    change lazyAverage S (discDepth u.1 u.2)
      (rowVector (lp.single 2 ⟨u, r⟩ v) u) q = 0
    rw [rowVector_single_same]
    apply lazyAverage_single_zero
    · intro he
      subst q
      simp only [dist_self] at hdist
      exact (not_lt_of_ge (by norm_num : (0 : ℝ) ≤ 1)) hdist
    · intro s hs he
      subst q
      exact (not_lt_of_ge (leftMove_distance S t u.2 r s hs)) hdist
  · change lazyAverage S (discDepth u.1 u.2)
      (rowVector (lp.single 2 ⟨w, r⟩ v) u) q = 0
    rw [rowVector_single_ne huw, map_zero]
    rfl

theorem spatialAveragingPower_eq_pow (S : Finset ArithmeticGroup) (n : ℕ) :
    spatialAveragingPower (H := H) S n = spatialLazyAverage S ^ (n + 1) := by
  let M := fun u : BaseUnion => lazyAverage (H := H) S (discDepth u.1 u.2)
  let A := fun n => blockOperator (fun u : BaseUnion => M u ^ (n + 1))
    1 zero_le_one (fiberAveragingPower_norm (H := H) S n)
  let B := blockOperator M 1 zero_le_one
    (fun u : BaseUnion => lazyAverage_norm_le (H := H) S (discDepth u.1 u.2))
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : A (n + 1) = A n * B := by
      apply ContinuousLinearMap.ext
      intro x
      apply lp.ext
      funext u
      change (M u ^ (n + 1 + 1)) (x u) = (M u ^ (n + 1)) (M u (x u))
      rw [pow_succ]
      rfl
    change flattenOperator (Q := BaseFiber) (A (n + 1)) = _
    rw [he, flattenOperator_mul]
    change spatialAveragingPower S n * spatialLazyAverage S = _
    rw [ih, ← pow_succ]

theorem spatialAveragingPower_propagation (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    ∀ n, PropagationLE (n + 1 : ℕ) (spatialAveragingPower (H := H) S n) := by
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  have hfinite := (vertexUnion_uniform_balls S t).finite_closedBall
  have hM := spatialLazyAverage_propagation (H := H) S t
  intro n
  rw [spatialAveragingPower_eq_pow]
  induction n with
  | zero => simpa only [zero_add, pow_one, Nat.cast_one] using hM
  | succ n ih =>
    have hp := PropagationLE.mul hfinite ih hM
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one] using hp

/-- The concrete spatial transfer now requires only the published uniform
Kazhdan-gap specialization for these actual averages. -/
theorem concrete_transfer_of_gap (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (hS : S.Nonempty) (hgap : UniformAveragingGap S H) :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    MapsToRoe (fiberEmbedding (H := H) BaseFiber) := by
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  apply concrete_transfer_of_approximation S t (spatialAveragingPower S)
    (spatialAveragingPower_tendsto S hS hgap)
  intro n
  exact ⟨(n + 1 : ℕ), by positivity, spatialAveragingPower_propagation S t n⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_KazhdanInput
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed published spectral-gap input

The elementary matrices below and their inverses give a fixed finite
symmetric generating set of SL3(Z), with the identity included. The input
used in the conditional development is exactly the uniform lazy-averaging
estimate on the finite congruence quotients, with the standard ample
coefficient space. It is the specialization of Bekka–de la Harpe–Valette
(2008), Proposition 1.3.2 and Example 1.7.4, explained in manuscript §5.2.

No proof of that published input is asserted during the conditional phase.
The spatial Roe transfer itself is proved from it below.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

/-- The transfer in manuscript §5 for the fixed graph family, conditional
only on its identified published spectral-gap input. -/
theorem roe_transfer_of_published_gap (hgap : PublishedKazhdanInput) :
    letI : MetricSpace VertexUnion := vertexUnionMetric elementaryMoves chosenHolonomyUnit
    DiscreteRoe.MapsToRoe (fiberEmbedding (H := AmpleSpace) BaseFiber) :=
  concrete_transfer_of_gap elementaryMoves chosenHolonomyUnit elementaryMoves_nonempty hgap

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryAssemblyMaps
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual boundary assembly diagram

All three Roe maps below are constructed spatial homomorphisms on the
ordinary reduced locally compact Roe algebras. The transfer factorization
is proved before the two published assembly naturality equations are used.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Analytic DiscreteRoe

attribute [local instance] OAI.CoarseAssembly.boundaryAssemblyMetric1

def transferRoeHom (hgap : PublishedKazhdanInput) : BaseRoe →⋆ₙₐ[ℂ] TotalRoe :=
  conjugationHom (D := BaseUnion) (X := VertexUnion) (H := AmpleSpace)
    (fiberEmbedding (H := AmpleSpace) BaseFiber) (roe_transfer_of_published_gap hgap)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CircleCoefficient
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional circle class of coordinate index one -/

noncomputable section

namespace CoarseAssembly

open Analytic

/-- The complete published circle-index input, now a theorem. -/
def provedCircleInput : PublishedCircleInput :=
  circleInputOfIndexOne circleFundamental circleFundamental_coordinate_index

open Congruence Rips

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsBoundaryDegeneracy
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degenerate families have zero whole-union Roe boundary

Vanishing is proved from an exact global involution, not from vanishing of
the individual finite-component K-theory classes.
-/

noncomputable section

namespace CoarseAssembly

namespace Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem ripsCompression_degenerate (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hc : c.Degenerate) :
    partitionCompression (representedSqrt r c) c.operator = c.operator := by
  rw [ripsCompression_eq_localized]
  apply localizedOperator_degenerate c _ hc
  simp only [← map_mul, ← map_sum, sqrtCoordinate_square_sum, hπ]

theorem ripsSpatialOperator_degenerate_sq (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hc : c.Degenerate) :
    ripsSpatialOperator r c hπ * ripsSpatialOperator r c hπ = 1 := by
  have hs : c.operator * c.operator = 1 := by
    have h := hc.2.1 1
    rw [hπ, mul_one] at h
    exact sub_eq_zero.mp h
  unfold ripsSpatialOperator localizedSpatialOperator
  apply isometricExtension_sq_eq_one
  rwa [ripsCompression_degenerate r c hπ hc]

theorem ampleRipsOperator_degenerate_sq (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hc : c.Degenerate) :
    ampleRipsOperator r c hπ * ampleRipsOperator r c hπ = 1 :=
  isometricExtension_sq_eq_one _ _ (ripsSpatialOperator_degenerate_sq r c hπ hc)

end Rips

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsFamilyInclusion
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the controlled Rips boundary under component inclusions -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] {r : ℝ}

def ControlledCycleFamily.included (c : ControlledCycleFamily Q r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y) :
    ControlledCycleFamily P r where
  cycle i := includedCycle r (e i) (hei i) (c.cycle i)
  unital i := includedCycle_unital r (e i) (hei i) (c.cycle i) (c.unital i)
  selfAdjoint := c.selfAdjoint
  bound := c.bound
  bound_nonneg := c.bound_nonneg
  norm_le := c.norm_le

end CoarseAssembly.Rips

end

end OAI
end


