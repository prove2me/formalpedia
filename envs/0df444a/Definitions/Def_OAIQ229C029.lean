-- Prove2me | Definitions.Def_OAIQ229C029
-- name    : OAIQ229C029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:40:04.958985+00:00
-- url     : https://prove2.me/theorems/fec13e3b-b98e-42f9-aef0-3207e7fd426c
-- title:
--   Definitions bundle OAIQ229C029 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 3 definitions and 7 theorems. The definitions and types are `OAI.CoarseAssembly.Rips.ripsFamilyBoundaryWithEmbeddings`, `OAI.CoarseAssembly.circleSigmaCycle`, `OAI.CoarseAssembly.explicitFiberLoops`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_ExplicitCircleFamily`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ExplicitCircleFamily.lean), [`CoarseAssembly_ExplicitPersistence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ExplicitPersistence.lean), [`CoarseAssembly_FiniteHeadBoundary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FiniteHeadBoundary.lean), [`CoarseAssembly_FiniteTailIndependence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FiniteTailIndependence.lean), [`CoarseAssembly_RipsEmbeddingIndependence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsEmbeddingIndependence.lean), [`CoarseAssembly_RipsUnitaryLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsUnitaryLocalization.lean), [`CoarseAssembly_SampledRipsEstimates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SampledRipsEstimates.lean), [`CoarseAssembly_SeparatedFamilyPerturbation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SeparatedFamilyPerturbation.lean), [`CoarseAssembly_SpatialBoundaryNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SpatialBoundaryNaturality.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C024`, `OAIQ229C025`, `OAIQ229C026` and `OAIQ229C027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C032` and `OAIQ229C033`; the statements `OAI_NuclearUltrapower_SOS_residual_augmentation`, `OAI_NuclearUltrapower_SOS_residual_eval` and `OAI_NuclearUltrapower_SOS_residual_l1`; the proofs of `OAI_NuclearUltrapower_SOS_residual_augmentation`, `OAI_NuclearUltrapower_SOS_residual_eval`, `OAI_NuclearUltrapower_SOS_residual_l1`, `OAI_NuclearUltrapower_SOS_row_lengths` and `OAI_NuclearUltrapower_SOS_row_normalizations`.
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
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
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
import Mathlib.Topology.DenseEmbedding
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
import Definitions.Def_OAIQ229C024
import Definitions.Def_OAIQ229C025
import Definitions.Def_OAIQ229C026
import Definitions.Def_OAIQ229C027

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitCircleFamily
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The circle-family class without a countable-additivity assumption -/

noncomputable section

namespace CoarseAssembly

open Analytic
open scoped ZeroAtInfty

def circleSigmaCycle : OddCycle C₀(Sigma CircleFamily, ℂ) :=
  sigmaCycle CircleFamily (fun _ => windingCircleCycle) 1 (by norm_num)
    (fun _ => windingCircleCycle_norm) (fun _ => negativeCircleOperator_selfAdjoint)
    (fun _ => negativeCircleOperator_sq)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitPersistence
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Persistence of the explicit circle cycle in the actual graph union -/

noncomputable section

namespace CoarseAssembly

open Topology Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.explicitPersistenceComponent
def explicitFiberLoops (r : ℕ) (hr : 1 ≤ r) :=
  fiberedBoundaryLoops elementaryMoves
    (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit) r hr

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedFamilyPerturbation
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact changes on components give Roe perturbations on the whole union -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Componentwise compact changes preserve the whole-union class, even when
these compact operators do not tend to zero in norm. -/
theorem separatedFamilyBoundary_eq_of_component_compact (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (V i) H)))
    (hAB : ∀ i, IsCompactOperator (A i - B i)) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq =
      separatedFamilyBoundary o B D hD hB s hs hq hBs hBsq := by
  let := separatedMetric o
  have hdiff := diagonalFamily_sub_mem_roe o A B C D hC hD hA hB r s hr hs hp hq hAs hBs hAB
  have hrev : diagonalFamily B D hD hB - diagonalFamily A C hC hA ∈
      algebra (X := Sigma V) (H := H) := by
    have he : diagonalFamily B D hD hB - diagonalFamily A C hC hA =
        -(diagonalFamily A C hC hA - diagonalFamily B D hD hB) := by abel
    rw [he]
    exact (algebra (X := Sigma V) (H := H)).neg_mem hdiff
  exact multiplierBoundaryClass_roePerturbation
    (separatedFamilyMultiplier o A C hC hA r hr hp)
    (separatedFamilyMultiplier o B D hD hB s hs hq)
    (separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hp hAs)
    (separatedFamilyMultiplier_selfAdjoint o B D hD hB s hs hq hBs)
    (diagonalFamily_square_mem_roe o A C hC hA r hr hp hAs hAsq)
    (diagonalFamily_square_mem_roe o B D hD hB s hs hq hBs hBsq) hrev

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteHeadBoundary
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing finitely many components from the whole-union boundary

The argument works with the actual rational boundary unitary. Involutive
components contribute the identity in that unitary, before taking K-theory.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite head can differ arbitrarily when its operators are exact
involutions. Equality is proved for the entire Roe boundary. -/
theorem separatedFamilyBoundary_eq_of_involutive_head (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (V i) H)))
    (J : Finset ℕ) (htail : ∀ i, i ∉ J → A i = B i)
    (hAi : ∀ i, i ∈ J → A i * A i = 1) (hBi : ∀ i, i ∈ J → B i * B i = 1) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq =
      separatedFamilyBoundary o B D hD hB s hs hq hBs hBsq := by
  apply separatedFamilyBoundary_eq_of_rational o A B C D hC hD hA hB r s hr hs hp hq hAs hBs hAsq hBsq
  intro i
  by_cases hi : i ∈ J
  · exact (rationalBoundaryUnitary_eq_one (A i) (hAs i) (hAi i hi)).trans
      (rationalBoundaryUnitary_eq_one (B i) (hBs i) (hBi i hi)).symm
  · have hcongr (T U : Operator (V i) H) (hT : IsSelfAdjoint T) (hU : IsSelfAdjoint U)
        (he : T = U) : rationalBoundaryUnitary T hT = rationalBoundaryUnitary U hU := by
      subst U
      rfl
    exact hcongr _ _ _ _ (htail i hi)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteTailIndependence
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The whole-union boundary is unchanged by finitely many component changes -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SecondCountableTopology H]

/-- Finite-head independence is proved within the single Roe algebra,
using controlled compact perturbations and equality of rational unitaries. -/
theorem separatedFamilyBoundary_eq_of_tail (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (V i) H)))
    (J : Finset ℕ) (htail : ∀ i, i ∉ J → A i = B i) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq =
      separatedFamilyBoundary o B D hD hB s hs hq hBs hBsq := by
  let := separatedMetric o
  let a := finiteHeadReplacement J A C hA r hp hAs hAsq
  let b := finiteHeadReplacement J B D hB s hq hBs hBsq
  have hC' : 0 ≤ max C 1 := zero_le_one.trans (le_max_right C 1)
  have hD' : 0 ≤ max D 1 := zero_le_one.trans (le_max_right D 1)
  have hr' : 0 ≤ max r (finiteHeadRadius (V := V) J) := hr.trans (le_max_left _ _)
  have hs' : 0 ≤ max s (finiteHeadRadius (V := V) J) := hs.trans (le_max_left _ _)
  have h1 := separatedFamilyBoundary_eq_of_component_compact o a.operator A (max C 1) C hC' hC a.norm_le hA
    (max r (finiteHeadRadius (V := V) J)) r hr' hr a.propagation hp a.selfAdjoint hAs (a.square_compact hAsq) hAsq a.compact_diff
  have h2 := separatedFamilyBoundary_eq_of_component_compact o b.operator B (max D 1) D hD' hD b.norm_le hB
    (max s (finiteHeadRadius (V := V) J)) s hs' hs b.propagation hq b.selfAdjoint hBs (b.square_compact hBsq) hBsq b.compact_diff
  have hm := separatedFamilyBoundary_eq_of_involutive_head o a.operator b.operator (max C 1) (max D 1)
    hC' hD' a.norm_le b.norm_le (max r (finiteHeadRadius (V := V) J))
    (max s (finiteHeadRadius (V := V) J)) hr' hs' a.propagation b.propagation a.selfAdjoint b.selfAdjoint (a.square_compact hAsq) (b.square_compact hBsq) J
    (fun i hi => (a.tail i hi).trans ((htail i hi).trans (b.tail i hi).symm)) a.involutive b.involutive
  exact h1.symm.trans (hm.trans h2)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsEmbeddingIndependence
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-union Rips boundaries are independent of the ample embeddings -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

def ripsFamilyBoundaryWithEmbeddings (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖(c i).operator‖ ≤ C)
    (V : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    letI := separatedMetric o
    OperatorKTheory.K1 (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2)) :=
  coefficientFamilyBoundary o (fun i => ripsSpatialOperator r (c i) (hπ i))
    (C + 2) (by linarith)
    (fun i => (ripsSpatialOperator_norm_le r (c i) (hπ i)).trans (by linarith [hc i]))
    (r + r) (add_nonneg hr hr) (fun i => ripsSpatialOperator_propagation r hr (c i) (hπ i))
    (fun i => ripsSpatialOperator_selfAdjoint r (c i) (hπ i) (hF i))
    (fun i => ripsSpatialOperator_square_compact r (c i) (hπ i) (hF i)) V

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsUnitaryLocalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.compactIndexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.indexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unitary equivalence commutes with finite-Rips localization -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d : OddCycle C(Point X r, ℂ)}

theorem partitionIsometry_unitary (e : c.UnitaryEquivalent d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) :
    (partitionIsometry (representedSqrt r d) (representedSqrt_partition r d hd)).comp
        e.unitary.toLinearIsometry =
      (coefficientIsometry e.unitary.toLinearIsometry).comp
        (partitionIsometry (representedSqrt r c) (representedSqrt_partition r c hc)) := by
  ext v x
  change partitionIsometry (representedSqrt r d) _ (e.unitary v) x =
    e.unitary (partitionIsometry (representedSqrt r c) _ v x)
  rw [partitionIsometry_apply, partitionIsometry_apply]
  rw [show representedSqrt r d x = operatorConjugation e.unitary.toLinearIsometry
    (representedSqrt r c x) from e.representation_eq (sqrtCoordinate r x)]
  have hU : e.unitary.toLinearIsometry.toContinuousLinearMap.adjoint =
      e.unitary.symm.toLinearIsometry.toContinuousLinearMap :=
    LinearIsometryEquiv.adjoint_eq_symm e.unitary
  simp [operatorConjugation, hU]

theorem ripsSpatialOperator_unitary (e : c.UnitaryEquivalent d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) :
    ripsSpatialOperator r d hd =
      isometricExtension (coefficientIsometry e.unitary.toLinearIsometry)
        (ripsSpatialOperator r c hc) := by
  change isometricExtension (partitionIsometry (representedSqrt r d) _)
    (partitionCompression (representedSqrt r d) d.operator) =
      isometricExtension (coefficientIsometry e.unitary.toLinearIsometry)
        (isometricExtension (partitionIsometry (representedSqrt r c) _)
          (partitionCompression (representedSqrt r c) c.operator))
  rw [ripsCompression_unitary r e, ← isometricExtension_equiv e.unitary,
    isometricExtension_comp, isometricExtension_comp, partitionIsometry_unitary r e hc hd]

end Rips
end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SampledRipsEstimates
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.compactIndexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.indexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.intervalGrid_finish _root_.OAI.CoarseAssembly.Analytic.intervalGrid_start _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_succ _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_zero _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.familyCoefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the localized finite sums used in homotopy telescoping -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem sampledFiniteSum_partition_sub_norm_le
    (r : ℝ) (h : OddHomotopy C(Point X r, ℂ)) (χ : C(Point X r, ℂ) →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ σ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (δ : ℝ) (hδ : 0 ≤ δ)
    (hnear : ∀ x j, j < N → ‖h.representation (τ j) (sqrtCoordinate r x) -
      h.representation (σ j) (sqrtCoordinate r x)‖ ≤ δ) :
    ‖(show repeatedHilbert h.space →L[ℂ] Module X (repeatedHilbert h.space) from
        partitionMap (representedSqrt r (sampledFiniteSum h χ N τ C hC hF))) -
      (show repeatedHilbert h.space →L[ℂ] Module X (repeatedHilbert h.space) from
        partitionMap (representedSqrt r (sampledFiniteSum h χ N σ C hC hF)))‖ ≤
      (Fintype.card X : ℝ) * δ := by
  apply (partitionMap_sub_norm_le_sum _ _).trans
  calc
    _ ≤ ∑ _x : X, δ := Finset.sum_le_sum (fun x _ =>
      sampledFiniteSum_representation_sub_norm_le h χ N τ σ C hC hF
        (sqrtCoordinate r x) δ hδ (hnear x))
    _ = _ := by simp

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SpatialBoundaryNaturality
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The boundary representative respects spatial Roe maps

The target Fredholm operator is extended by the identity on the complement
of the spatial isometry. The conclusion is the actual K₁ map equality.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X Y H : Type*} [DecidableEq X] [DecidableEq Y]
  [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance spatialBoundaryScalarTower_rb1680e_1 {Z : Type*} : IsScalarTower ℂ (Operator Z H) (Operator Z H) where
  smul_assoc c T S := by ext v; simp
local instance spatialBoundaryScalarComm_rb1680e_1 {Z : Type*} : SMulCommClass ℂ (Operator Z H) (Operator Z H) where
  smul_comm c T S := by ext v; simp
theorem multiplierBoundaryClass_spatial
    (V : Module X H →ₗᵢ[ℂ] Module Y H) (hV : MapsToRoe V)
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (G : multiplierAlgebra (X := Y) (H := H)) (hG : IsSelfAdjoint G)
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := Y) (H := H))
    (hGF : G.val = isometricExtension V F.val) :
    OperatorKTheory.map (conjugationHom V hV) (multiplierBoundaryClass F hF hFd) =
      multiplierBoundaryClass G hG hGd := by
  apply OperatorKTheory.map_relativeClass (hS := algebra_isClosed) (hT := algebra_isClosed)
  apply Subtype.ext
  exact (multiplierBoundaryUnitary_spatial V F hF G hG hGF).symm

end CoarseAssembly.DiscreteRoe

end

end OAI
end


