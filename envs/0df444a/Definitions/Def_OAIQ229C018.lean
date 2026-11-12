-- Prove2me | Definitions.Def_OAIQ229C018
-- name    : OAIQ229C018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:05:48.464905+00:00
-- url     : https://prove2.me/theorems/342cf85c-5acc-4a11-96a7-e145770a3975
-- title:
--   Definitions bundle OAIQ229C018 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 3 definitions, 1 instance and 52 theorems. The definitions and types are `OAI.CoarseAssembly.DiscreteRoe.componentHilbert`, `OAI.CoarseAssembly.DiscreteRoe.finiteHeadReplacement`, `OAI.CoarseAssembly.boundaryFiberHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_AlgebraicRoe`, `CoarseAssembly_BoundaryWalks`, `CoarseAssembly_ComponentHilbertInclusion`, `CoarseAssembly_DiagonalFamilyContinuity`, `CoarseAssembly_DiagonalSpatialFamily`, `CoarseAssembly_FiberDegree`, `CoarseAssembly_FiniteHeadNormalization`, `CoarseAssembly_MultiplierBoundaryClass`, `CoarseAssembly_MultiplierBoundaryHomotopy`, `CoarseAssembly_MultiplierBoundaryNearby`, `CoarseAssembly_PartitionCompression`, `CoarseAssembly_PartitionInclusion`, `CoarseAssembly_PartitionIntertwining`, `CoarseAssembly_PartitionIsometry`, `CoarseAssembly_PartitionMapNorm`, `CoarseAssembly_PartitionSpatialControl`, `CoarseAssembly_RelativePartialIsometry`, `CoarseAssembly_Roe`, `CoarseAssembly_RoeCalculus`, `CoarseAssembly_RoeIdealizer`, `CoarseAssembly_RoeInclusion`, `CoarseAssembly_RoeTransfer`, `CoarseAssembly_SpatialLocalization`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C009`, `OAIQ229C010` and `OAIQ229C011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C024`, `OAIQ229C025` and `OAIQ229C026`; the statements `OAI_NuclearUltrapower_SOS_row_length_100`, `OAI_NuclearUltrapower_SOS_row_length_101`, `OAI_NuclearUltrapower_SOS_row_length_102`, `OAI_NuclearUltrapower_SOS_row_length_103`, `OAI_NuclearUltrapower_SOS_row_length_104`, `OAI_NuclearUltrapower_SOS_row_partition_100`, `OAI_NuclearUltrapower_SOS_row_partition_101`, `OAI_NuclearUltrapower_SOS_row_partition_102`, `OAI_NuclearUltrapower_SOS_row_partition_103` and `OAI_NuclearUltrapower_SOS_row_partition_104`; the proofs of `OAI_NuclearUltrapower_SOS_row_length_100`, `OAI_NuclearUltrapower_SOS_row_length_101`, `OAI_NuclearUltrapower_SOS_row_length_102`, `OAI_NuclearUltrapower_SOS_row_length_103`, `OAI_NuclearUltrapower_SOS_row_length_104`, `OAI_NuclearUltrapower_SOS_row_partition_100`, `OAI_NuclearUltrapower_SOS_row_partition_101`, `OAI_NuclearUltrapower_SOS_row_partition_102`, `OAI_NuclearUltrapower_SOS_row_partition_103` and `OAI_NuclearUltrapower_SOS_row_partition_104`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
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
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
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
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.TransferInstance
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C009
import Definitions.Def_OAIQ229C010
import Definitions.Def_OAIQ229C011

section
-- module Solutions.Q229_CA.CoarseAssembly_Roe
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Discrete reduced Roe algebras

Operators act on the actual Hilbert sum `ℓ²(X; H)`. Matrix entries are
continuous linear maps on the coefficient Hilbert space. The Roe algebra is
the norm-closed star algebra generated by finite-propagation operators whose
entries, and adjoint entries, are compact. On a discrete space with finite
metric balls these are the usual locally compact generators.

The coefficient space is a parameter; the ample module used in the paper
is obtained by taking it to be an infinite-dimensional separable Hilbert
space. No compactness is imposed on the averaging projection itself.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped Topology

variable {X Y H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [DecidableEq X] [DecidableEq Y]

variable [CompleteSpace H] [PseudoMetricSpace X]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.operatorScalarTower

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.operatorScalarComm

instance instCompleteSpaceSubtypeOperatorMemNonUnitalStarSubalgebraComplexAlgebra : CompleteSpace (algebra (X := X) (H := H)) :=
  algebra_isClosed.completeSpace_coe

variable [PseudoMetricSpace Y]

/-- A continuous spatial homomorphism maps the whole Roe algebra once its
range has been proved on the locally compact finite-propagation generators.
The range proof remains an obligation, rather than part of the definition. -/
theorem map_mem (φ : Operator X H →⋆ₙₐ[ℂ] Operator Y H) (hφ : Continuous φ)
    (hgen : ∀ T, Generator T → φ T ∈ algebra (X := Y) (H := H))
    {T : Operator X H} (hT : T ∈ algebra (X := X) (H := H)) : φ T ∈ algebra (X := Y) (H := H) := by
  let S := (algebra (X := Y) (H := H)).comap φ
  have hS : IsClosed (S : Set (Operator X H)) := algebra_isClosed.preimage hφ
  have hle : NonUnitalStarAlgebra.adjoin ℂ {T : Operator X H | Generator T} ≤ S :=
    NonUnitalStarAlgebra.adjoin_le hgen
  exact (NonUnitalStarSubalgebra.topologicalClosure_minimal _ hle hS) hT

/-- The final norm-closure step in the finite-fiber transfer argument. -/
theorem sandwich_mem {P A : Operator X H} {Pn : ℕ → Operator X H}
    (hlim : Filter.Tendsto Pn Filter.atTop (nhds P))
    (hgen : ∀ n, Generator (Pn n * A * Pn n)) : P * A * P ∈ algebra (X := X) (H := H) :=
  sandwich_mem_of_tendsto _ algebra_isClosed P Pn hlim A
    (fun n => generator_mem (hgen n))

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RoeCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-propagation matrix calculus

The local-compactness step of the finite-fiber transfer states that
sandwiching a locally compact, finite-propagation operator by arbitrary
finite-propagation operators preserves local compactness. The multipliers
themselves are not assumed locally compact.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PseudoMetricSpace X]

variable (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)

include finiteBalls in
/-- Finite-propagation multipliers preserve locally compact generators.
In particular this applies to amplified finite-propagation projections,
without asserting that those projections are locally compact. -/
theorem generator_sandwich {A Q : Operator X H} {q : ℝ}
    (hA : Generator A) (hq : 0 ≤ q) (hQ : PropagationLE q Q) :
    Generator (Q * A * Q) := by
  obtain ⟨⟨a, ha, hprop⟩, hc, hcs⟩ := hA
  refine ⟨⟨(q + a) + q, by linarith,
    (hQ.mul finiteBalls hprop).mul finiteBalls hQ⟩, ?_, ?_⟩
  · exact (hc.mul_right finiteBalls hprop).mul_left finiteBalls hQ
  · rw [star_mul, star_mul, ← mul_assoc]
    exact (hcs.mul_right finiteBalls hprop.star).mul_left finiteBalls hQ.star

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AlgebraicRoe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The algebra of locally compact finite-propagation operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instContinuousStarOperator

theorem roe_eq_closure_algebraic
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite) :
    algebra (X := X) (H := H) = (algebraicRoe (H := H) finiteBalls).topologicalClosure := by
  have he : NonUnitalStarAlgebra.adjoin ℂ {T : Operator X H | Generator T} =
      algebraicRoe (H := H) finiteBalls := by
    apply le_antisymm
    · exact NonUnitalStarAlgebra.adjoin_le (fun _ h => h)
    · intro T hT
      exact NonUnitalStarAlgebra.subset_adjoin ℂ _ hT
  unfold algebra
  rw [he]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform degree bound for the finite fibered graphs

A neighbor is encoded by its base vertex, one integral left move, and nine
binary digits. The digits distinguish children in a successive congruence
fiber; at equal or smaller depth the reduced equation already determines
the target. The resulting bound is independent of the disc radius.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem fiberBits_injective {k l : ℕ} (h : l = k + 1)
    (q r : Quotient l) (he : quotientMap (by omega : k ≤ l) q =
      quotientMap (by omega : k ≤ l) r) (hb : fiberBits l q = fiberBits l r) : q = r := by
  subst l
  exact quotient_fiber_code_injective k he hb

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RoeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Norm-closure and spatial factorization for the finite-fiber transfer

The missing construction of the finite-propagation lift is isolated as an
explicit witness here; it is not treated as a published input. Once a lift
has been constructed by matchings, the following argument proves that the
spatial homomorphism lands in the actual reduced Roe algebra.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped Topology

variable {B D X H : Type*} [DecidableEq B] [DecidableEq D] [DecidableEq X]
variable [PseudoMetricSpace B] [PseudoMetricSpace D] [PseudoMetricSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range proof after constructing the matching lift of each generator. -/
theorem conjugation_mem_of_sandwich_lifts
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    (V : Module D H →ₗᵢ[ℂ] Module X H)
    (P : Operator X H) (Pn : ℕ → Operator X H)
    (hlim : Filter.Tendsto Pn Filter.atTop (nhds P))
    (hprop : ∀ n, ∃ r : ℝ, 0 ≤ r ∧ PropagationLE r (Pn n))
    (hlift : ∀ T : Operator D H, Generator T →
      ∃ A : Operator X H, Generator A ∧ P * A * P = operatorConjugation V T)
    {T : Operator D H} (hT : T ∈ algebra (X := D) (H := H)) :
    operatorConjugation V T ∈ algebra (X := X) (H := H) := by
  apply map_mem (operatorConjugationHom V) (conjugation_continuous V) _ hT
  intro S hS
  obtain ⟨A, hA, heq⟩ := hlift S hS
  change operatorConjugation V S ∈ algebra (X := X) (H := H)
  rw [← heq]
  apply sandwich_mem hlim
  intro n
  obtain ⟨r, hr, hn⟩ := hprop n
  exact generator_sandwich finiteBalls hA hr hn

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RoeInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced Roe map for an actual injective nonexpanding inclusion

Extension by zero preserves each matrix entry on the image, and all other
entries vanish. Thus propagation and local compactness are proved directly
before extending to the norm closure.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

universe sourceUniverse targetUniverse coefficientUniverse

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.inclusionExponentFact

variable {X : Type sourceUniverse} {Y : Type targetUniverse} {H : Type coefficientUniverse}
  [sourceDecidable : DecidableEq X] [targetDecidable : DecidableEq Y]
  [coefficientNormed : NormedAddCommGroup H] [coefficientInner : InnerProductSpace ℂ H]
  [coefficientComplete : CompleteSpace H]

theorem inclusion_adjoint_apply (e : X ↪ Y) (v : Module Y H) (x : X) :
    (inclusionIsometry (H := H) e).toContinuousLinearMap.adjoint v x = v (e x) := by
  have hi : (inclusionIsometry (H := H) e).toContinuousLinearMap.comp (insert x) =
      insert (e x) := by
    apply ContinuousLinearMap.ext
    intro h
    exact inclusionIsometry_single e x h
  have ha := congrArg ContinuousLinearMap.adjoint hi
  simp only [ContinuousLinearMap.adjoint_comp, insert_adjoint] at ha
  exact DFunLike.congr_fun ha v

theorem inclusion_entry_col_zero (e : X ↪ Y) (T : Operator X H) (x y : Y)
    (hy : y ∉ Set.range e) :
    entry (operatorConjugation (inclusionIsometry e) T) x y = 0 := by
  ext h
  have hz : (inclusionIsometry (H := H) e).toContinuousLinearMap.adjoint
      (lp.single 2 y h) = 0 := by
    apply lp.ext
    funext z
    rw [inclusion_adjoint_apply]
    exact lp.single_apply_ne (E := fun _ : Y => H) 2 y h (fun heq => hy ⟨z, heq⟩)
  simp only [entry_apply, operatorConjugation, ContinuousLinearMap.comp_apply, hz, map_zero,
    lp.coeFn_zero, Pi.zero_apply, zero_apply]

theorem inclusion_compactEntries (e : X ↪ Y) {T : Operator X H}
    (hT : CompactEntries T) : CompactEntries (operatorConjugation (inclusionIsometry e) T) := by
  intro x y
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    by_cases hy : y ∈ Set.range e
    · obtain ⟨b, rfl⟩ := hy
      rw [inclusion_entry]
      exact hT a b
    · rw [inclusion_entry_col_zero e T _ _ hy]
      exact isCompactOperator_zero
  · rw [inclusion_entry_row_zero e T _ _ hx]
    exact isCompactOperator_zero

variable [sourceMetric : PseudoMetricSpace X] [targetMetric : PseudoMetricSpace Y]

theorem inclusion_propagation (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y) {T : Operator X H} {r : ℝ}
    (hT : PropagationLE r T) : PropagationLE r (operatorConjugation (inclusionIsometry e) T) := by
  intro x y hxy
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    by_cases hy : y ∈ Set.range e
    · obtain ⟨b, rfl⟩ := hy
      rw [inclusion_entry]
      exact hT a b (hxy.trans_le (he a b))
    · exact inclusion_entry_col_zero e T _ _ hy
  · exact inclusion_entry_row_zero e T _ _ hx

theorem inclusion_generator (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y) {T : Operator X H}
    (hT : Generator T) : Generator (operatorConjugation (inclusionIsometry e) T) := by
  obtain ⟨⟨r, hr, hprop⟩, hc, hcs⟩ := hT
  refine ⟨⟨r, hr, inclusion_propagation e he hprop⟩, inclusion_compactEntries e hc, ?_⟩
  rw [← operatorConjugation_star (inclusionIsometry e) T]
  exact inclusion_compactEntries e hcs

theorem inclusion_mapsToRoe
    {Domain : Type sourceUniverse} {Range : Type targetUniverse}
    {Coefficient : Type coefficientUniverse}
    [domainDecidable : DecidableEq Domain] [rangeDecidable : DecidableEq Range]
    [normedCoefficient : NormedAddCommGroup Coefficient]
    [innerCoefficient : InnerProductSpace ℂ Coefficient]
    [completeCoefficient : CompleteSpace Coefficient]
    [domainMetric : PseudoMetricSpace Domain] [rangeMetric : PseudoMetricSpace Range]
    (e : Domain ↪ Range) (he : ∀ x y, dist (e x) (e y) ≤ dist x y) :
    MapsToRoe.{sourceUniverse, targetUniverse, coefficientUniverse}
      (D := Domain) (X := Range) (H := Coefficient)
      (inclusionIsometry.{sourceUniverse, targetUniverse, coefficientUniverse}
        (H := Coefficient) e) :=
  let isometry := @inclusionIsometry.{sourceUniverse, targetUniverse, coefficientUniverse}
    Domain Range Coefficient normedCoefficient innerCoefficient.toNormedSpace e
  let conjugation := @operatorConjugationHom.{max sourceUniverse coefficientUniverse,
      max targetUniverse coefficientUniverse}
    (Module Domain Coefficient) (Module Range Coefficient)
    (lp.normedAddCommGroup (E := fun _ : Domain => Coefficient) (p := 2)
      (hp := inclusionExponentFact))
    (lp.instInnerProductSpace (𝕜 := ℂ) (G := fun _ : Domain => Coefficient))
    (lp.completeSpace (E := fun _ : Domain => Coefficient) (p := 2))
    (lp.normedAddCommGroup (E := fun _ : Range => Coefficient) (p := 2)
      (hp := inclusionExponentFact))
    (lp.instInnerProductSpace (𝕜 := ℂ) (G := fun _ : Range => Coefficient))
    (lp.completeSpace (E := fun _ : Range => Coefficient) (p := 2)) isometry
  fun operator operator_mem =>
    @map_mem.{sourceUniverse, targetUniverse, coefficientUniverse}
      Domain Range Coefficient normedCoefficient innerCoefficient
      domainDecidable rangeDecidable completeCoefficient domainMetric rangeMetric conjugation
      (@conjugation_continuous.{sourceUniverse, targetUniverse, coefficientUniverse}
        Domain Range Coefficient normedCoefficient innerCoefficient completeCoefficient isometry)
      (fun generator is_generator =>
        @generator_mem.{targetUniverse, coefficientUniverse}
          Range Coefficient normedCoefficient innerCoefficient rangeDecidable
          completeCoefficient rangeMetric (conjugation generator)
          (@inclusion_generator.{sourceUniverse, targetUniverse, coefficientUniverse}
            Domain Range Coefficient domainDecidable rangeDecidable normedCoefficient
            innerCoefficient completeCoefficient domainMetric rangeMetric e he
            generator is_generator))
      operator operator_mem

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary walks and their canonical lifts

Depth-zero fibers are singletons, so every edge of the actual boundary
subgraph has its unique lift. The walk construction and charge comparison
here leave only the explicit hexagonal boundary walk to be supplied.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem boundaryFiber_adj (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) {j : ℕ}
    {u v : BoundaryComponent j} (h : (boundaryGraph j).Adj u v) :
    (fiberedGraph S t j).Adj (boundaryFiberEmbedding j u) (boundaryFiberEmbedding j v) := by
  refine ⟨?_, 1, one_mem_symmetricMoves S, Or.inr ⟨h, rfl⟩, ?_⟩
  · intro he
    have huv := (boundaryFiberEmbedding j).injective he
    exact h.2.2.2 (congrArg (fun w : BoundaryComponent j => w.val.val) huv)
  · intro l hl _
    have hl0 : l = 0 := by
      change l ≤ discDepth j u.val at hl
      rw [u.property] at hl
      omega
    subst l
    exact Subsingleton.elim _ _

def boundaryFiberHom (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) :
    boundaryGraph j →g fiberedGraph S t j where
  toFun := boundaryFiberEmbedding j
  map_rel' := boundaryFiber_adj S t

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalSpatialFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform diagonal families on the actual separated vertex union -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, DecidableEq (V i)] [CompleteSpace H] in
theorem diagonalFamily_norm_le (A : ∀ i, Operator (V i) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) : ‖diagonalFamily A C hC hA‖ ≤ C :=
  (flattenOperator_norm_le _).trans (blockOperator_norm_le _ _ _ _)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ComponentHilbertInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Componentwise and whole-union spatial inclusions agree -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)] in
theorem row_inclusion_adjoint (e : ∀ i, Q i ↪ P i) (v : Module (Sigma P) H) (i : ℕ) :
    rowVector ((inclusionIsometry (H := H) (componentEmbedding e)).toContinuousLinearMap.adjoint v) i =
      (inclusionIsometry (H := H) (e i)).toContinuousLinearMap.adjoint (rowVector v i) := by
  apply lp.ext
  funext x
  change ((inclusionIsometry (H := H) (componentEmbedding e)).toContinuousLinearMap.adjoint v) ⟨i, x⟩ =
    ((inclusionIsometry (H := H) (e i)).toContinuousLinearMap.adjoint (rowVector v i)) x
  rw [inclusion_adjoint_apply, inclusion_adjoint_apply]
  rfl

omit [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)] [CompleteSpace H]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem row_inclusion (e : ∀ i, Q i ↪ P i) (v : Module (Sigma Q) H) (i : ℕ) :
    rowVector (inclusionIsometry (H := H) (componentEmbedding e) v) i =
      inclusionIsometry (H := H) (e i) (rowVector v i) := by
  apply lp.ext
  funext y
  by_cases hy : y ∈ Set.range (e i)
  · obtain ⟨x, rfl⟩ := hy
    change inclusionVector (componentEmbedding e) v (componentEmbedding e ⟨i, x⟩) =
      inclusionVector (e i) (rowVector v i) (e i x)
    rw [inclusionVector_apply, inclusionVector_apply]
    rfl
  · have hglobal : (⟨i, y⟩ : Sigma P) ∉ Set.range (componentEmbedding e) :=
      fun h => hy ((componentEmbedding_range e i y).mp h)
    change inclusionVector (componentEmbedding e) v ⟨i, y⟩ =
      inclusionVector (e i) (rowVector v i) y
    rw [inclusionVector_zero _ _ _ hglobal, inclusionVector_zero _ _ _ hy]

omit [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)] in
theorem row_isometricExtension (e : ∀ i, Q i ↪ P i) (T : Operator (Sigma Q) H)
    (A : ∀ i, Operator (Q i) H)
    (hT : ∀ v i, rowVector (T v) i = A i (rowVector v i))
    (v : Module (Sigma P) H) (i : ℕ) :
    rowVector (isometricExtension (inclusionIsometry (componentEmbedding e)) T v) i =
      isometricExtension (inclusionIsometry (e i)) (A i) (rowVector v i) := by
  apply lp.ext
  funext y
  change (rowVector (v + operatorConjugation (inclusionIsometry (componentEmbedding e)) (T - 1) v) i) y = _
  change v ⟨i, y⟩ +
    (rowVector (inclusionIsometry (componentEmbedding e)
      ((T - 1) ((inclusionIsometry (componentEmbedding e)).toContinuousLinearMap.adjoint v))) i) y = _
  rw [row_inclusion]
  have hsub : rowVector ((T - 1)
      ((inclusionIsometry (componentEmbedding e)).toContinuousLinearMap.adjoint v)) i =
      (A i - 1) ((inclusionIsometry (e i)).toContinuousLinearMap.adjoint (rowVector v i)) := by
    apply lp.ext
    funext x
    change rowVector (T ((inclusionIsometry (componentEmbedding e)).toContinuousLinearMap.adjoint v)) i x -
      rowVector ((inclusionIsometry (componentEmbedding e)).toContinuousLinearMap.adjoint v) i x = _
    rw [hT, row_inclusion_adjoint]
    rfl
  rw [hsub]
  rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalFamilyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform component estimates give norm-continuous spatial families -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Filter Topology

variable {V : ℕ → Type*} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem diagonalFamily_sub_eq (A B : ∀ i, Operator (V i) H)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (δ : ℝ) (hδ : 0 ≤ δ) (hAB : ∀ i, ‖A i - B i‖ ≤ δ) :
    diagonalFamily A C hC hA - diagonalFamily B D hD hB =
      diagonalFamily (fun i => A i - B i) δ hδ hAB := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext z
  rcases z with ⟨i, x⟩
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, diagonalFamily_apply]

/-- The bound does not depend on the number or sizes of the components. -/
theorem diagonalFamily_sub_norm_le (A B : ∀ i, Operator (V i) H)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (δ : ℝ) (hδ : 0 ≤ δ) (hAB : ∀ i, ‖A i - B i‖ ≤ δ) :
    ‖diagonalFamily A C hC hA - diagonalFamily B D hD hB‖ ≤ δ := by
  rw [diagonalFamily_sub_eq A B C D hC hD hA hB δ hδ hAB]
  exact diagonalFamily_norm_le _ _ _ _

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RoeIdealizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplication of the Roe ideal by controlled pseudolocal operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instContinuousStarOperator_1

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instIsScalarTowerComplexOperator_2

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instSMulCommClassComplexOperator_2

theorem finitePropagation_multiplier
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T : Operator X H} {r : ℝ} (hr : 0 ≤ r) (hp : PropagationLE r T) : RoeMultiplier T := by
  have hprod (S : Operator X H) (hS : Generator S) :
      T * S ∈ algebra (X := X) (H := H) ∧ S * T ∈ algebra (X := X) (H := H) := by
    obtain ⟨⟨s, hs, hq⟩, hc, hcs⟩ := hS
    constructor
    · apply generator_mem
      refine ⟨⟨r + s, add_nonneg hr hs, hp.mul finiteBalls hq⟩,
        hc.mul_right finiteBalls hq, ?_⟩
      rw [star_mul]
      exact hcs.mul_left finiteBalls hp.star
    · apply generator_mem
      refine ⟨⟨s + r, add_nonneg hs hr, hq.mul finiteBalls hp⟩,
        hc.mul_left finiteBalls hp, ?_⟩
      rw [star_mul]
      exact hcs.mul_right finiteBalls hq.star
  have hclosed : IsClosed {S : Operator X H |
      T * S ∈ algebra (X := X) (H := H) ∧ S * T ∈ algebra (X := X) (H := H)} :=
    (algebra_isClosed.preimage (continuous_const.mul continuous_id)).inter
      (algebra_isClosed.preimage (continuous_id.mul continuous_const))
  intro S
  have hm : S.val ∈ (algebraicRoe (H := H) finiteBalls).topologicalClosure := by
    rw [← roe_eq_closure_algebraic finiteBalls]
    exact S.property
  exact closure_minimal hprod hclosed hm

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_MultiplierBoundaryClass
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalFamily_apply _root_.OAI.CoarseAssembly.DiscreteRoe.entry_diagonalFamily_same _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary classes in the closed Roe multiplier algebra

A controlled Rips operator is a Roe multiplier even when it is not
pseudolocal for the discrete vertex representation. The ideal-boundary
construction is therefore performed in this actual closed multiplier
algebra before constructing the coarse assembly map.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem multiplierBoundaryUnitary_sub_one_mem
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hdefect : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    (multiplierBoundaryUnitary F hF : Operator X H) - 1 ∈ algebra (X := X) (H := H) := by
  have hF' : F ^ 2 - 1 ∈ multiplierRoeIdeal (X := X) (H := H) := by
    rw [mem_multiplierRoeIdeal]
    simpa using hdefect
  have h := Analytic.rationalBoundaryUnitary_sub_one_mem
    (multiplierRoeIdeal (X := X) (H := H)) F hF hF'
  rw [mem_multiplierRoeIdeal] at h
  exact h

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_MultiplierBoundaryHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm homotopy invariance of the Roe multiplier boundary class -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance multiplierHomotopyScalarTower_r202910_1 : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance multiplierHomotopyScalarComm_r202910_1 : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
theorem multiplierBoundaryClass_eq_zero
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hdefect : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) (hsq : F * F = 1) :
    multiplierBoundaryClass F hF hdefect = 0 := by
  apply OperatorKTheory.relativeClass_eq_zero (hS := algebra_isClosed)
  have hu := Analytic.rationalBoundaryUnitary_eq_one F hF hsq
  apply Subtype.ext
  change ((Analytic.rationalBoundaryUnitary F hF : multiplierAlgebra (X := X) (H := H)) : Operator X H) = 1
  rw [hu]
  rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteHeadNormalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly controlled involutive replacement of a finite head -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem finiteHead_propagation (J : Finset ℕ) (A B : ∀ i, Operator (V i) H)
    (r : ℝ) (hp : ∀ i, PropagationLE r (A i)) (htail : ∀ i, i ∉ J → B i = A i) :
    ∀ i, PropagationLE (max r (finiteHeadRadius (V := V) J)) (B i) := by
  intro i x y hxy
  by_cases hi : i ∈ J
  · exact False.elim ((not_lt_of_ge ((finiteHeadRadius_diam J hi x y).trans (le_max_right _ _))) hxy)
  · rw [htail i hi]
    exact hp i x y ((le_max_left _ _).trans_lt hxy)

variable [SecondCountableTopology H]

def componentHilbert (i : ℕ) : HilbertSpace where
  Carrier := Module (V i) H
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := (lpPiLpₗᵢ (fun _ : V i => H) ℂ (p := 2)).isometry.isEmbedding.secondCountableTopology

/-- Only finitely many components are changed. Their new operators are
involutions, their differences are compact, and all propagation stays bounded. -/
theorem exists_finiteHead_involution (J : Finset ℕ) (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hA : ∀ i, ‖A i‖ ≤ C) (r : ℝ)
    (hp : ∀ i, PropagationLE r (A i))
    (hs : ∀ i, IsSelfAdjoint (A i))
    (hc : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) :
    ∃ B : ∀ i, Operator (V i) H,
      (∀ i, IsSelfAdjoint (B i)) ∧
      (∀ i, ‖B i‖ ≤ max C 1) ∧
      (∀ i, PropagationLE (max r (finiteHeadRadius (V := V) J)) (B i)) ∧
      (∀ i, IsCompactOperator (B i - A i)) ∧
      (∀ i, i ∈ J → B i * B i = 1) ∧
      (∀ i, i ∉ J → B i = A i) := by
  have hex (i : ℕ) : ∃ N : Operator (V i) H,
      IsSelfAdjoint N ∧ N * N = 1 ∧ IsCompactOperator (N - A i : Operator (V i) H) ∧
        IsCompactOperator (star (N - A i) : Operator (V i) H) :=
    @exists_compact_involution (componentHilbert (V := V) (H := H) i) (A i) (hs i) (hc i)
  choose N hNs hNi hNc _hNcs using hex
  let B : ∀ i, Operator (V i) H := fun i => if i ∈ J then N i else A i
  have htail (i : ℕ) (hi : i ∉ J) : B i = A i := by simp only [B, ite_eq_right hi]
  refine ⟨B, ?_, ?_, finiteHead_propagation J A B r hp htail, ?_, ?_, htail⟩
  · intro i
    dsimp only [B]
    split_ifs with hi
    · exact hNs i
    · exact hs i
  · intro i
    dsimp only [B]
    split_ifs with hi
    · exact (@involution_norm_le_one (componentHilbert (V := V) (H := H) i) (N i) (hNs i) (hNi i)).trans (le_max_right _ _)
    · exact (hA i).trans (le_max_left _ _)
  · intro i
    dsimp only [B]
    split_ifs with hi
    · exact hNc i
    · rw [sub_self]
      change IsCompactOperator (0 : Module (V i) H → Module (V i) H)
      exact isCompactOperator_zero
  · intro i hi
    dsimp only [B]
    rw [ite_eq_left hi]
    exact hNi i


def finiteHeadReplacement (J : Finset ℕ) (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hA : ∀ i, ‖A i‖ ≤ C) (r : ℝ)
    (hp : ∀ i, PropagationLE r (A i)) (hs : ∀ i, IsSelfAdjoint (A i))
    (hc : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) :
    FiniteHeadReplacement J A C r :=
  let h := exists_finiteHead_involution J A C hA r hp hs hc
  { operator := h.choose
    selfAdjoint := h.choose_spec.1
    norm_le := h.choose_spec.2.1
    propagation := h.choose_spec.2.2.1
    compact_diff := h.choose_spec.2.2.2.1
    involutive := h.choose_spec.2.2.2.2.1
    tail := h.choose_spec.2.2.2.2.2 }

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_MultiplierBoundaryNearby
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm-local constancy of the actual Roe boundary class -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem multiplierBoundaryClass_eq_of_nearby
    (F G : multiplierAlgebra (X := X) (H := H))
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hnear : ‖G - F‖ < (1 / 4 : ℝ)) :
    multiplierBoundaryClass F hF hFd = multiplierBoundaryClass G hG hGd := by
  apply OperatorKTheory.relativeClass_eq_of_nearby (hS := algebra_isClosed)
  have hb := Analytic.rationalBoundaryUnitary_sub_norm_le G F hG hF
  change ‖(Analytic.rationalBoundaryUnitary G hG : multiplierAlgebra (X := X) (H := H)) -
    Analytic.rationalBoundaryUnitary F hF‖ < 1
  exact hb.trans_lt (by linarith)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Hilbert-space isometry of a finite square partition -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem partitionMap_adjoint (a : X → H →L[ℂ] H) :
    (partitionMap a).adjoint = ∑ x, (a x).adjoint.comp (coordinate x) := by
  simp only [partitionMap, map_sum, ContinuousLinearMap.adjoint_comp, insert_adjoint]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The contraction estimate for finite partition localization -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype X] [DecidableEq X] [CompleteSpace H] in
theorem constantBlock_norm_le (F : H →L[ℂ] H) : ‖constantBlock (X := X) F‖ ≤ ‖F‖ :=
  blockOperator_norm_le _ _ _ _

theorem partitionMap_adjoint_apply (a : X → H →L[ℂ] H) (v : Module X H) :
    (partitionMap a).adjoint v = ∑ x, (a x).adjoint (v x) := by
  rw [partitionMap_adjoint]
  simp only [sum_apply, ContinuousLinearMap.comp_apply, coordinate_apply]

theorem partitionCompression_eq_sum (a : X → H →L[ℂ] H) (F : H →L[ℂ] H) :
    partitionCompression a F = ∑ x, (a x).adjoint.comp (F.comp (a x)) := by
  ext v
  simp only [partitionCompression, ContinuousLinearMap.comp_apply, partitionMap_adjoint_apply,
    constantBlock_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  have hx := DFunLike.congr_fun (coordinate_partitionMap a x) v
  exact congrArg (fun h => (a x).adjoint (F h)) hx

theorem partitionCompression_norm_le (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    ‖partitionCompression a F‖ ≤ ‖F‖ := by
  have hv : ‖partitionMap a‖ ≤ 1 := by
    exact (partitionIsometry a hpart).norm_toContinuousLinearMap_le
  have hvs : ‖(partitionMap a).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hv
  calc
    ‖partitionCompression a F‖ ≤ ‖(partitionMap a).adjoint‖ *
        (‖constantBlock (X := X) F‖ * ‖partitionMap a‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖F‖ * 1) := by
      gcongr
      exact constantBlock_norm_le F
    _ = ‖F‖ := by ring

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionSpatialControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial control of the partition-localized operator -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem partitionMap_adjoint_insert (a : X → H →L[ℂ] H) (y : X) :
    (partitionMap a).adjoint.comp (insert y) = (a y).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (coordinate_partitionMap a y)
  simpa only [ContinuousLinearMap.adjoint_comp, coordinate_adjoint] using h

theorem entry_partitionConjugate (a : X → H →L[ℂ] H) (F : H →L[ℂ] H) (x y : X) :
    entry (partitionConjugate a F) x y = a x * F * (a y).adjoint := by
  calc
    entry (partitionConjugate a F) x y =
        ((coordinate x).comp (partitionMap a)).comp
          (F.comp ((partitionMap a).adjoint.comp (insert y))) := by
      simp only [entry, partitionConjugate, ContinuousLinearMap.comp_assoc]
    _ = _ := by
      rw [coordinate_partitionMap, partitionMap_adjoint_insert]
      rfl

variable [PseudoMetricSpace X]

theorem partitionConjugate_one_propagation (a : X → H →L[ℂ] H)
    (ha : ∀ x, (a x).adjoint = a x) (r : ℝ)
    (hsupport : ∀ x y, r < dist x y → a x * a y = 0) :
    PropagationLE r (partitionConjugate a 1) := by
  intro x y hxy
  rw [entry_partitionConjugate, ha y, mul_one]
  exact hsupport x y hxy

theorem partitionLocalization_propagation (a : X → H →L[ℂ] H)
    (ha : ∀ x, (a x).adjoint = a x) (r : ℝ)
    (hsupport : ∀ x y, r < dist x y → a x * a y = 0) (F : H →L[ℂ] H) :
    PropagationLE (r + r) (partitionConjugate a (partitionCompression a F)) := by
  intro x y hxy
  rw [entry_partitionConjugate, partitionCompression_eq_sum, ha y]
  change a x * (∑ z, (a z).adjoint * F * a z) * a y = 0
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro z _
  rw [ha z]
  by_cases hxz : r < dist x z
  · rw [← mul_assoc (a x), ← mul_assoc (a x), hsupport x z hxz, zero_mul, zero_mul,
      zero_mul]
  · have hzy : r < dist z y := by
      have ht := dist_triangle x z y
      have hxz' := le_of_not_gt hxz
      linarith
    simp only [mul_assoc, hsupport z y hzy, mul_zero]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SpatialLocalization
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalFamily_apply _root_.OAI.CoarseAssembly.DiscreteRoe.entry_diagonalFamily_same _root_.OAI.CoarseAssembly.DiscreteRoe.mem_multiplierRoeIdeal _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The controlled spatial representative of a localized operator -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.spatialLocalizationContinuousAdd

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.spatialLocalizationRingHomCompTriple

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.spatialLocalizationCompleteSpace

theorem partitionConjugate_eq (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    partitionConjugate a F = operatorConjugation (partitionIsometry a hpart) F := by
  rfl

theorem localizedSpatialOperator_eq (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    localizedSpatialOperator a hpart F =
      1 + partitionConjugate a (partitionCompression a F) - partitionConjugate a 1 := by
  rw [partitionConjugate_eq a hpart, partitionConjugate_eq a hpart]
  change 1 + operatorConjugationHom (partitionIsometry a hpart) (partitionCompression a F - 1) =
    1 + operatorConjugationHom (partitionIsometry a hpart) (partitionCompression a F) -
      operatorConjugationHom (partitionIsometry a hpart) 1
  rw [map_sub, add_sub_assoc]

theorem partitionCompression_selfAdjoint (a : X → H →L[ℂ] H)
    (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) : IsSelfAdjoint (partitionCompression a F) := by
  rw [partitionCompression_eq_sum]
  exact isSelfAdjoint_sum _ (fun x _ => hF.conjugate' (a x))

theorem localizedSpatialOperator_selfAdjoint (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (localizedSpatialOperator a hpart F) :=
  isometricExtension_selfAdjoint _ _ (partitionCompression_selfAdjoint a F hF)

theorem localizedSpatialOperator_norm_le (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    ‖localizedSpatialOperator a hpart F‖ ≤ ‖F‖ + 2 :=
  (isometricExtension_norm_le _ _).trans
    (add_le_add (partitionCompression_norm_le a hpart F) le_rfl)

variable [PseudoMetricSpace X]

omit [Fintype X] [CompleteSpace H] [PseudoMetricSpace X] in
theorem entry_sub (T S : Operator X H) (x y : X) :
    entry (T - S) x y = entry T x y - entry S x y := by
  ext v
  simp [entry]

theorem localizedSpatialOperator_propagation (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1)
    (ha : ∀ x, (a x).adjoint = a x) (r : ℝ) (hr : 0 ≤ r)
    (hsupport : ∀ x y, r < dist x y → a x * a y = 0) (F : H →L[ℂ] H) :
    PropagationLE (r + r) (localizedSpatialOperator a hpart F) := by
  intro x y hxy
  rw [localizedSpatialOperator_eq, entry_sub, entry_add,
    partitionLocalization_propagation a ha r hsupport F x y hxy,
    partitionConjugate_one_propagation a ha r hsupport x y (by linarith),
    add_zero, sub_zero]
  exact propagationLE_one x y (by linarith)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite partition localization under vertex inclusions -/

noncomputable section

namespace CoarseAssembly

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

namespace DiscreteRoe

variable {X Y H : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem partitionMap_inclusion (e : X ↪ Y) (a : X → H →L[ℂ] H) (b : Y → H →L[ℂ] H)
    (he : ∀ x, b (e x) = a x) (hz : ∀ y, y ∉ Set.range e → b y = 0) :
    (inclusionIsometry (H := H) e).toContinuousLinearMap.comp (partitionMap a) =
      partitionMap b := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext y
  change inclusionVector e (partitionMap a v) y = partitionMap b v y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [inclusionVector_apply, partitionMap_apply, partitionMap_apply, he]
  · rw [inclusionVector_zero e _ _ hy, partitionMap_apply, hz y hy, zero_apply]

theorem partitionIsometry_inclusion (e : X ↪ Y) (a : X → H →L[ℂ] H) (b : Y → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hb : ∑ y, (b y).adjoint.comp (b y) = 1)
    (he : ∀ x, b (e x) = a x) (hz : ∀ y, y ∉ Set.range e → b y = 0) :
    (inclusionIsometry e).comp (partitionIsometry a ha) = partitionIsometry b hb := by
  apply DFunLike.ext
  intro v
  exact DFunLike.congr_fun (partitionMap_inclusion e a b he hz) v

omit [Fintype Y] [DecidableEq X] [CompleteSpace H] in
theorem constantBlock_inclusion (e : X ↪ Y) (T : H →L[ℂ] H) :
    (constantBlock (X := Y) T).comp (inclusionIsometry e).toContinuousLinearMap =
      (inclusionIsometry e).toContinuousLinearMap.comp (constantBlock (X := X) T) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext y
  change T (inclusionVector e v y) = inclusionVector e (constantBlock T v) y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [inclusionVector_apply, inclusionVector_apply, constantBlock_apply]
  · rw [inclusionVector_zero e _ _ hy, inclusionVector_zero e _ _ hy, map_zero]

theorem partitionCompression_inclusion (e : X ↪ Y)
    (a : X → H →L[ℂ] H) (b : Y → H →L[ℂ] H)
    (he : ∀ x, b (e x) = a x) (hz : ∀ y, y ∉ Set.range e → b y = 0) (T : H →L[ℂ] H) :
    partitionCompression b T = partitionCompression a T := by
  unfold partitionCompression
  rw [← partitionMap_inclusion e a b he hz, ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro v
  change (partitionMap a).adjoint ((inclusionIsometry e).toContinuousLinearMap.adjoint
    (constantBlock T (inclusionIsometry e (partitionMap a v)))) =
      (partitionMap a).adjoint (constantBlock T (partitionMap a v))
  have h := DFunLike.congr_fun (constantBlock_inclusion e T) (partitionMap a v)
  change constantBlock T (inclusionIsometry e (partitionMap a v)) =
    inclusionIsometry e (constantBlock T (partitionMap a v)) at h
  rw [h, adjoint_apply_isometry]

theorem localizedSpatialOperator_inclusion (e : X ↪ Y)
    (a : X → H →L[ℂ] H) (b : Y → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hb : ∑ y, (b y).adjoint.comp (b y) = 1)
    (he : ∀ x, b (e x) = a x) (hz : ∀ y, y ∉ Set.range e → b y = 0) (T : H →L[ℂ] H) :
    localizedSpatialOperator b hb T =
      isometricExtension (inclusionIsometry e) (localizedSpatialOperator a ha T) := by
  unfold localizedSpatialOperator
  rw [isometricExtension_comp, partitionIsometry_inclusion e a b ha hb he hz,
    partitionCompression_inclusion e a b he hz]

end DiscreteRoe
end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativePartialIsometry
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.homotopySlice_finish _root_.OAI.CoarseAssembly.Analytic.homotopySlice_start _root_.OAI.CoarseAssembly.Analytic.intervalGrid_finish _root_.OAI.CoarseAssembly.Analytic.intervalGrid_start _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_succ _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_zero _root_.OAI.CoarseAssembly.TopologicalK1.nearbyUnitPath_finish _root_.OAI.CoarseAssembly.TopologicalK1.nearbyUnitPath_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative K₁ classes agree under equivalence of their supported corners -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open Analytic

variable {A R : Type*} [CStarAlgebra A] [CStarAlgebra R]

theorem partialIsometryDilation_conjugates_unitary
    (T : A) (hT : T * star T * T = T) (u v : unitary A)
    (hleft : (star T * T) * ((u : A) - 1) = (u : A) - 1)
    (hright : ((u : A) - 1) * (star T * T) = (u : A) - 1)
    (hv : (v : A) = 1 + T * ((u : A) - 1) * star T) :
    partialIsometryDilation T * (diagonalTwoUnitary u 1).val *
      star (partialIsometryDilation T) = (diagonalTwoUnitary 1 v).val := by
  rw [(partialIsometryDilation_selfAdjoint T).star_eq]
  have hd : (diagonalTwoUnitary u 1).val = !![1 + ((u : A) - 1), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalTwoUnitary, Matrix.diagonal]
  rw [hd, partialIsometryDilation_conjugation T ((u : A) - 1) hT hleft hright]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalTwoUnitary, Matrix.diagonal, hv]

variable (S : NonUnitalStarSubalgebra ℂ R) [hS : IsClosed (S : Set R)]

/-- A partial isometry between supported defects gives equality in the original K₁. -/
theorem relativeClass_partialIsometry (φ : A →⋆ₐ[ℂ] R) (hφc : Continuous φ)
    (hφ : ∀ a b, b ∈ S → φ a * b ∈ S ∧ b * φ a ∈ S)
    (T : A) (hT : T * star T * T = T) (u v : unitary A)
    (hleft : (star T * T) * ((u : A) - 1) = (u : A) - 1)
    (hright : ((u : A) - 1) * (star T * T) = (u : A) - 1)
    (hv : (v : A) = 1 + T * ((u : A) - 1) * star T)
    (huS : φ (u : A) - 1 ∈ S) (hvS : φ (v : A) - 1 ∈ S) :
    relativeClass S (Unitary.map (StarMonoidHom.ofClass φ) u) huS =
      relativeClass S (Unitary.map (StarMonoidHom.ofClass φ) v) hvS := by
  let W := partialIsometryDilationPath T hT
  let u' := Unitary.map (StarMonoidHom.ofClass φ) u
  let v' := Unitary.map (StarMonoidHom.ofClass φ) v
  have h0 : conjugatedTwoUnitary (mapTwoUnitary φ (W start)) (diagonalTwoUnitary u' 1) =
      diagonalTwoUnitary u' 1 := by
    change conjugatedTwoUnitary (mapTwoUnitary φ (partialIsometryDilationPath T hT start)) _ = _
    rw [partialIsometryDilationPath_start, mapTwoUnitary_one]
    simp [conjugatedTwoUnitary]
  have hd : conjugatedTwoUnitary (W finish) (diagonalTwoUnitary u 1) =
      diagonalTwoUnitary 1 v := by
    apply Subtype.ext
    change (W finish).val * (diagonalTwoUnitary u 1).val * star (W finish).val = _
    dsimp only [W]
    rw [partialIsometryDilationPath_finish]
    exact partialIsometryDilation_conjugates_unitary T hT u v hleft hright hv
  have h1 : conjugatedTwoUnitary (mapTwoUnitary φ (W finish)) (diagonalTwoUnitary u' 1) =
      diagonalTwoUnitary 1 v' := by
    have hm := congrArg (mapTwoUnitary φ) hd
    rw [mapTwoUnitary_conjugate, mapTwoUnitary_diagonal, mapTwoUnitary_diagonal] at hm
    simpa only [map_one] using hm
  have hz : ((1 : unitary R) : R) - 1 ∈ S := by simp
  have h := relativeTwoClass_conjugationPath S φ hφc hφ W
    (partialIsometryDilationPath_continuous T hT) (diagonalTwoUnitary u' 1)
    (diagonalTwoUnitary_relative S u' 1 huS hz)
  simp only [h0, h1] at h
  rw [relativeTwoClass_diagonal S u' 1 huS hz,
    relativeTwoClass_diagonal S 1 v' hz hvS, relativeClass_one S hz, add_zero, zero_add] at h
  exact h

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite localization respects reducing isometric intertwiners -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem partitionCompression_intertwines (I : E →ₗᵢ[ℂ] H)
    (a : X → E →L[ℂ] E) (b : X → H →L[ℂ] H)
    (ha : ∀ x, (a x).adjoint = a x) (hb : ∀ x, (b x).adjoint = b x)
    (hI : ∀ x v, b x (I v) = I (a x v))
    (F : E →L[ℂ] E) (G : H →L[ℂ] H) (hF : ∀ v, G (I v) = I (F v)) (v : E) :
    partitionCompression b G (I v) = I (partitionCompression a F v) := by
  simp only [partitionCompression_eq_sum, sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [ha, hb, hI, hF, hI]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionMapNorm
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalFamily_apply _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalMultiplier_apply _root_.OAI.CoarseAssembly.DiscreteRoe.entry_diagonalFamily_same _root_.OAI.CoarseAssembly.DiscreteRoe.mem_multiplierRoeIdeal _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite-coordinate estimate for partition isometries -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [Fintype X] in
theorem insert_norm_le_one (x : X) : ‖insert (H := H) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖lp.single (E := fun _ : X => H) 2 x v‖ ≤ 1 * ‖v‖
  simpa only [one_mul] using
    (lp.norm_single (E := fun _ : X => H) (by norm_num : (0 : ENNReal) < 2) x v).le

theorem partitionMap_sub (a b : X → H →L[ℂ] H) :
    partitionMap a - partitionMap b = ∑ x, (insert x).comp (a x - b x) := by
  simp only [partitionMap, ContinuousLinearMap.comp_sub, Finset.sum_sub_distrib]

theorem partitionMap_sub_norm_le_sum (a b : X → H →L[ℂ] H) :
    ‖partitionMap a - partitionMap b‖ ≤ ∑ x, ‖a x - b x‖ := by
  rw [partitionMap_sub]
  apply (norm_sum_le Finset.univ (fun x => (insert (H := H) x).comp (a x - b x))).trans
  apply Finset.sum_le_sum
  intro x _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (insert_norm_le_one (H := H) x) (norm_nonneg (a x - b x)))

end CoarseAssembly.DiscreteRoe

end

end OAI
end


