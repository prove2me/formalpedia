-- Prove2me | Definitions.Def_OAIQ229C034
-- name    : OAIQ229C034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T15:26:23.847776+00:00
-- url     : https://prove2.me/theorems/6c5382ab-8cf2-4fc3-a05d-b8fcbcd10ddd
-- title:
--   Definitions bundle OAIQ229C034 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_CoefficientInclusion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/CoefficientInclusion.lean), [`CoarseAssembly_RegularizedRipsRelations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RegularizedRipsRelations.lean), [`CoarseAssembly_RipsBoundaryDegeneracy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsBoundaryDegeneracy.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C028` and `OAIQ229C030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C036` and `OAIQ229C038`; the statement `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_certificate`; the proofs of `OAI_CoarseAssembly_provedKazhdanInput` and `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_certificate`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
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
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C028
import Definitions.Def_OAIQ229C030

section
-- module Solutions.Q229_CA.CoarseAssembly_CoefficientInclusion
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ample coefficient transport commutes with vertex inclusion -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem ampleRipsOperator_inclusion (r : ℝ) (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (c : OddCycle C(Point X r, ℂ)) (hπ : c.representation 1 = 1) :
    ampleRipsOperator r (includedCycle r e he c) (includedCycle_unital r e he c hπ) =
      isometricExtension (inclusionIsometry e) (ampleRipsOperator r c hπ) := by
  let V := ampleIsometry c.space
  change isometricExtension (coefficientIsometry (X := Y) V)
      (ripsSpatialOperator r (includedCycle r e he c) (includedCycle_unital r e he c hπ)) =
    isometricExtension (inclusionIsometry e)
      (isometricExtension (coefficientIsometry (X := X) V) (ripsSpatialOperator r c hπ))
  have h := ripsSpatialOperator_inclusion r e he c hπ
  rw [h]
  simp only [isometricExtension_comp, coefficientIsometry_inclusion]

end CoarseAssembly.Rips

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

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

theorem ampleRipsFamilyBoundary_degenerate (o : ∀ i, V i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (V i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hnorm : ∀ i, ‖(c i).operator‖ ≤ C)
    (hc : ∀ i, (c i).Degenerate) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hπ hF C hC hnorm = 0 := by
  let := separatedMetric o
  exact separatedFamilyBoundary_involution o
    (fun i => ampleRipsOperator r (c i) (hπ i)) (C + 4) (by linarith)
    (fun i => (ampleRipsOperator_norm_le r (c i) (hπ i)).trans (by linarith [hnorm i]))
    (r + r) (add_nonneg hr hr)
    (fun i => ampleRipsOperator_propagation r hr (c i) (hπ i))
    (fun i => ampleRipsOperator_selfAdjoint r (c i) (hπ i) (hF i))
    (fun i => ampleRipsOperator_square_compact r (c i) (hπ i) (hF i))
    (fun i => ampleRipsOperator_degenerate_sq r (c i) (hπ i) (hc i))

end Rips

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RegularizedRipsRelations
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regularized whole-union boundary respects all analytic cycle relations -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

theorem regularizedFamily_degenerate
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).Degenerate)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ) (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (regularizedFamily c χ).boundary o hr = 0 := by
  let := separatedMetric o
  let C := regularizedFamily c χ
  exact ampleRipsFamilyBoundary_degenerate o r hr C.cycle C.unital C.selfAdjoint
    C.bound C.bound_nonneg C.norm_le (fun i => (h i).regularize (χ i))

end CoarseAssembly.Rips

end

end OAI
end


