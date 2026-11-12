-- Prove2me | Definitions.Def_OAIQ229C038
-- name    : OAIQ229C038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:47:53.725243+00:00
-- url     : https://prove2.me/theorems/e22025c7-99e6-43a1-8e32-66fa444f711a
-- title:
--   Definitions bundle OAIQ229C038 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_AnalyticFamilyIndex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/AnalyticFamilyIndex.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C034` and `OAIQ229C037` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ229C039`; the proof of `OAI_CoarseAssembly_provedKazhdanInput_ca`.
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
import Definitions.Def_OAIQ229C034
import Definitions.Def_OAIQ229C037

section
-- module Solutions.Q229_CA.CoarseAssembly_AnalyticFamilyIndex
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A whole-union index on the actual analytic K-homology domain

Restriction homomorphisms into a family of finite Rips function algebras
are explicit parameters. The map descends through every relation of the
original Fredholm-module group, without a countable-additivity assumption.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ} {A : Type} [NonUnitalCStarAlgebra A]

theorem analyticFamilyIndexFree_relation (o : ∀ i, Q i) (hr : 0 ≤ r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (η : ∀ i, C(Point (Q i) r, ℂ) →⋆ₙₐ[ℂ] A)
    {z : FreeAbelianGroup (OddCycle A)} (hz : CycleRelation A z) :
    analyticFamilyIndexFree o hr χ η z = 0 := by
  let := separatedMetric o
  cases hz with
  | degenerate c h =>
    simpa only [analyticFamilyIndexFree, FreeAbelianGroup.lift_apply_of] using
      regularizedFamily_degenerate (fun i => c.precomp (η i))
        (fun i => h.precomp (η i)) χ o hr
  | unitary c d h =>
    simp only [analyticFamilyIndexFree, map_sub, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (regularizedFamily_unitary _ _ (fun i => h.precomp (η i)) χ o hr)
  | directSum c d e h =>
    simp only [analyticFamilyIndexFree, map_sub, map_add, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (regularizedFamily_directSum _ _ _ (fun i => h.precomp (η i)) χ o hr)
  | homotopy h =>
    simp only [analyticFamilyIndexFree, map_sub, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (regularizedFamily_homotopy (fun i => h.precomp (η i)) χ o hr)

end CoarseAssembly.Rips

end

end OAI
end


