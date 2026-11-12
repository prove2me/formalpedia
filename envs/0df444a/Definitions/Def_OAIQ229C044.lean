-- Prove2me | Definitions.Def_OAIQ229C044
-- name    : OAIQ229C044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T00:31:32.970585+00:00
-- url     : https://prove2.me/theorems/54678f7a-cdbd-4f2d-abe3-51394a80ec21
-- title:
--   Definitions bundle OAIQ229C044 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_SeparatedIndexNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SeparatedIndexNaturality.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C036` and `OAIQ229C042` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C045`, `OAIQ229C046`, `OAIQ229C047` and `OAIQ229C049`; the proof of `OAI_NuclearUltrapower_SOS_bucket_support_original_ca`.
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
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
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
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C036
import Definitions.Def_OAIQ229C042

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedIndexNaturality
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric naturality on the actual locally finite analytic domain -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe
open scoped ZeroAtInfty

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] {r : ℝ}

theorem separatedRipsIndex_inclusion (o : ∀ i, Q i) (p : ∀ i, P i) (hr : 0 ≤ r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (hroot : ∀ i, e i (o i) = p i)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y) :
    letI := separatedMetric o
    letI := separatedMetric p
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    letI : Ring (Unitization ℂ (algebra (X := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    (separatedRipsIndex p r hr).comp (pushforward (embeddingMap (componentEmbedding e) he r)) =
      (OperatorKTheory.map (inclusionHom (X := Sigma Q) (Y := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2)
      (componentEmbedding e) he)).comp (separatedRipsIndex o r hr) := by
  let := separatedMetric o
  let := separatedMetric p
  let : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
    inferInstance
  let : Ring (Unitization ℂ (algebra (X := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2))) :=
    inferInstance
  apply Analytic.hom_ext
  intro c
  let K := OperatorKTheory.map (inclusionHom (X := Sigma Q) (Y := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2)
      (componentEmbedding e) he)
  let C := regularizedFamily (fun i => c.precomp (lateRipsFunctionHom o r i)) (ripsPointCharacter o r hr)
  let D := regularizedFamily
    (fun i => (c.precomp (pullback (embeddingMap (componentEmbedding e) he r))).precomp
      (lateRipsFunctionHom p r i)) (ripsPointCharacter p r hr)
  let J : Finset ℕ := Finset.range (Nat.ceil r + 1)
  have ht := D.boundary_eq_of_tail (C.included e hei) p hr hr J (by
    intro i hi
    have hni : Nat.ceil r < i := Nat.lt_of_succ_le (Nat.le_of_not_lt (by
      simpa only [J, Finset.mem_range] using hi))
    have hil : r < i := (Nat.le_ceil r).trans_lt (by exact_mod_cast hni)
    exact ampleRipsOperator_eq_of_cycle_eq r _ _
      (late_regularizedCycle_included o p hr e hei hroot he c i hil) _ _)
  have hbd : D.boundary p hr = K (C.boundary o hr) :=
    ht.trans (C.boundary_included o p hr e hei he).symm
  have hp := congrArg (separatedRipsIndex p r hr)
    (Analytic.precomp_cycleClass (pullback (embeddingMap (componentEmbedding e) he r)) c)
  have hsource := congrArg K (separatedRipsIndex_class o r hr c)
  exact hp.trans ((separatedRipsIndex_class p r hr
    (c.precomp (pullback (embeddingMap (componentEmbedding e) he r)))).trans
      (hbd.trans hsource.symm))

end CoarseAssembly.Rips

end

end OAI
end


