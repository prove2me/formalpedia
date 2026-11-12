-- Prove2me | Definitions.Def_OAIQ229C041
-- name    : OAIQ229C041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T23:32:56.852113+00:00
-- url     : https://prove2.me/theorems/dbc7a0f7-2b94-4097-9011-9cf5102eb0fe
-- title:
--   Definitions bundle OAIQ229C041 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_ComponentRestrictionNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ComponentRestrictionNaturality.lean), [`CoarseAssembly_LateRipsCoarsening`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/LateRipsCoarsening.lean), [`CoarseAssembly_SeparatedIndexCoarsening`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SeparatedIndexCoarsening.lean), [`CoarseAssembly_SeparatedIndexNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SeparatedIndexNaturality.lean), [`CoarseAssembly_SeparatedRipsIndex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SeparatedRipsIndex.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundle `OAIQ229C040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C042`, `OAIQ229C046`, `OAIQ229C047` and `OAIQ229C049`.
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
import Definitions.Def_OAIQ229C040

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedRipsIndex
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.compactIndexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.indexPairing_cycleClass _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A scale index on the actual locally finite analytic domain

Late Rips components are compact and open in the full realization. Their
extension-by-zero homomorphisms give the restriction family used by the
constructed index. Finitely many early components are omitted; compatibility
of this omission across scales is proved separately.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe
open scoped ZeroAtInfty

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

@[simp] theorem separatedRipsIndex_class (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : letI := separatedMetric o; OddCycle C₀(Point (Sigma Q) r, ℂ)) :
    separatedRipsIndex o r hr (cycleClass _ c) =
      (regularizedFamily (fun i => c.precomp (lateRipsFunctionHom o r i))
        (ripsPointCharacter o r hr)).boundary o hr :=
  analyticFamilyIndex_class _ _ _ _ _

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LateRipsCoarsening
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarsening commutes with restriction to every sufficiently late component -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic
open scoped ZeroAtInfty

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
theorem separatedRips_coarsen_preimage (o : ∀ i, Q i) (hrs : r ≤ s) (i : ℕ) :
    letI := separatedMetric o
    ∀ x : Point (Sigma Q) r,
      coarsen hrs x ∈ Set.range (separatedRipsEmbedding o s i) ↔
        x ∈ Set.range (separatedRipsEmbedding o r i) := by
  let := separatedMetric o
  intro x
  change coarsen hrs x ∈ Set.range (mapPoint (separatedComponent i)
    (fun a b => ((separatedComponent_isometry o i).dist_eq a b).le)) ↔
      x ∈ Set.range (mapPoint (separatedComponent i)
        (fun a b => ((separatedComponent_isometry o i).dist_eq a b).le))
  rw [mapPoint_range (separatedComponent i) (separatedComponent_isometry o i),
    mapPoint_range (separatedComponent i) (separatedComponent_isometry o i)]
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem lateRipsFunctionHom_coarsen (o : ∀ i, Q i) (hrs : r ≤ s)
    (i : ℕ) (hi : s < i) :
    letI := separatedMetric o
    (pullback (inclusion (X := Sigma Q) hrs)).comp (lateRipsFunctionHom o s i) =
      (lateRipsFunctionHom o r i).comp (scaleFunctionHom hrs).toNonUnitalStarAlgHom := by
  let := separatedMetric o
  have hir : r < i := hrs.trans_lt hi
  have heq := pullback_zeroExtension
    (separatedRipsEmbedding o r i) (separatedRipsEmbedding_open o r i hir)
    (separatedRipsEmbedding o s i) (separatedRipsEmbedding_open o s i hi)
    (inclusion (X := Sigma Q) hrs) (inclusion (X := Q i) hrs)
    (fun a => coarsen_mapPoint hrs (separatedComponent i)
      (fun x y => ((separatedComponent_isometry o i).dist_eq x y).le) a)
    (separatedRips_coarsen_preimage o hrs i)
  ext f x
  have hx := congrArg (fun g : C₀(Point (Sigma Q) r, ℂ) => g x)
    (DFunLike.congr_fun heq (compactFunctionLift f))
  have hc : pullback (inclusion (X := Q i) hrs) (compactFunctionLift f) =
      compactFunctionLift ((scaleFunctionHom hrs) f) := by
    ext p
    rfl
  simp only [NonUnitalStarAlgHom.comp_apply] at hx
  rw [hc] at hx
  simpa only [lateRipsFunctionHom, dite_eq_left hi, dite_eq_left hir,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom] using hx

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ComponentRestrictionNaturality
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact restriction identity for a component-preserving geometric inclusion -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic
open scoped ZeroAtInfty

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)]

omit [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem componentRips_commutes (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (r : ℝ) (i : ℕ) :
    letI := separatedMetric o
    letI := separatedMetric p
    ∀ x, mapPoint (componentEmbedding e) he (separatedRipsEmbedding o r i x) =
      separatedRipsEmbedding p r i (mapPoint (e i) (hei i) x) := by
  let := separatedMetric o
  let := separatedMetric p
  intro x
  apply Point.ext
  change (x.weight.embDomain (separatedComponent i)).embDomain (componentEmbedding e) =
    (x.weight.embDomain (e i)).embDomain (separatedComponent i)
  rw [← Finsupp.embDomain_trans_apply, ← Finsupp.embDomain_trans_apply]
  rfl

omit [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem lateRipsFunctionHom_inclusion (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (r : ℝ) (i : ℕ) (hi : r < i) :
    letI := separatedMetric o
    letI := separatedMetric p
    (pullback (embeddingMap (componentEmbedding e) he r)).comp (lateRipsFunctionHom p r i) =
      (lateRipsFunctionHom o r i).comp (inclusionFunctionHom r (e i) (hei i)).toNonUnitalStarAlgHom := by
  let := separatedMetric o
  let := separatedMetric p
  have heq := pullback_zeroExtension
    (separatedRipsEmbedding o r i) (separatedRipsEmbedding_open o r i hi)
    (separatedRipsEmbedding p r i) (separatedRipsEmbedding_open p r i hi)
    (embeddingMap (componentEmbedding e) he r) (embeddingMap (e i) (hei i) r)
    (componentRips_commutes o p e hei he r i)
    (componentRips_preimage o p e r he i)
  ext f x
  have hx := congrArg (fun g : C₀(Point (Sigma Q) r, ℂ) => g x)
    (DFunLike.congr_fun heq (compactFunctionLift f))
  simp only [NonUnitalStarAlgHom.comp_apply] at hx
  have hc : pullback (embeddingMap (e i) (hei i) r) (compactFunctionLift f) =
      compactFunctionLift (inclusionFunctionHom r (e i) (hei i) f) := by
    ext a
    rfl
  rw [hc] at hx
  simpa only [lateRipsFunctionHom, dite_eq_left hi, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.coe_toNonUnitalStarAlgHom] using hx

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedIndexCoarsening
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarsening compatibility of the index on the full analytic domain -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe
open scoped ZeroAtInfty

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
theorem ripsPointCharacter_coarsen (o : ∀ i, Q i) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r ≤ s) (i : ℕ) :
    ripsPointCharacter o s hs i = (ripsPointCharacter o r hr i).comp (scaleFunctionHom hrs) := by
  ext f
  change f (vertex (o i) hs) = f (coarsen hrs (vertex (o i) hr))
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem late_regularizedCycle_coarsen (o : ∀ i, Q i) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r ≤ s) (c : letI := separatedMetric o; OddCycle C₀(Point (Sigma Q) r, ℂ))
    (i : ℕ) (hi : s < i) :
    letI := separatedMetric o
    ((c.precomp (pullback (inclusion hrs))).precomp (lateRipsFunctionHom o s i)).regularize
      (ripsPointCharacter o s hs i) =
    coarsenedCycle hrs ((c.precomp (lateRipsFunctionHom o r i)).regularize
      (ripsPointCharacter o r hr i)) := by
  let := separatedMetric o
  have hp : (c.precomp (pullback (inclusion hrs))).precomp (lateRipsFunctionHom o s i) =
      (c.precomp (lateRipsFunctionHom o r i)).precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom :=
    congrArg (fun η => c.precomp η) (lateRipsFunctionHom_coarsen o hrs i hi)
  rw [hp, ripsPointCharacter_coarsen o hr hs hrs i]
  exact (c.precomp (lateRipsFunctionHom o r i)).regularize_precomp_eq
    (scaleFunctionHom hrs) (ripsPointCharacter o r hr i)

theorem ampleRipsOperator_congr {X : Type} [MetricSpace X] [Fintype X] [DecidableEq X]
    (r : ℝ) (c d : OddCycle C(Point X r, ℂ)) (h : c = d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) :
    ampleRipsOperator r c hc = ampleRipsOperator r d hd := by
  subst d
  rfl

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedIndexNaturality
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
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

omit [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem ripsPointCharacter_included (o : ∀ i, Q i) (p : ∀ i, P i) (hr : 0 ≤ r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (hroot : ∀ i, e i (o i) = p i) (i : ℕ) :
    ripsPointCharacter p r hr i =
      (ripsPointCharacter o r hr i).comp (inclusionFunctionHom r (e i) (hei i)) := by
  ext f
  change f (vertex (p i) hr) = f (mapPoint (e i) (hei i) (vertex (o i) hr))
  rw [mapPoint_vertex, hroot i]

theorem ampleRipsOperator_eq_of_cycle_eq {X : Type} [MetricSpace X] [Fintype X] [DecidableEq X]
    (r : ℝ) (c d : OddCycle C(Point X r, ℂ)) (h : c = d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) :
    ampleRipsOperator r c hc = ampleRipsOperator r d hd := by
  subst d
  rfl

end CoarseAssembly.Rips

end

end OAI
end


