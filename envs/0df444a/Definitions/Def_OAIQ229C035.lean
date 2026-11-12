-- Prove2me | Definitions.Def_OAIQ229C035
-- name    : OAIQ229C035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:16:58.77455+00:00
-- url     : https://prove2.me/theorems/2f8c221b-ab40-498b-9422-71cd4f3ebdef
-- title:
--   Definitions bundle OAIQ229C035 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 6 definitions and 12 theorems. The definitions and types are `OAI.NuclearUltrapower.Elementary.ResidueHilbert`, `OAI.NuclearUltrapower.Elementary.residuePermutation`, `OAI.NuclearUltrapower.Elementary.residueUnitary`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value`, `OAI.NuclearUltrapower.SOS.GoodWord`, `OAI.NuclearUltrapower.SOS.eGenSet`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_BoundedFamilyHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/BoundedFamilyHomotopy.lean), [`CoarseAssembly_RegularizedRipsRelations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RegularizedRipsRelations.lean), [`CoarseAssembly_RipsDirectSumBoundary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsDirectSumBoundary.lean), [`CoarseAssembly_UnrestrictedBoundedHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/UnrestrictedBoundedHomotopy.lean), `NuclearUltrapower_IntegerMatrices`, `NuclearUltrapower_Kazhdan`, `NuclearUltrapower_SOSGap`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C032` and `OAIQ229C033` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ229C037`; the statements `OAI.NuclearUltrapower.SOS.ElementarySpectral.sum_gen_star_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul_ca`, `OAI.NuclearUltrapower.SOS.basis_good_ca`, `OAI.NuclearUltrapower.SOS.delta_good_ca`, `OAI.NuclearUltrapower.SOS.goodWord_inv_ca` and `OAI.NuclearUltrapower.SOS.goodWord_mul_ca`; the proofs of `OAI.NuclearUltrapower.SOS.ElementarySpectral.sum_gen_star_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul_ca`, `OAI.NuclearUltrapower.SOS.basis_good_ca`, `OAI.NuclearUltrapower.SOS.delta_good_ca`, `OAI.NuclearUltrapower.SOS.goodWord_inv_ca` and `OAI.NuclearUltrapower.SOS.goodWord_mul_ca`.
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
import Definitions.Def_OAIQ229C032
import Definitions.Def_OAIQ229C033

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsDirectSumBoundary
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct sums of Fredholm cycles add their whole-union Rips boundaries -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

theorem ripsFamilyBoundaryWithEmbeddings_directSum
    (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c d e : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).IsDirectSum (d i) (e i))
    (hc : ∀ i, (c i).representation 1 = 1) (hd : ∀ i, (d i).representation 1 = 1)
    (he : ∀ i, (e i).representation 1 = 1)
    (hsC : ∀ i, IsSelfAdjoint (c i).operator) (hsD : ∀ i, IsSelfAdjoint (d i).operator)
    (hsE : ∀ i, IsSelfAdjoint (e i).operator)
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hnC : ∀ i, ‖(c i).operator‖ ≤ C) (hnD : ∀ i, ‖(d i).operator‖ ≤ D)
    (hnE : ∀ i, ‖(e i).operator‖ ≤ K)
    (U : ∀ i, (e i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    letI := separatedMetric o
    ripsFamilyBoundaryWithEmbeddings o r hr e he hsE K hK hnE U =
      ripsFamilyBoundaryWithEmbeddings o r hr c hc hsC C hC hnC
        (fun i => (U i).comp (h i).left) +
      ripsFamilyBoundaryWithEmbeddings o r hr d hd hsD D hD hnD
        (fun i => (U i).comp (h i).right) := by
  let := separatedMetric o
  exact coefficientFamilyBoundary_add o
    (fun i => ripsSpatialOperator r (c i) (hc i))
    (fun i => ripsSpatialOperator r (d i) (hd i))
    (fun i => ripsSpatialOperator r (e i) (he i))
    (C + 2) (D + 2) (K + 2) (by linarith) (by linarith) (by linarith)
    (fun i => (ripsSpatialOperator_norm_le r (c i) (hc i)).trans (by linarith [hnC i]))
    (fun i => (ripsSpatialOperator_norm_le r (d i) (hd i)).trans (by linarith [hnD i]))
    (fun i => (ripsSpatialOperator_norm_le r (e i) (he i)).trans (by linarith [hnE i]))
    (r + r) (add_nonneg hr hr)
    (fun i => ripsSpatialOperator_propagation r hr (c i) (hc i))
    (fun i => ripsSpatialOperator_propagation r hr (d i) (hd i))
    (fun i => ripsSpatialOperator_propagation r hr (e i) (he i))
    (fun i => ripsSpatialOperator_selfAdjoint r (c i) (hc i) (hsC i))
    (fun i => ripsSpatialOperator_selfAdjoint r (d i) (hd i) (hsD i))
    (fun i => ripsSpatialOperator_selfAdjoint r (e i) (he i) (hsE i))
    (fun i => ripsSpatialOperator_square_compact r (c i) (hc i) (hsC i))
    (fun i => ripsSpatialOperator_square_compact r (d i) (hd i) (hsD i))
    (fun i => ripsSpatialOperator_square_compact r (e i) (he i) (hsE i))
    (fun i => (h i).left) (fun i => (h i).right)
    (fun i => (h i).orthogonal) (fun i => (h i).exhaustive)
    (fun i => ripsSpatialOperator_directSum_left r (h i) (hc i) (he i))
    (fun i => ripsSpatialOperator_directSum_right r (h i) (hd i) (he i)) U

theorem ampleRipsFamilyBoundary_directSum
    (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c d e : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).IsDirectSum (d i) (e i))
    (hc : ∀ i, (c i).representation 1 = 1) (hd : ∀ i, (d i).representation 1 = 1)
    (he : ∀ i, (e i).representation 1 = 1)
    (hsC : ∀ i, IsSelfAdjoint (c i).operator) (hsD : ∀ i, IsSelfAdjoint (d i).operator)
    (hsE : ∀ i, IsSelfAdjoint (e i).operator)
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hnC : ∀ i, ‖(c i).operator‖ ≤ C) (hnD : ∀ i, ‖(d i).operator‖ ≤ D)
    (hnE : ∀ i, ‖(e i).operator‖ ≤ K) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr e he hsE K hK hnE =
      ampleRipsFamilyBoundary o r hr c hc hsC C hC hnC +
      ampleRipsFamilyBoundary o r hr d hd hsD D hD hnD := by
  let := separatedMetric o
  let U : ∀ i, (e i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 := fun i => ampleIsometry (e i).space
  calc
    _ = ripsFamilyBoundaryWithEmbeddings o r hr e he hsE K hK hnE U :=
      ampleRipsFamilyBoundary_embeddings o r hr e he hsE K hK hnE U
    _ = ripsFamilyBoundaryWithEmbeddings o r hr c hc hsC C hC hnC
          (fun i => (U i).comp (h i).left) +
        ripsFamilyBoundaryWithEmbeddings o r hr d hd hsD D hD hnD
          (fun i => (U i).comp (h i).right) :=
      ripsFamilyBoundaryWithEmbeddings_directSum o r hr c d e h hc hd he hsC hsD hsE
        C D K hC hD hK hnC hnD hnE U
    _ = _ := congrArg₂ (fun x y => x + y)
      (ampleRipsFamilyBoundary_embeddings o r hr c hc hsC C hC hnC _).symm
      (ampleRipsFamilyBoundary_embeddings o r hr d hd hsD D hD hnD _).symm

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedFamilyHomotopy
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded analytic homotopies without uniform continuity assumptions -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable (Q : ℕ → Type) [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] (r : ℝ)

variable {Q r}

namespace BoundedFamilyHomotopy

theorem sample_head_tail_boundary (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval) :
    (h.sample χ (fun i => N i + 1) τ).boundary o hr =
      (h.eval (fun i => τ i 0)).boundary o hr +
      (h.sample χ N (fun i j => τ i (j + 1))).boundary o hr := by
  let := separatedMetric o
  exact ampleRipsFamilyBoundary_directSum o r hr _ _ _
    (fun i => sampledFiniteSum_head_tail (h.homotopy i) (χ i) (N i) (τ i)
      h.bound h.one_le_bound (fun t => h.norm_le t i))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_UnrestrictedBoundedHomotopy
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-union boundary invariance without uniform homotopy speeds

Finite subdivisions are chosen separately on each component. The two sums
of consecutive samples have uniformly close localized operators. Rotation
and direct-sum additivity cancel the common interior samples in actual Roe K₁.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

namespace BoundedFamilyHomotopy

theorem sampled_telescope (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval)
    (hnear : (h.sample χ (fun i => N i + 1) τ).boundary o hr =
      (h.sample χ (fun i => N i + 1) (fun i j => τ i (j + 1))).boundary o hr) :
    (h.eval (fun i => τ i 0)).boundary o hr =
      (h.eval (fun i => τ i (N i + 1))).boundary o hr := by
  let := separatedMetric o
  have hleft := h.sample_head_tail_boundary χ o hr N τ
  have hright := h.sample_head_tail_boundary χ o hr N
    (fun i => lastEndpointFirst (N i) (τ i))
  have hh : (fun i => lastEndpointFirst (N i) (τ i) 0) =
      (fun i => τ i (N i + 1)) := funext (fun i => lastEndpointFirst_zero (N i) (τ i))
  have ht : (fun i j => lastEndpointFirst (N i) (τ i) (j + 1)) =
      (fun i j => τ i (j + 1)) := funext (fun i => funext (fun j => lastEndpointFirst_succ (N i) (τ i) j))
  have hh' := congrArg (fun t : ℕ → Interval => (h.eval t).boundary o hr) hh
  have ht' := congrArg (fun t : ℕ → ℕ → Interval => (h.sample χ N t).boundary o hr) ht
  have hright' := hright.trans (congrArg₂ (fun a b => a + b) hh' ht')
  have hrotate := h.sample_rotate_boundary χ o hr N τ
  exact add_right_cancel (hleft.symm.trans (hnear.trans (hrotate.symm.trans hright')))

theorem endpoint_boundary_eq (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (h.eval (fun _ => start)).boundary o hr = (h.eval (fun _ => finish)).boundary o hr := by
  let s := h.smallSubdivision
  have he := h.sampled_telescope χ o hr s.count s.time
    (h.sampled_boundary_eq χ o hr s.count s.time s.step)
  have h0 : (fun i => s.time i 0) = (fun _ => start) := funext s.at_start
  have h1 : (fun i => s.time i (s.count i + 1)) = (fun _ => finish) := funext s.at_finish
  have he0 := congrArg (fun t : ℕ → Interval => (h.eval t).boundary o hr) h0
  have he1 := congrArg (fun t : ℕ → Interval => (h.eval t).boundary o hr) h1
  exact he0.symm.trans (he.trans he1)

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

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

theorem regularizedFamily_unitary
    (c d : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).UnitaryEquivalent (d i))
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ) (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (regularizedFamily c χ).boundary o hr = (regularizedFamily d χ).boundary o hr := by
  let := separatedMetric o
  let C := regularizedFamily c χ
  let D := regularizedFamily d χ
  exact ampleRipsFamilyBoundary_unitary o r hr C.cycle D.cycle
    (fun i => (h i).regularize (χ i)) C.unital D.unital C.selfAdjoint D.selfAdjoint
    C.bound D.bound C.bound_nonneg D.bound_nonneg C.norm_le D.norm_le

theorem regularizedFamily_directSum
    (c d e : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).IsDirectSum (d i) (e i))
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ) (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (regularizedFamily e χ).boundary o hr =
      (regularizedFamily c χ).boundary o hr + (regularizedFamily d χ).boundary o hr := by
  let := separatedMetric o
  let C := regularizedFamily c χ
  let D := regularizedFamily d χ
  let E := regularizedFamily e χ
  exact ampleRipsFamilyBoundary_directSum o r hr C.cycle D.cycle E.cycle
    (fun i => (h i).regularize (χ i)) C.unital D.unital E.unital
    C.selfAdjoint D.selfAdjoint E.selfAdjoint C.bound D.bound E.bound
    C.bound_nonneg D.bound_nonneg E.bound_nonneg C.norm_le D.norm_le E.norm_le

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

def GoodWord (n : ℕ) (m : Mat3) : Prop :=
  (toMatrix m).det = 1 ∧ ∃ w : List SL, w.prod = interpret m ∧ w.length ≤ n ∧
    ∀ s ∈ w, s ∈ genSet

end NuclearUltrapower.SOS
end
end

section

noncomputable section
namespace NuclearUltrapower.SOS

def eGenSet : Finset E := (generators.map eInterpret).toFinset

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

section Algebra
variable {A : Type*} [CStarAlgebra A]

def value (ρ : E →* unitary A) (m : Mat3) : A := ρ (eInterpret m)

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_Kazhdan
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary

theorem residue_mul (g h : IntegralGroup) :
    residue (g * h) = residue g + residueMatrix g.right (residue h) := by
  funext i
  simp [residue, integralAction, residueMatrix, Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.mulVec, dotProduct]

@[simp] theorem residue_one : residue 1 = 0 := by ext; simp [residue]

@[simp] theorem residue_theta (g : IntegralGroup) : residue (integralTheta g) = 0 := by
  ext i
  change ((2 * g.left.toAdd i : ℤ) : ZMod 2) = 0
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  simp [htwo]

/-- Reduction modulo two, acting by affine permutations on its eight points. -/
def residuePermutation : IntegralGroup →* Equiv.Perm Residue3 where
  toFun g := (residueMatrix g.right).toEquiv.trans (Equiv.addLeft (residue g))
  map_one' := by
    ext x i
    simp [residueMatrix]
  map_mul' g h := by
    ext x i
    change (residue (g * h) + residueMatrix (g * h).right x) i =
      (residue g + residueMatrix g.right (residue h + residueMatrix h.right x)) i
    rw [residue_mul, map_add]
    simp [residueMatrix, map_mul, add_assoc]

@[simp] theorem residuePermutation_apply (g : IntegralGroup) (x : Residue3) :
    residuePermutation g x = residue g + residueMatrix g.right x := rfl

abbrev ResidueHilbert := EuclideanSpace ℂ Residue3

def residueUnitary : IntegralGroup →* (ResidueHilbert ≃ₗᵢ[ℂ] ResidueHilbert) where
  toFun g := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (residuePermutation g)
  map_one' := by
    ext f x
    change f ((residuePermutation 1).symm x) = f x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext f x
    change f ((residuePermutation (g * h)).symm x) =
      f ((residuePermutation h).symm ((residuePermutation g).symm x))
    rw [map_mul]
    rfl

@[simp] theorem residueUnitary_apply (g : IntegralGroup) (f : ResidueHilbert) (x : Residue3) :
    residueUnitary g f x = f ((residuePermutation g).symm x) := rfl

end NuclearUltrapower.Elementary
end
end

end OAI
end


