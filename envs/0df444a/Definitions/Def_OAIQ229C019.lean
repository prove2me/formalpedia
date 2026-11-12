-- Prove2me | Definitions.Def_OAIQ229C019
-- name    : OAIQ229C019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T08:27:18.201806+00:00
-- url     : https://prove2.me/theorems/32cab6b7-6509-487b-816b-8ffb8ebbe283
-- title:
--   Definitions bundle OAIQ229C019 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 14 definitions, 3 inductive types or structures and 23 theorems. The definitions and types are `OAI.CoarseAssembly.PublishedBoundaryAssemblyInput`, `OAI.CoarseAssembly.PublishedKazhdanInput`, `OAI.CoarseAssembly.Rips.BoundedFamilyHomotopy`, `OAI.CoarseAssembly.Rips.BoundedFamilyHomotopy.SmallSubdivision`, `OAI.CoarseAssembly.Rips.BoundedFamilyHomotopy.eval`, `OAI.CoarseAssembly.Rips.BoundedFamilyHomotopy.samplingTolerance`, `OAI.CoarseAssembly.Rips.BoundedFamilyHomotopy.smallSubdivision`, `OAI.CoarseAssembly.Rips.ControlledCycleFamily.coarsen`, `OAI.CoarseAssembly.Rips.coarsenedCycle`, `OAI.CoarseAssembly.Rips.scalarHilbert`, `OAI.CoarseAssembly.UniformAveragingGap`, `OAI.CoarseAssembly.boundaryBaseCoarsening`, `OAI.CoarseAssembly.boundaryBaseRoeHom`, `OAI.CoarseAssembly.constantProjection`, `OAI.CoarseAssembly.lazyAverage`, `OAI.CoarseAssembly.leftTranslation`, `OAI.CoarseAssembly.meanTranslation`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_Averaging`, `CoarseAssembly_BlockOperators`, `CoarseAssembly_BoundaryAssemblyMaps`, `CoarseAssembly_BoundaryGeometry`, `CoarseAssembly_BoundedFamilyHomotopy`, `CoarseAssembly_BoundedFamilySubdivision`, `CoarseAssembly_ConcreteSpaces`, `CoarseAssembly_ControlledRipsCoarsening`, `CoarseAssembly_FiberConnected`, `CoarseAssembly_GraphFiberOperators`, `CoarseAssembly_HomotopySubdivision`, `CoarseAssembly_KazhdanInput`, `CoarseAssembly_PathFiberOperators`, `CoarseAssembly_RipsFiniteTail`, `CoarseAssembly_RipsLocalization`, `CoarseAssembly_RipsScaleCompatibility`, `CoarseAssembly_SeparatedBoundaryCongruence`, `CoarseAssembly_SpatialAveraging`, `CoarseAssembly_TensorFibers`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C009`, `OAIQ229C010` and `OAIQ229C011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C024`, `OAIQ229C025`, `OAIQ229C026` and `OAIQ229C027`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
import Mathlib.LinearAlgebra.Isomorphisms
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
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C009
import Definitions.Def_OAIQ229C010
import Definitions.Def_OAIQ229C011

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockOperators
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform block operators on Hilbert sums

The averaging operators used in the transfer act separately on finite
fibers. A uniform norm bound, rather than finiteness of the set of fibers,
makes their direct sum a bounded operator. The resulting operator admits the uniform approximation needed for the
fiber projection.
-/

noncomputable section

namespace CoarseAssembly

open Filter
open scoped Topology

variable {ι : Type*} {E F : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]

theorem power_mul_fixed {R : Type*} [Monoid R] (M P : R) (hMP : M * P = P) (n : ℕ) :
    M ^ n * P = P := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, hMP, ih]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite-quotient averaging operators

Normalized left translations and their lazy average act on the spatial
fiber Hilbert spaces. They are contractions fixing the constant subspace.
The strict norm bound off constants is kept as the precise published
Kazhdan-gap input, rather than assuming any Roe transfer conclusion.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (Q : Type*) [Fintype Q] [Nonempty Q]

def constantProjection : lp (fun _ : Q => H) 2 →L[ℂ] lp (fun _ : Q => H) 2 :=
  (fiberConstantIsometry Q).toContinuousLinearMap.comp
    (fiberConstantIsometry Q).toContinuousLinearMap.adjoint

variable [Group Q]

def leftTranslation (g : Q) : lp (fun _ : Q => H) 2 ≃ₗᵢ[ℂ] lp (fun _ : Q => H) 2 :=
  reindexFiber (Equiv.mulLeft g)

variable (S : Finset ArithmeticGroup)

def meanTranslation (k : ℕ) :
    lp (fun _ : Quotient k => H) 2 →L[ℂ] lp (fun _ : Quotient k => H) 2 :=
  ((S.card : ℂ)⁻¹) • ∑ s ∈ S, (leftTranslation (Quotient k) (reduce k s)).toLinearIsometry.toContinuousLinearMap

def lazyAverage (k : ℕ) :
    lp (fun _ : Quotient k => H) 2 →L[ℂ] lp (fun _ : Quotient k => H) 2 :=
  (1 / 2 : ℂ) • (1 + meanTranslation S k)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_GraphFiberOperators
attribute [-instance] _root_.OAI.CoarseAssembly.discGraphMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled transport along the base graph

The three depth cases give actual contractions on the finite scalar Hilbert
spaces. Their nonzero coefficients are supported on edges of the constructed
fibered graph, not on an assumed transport relation.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

/-- Transport between adjacent depths, with its exact reduced support. -/
theorem exists_depth_operator (t : ℤ_[2]ˣ) (k l : ℕ) (a : ℤ)
    (hkl : |(k : ℤ) - (l : ℤ)| ≤ 1) :
    ∃ O : lp (fun _ : Quotient k => ℂ) 2 →L[ℂ] lp (fun _ : Quotient l => ℂ) 2,
      ‖O‖ ≤ 1 ∧ O (fiberConstant (Quotient k) (1 : ℂ)) =
        fiberConstant (Quotient l) 1 ∧
      ∀ q z, O (lp.single 2 q 1) z ≠ 0 →
        ∀ m (hm : m ≤ k) (hl : m ≤ l),
          quotientMap hl z = quotientMap hm q * holonomy t m ^ a := by
  have hcases : k = l ∨ l = k + 1 ∨ k = l + 1 := by
    rw [abs_le] at hkl
    omega
  rcases hcases with rfl | rfl | rfl
  · refine ⟨(sameLevelIsometry t k a).toLinearIsometry.toContinuousLinearMap,
      isometry_norm_le_one _, sameLevelIsometry_constant t k a, ?_⟩
    intro q z hn m hm hl
    have he : z = q * holonomy t k ^ a := by
      by_contra he
      exact hn (sameLevelIsometry_support t k a q z he)
    rw [he, map_mul, map_zpow, quotientMap_holonomy]
  · refine ⟨(childIsometry t k a).toContinuousLinearMap,
      isometry_norm_le_one _, childIsometry_constant t k a, ?_⟩
    intro q z hn m hm hl
    have he : quotientMap (Nat.le_succ k) z = q * holonomy t k ^ a := by
      by_contra he
      exact hn (childIsometry_support t k a q z he)
    have hr := congrArg (quotientMap hm) he
    simpa only [map_mul, map_zpow, quotientMap_holonomy, quotientMap_comp] using hr
  · refine ⟨(childIsometry t l (-a)).toContinuousLinearMap.adjoint, ?_,
      childAdjoint_constant t l (-a), ?_⟩
    · rw [LinearIsometryEquiv.norm_map]
      exact isometry_norm_le_one _
    · intro q z hn m hm hl
      have he : quotientMap (Nat.le_succ l) q = z * holonomy t l ^ (-a) := by
        by_contra he
        exact hn (childAdjoint_support t l (-a) z q he)
      have hz : z = quotientMap (Nat.le_succ l) q * holonomy t l ^ a := by
        rw [he, zpow_neg]
        group
      have hr := congrArg (quotientMap hl) hz
      simpa only [map_mul, map_zpow, quotientMap_holonomy, quotientMap_comp] using hr

/-- Each base edge has a contraction preserving constants, whose matrix
coefficients are supported on actual edges upstairs. -/
theorem exists_base_edge_operator (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} {u v : Disc j} (huv : (discGraph j).Adj u v) :
    ∃ O : lp (fun _ : Quotient (discDepth j u) => ℂ) 2 →L[ℂ]
        lp (fun _ : Quotient (discDepth j v) => ℂ) 2,
      ‖O‖ ≤ 1 ∧ O (fiberConstant (Quotient (discDepth j u)) (1 : ℂ)) =
        fiberConstant (Quotient (discDepth j v)) 1 ∧
      ∀ q z, ¬(fiberedGraph S t j).Adj ⟨u, q⟩ ⟨v, z⟩ →
        O (lp.single 2 q 1) z = 0 := by
  obtain ⟨O, hnorm, hconst, hsupp⟩ := exists_depth_operator t
    (discDepth j u) (discDepth j v) (latticeCharge u.val v.val) (discDepth_adj huv)
  refine ⟨O, hnorm, hconst, ?_⟩
  intro q z hnot
  by_contra hn
  apply hnot
  refine ⟨?_, 1, one_mem_symmetricMoves S, Or.inr ⟨huv, rfl⟩, ?_⟩
  · intro heq
    have huv' := congrArg (fun x : FiberVertex j => x.1.val) heq
    exact huv.2.2.2 huv'
  · intro m hm hl
    simpa only [fiberCoordinate, fiberCharge, map_one, one_mul] using hsupp q z hn m hm hl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PathFiberOperators
attribute [-instance] _root_.OAI.CoarseAssembly.discGraphMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composing the concrete fiber transports

Every base walk gives a contraction preserving normalized constants.
A nonzero matrix coefficient comes with an actual lifted walk of the same
length, which is the propagation estimate needed by the transfer criterion.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

/-- The concrete edge maps compose without any loss in the propagation
bound. This includes the length-zero identity case. -/
theorem exists_base_walk_operator (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} {u v : Disc j} (p : (discGraph j).Walk u v) :
    ∃ O : lp (fun _ : Quotient (discDepth j u) => ℂ) 2 →L[ℂ]
        lp (fun _ : Quotient (discDepth j v) => ℂ) 2,
      ‖O‖ ≤ 1 ∧ O (fiberConstant (Quotient (discDepth j u)) (1 : ℂ)) =
        fiberConstant (Quotient (discDepth j v)) 1 ∧
      ∀ q z, O (lp.single 2 q 1) z ≠ 0 →
        ∃ w : (fiberedGraph S t j).Walk ⟨u, q⟩ ⟨v, z⟩, w.length = p.length := by
  classical
  induction p with
  | @nil u =>
    refine ⟨ContinuousLinearMap.id ℂ _, ContinuousLinearMap.norm_id_le, rfl, ?_⟩
    intro q z hn
    have hz : z = q := by
      by_contra hne
      apply hn
      exact lp.single_apply_ne 2 q 1 hne
    subst z
    exact ⟨.nil, rfl⟩
  | @cons u v w huv p ih =>
    obtain ⟨A, hA, hAc, hAs⟩ := exists_base_edge_operator S t huv
    obtain ⟨B, hB, hBc, hBs⟩ := ih
    refine ⟨B.comp A, ?_, ?_, ?_⟩
    · exact (ContinuousLinearMap.opNorm_comp_le B A).trans
        ((mul_le_mul hB hA (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))
    · rw [ContinuousLinearMap.comp_apply, hAc, hBc]
    · intro q z hn
      obtain ⟨r, hAr, hBr⟩ := scalarFiber_comp_nonzero A B q z hn
      have he : (fiberedGraph S t j).Adj ⟨u, q⟩ ⟨v, r⟩ := by
        by_contra he
        exact hAr (hAs q r he)
      obtain ⟨p', hp'⟩ := hBs r z hBr
      exact ⟨.cons he p', by simp only [SimpleGraph.Walk.length_cons, hp']⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberConnected
attribute [-instance] _root_.OAI.CoarseAssembly.discGraphMetric
attribute [-simp] _root_.OAI.CoarseAssembly.discHatWeights_apply _root_.OAI.CoarseAssembly.mem_baseNeighbors _root_.OAI.CoarseAssembly.mem_fiberedNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connectivity of the finite fibered graphs

Transport from a singleton boundary fiber reaches every vertex: its image
is the normalized constant vector, which has no zero coordinate. Thus
connectivity does not require an additional Cayley-generation assumption.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem constant_coordinate_ne_zero (k : ℕ) (q : Quotient k) :
    fiberConstant (Quotient k) (1 : ℂ) q ≠ 0 := by
  have hc : (0 : ℝ) < Fintype.card (Quotient k) := by exact_mod_cast Fintype.card_pos
  have hn : fiberNormalization (Quotient k) ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hc))
  simpa only [fiberConstant_apply, smul_eq_mul, mul_one, ne_eq, Complex.ofReal_eq_zero] using hn

theorem fiberBoundary_reaches (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x : FiberVertex j) :
    (fiberedGraph S t j).Reachable (fiberBoundaryBase j) x := by
  classical
  have hsub : Subsingleton (Quotient (discDepth j (discBoundaryBase j))) := by
    rw [discBoundaryBase_depth]
    infer_instance
  let : Unique (Quotient (discDepth j (discBoundaryBase j))) :=
    ⟨⟨1⟩, fun q => hsub.elim q 1⟩
  have hc : fiberConstant (Quotient (discDepth j (discBoundaryBase j))) (1 : ℂ) =
      lp.single 2 1 1 := by
    apply lp.ext
    funext q
    simp [fiberConstant_apply, lp.single_apply, hsub.elim q 1]
  obtain ⟨p⟩ := discGraph_connected j (discBoundaryBase j) x.1
  obtain ⟨O, hnorm, hconst, hsupp⟩ := exists_base_walk_operator S t p
  have hn : O (lp.single 2 1 1) x.2 ≠ 0 := by
    rw [← hc, hconst]
    exact constant_coordinate_ne_zero _ _
  obtain ⟨w, hw⟩ := hsupp 1 x.2 hn
  exact ⟨w⟩

theorem fiberedGraph_connected (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) :
    (fiberedGraph S t j).Connected where
  preconnected x y :=
    (fiberBoundary_reaches S t x).symm.trans (fiberBoundary_reaches S t y)
  nonempty := ⟨fiberBoundaryBase j⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TensorFibers
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.CoarseAssembly.fiberEmbedding_apply _root_.OAI.CoarseAssembly.quotientCopy_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Amplifying finite-fiber operators

The algebraic Hilbert tensor product of a finite scalar fiber with the
coefficient Hilbert space is isometrically the fiber's vector-valued ℓ²
space. This gives the norm-controlled amplification used in each transfer
block, using Mathlib's Hilbert tensor-product operator norm theorem.
-/

noncomputable section

namespace CoarseAssembly

open scoped TensorProduct

variable {Q R H : Type*} [Fintype Q] [Fintype R]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [DecidableEq Q]

theorem fiberTensor_constant (h : H) :
    fiberTensorEquiv (fiberConstant Q (1 : ℂ) ⊗ₜ[ℂ] h) = fiberConstant Q h := by
  apply lp.ext
  funext q
  simp [fiberTensorMap_tmul_apply, fiberConstant_apply]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual base and fibered coarse unions

Both metrics restrict to shortest-path metrics on the components. The
fibered union is indexed by base vertices so its Hilbert module has exactly
the form used by the finite-fiber transfer theorem.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem componentMetric_eq (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) :
    componentMetric S t j = connectedGraphMetric (fiberedGraph S t j) (fiberedGraph_connected S t j) :=
  graphMetricOrDiscrete_eq _ _

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete proper boundary inclusions

The boundary is the depth-zero vertex subset with the induced metric from
the total graph family. Its projection to the base is nonexpanding. These
are the actual two vertex inclusions used for assembly naturality.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic DiscreteRoe

theorem fiberProjection_nonexpanding (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (j : ℕ) (x y : FiberVertex j) :
    dist x.1 y.1 ≤ @dist _ (componentMetric S t j).toDist x y := by
  obtain ⟨p, hp⟩ := (fiberedGraph_connected S t j).exists_walk_length_eq_dist x y
  rw [componentMetric_eq]
  change dist x.1 y.1 ≤ ((fiberedGraph S t j).dist x y : ℝ)
  rw [← hp]
  apply walk_image_dist_le (fiberedGraph S t j) (fun z => z.1)
  intro u v h
  obtain ⟨s, hs, hp, _⟩ := h.2
  rcases hp with hsame | ⟨hadj, _⟩
  · simp [hsame]
  · exact discEdgeBound u.1 v.1 hadj

theorem vertexProjection_nonexpanding (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (x y : VertexUnion) :
    dist x.1 y.1 ≤ @dist _ (vertexUnionMetric S t).toDist x y := by
  let := componentMetric S t
  rcases x with ⟨⟨i, u⟩, q⟩
  rcases y with ⟨⟨j, v⟩, z⟩
  change separatedDist discBoundaryBase ⟨i, u⟩ ⟨j, v⟩ ≤
    separatedDist fiberBoundaryBase ⟨i, ⟨u, q⟩⟩ ⟨j, ⟨v, z⟩⟩
  by_cases hij : i = j
  · subst j
    simp only [separatedDist_same]
    exact fiberProjection_nonexpanding S t i ⟨u, q⟩ ⟨v, z⟩
  · rw [separatedDist_different discBoundaryBase hij,
      separatedDist_different fiberBoundaryBase hij]
    exact add_le_add
      (add_le_add (fiberProjection_nonexpanding S t i ⟨u, q⟩ (fiberBoundaryBase i)) le_rfl)
      (fiberProjection_nonexpanding S t j (fiberBoundaryBase j) ⟨v, z⟩)

theorem boundaryToBase_nonexpanding (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    ∀ x y, dist (boundaryToBase x) (boundaryToBase y) ≤
      @dist BoundaryVertex (boundaryMetric S t).toDist x y :=
  fun x y => vertexProjection_nonexpanding S t (boundaryToVertex x) (boundaryToVertex y)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SpatialAveraging
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

/-- The precise uniform operator consequence of the Kazhdan estimate for
the chosen generators, on the coefficient Hilbert space used by the Roe
module. For the standard generators this is the specialization of BHV,
Proposition 1.3.2 and Example 1.7.4, described in manuscript §5.2. -/
def UniformAveragingGap (S : Finset ArithmeticGroup) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ k,
    ‖lazyAverage (H := H) S k - constantProjection (H := H) (Quotient k)‖ ≤ c

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_KazhdanInput
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

def PublishedKazhdanInput : Prop := UniformAveragingGap elementaryMoves AmpleSpace

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryAssemblyMaps
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

local instance boundaryAssemblyMetric2_r7811c7_1 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.boundaryAssemblyMetric3
def boundaryBaseCoarsening : CoarseningMorphism (Rips.coarsening BoundaryVertex)
    (Rips.coarsening BaseUnion) :=
  Rips.embeddingCoarsening boundaryToBase
    (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)

def boundaryBaseRoeHom : BoundaryRoe →⋆ₙₐ[ℂ] BaseRoe :=
  inclusionHom (X := BoundaryVertex) (Y := BaseUnion) (H := AmpleSpace)
    boundaryToBase (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)

/-- The exact published index/naturality specializations used here:
Willett--Yu, *Higher Index Theory* (2020), §§5.1, 6.7, 7.1--7.2,
with errata 30--31. The objects and both geometric/Roe maps are fixed above.
There is no transfer-naturality premise. -/
structure PublishedBoundaryAssemblyInput where
  boundary : CompatibleIndexFamily (Rips.coarsening BoundaryVertex) BoundaryRoe
  base : CompatibleIndexFamily (Rips.coarsening BaseUnion) BaseRoe
  total : CompatibleIndexFamily (Rips.coarsening VertexUnion) TotalRoe
  natural_base : ∀ r, (base.atScale r).comp (pushforward (boundaryBaseCoarsening.atScale r)) =
    (OperatorKTheory.map boundaryBaseRoeHom).comp (boundary.atScale r)
  natural_total : ∀ r, (total.atScale r).comp (pushforward (boundaryTotalCoarsening.atScale r)) =
    (OperatorKTheory.map boundaryTotalRoeHom).comp (boundary.atScale r)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsLocalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The spatial localization of a unital finite-Rips Fredholm cycle -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)

omit [DecidableEq X] in
theorem representedSqrt_adjoint (c : OddCycle C(Point X r, ℂ)) (x : X) :
    (representedSqrt r c x).adjoint = representedSqrt r c x := by
  exact ((sqrtCoordinate_selfAdjoint r x).map c.representation).star_eq

omit [DecidableEq X] in
theorem representedSqrt_partition (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) :
    ∑ x, (representedSqrt r c x).adjoint.comp (representedSqrt r c x) = 1 := by
  simp only [representedSqrt_adjoint]
  change (∑ x, c.representation (sqrtCoordinate r x) *
    c.representation (sqrtCoordinate r x)) = 1
  simp only [← map_mul, ← map_sum, sqrtCoordinate_square_sum, hπ]

omit [DecidableEq X] in
theorem representedSqrt_disjoint (c : OddCycle C(Point X r, ℂ))
    (x y : X) (hxy : r < dist x y) :
    representedSqrt r c x * representedSqrt r c y = 0 := by
  change c.representation (sqrtCoordinate r x) * c.representation (sqrtCoordinate r y) = 0
  rw [← map_mul, sqrtCoordinate_mul_eq_zero r x y hxy, map_zero]

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedBoundaryCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A boundary class does not depend on its norm or propagation certificate -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_bound_independent (o : ∀ i, Q i)
    (A : ∀ i, Operator (Q i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖A i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (A i))
    (hself : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) H))) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hself hsq =
      separatedFamilyBoundary o A D hD hB s hs hq hself hsq := by
  let := separatedMetric o
  have he : separatedFamilyMultiplier o A C hC hA r hr hp =
      separatedFamilyMultiplier o A D hD hB s hs hq := by
    apply Subtype.ext
    ext v p
    rcases p with ⟨i, x⟩
    rfl
  unfold separatedFamilyBoundary
  simp only [he]

theorem separatedFamilyBoundary_congr (o : ∀ i, Q i)
    (A B : ∀ i, Operator (Q i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hselfA : ∀ i, IsSelfAdjoint (A i)) (hselfB : ∀ i, IsSelfAdjoint (B i))
    (hsqA : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) H)))
    (hsqB : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (Q i) H)))
    (hAB : A = B) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hselfA hsqA =
      separatedFamilyBoundary o B D hD hB s hs hq hselfB hsqB := by
  subst B
  exact separatedFamilyBoundary_bound_independent o A C D hC hD hA hB r s hr hs hp hq hselfA hsqA

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedFamilyHomotopy
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
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

structure BoundedFamilyHomotopy where
  homotopy : ∀ i, OddHomotopy C(Point (Q i) r, ℂ)
  unital : ∀ t i, (homotopy i).representation t 1 = 1
  selfAdjoint : ∀ t i, IsSelfAdjoint ((homotopy i).operator t)
  bound : ℝ
  one_le_bound : 1 ≤ bound
  norm_le : ∀ t i, ‖(homotopy i).operator t‖ ≤ bound

variable {Q r}

namespace BoundedFamilyHomotopy

def eval (h : BoundedFamilyHomotopy Q r) (τ : ℕ → Interval) : ControlledCycleFamily Q r where
  cycle i := (h.homotopy i).eval (τ i)
  unital i := h.unital (τ i) i
  selfAdjoint i := h.selfAdjoint (τ i) i
  bound := h.bound
  bound_nonneg := zero_le_one.trans h.one_le_bound
  norm_le i := h.norm_le (τ i) i

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HomotopySubdivision
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous finite subdivision of the operator and partition coordinates -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {X : Type} [PseudoMetricSpace X] [Fintype X]

theorem exists_rips_homotopy_subdivision (r : ℝ) (h : OddHomotopy C(Point X r, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ j, j < N →
      ‖h.operator (intervalGrid N hN (j + 1)) - h.operator (intervalGrid N hN j)‖ ≤ ε ∧
      ∀ x, ‖h.representation (intervalGrid N hN (j + 1)) (sqrtCoordinate r x) -
        h.representation (intervalGrid N hN j) (sqrtCoordinate r x)‖ ≤ ε := by
  let f : Interval → End h.space × (X → End h.space) :=
    fun t => (h.operator t, fun x => h.representation t (sqrtCoordinate r x))
  have hf : Continuous f := h.continuous_operator.prodMk
    (continuous_pi (fun x => h.continuous_representation (sqrtCoordinate r x)))
  obtain ⟨N, hN, hstep⟩ := exists_interval_subdivision f hf ε hε
  refine ⟨N, hN, fun j hj => ?_⟩
  have he : ‖f (intervalGrid N hN (j + 1)) - f (intervalGrid N hN j)‖ ≤ ε := by
    simpa only [dist_eq_norm] using (hstep j hj).le
  refine ⟨(norm_fst_le _).trans he, fun x => ?_⟩
  exact (norm_le_pi_norm _ x).trans ((norm_snd_le _).trans he)

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedFamilySubdivision
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Component-dependent subdivisions with uniformly close sampled Roe operators -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

namespace BoundedFamilyHomotopy

def samplingTolerance (h : BoundedFamilyHomotopy Q r) (i : ℕ) : ℝ :=
  1 / (8 * (1 + (4 * h.bound + 2) * Fintype.card (Q i)))

omit [∀ i, DecidableEq (Q i)] in
theorem samplingTolerance_pos (h : BoundedFamilyHomotopy Q r) (i : ℕ) :
    0 < h.samplingTolerance i := by
  have hb : 0 ≤ h.bound := zero_le_one.trans h.one_le_bound
  unfold samplingTolerance
  positivity

omit [∀ i, DecidableEq (Q i)] in
theorem samplingTolerance_estimate (h : BoundedFamilyHomotopy Q r) (i : ℕ) :
    h.samplingTolerance i + (4 * h.bound + 2) *
      ((Fintype.card (Q i) : ℝ) * h.samplingTolerance i) = 1 / 8 := by
  have hb : 0 ≤ h.bound := zero_le_one.trans h.one_le_bound
  have hd : 0 < 1 + (4 * h.bound + 2) * (Fintype.card (Q i) : ℝ) := by positivity
  unfold samplingTolerance
  field_simp

omit [∀ i, DecidableEq (Q i)] in
theorem exists_small_subdivision (h : BoundedFamilyHomotopy Q r) :
    ∃ (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval),
      (∀ i, τ i 0 = start) ∧ (∀ i, τ i (N i + 1) = finish) ∧
      ∀ i j, j < N i + 1 →
        ‖(h.homotopy i).operator (τ i (j + 1)) - (h.homotopy i).operator (τ i j)‖ ≤
          h.samplingTolerance i ∧
        ∀ x, ‖(h.homotopy i).representation (τ i (j + 1)) (sqrtCoordinate r x) -
          (h.homotopy i).representation (τ i j) (sqrtCoordinate r x)‖ ≤ h.samplingTolerance i := by
  choose K hK hstep using fun i => exists_rips_homotopy_subdivision r (h.homotopy i)
    (h.samplingTolerance i) (h.samplingTolerance_pos i)
  refine ⟨(fun i => K i - 1), (fun i => intervalGrid (K i) (hK i)), ?_, ?_, ?_⟩
  · intro i
    exact intervalGrid_start _ _
  · intro i
    have hk := hK i
    have hi : K i - 1 + 1 = K i := by omega
    dsimp only
    rw [hi]
    exact intervalGrid_finish _ _
  · intro i j hj
    apply hstep i j
    dsimp only at hj
    have hk := hK i
    omega

structure SmallSubdivision (h : BoundedFamilyHomotopy Q r) where
  count : ℕ → ℕ
  time : ℕ → ℕ → Interval
  at_start : ∀ i, time i 0 = start
  at_finish : ∀ i, time i (count i + 1) = finish
  step : ∀ i j, j < count i + 1 →
    ‖(h.homotopy i).operator (time i (j + 1)) - (h.homotopy i).operator (time i j)‖ ≤
      h.samplingTolerance i ∧
    ∀ x, ‖(h.homotopy i).representation (time i (j + 1)) (sqrtCoordinate r x) -
      (h.homotopy i).representation (time i j) (sqrtCoordinate r x)‖ ≤ h.samplingTolerance i

def smallSubdivision (h : BoundedFamilyHomotopy Q r) : SmallSubdivision h := by
  let N := Classical.choose h.exists_small_subdivision
  have hN := Classical.choose_spec h.exists_small_subdivision
  let τ := Classical.choose hN
  have ht := Classical.choose_spec hN
  exact ⟨N, τ, ht.1, ht.2.1, ht.2.2⟩

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsScaleCompatibility
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Increasing-scale compatibility of the explicit Rips representatives

The barycentric coordinate functions pull back identically under increasing
the Rips scale. Consequently the localized operators themselves agree,
before taking a K-theory class.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X]
  {r s : ℝ} (hrs : r ≤ s)

def coarsenedCycle (c : OddCycle C(Point X r, ℂ)) : OddCycle C(Point X s, ℂ) :=
  c.precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom

theorem coarsenedCycle_unital (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) : (coarsenedCycle hrs c).representation 1 = 1 := by
  change c.representation (scaleFunctionHom hrs 1) = 1
  rw [map_one, hπ]

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ControlledRipsCoarsening
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarsening and the constructed controlled assembly homomorphism -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

def ControlledCycleFamily.coarsen (hrs : r ≤ s) (c : ControlledCycleFamily Q r) :
    ControlledCycleFamily Q s where
  cycle i := coarsenedCycle hrs (c.cycle i)
  unital i := coarsenedCycle_unital hrs (c.cycle i) (c.unital i)
  selfAdjoint := c.selfAdjoint
  bound := c.bound
  bound_nonneg := c.bound_nonneg
  norm_le := c.norm_le

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsFiniteTail
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-tail invariance for the analytic Rips boundary -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

abbrev scalarHilbert : HilbertSpace where
  Carrier := ℂ
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

local instance instSecondCountableTopologySubtypePreLpNatComplexMemAddSubgroupLpOfNatENNReal_solutions : SecondCountableTopology (lp (fun _ : ℕ => ℂ) 2) :=
  hilbertSum_secondCountable (fun _ => scalarHilbert)

end CoarseAssembly.Rips

end

end OAI
end


