-- Prove2me | Definitions.Def_OAIQ229C003
-- name    : OAIQ229C003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T02:51:00.884661+00:00
-- url     : https://prove2.me/theorems/b06a154d-0735-448f-b9e1-d88fca4a1315
-- title:
--   Definitions bundle OAIQ229C003 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 412 declarations of OpenAI's Lean: 394 definitions and 18 theorems. The definitions and types are `OAI.CoarseAssembly.componentPrefix`, `OAI.CoarseAssembly.concreteDiagramTotalMetric`, `OAI.CoarseAssembly.diagonalTrace`, `OAI.CoarseAssembly.fiberBlockEntry`, `OAI.CoarseAssembly.fiberTensorBilinear`, `OAI.CoarseAssembly.fiberTensorMap`, `OAI.CoarseAssembly.latticeNeighbors`, `OAI.CoarseAssembly.walkBall`, `OAI.NuclearUltrapower.IntegralVector3`, `OAI.NuclearUltrapower.SOS.Mat3`, `OAI.NuclearUltrapower.SOS.Poly`, `OAI.NuclearUltrapower.SOS.SL`, `OAI.NuclearUltrapower.SOS.entry`, `OAI.NuclearUltrapower.SOS.eval`, `OAI.NuclearUltrapower.SOS.generators`, `OAI.NuclearUltrapower.SOS.interpret`, `OAI.NuclearUltrapower.SOS.label1`, `OAI.NuclearUltrapower.SOS.label100`, `OAI.NuclearUltrapower.SOS.label101`, `OAI.NuclearUltrapower.SOS.label1010`, `OAI.NuclearUltrapower.SOS.label1012`, `OAI.NuclearUltrapower.SOS.label1023`, `OAI.NuclearUltrapower.SOS.label1038`, `OAI.NuclearUltrapower.SOS.label1039`, `OAI.NuclearUltrapower.SOS.label1046`, `OAI.NuclearUltrapower.SOS.label107`, `OAI.NuclearUltrapower.SOS.label1080`, `OAI.NuclearUltrapower.SOS.label1095`, `OAI.NuclearUltrapower.SOS.label1097`, `OAI.NuclearUltrapower.SOS.label1104`, `OAI.NuclearUltrapower.SOS.label1114`, `OAI.NuclearUltrapower.SOS.label1119`, `OAI.NuclearUltrapower.SOS.label1120`, `OAI.NuclearUltrapower.SOS.label1128`, `OAI.NuclearUltrapower.SOS.label1136`, `OAI.NuclearUltrapower.SOS.label1140`, `OAI.NuclearUltrapower.SOS.label1147`, `OAI.NuclearUltrapower.SOS.label1163`, `OAI.NuclearUltrapower.SOS.label1164`, `OAI.NuclearUltrapower.SOS.label1202` and 354 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BlockOperators`, `CoarseAssembly_BoundaryLoopMaps`, `CoarseAssembly_BoundedGeometry`, `CoarseAssembly_ConcreteIndexDiagrams`, `CoarseAssembly_ConcreteSpaces`, `CoarseAssembly_ConcreteTransfer`, `CoarseAssembly_GraphMetric`, `CoarseAssembly_Lattice`, `CoarseAssembly_SeparatedGeometry`, `CoarseAssembly_TensorFibers`, `CoarseAssembly_TraceSeparation`, `CoarseAssembly_TransferLift`, `NuclearUltrapower_DyadicGroup`, `NuclearUltrapower_SOSResidual`, `NuclearUltrapower_SOSSemantics`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C011`, `OAIQ229C012`, `OAIQ229C013`, `OAIQ229C014` and `OAIQ229C015`; the statements `OAI_NuclearUltrapower_SOS_eval_mul`, `OAI.NuclearUltrapower.SOS.eval_mul_ca`, `OAI_NuclearUltrapower_SOS_row_length_0`, `OAI.NuclearUltrapower.SOS.row_length_0_ca`, `OAI_NuclearUltrapower_SOS_row_length_1`, `OAI.NuclearUltrapower.SOS.row_length_100_ca`, `OAI.NuclearUltrapower.SOS.row_length_10_ca` and `OAI.NuclearUltrapower.SOS.row_length_1_ca`; the proofs of `OAI_NuclearUltrapower_SOS_row_length_0`, `OAI.NuclearUltrapower.SOS.row_length_0_ca`, `OAI_NuclearUltrapower_SOS_row_length_1`, `OAI.NuclearUltrapower.SOS.row_length_100_ca`, `OAI.NuclearUltrapower.SOS.row_length_10_ca` and `OAI.NuclearUltrapower.SOS.row_length_1_ca`.
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
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CoarseAssembly

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockOperators
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

theorem averaging_power_norm_le (M : ∀ i, E i →L[ℂ] E i)
    (hM : ∀ i, ‖M i‖ ≤ 1) (n : ℕ) (i : ι) : ‖M i ^ (n + 1)‖ ≤ 1 := by
  calc
    _ ≤ ‖M i‖ ^ (n + 1) := norm_pow_le' _ (Nat.succ_pos n)
    _ ≤ 1 ^ (n + 1) := by gcongr; exact hM i
    _ = 1 := one_pow _

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Lattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The triangular-lattice discs

The vertex set, adjacency, radius and depth used in §3 of the coarse Novikov
manuscript. The three integer linear forms are precisely those in its hexagonal
radius `max {|a|, |b|, |a+b|}`. These definitions do not assert the unproved
identification of the filled geometric realization with a topological disc.
-/

namespace CoarseAssembly

def latticeNeighbors (u : LatticeVertex) : Finset LatticeVertex :=
  {(u.1 + 1, u.2), (u.1 - 1, u.2), (u.1, u.2 + 1),
    (u.1, u.2 - 1), (u.1 + 1, u.2 - 1), (u.1 - 1, u.2 + 1)}

theorem mem_latticeNeighbors_iff (u v : LatticeVertex) :
    v ∈ latticeNeighbors u ↔ triangularGraph.Adj u v := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  simp only [latticeNeighbors, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    triangularGraph, abs_le, ne_eq, Prod.mk.injEq]
  omega

theorem card_latticeNeighbors_le (u : LatticeVertex) : (latticeNeighbors u).card ≤ 6 := by
  unfold latticeNeighbors
  exact le_trans (Finset.card_insert_le _ _) (by
    apply Nat.succ_le_succ
    exact le_trans (Finset.card_insert_le _ _) (by
      apply Nat.succ_le_succ
      exact le_trans (Finset.card_insert_le _ _) (by
        apply Nat.succ_le_succ
        exact le_trans (Finset.card_insert_le _ _) (by
          apply Nat.succ_le_succ
          exact le_trans (Finset.card_insert_le _ _) (by simp)))))

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TraceSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Trace separation for the congruence-fiber construction

These are elementary ingredients of Lemma 3.1 of *A counterexample to the
coarse Novikov conjecture* (September 23, 2026). No analytic index theorem or
property (T) is assumed here. The actual reduction maps are the existing
`PadicInt.toZModPow` maps.
-/

namespace CoarseAssembly

section LaurentTrace

variable {R : Type*} [CommRing R]

/-- The trace of `diag(t^n,t^(-n),1)`, expressed using a unit so that the
inverse is available in an arbitrary commutative ring. -/
def diagonalTrace (t : Rˣ) (n : ℕ) : R :=
  (t ^ n : Rˣ) + ((t ^ n)⁻¹ : Rˣ) + 1

end LaurentTrace

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniformly bounded degree gives uniformly finite graph balls

The elementary bounded-geometry argument used in §3 of the coarse Novikov
manuscript. Finite neighbor lists are supplied for an arbitrary graph; no
finiteness assumption is made about the whole vertex set. The bound
`(degreeBound + 1)^radius` is sufficient for the application.
-/

namespace CoarseAssembly

variable {V : Type*} [DecidableEq V]

/-- A finite over-approximation of vertices reached in at most `r` edges. -/
def walkBall (neighbors : V → Finset V) (x : V) : ℕ → Finset V
  | 0 => {x}
  | r + 1 => walkBall neighbors x r ∪ (walkBall neighbors x r).biUnion neighbors

@[simp] theorem mem_walkBall_zero (neighbors : V → Finset V) (x y : V) :
    y ∈ walkBall neighbors x 0 ↔ y = x := by simp [walkBall]

theorem walkBall_mono_step (neighbors : V → Finset V) (x : V) (r : ℕ) :
    walkBall neighbors x r ⊆ walkBall neighbors x (r + 1) :=
  Finset.subset_union_left

theorem walkBall_mono (neighbors : V → Finset V) (x : V) {r s : ℕ} (h : r ≤ s) :
    walkBall neighbors x r ⊆ walkBall neighbors x s := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @step s h ih => exact ih.trans (walkBall_mono_step neighbors x s)

/-- A uniform degree bound bounds every finite combinatorial ball. -/
theorem card_walkBall_le (neighbors : V → Finset V) (d : ℕ)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (r : ℕ) :
    (walkBall neighbors x r).card ≤ (d + 1) ^ r := by
  induction r with
  | zero => simp [walkBall]
  | succ r ih =>
    calc
      (walkBall neighbors x (r + 1)).card ≤
          (walkBall neighbors x r).card + ((walkBall neighbors x r).biUnion neighbors).card :=
        Finset.card_union_le _ _
      _ ≤ (walkBall neighbors x r).card + (walkBall neighbors x r).card * d := by
        exact Nat.add_le_add_left
          (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => hd v)) _
      _ = (d + 1) * (walkBall neighbors x r).card := by ring
      _ ≤ (d + 1) * (d + 1) ^ r := Nat.mul_le_mul_left _ ih
      _ = (d + 1) ^ (r + 1) := by rw [pow_succ, Nat.mul_comm]

variable {G : SimpleGraph V}

/-- Each walk endpoint belongs to the finite ball of its length. -/
theorem endpoint_mem_walkBall (neighbors : V → Finset V)
    (hN : ∀ u v, G.Adj u v → v ∈ neighbors u) {x y : V} (p : G.Walk x y) :
    y ∈ walkBall neighbors x p.length := by
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => simp [walkBall]
  | @Hconcat x y z p h ih =>
    rw [SimpleGraph.Walk.length_concat]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, ih, hN y z h⟩)

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_GraphMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The metric of a connected graph

The metric on a connected graph is exactly the real-valued shortest-path
length. A proof-independent extension uses the discrete metric otherwise.
-/

noncomputable section

namespace CoarseAssembly

variable {V : Type*} (G : SimpleGraph V)

/-- An exact metric ball, with the explicit bound inherited from degree. -/
theorem graphMetric_ball_bound [DecidableEq V] (hG : G.Connected)
    (neighbors : V → Finset V) (d : ℕ)
    (hN : ∀ x y, G.Adj x y → y ∈ neighbors x)
    (hd : ∀ x, (neighbors x).card ≤ d) (R : ℝ) (x : V) :
    ∃ b : Finset V,
      (∀ y, y ∈ b ↔ (G.dist x y : ℝ) ≤ R) ∧ b.card ≤ (d + 1) ^ ⌈R⌉₊ := by
  classical
  let b := (walkBall neighbors x ⌈R⌉₊).filter (fun y => (G.dist x y : ℝ) ≤ R)
  refine ⟨b, ?_, ?_⟩
  · intro y
    simp only [b, Finset.mem_filter]
    refine ⟨fun h => h.2, fun hy => ⟨?_, hy⟩⟩
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
    have hlen : p.length ≤ ⌈R⌉₊ := by
      rw [hp]
      exact_mod_cast hy.trans (Nat.le_ceil R)
    exact walkBall_mono neighbors x hlen (endpoint_mem_walkBall neighbors hN p)
  · exact (Finset.card_filter_le _ _).trans (card_walkBall_le neighbors d hd x ⌈R⌉₊)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TensorFibers
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

def fiberTensorBilinear : lp (fun _ : Q => ℂ) 2 →ₗ[ℂ]
    H →ₗ[ℂ] lp (fun _ : Q => H) 2 where
  toFun a :=
    { toFun := fun h => ⟨fun q => a q • h, Memℓp.all _⟩
      map_add' := by intro x y; apply lp.ext; funext q; exact smul_add _ _ _
      map_smul' := by intro c h; apply lp.ext; funext q; exact smul_comm _ _ _ }
  map_add' a b := by
    apply LinearMap.ext
    intro h
    apply lp.ext
    funext q
    exact add_smul (a q) (b q) h
  map_smul' c a := by
    apply LinearMap.ext
    intro h
    apply lp.ext
    funext q
    exact mul_smul c (a q) h

def fiberTensorMap : (lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) →ₗ[ℂ] lp (fun _ : Q => H) 2 :=
  TensorProduct.lift fiberTensorBilinear

@[simp] theorem fiberTensorMap_tmul_apply (a : lp (fun _ : Q => ℂ) 2) (h : H) (q : Q) :
    fiberTensorMap (a ⊗ₜ[ℂ] h) q = a q • h := rfl

variable [DecidableEq Q]

theorem fiberTensorMap_surjective : Function.Surjective (fiberTensorMap (Q := Q) (H := H)) := by
  intro x
  refine ⟨∑ q : Q, lp.single 2 q (1 : ℂ) ⊗ₜ[ℂ] x q, ?_⟩
  apply lp.ext
  funext r
  simp only [map_sum, lp.coeFn_sum, Finset.sum_apply, fiberTensorMap_tmul_apply]
  simp [lp.single_apply, Pi.single_apply]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TransferLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The controlled lift and its exact compression

The lift is constructed as a bounded block matrix. Its scalar coefficient
condition proves local compactness, while preservation of constant-fiber
vectors proves the compression identity. These are explicit construction
conditions, not published hypotheses for the main result.
-/

noncomputable section

namespace CoarseAssembly

open DiscreteRoe

variable {I : Type*} {Q : I → Type*} {H : Type*}
variable [DecidableEq I] [∀ i, DecidableEq (Q i)]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fiberBlockEntry {i j : I}
    (B : lp (fun _ : Q j => H) 2 →L[ℂ] lp (fun _ : Q i => H) 2)
    (q : Q i) (r : Q j) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : Q i => H) 2 q).comp
    (B.comp (lp.singleContinuousLinearMap ℂ (fun _ : Q j => H) 2 r))

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded geometry of the separated union

Uniform component ball bounds pass to the union. All cross-component pairs
in a fixed distance range lie in a finite prefix, which also supplies the
finite exceptional set in the transfer argument.
-/

noncomputable section

namespace CoarseAssembly

variable {V : ℕ → Type*} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]

def componentPrefix (N : ℕ) : Finset (Sigma V) :=
  (Finset.range (N + 1)).sigma (fun _ => Finset.univ)

omit [∀ i, MetricSpace (V i)] in
@[simp] theorem mem_componentPrefix (N : ℕ) (x : Sigma V) :
    x ∈ componentPrefix N ↔ x.1 ≤ N := by
  classical
  simp only [componentPrefix, Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true,
    Nat.lt_succ_iff]

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

/-- Transport an exact finite-ball bound across an isometric equivalence. -/
theorem uniform_balls_of_equiv {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : X ≃ Y) (he : ∀ x y, dist (e x) (e y) = dist x y)
    (hY : UniformFiniteBalls Y) : UniformFiniteBalls X := by
  classical
  intro R hR
  obtain ⟨N, hN⟩ := hY R hR
  refine ⟨N, ?_⟩
  intro x
  obtain ⟨b, hb, hcard⟩ := hN (e x)
  refine ⟨b.map e.symm.toEmbedding, ?_, ?_⟩
  · intro y
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, hb, he]
  · simpa only [Finset.card_map] using hcard

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The transfer on the actual coarse spaces

All metric and inter-fiber hypotheses have been discharged. Only the
averaging projection approximation remains in this intermediate theorem;
it is an own-paper obligation, not an assumed published theorem.
-/

noncomputable section

namespace CoarseAssembly

open DiscreteRoe
open scoped Topology

theorem UniformFiniteBalls.finite_closedBall {X : Type*} [PseudoMetricSpace X]
    (hX : UniformFiniteBalls X) (x : X) (r : ℝ) : (Metric.closedBall x r).Finite := by
  by_cases hr : 0 ≤ r
  · obtain ⟨N, hN⟩ := hX r hr
    obtain ⟨b, hb, hcard⟩ := hN x
    apply b.finite_toSet.subset
    intro y hy
    exact (hb y).mpr (by simpa only [Metric.mem_closedBall, dist_comm] using hy)
  · have he : Metric.closedBall x r = ∅ := Metric.closedBall_eq_empty.mpr (lt_of_not_ge hr)
    rw [he]
    exact Set.finite_empty

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryLoopMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same boundary family maps to the filled base and detected total space

The source class is defined on the actual boundary Rips complex. Its base
image is identified with the previously constructed filled loop family.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric7

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric8

theorem totalToFiber_dist (x y : VertexUnion) : dist (totalToFiber x) (totalToFiber y) = dist x y := rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteIndexDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact geometric and Roe squares for the two boundary inclusions -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance concreteDiagramTotalMetric : MetricSpace VertexUnion :=
  vertexUnionMetric elementaryMoves chosenHolonomyUnit

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_DyadicGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter

namespace NuclearUltrapower

/-! The exact integral subgroup and dilation in the tensor-norm formulation. -/

abbrev IntegralVector3 := Fin 3 → ℤ

end NuclearUltrapower

end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

/-- Sparse integral polynomials, before combining repeated labels. -/
abbrev Poly (α : Type*) := List (α × ℤ)

section Evaluation
variable [AddCommGroup A]

def eval (f : α → A) (ps : Poly α) : A :=
  (ps.map (fun p => p.2 • f p.1)).sum

omit [DecidableEq α] in
@[simp] theorem eval_nil (f : α → A) : eval f [] = 0 := rfl
omit [DecidableEq α] in
@[simp] theorem eval_cons (f : α → A) (p : α × ℤ) (ps : Poly α) :
    eval f (p::ps) = p.2 • f p.1 + eval f ps := rfl

end Evaluation

/-- Flat 3-by-3 integer matrices, used only as kernel-computable labels. -/
abbrev Mat3 := List ℤ

def entry (a : Mat3) (i j : Nat) : ℤ := a.getD (3*i+j) 0

end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS
def label1 : Mat3 := [-3, 0, -2, 0, 1, 0, 2, 0, 1]
def label6 : Mat3 := [-2, 0, -3, 0, 1, 0, 1, 0, 1]
def label13 : Mat3 := [-1, -2, -2, 0, 1, 0, 1, 1, 1]
def label14 : Mat3 := [-1, -2, -2, 1, 1, 0, 1, 1, 1]
def label44 : Mat3 := [-1, -1, -2, 0, 1, 0, 1, 0, 1]
def label45 : Mat3 := [-1, -1, -2, 0, 1, 0, 1, 1, 1]
def label89 : Mat3 := [-1, 0, -3, 0, 1, 0, 1, 0, 2]
def label91 : Mat3 := [-1, 0, -2, -1, 1, -1, 1, 0, 1]
def label92 : Mat3 := [-1, 0, -2, -1, 1, 0, 1, 0, 1]
def label93 : Mat3 := [-1, 0, -2, 0, 1, -1, 1, 0, 1]
def label96 : Mat3 := [-1, 0, -2, 0, 1, 0, 1, 0, 1]
def label99 : Mat3 := [-1, 0, -2, 0, 1, 1, 1, 0, 1]
def label100 : Mat3 := [-1, 0, -2, 1, 1, 0, 1, 0, 1]
def label101 : Mat3 := [-1, 0, -2, 1, 1, 1, 1, 0, 1]
def label107 : Mat3 := [-1, 0, -1, 0, 1, 0, 1, 0, 0]
def label150 : Mat3 := [-1, 1, -2, 0, 1, 0, 1, -1, 1]
def label151 : Mat3 := [-1, 1, -2, 0, 1, 0, 1, 0, 1]
def label194 : Mat3 := [-1, 2, -2, -1, 1, 0, 1, -1, 1]
def label195 : Mat3 := [-1, 2, -2, 0, 1, 0, 1, -1, 1]
def label223 : Mat3 := [-1, 3, 0, -1, 2, 0, 0, 0, 1]
def label242 : Mat3 := [0, -1, -2, 1, 1, 0, 0, 0, 1]
def label341 : Mat3 := [0, -1, 0, 1, 1, 0, 0, 0, 1]
def label477 : Mat3 := [0, 0, -1, 0, 1, 0, 1, 0, 1]
def label550 : Mat3 := [0, 0, 1, 0, 1, 0, -1, 0, 1]
def label591 : Mat3 := [0, 1, -2, -1, 1, 0, 0, 0, 1]
def label594 : Mat3 := [0, 1, -2, 0, 1, -1, 1, 0, 1]
def label686 : Mat3 := [0, 1, 0, -1, 1, 0, 0, 0, 1]
def label786 : Mat3 := [0, 1, 2, 0, 1, 1, -1, 0, 1]
def label804 : Mat3 := [1, -4, -2, 0, 1, 0, 0, 2, 1]
def label809 : Mat3 := [1, -3, -3, 0, 1, 0, 0, 1, 1]
def label811 : Mat3 := [1, -3, -2, 0, 1, 0, 0, 1, 1]
def label854 : Mat3 := [1, -2, -4, 0, 1, 1, 0, 1, 2]
def label856 : Mat3 := [1, -2, -3, 0, 1, 0, 0, 1, 1]
def label862 : Mat3 := [1, -2, -2, -1, 1, 0, 0, 1, 1]
def label866 : Mat3 := [1, -2, -2, 0, 0, -1, 0, 1, 1]
def label868 : Mat3 := [1, -2, -2, 0, 1, 0, 0, 0, 1]
def label869 : Mat3 := [1, -2, -2, 0, 1, 0, 0, 1, 1]
def label882 : Mat3 := [1, -2, -2, 0, 2, 1, 0, 1, 1]
def label886 : Mat3 := [1, -2, -2, 1, 1, 0, 0, 1, 1]
def label905 : Mat3 := [1, -2, -1, 0, 1, 0, 0, 1, 1]
def label961 : Mat3 := [1, -2, 0, 0, 1, -1, 0, 1, 0]
def label975 : Mat3 := [1, -2, 0, 0, 1, 0, 0, 0, 1]
def label1010 : Mat3 := [1, -2, 0, 1, 0, 1, 1, -1, 1]
def label1012 : Mat3 := [1, -2, 0, 1, 1, 1, 1, 0, 1]
def label1023 : Mat3 := [1, -2, 1, 0, 0, 1, 0, -1, 1]
def label1038 : Mat3 := [1, -2, 1, 0, 1, 0, 0, -1, 1]
def label1039 : Mat3 := [1, -2, 1, 0, 1, 0, 0, 0, 1]
def label1046 : Mat3 := [1, -2, 1, 0, 1, 1, 0, 0, 1]
def label1080 : Mat3 := [1, -2, 2, 0, 1, 0, 0, 0, 1]
def label1095 : Mat3 := [1, -1, -3, 0, 1, 0, 0, 0, 1]
def label1097 : Mat3 := [1, -1, -3, 0, 1, 1, 0, 0, 1]
def label1104 : Mat3 := [1, -1, -2, -1, 2, 0, 0, 0, 1]
def label1114 : Mat3 := [1, -1, -2, 0, 1, -1, 0, 0, 1]
def label1119 : Mat3 := [1, -1, -2, 0, 1, 0, 0, 0, 1]
def label1120 : Mat3 := [1, -1, -2, 0, 1, 0, 0, 1, 1]
def label1128 : Mat3 := [1, -1, -2, 0, 1, 1, 0, 0, 1]
def label1136 : Mat3 := [1, -1, -2, 0, 1, 2, 0, 0, 1]
def label1140 : Mat3 := [1, -1, -2, 0, 1, 3, 0, 0, 1]
def label1147 : Mat3 := [1, -1, -2, 1, 0, 0, 0, 0, 1]
def label1163 : Mat3 := [1, -1, -1, -1, 1, 2, -1, 0, 1]
def label1164 : Mat3 := [1, -1, -1, -1, 1, 2, -1, 0, 2]
def label1202 : Mat3 := [1, -1, -1, 0, 0, 1, 0, -1, 0]
def label1203 : Mat3 := [1, -1, -1, 0, 0, 1, 0, -1, 1]
def label1207 : Mat3 := [1, -1, -1, 0, 1, -1, 0, 0, 1]
def label1221 : Mat3 := [1, -1, -1, 0, 1, 0, 0, 0, 1]
def label1222 : Mat3 := [1, -1, -1, 0, 1, 0, 0, 1, 1]
def label1241 : Mat3 := [1, -1, -1, 0, 1, 1, 0, 0, 1]
def label1253 : Mat3 := [1, -1, -1, 0, 1, 2, 0, 0, 1]
def label1260 : Mat3 := [1, -1, -1, 0, 2, 1, 0, 1, 1]
def label1263 : Mat3 := [1, -1, -1, 0, 2, 3, 0, 1, 2]
def label1293 : Mat3 := [1, -1, -1, 1, 1, 0, 1, 0, 0]
def label1295 : Mat3 := [1, -1, -1, 1, 1, 2, 1, 0, 1]
def label1306 : Mat3 := [1, -1, 0, -2, 1, 1, -2, 0, 1]
def label1334 : Mat3 := [1, -1, 0, -1, 0, 1, -1, -1, 1]
def label1342 : Mat3 := [1, -1, 0, -1, 1, 1, -1, 0, 1]
def label1368 : Mat3 := [1, -1, 0, -1, 2, 0, 0, 0, 1]
def label1383 : Mat3 := [1, -1, 0, -1, 2, 1, -1, 1, 1]
def label1398 : Mat3 := [1, -1, 0, 0, -1, 1, 0, -2, 1]
def label1407 : Mat3 := [1, -1, 0, 0, 0, 1, 0, -1, 1]
def label1422 : Mat3 := [1, -1, 0, 0, 1, -1, 0, 0, 1]
def label1440 : Mat3 := [1, -1, 0, 0, 1, 0, -1, 0, 1]
def label1441 : Mat3 := [1, -1, 0, 0, 1, 0, -1, 1, 1]
def label1446 : Mat3 := [1, -1, 0, 0, 1, 0, 0, -1, 1]
def label1447 : Mat3 := [1, -1, 0, 0, 1, 0, 0, 0, 1]
def label1448 : Mat3 := [1, -1, 0, 0, 1, 0, 0, 1, 1]
def label1453 : Mat3 := [1, -1, 0, 0, 1, 0, 1, -1, 1]
def label1454 : Mat3 := [1, -1, 0, 0, 1, 0, 1, 0, 1]
def label1472 : Mat3 := [1, -1, 0, 0, 1, 1, 0, 0, 1]
def label1481 : Mat3 := [1, -1, 0, 0, 1, 2, 0, 0, 1]
def label1493 : Mat3 := [1, -1, 0, 0, 2, 1, 0, 1, 1]
def label1499 : Mat3 := [1, -1, 0, 0, 3, 1, 0, 2, 1]
def label1525 : Mat3 := [1, -1, 0, 1, 0, 0, 0, 0, 1]
def label1540 : Mat3 := [1, -1, 0, 1, 0, 1, 1, -1, 1]
def label1553 : Mat3 := [1, -1, 0, 1, 1, 1, 1, 0, 1]
def label1557 : Mat3 := [1, -1, 0, 1, 2, 1, 1, 1, 1]
def label1581 : Mat3 := [1, -1, 0, 2, 1, 1, 2, 0, 1]
def label1594 : Mat3 := [1, -1, 1, -1, 1, 0, -1, 0, 0]
def label1595 : Mat3 := [1, -1, 1, -1, 1, 0, -1, 0, 1]
def label1635 : Mat3 := [1, -1, 1, 0, 0, 1, 0, -1, 1]
def label1636 : Mat3 := [1, -1, 1, 0, 0, 1, 0, -1, 2]
def label1653 : Mat3 := [1, -1, 1, 0, 1, -1, 0, 0, 1]
def label1672 : Mat3 := [1, -1, 1, 0, 1, 0, 0, -1, 1]
def label1673 : Mat3 := [1, -1, 1, 0, 1, 0, 0, 0, 1]
def label1687 : Mat3 := [1, -1, 1, 0, 1, 1, 0, 0, 1]
def label1695 : Mat3 := [1, -1, 1, 0, 2, -1, 0, 1, 0]
def label1697 : Mat3 := [1, -1, 1, 0, 2, 1, 0, 1, 1]
def label1792 : Mat3 := [1, 0, -4, 0, 1, 0, 0, 0, 1]
def label1793 : Mat3 := [1, 0, -3, -1, 1, 0, 0, 0, 1]
def label1794 : Mat3 := [1, 0, -3, -1, 1, 1, 0, 0, 1]
def label1797 : Mat3 := [1, 0, -3, 0, 1, -1, 0, 0, 1]
def label1800 : Mat3 := [1, 0, -3, 0, 1, 0, 0, 0, 1]
def label1803 : Mat3 := [1, 0, -3, 0, 1, 1, 0, 0, 1]
def label1806 : Mat3 := [1, 0, -3, 1, 1, -1, 0, 0, 1]
def label1807 : Mat3 := [1, 0, -3, 1, 1, 0, 0, 0, 1]
def label1808 : Mat3 := [1, 0, -2, -2, 1, 0, 0, 0, 1]
def label1813 : Mat3 := [1, 0, -2, -1, 1, -1, 0, 0, 1]
def label1816 : Mat3 := [1, 0, -2, -1, 1, 0, 0, 0, 1]
def label1821 : Mat3 := [1, 0, -2, -1, 1, 1, 0, 0, 1]
def label1835 : Mat3 := [1, 0, -2, 0, 1, -2, 0, 0, 1]
def label1838 : Mat3 := [1, 0, -2, 0, 1, -1, 0, 0, 1]
def label1847 : Mat3 := [1, 0, -2, 0, 1, 0, 0, 0, 1]
def label1856 : Mat3 := [1, 0, -2, 0, 1, 1, 0, 0, 1]
def label1859 : Mat3 := [1, 0, -2, 0, 1, 2, 0, 0, 1]
def label1873 : Mat3 := [1, 0, -2, 1, 1, -1, 0, 0, 1]
def label1878 : Mat3 := [1, 0, -2, 1, 1, 0, 0, 0, 1]
def label1881 : Mat3 := [1, 0, -2, 1, 1, 1, 0, 0, 1]
def label1886 : Mat3 := [1, 0, -2, 2, 1, 0, 0, 0, 1]
def label1929 : Mat3 := [1, 0, -1, -1, 1, -1, 0, 0, 1]
def label1938 : Mat3 := [1, 0, -1, -1, 1, 0, 0, 0, 1]
def label1954 : Mat3 := [1, 0, -1, -1, 1, 1, 0, 0, 1]
def label2009 : Mat3 := [1, 0, -1, 0, 1, -1, 0, 0, 1]
def label2022 : Mat3 := [1, 0, -1, 0, 1, 0, -1, 0, 2]
def label2027 : Mat3 := [1, 0, -1, 0, 1, 0, 0, -1, 1]
def label2028 : Mat3 := [1, 0, -1, 0, 1, 0, 0, 0, 1]
def label2029 : Mat3 := [1, 0, -1, 0, 1, 0, 0, 1, 1]
def label2034 : Mat3 := [1, 0, -1, 0, 1, 0, 1, 0, 0]
def label2047 : Mat3 := [1, 0, -1, 0, 1, 1, 0, 0, 1]
def label2100 : Mat3 := [1, 0, -1, 1, 1, -1, 0, 0, 1]
def label2116 : Mat3 := [1, 0, -1, 1, 1, 0, 0, 0, 1]
def label2125 : Mat3 := [1, 0, -1, 1, 1, 1, 0, 0, 1]
def label2247 : Mat3 := [1, 0, 0, -2, 1, 0, 0, 0, 1]
def label2345 : Mat3 := [1, 0, 0, -1, 1, -1, 0, 0, 1]
def label2350 : Mat3 := [1, 0, 0, -1, 1, -1, 1, 0, 1]
def label2369 : Mat3 := [1, 0, 0, -1, 1, 0, -1, 0, 1]
def label2370 : Mat3 := [1, 0, 0, -1, 1, 0, -1, 1, 1]
def label2375 : Mat3 := [1, 0, 0, -1, 1, 0, 0, -1, 1]
def label2376 : Mat3 := [1, 0, 0, -1, 1, 0, 0, 0, 1]
def label2377 : Mat3 := [1, 0, 0, -1, 1, 0, 0, 1, 1]
def label2382 : Mat3 := [1, 0, 0, -1, 1, 0, 1, -1, 1]
def label2383 : Mat3 := [1, 0, 0, -1, 1, 0, 1, 0, 1]
def label2402 : Mat3 := [1, 0, 0, -1, 1, 1, -1, 0, 1]
def label2407 : Mat3 := [1, 0, 0, -1, 1, 1, 0, 0, 1]
def label2494 : Mat3 := [1, 0, 0, 0, 0, -1, 0, 1, 1]
def label2507 : Mat3 := [1, 0, 0, 0, 0, 1, 0, -1, 1]
def label2526 : Mat3 := [1, 0, 0, 0, 1, -2, 0, 0, 1]
def label2539 : Mat3 := [1, 0, 0, 0, 1, -1, -1, 0, 1]
def label2544 : Mat3 := [1, 0, 0, 0, 1, -1, 0, -1, 2]
def label2545 : Mat3 := [1, 0, 0, 0, 1, -1, 0, 0, 1]
def label2546 : Mat3 := [1, 0, 0, 0, 1, -1, 0, 1, 0]
def label2551 : Mat3 := [1, 0, 0, 0, 1, -1, 1, 0, 1]
def label2564 : Mat3 := [1, 0, 0, 0, 1, 0, -2, 0, 1]
def label2569 : Mat3 := [1, 0, 0, 0, 1, 0, -1, -1, 1]
def label2570 : Mat3 := [1, 0, 0, 0, 1, 0, -1, 0, 1]
def label2571 : Mat3 := [1, 0, 0, 0, 1, 0, -1, 1, 1]
def label2576 : Mat3 := [1, 0, 0, 0, 1, 0, 0, -2, 1]
def label2577 : Mat3 := [1, 0, 0, 0, 1, 0, 0, -1, 1]
def label2578 : Mat3 := [1, 0, 0, 0, 1, 0, 0, 0, 1]
def label2579 : Mat3 := [1, 0, 0, 0, 1, 0, 0, 1, 1]
def label2580 : Mat3 := [1, 0, 0, 0, 1, 0, 0, 2, 1]
def label2585 : Mat3 := [1, 0, 0, 0, 1, 0, 1, -1, 1]
def label2586 : Mat3 := [1, 0, 0, 0, 1, 0, 1, 0, 1]
def label2587 : Mat3 := [1, 0, 0, 0, 1, 0, 1, 1, 1]
def label2592 : Mat3 := [1, 0, 0, 0, 1, 0, 2, 0, 1]
def label2605 : Mat3 := [1, 0, 0, 0, 1, 1, -1, 0, 1]
def label2610 : Mat3 := [1, 0, 0, 0, 1, 1, 0, -1, 0]
def label2611 : Mat3 := [1, 0, 0, 0, 1, 1, 0, 0, 1]
def label2612 : Mat3 := [1, 0, 0, 0, 1, 1, 0, 1, 2]
def label2617 : Mat3 := [1, 0, 0, 0, 1, 1, 1, 0, 1]
def label2630 : Mat3 := [1, 0, 0, 0, 1, 2, 0, 0, 1]
def label2655 : Mat3 := [1, 0, 0, 0, 2, -1, 0, -1, 1]
def label2668 : Mat3 := [1, 0, 0, 0, 2, 1, 0, 1, 1]
def label2762 : Mat3 := [1, 0, 0, 1, 1, -1, -1, 0, 1]
def label2766 : Mat3 := [1, 0, 0, 1, 1, -1, 0, 0, 1]
def label2787 : Mat3 := [1, 0, 0, 1, 1, 0, -1, -1, 1]
def label2788 : Mat3 := [1, 0, 0, 1, 1, 0, -1, 0, 1]
def label2793 : Mat3 := [1, 0, 0, 1, 1, 0, 0, -1, 1]
def label2794 : Mat3 := [1, 0, 0, 1, 1, 0, 0, 0, 1]
def label2795 : Mat3 := [1, 0, 0, 1, 1, 0, 0, 1, 1]
def label2800 : Mat3 := [1, 0, 0, 1, 1, 0, 1, 0, 1]
def label2801 : Mat3 := [1, 0, 0, 1, 1, 0, 1, 1, 1]
def label2822 : Mat3 := [1, 0, 0, 1, 1, 1, 0, 0, 1]
def label2826 : Mat3 := [1, 0, 0, 1, 1, 1, 1, 0, 1]
def label2915 : Mat3 := [1, 0, 0, 2, 1, 0, 0, 0, 1]
def label3062 : Mat3 := [1, 0, 1, -1, 1, -1, 0, 0, 1]
def label3078 : Mat3 := [1, 0, 1, -1, 1, 0, 0, 0, 1]
def label3125 : Mat3 := [1, 0, 1, 0, 1, -1, 0, 0, 1]
def label3138 : Mat3 := [1, 0, 1, 0, 1, 0, -1, 0, 0]
def label3143 : Mat3 := [1, 0, 1, 0, 1, 0, 0, -1, 1]
def label3144 : Mat3 := [1, 0, 1, 0, 1, 0, 0, 0, 1]
def label3145 : Mat3 := [1, 0, 1, 0, 1, 0, 0, 1, 1]
def label3150 : Mat3 := [1, 0, 1, 0, 1, 0, 1, 0, 2]
def label3163 : Mat3 := [1, 0, 1, 0, 1, 1, 0, 0, 1]
def label3208 : Mat3 := [1, 0, 1, 1, 1, 0, 0, 0, 1]
def label3224 : Mat3 := [1, 0, 1, 1, 1, 1, 0, 0, 1]
def label3323 : Mat3 := [1, 0, 2, 0, 1, 0, 0, 0, 1]
def label3383 : Mat3 := [1, 1, -3, 0, 1, -1, 0, 0, 1]
def label3385 : Mat3 := [1, 1, -3, 0, 1, 0, 0, 0, 1]
def label3386 : Mat3 := [1, 1, -2, -1, 0, 0, 0, 0, 1]
def label3409 : Mat3 := [1, 1, -2, 0, 1, -1, 0, 0, 1]
def label3417 : Mat3 := [1, 1, -2, 0, 1, 0, 0, -1, 1]
def label3418 : Mat3 := [1, 1, -2, 0, 1, 0, 0, 0, 1]
def label3422 : Mat3 := [1, 1, -2, 0, 1, 1, 0, 0, 1]
def label3433 : Mat3 := [1, 1, -2, 1, 2, 0, 0, 0, 1]
def label3495 : Mat3 := [1, 1, -1, 0, 1, -1, 0, 0, 1]
def label3499 : Mat3 := [1, 1, -1, 0, 1, -1, 1, 0, 1]
def label3516 : Mat3 := [1, 1, -1, 0, 1, 0, 0, -1, 1]
def label3517 : Mat3 := [1, 1, -1, 0, 1, 0, 0, 0, 1]
def label3529 : Mat3 := [1, 1, -1, 0, 1, 1, 0, 0, 1]
def label3637 : Mat3 := [1, 1, 0, -1, 0, 0, 0, 0, 1]
def label3696 : Mat3 := [1, 1, 0, 0, 1, -1, 0, 0, 1]
def label3714 : Mat3 := [1, 1, 0, 0, 1, 0, -1, -1, 1]
def label3715 : Mat3 := [1, 1, 0, 0, 1, 0, -1, 0, 1]
def label3716 : Mat3 := [1, 1, 0, 0, 1, 0, -1, 1, 1]
def label3720 : Mat3 := [1, 1, 0, 0, 1, 0, 0, -1, 1]
def label3721 : Mat3 := [1, 1, 0, 0, 1, 0, 0, 0, 1]
def label3722 : Mat3 := [1, 1, 0, 0, 1, 0, 0, 1, 1]
def label3726 : Mat3 := [1, 1, 0, 0, 1, 0, 1, -1, 1]
def label3727 : Mat3 := [1, 1, 0, 0, 1, 0, 1, 0, 1]
def label3728 : Mat3 := [1, 1, 0, 0, 1, 0, 1, 1, 1]
def label3746 : Mat3 := [1, 1, 0, 0, 1, 1, 0, 0, 1]
def label3810 : Mat3 := [1, 1, 0, 1, 2, 0, 0, 0, 1]
def label3929 : Mat3 := [1, 1, 1, 0, 1, 0, 0, 0, 1]
def label3930 : Mat3 := [1, 1, 1, 0, 1, 0, 0, 1, 1]
def label3947 : Mat3 := [1, 1, 1, 0, 1, 1, -1, 0, 1]
def label3951 : Mat3 := [1, 1, 1, 0, 1, 1, 0, 0, 1]
def label4044 : Mat3 := [1, 1, 2, 0, 1, 1, 0, 0, 1]
def label4077 : Mat3 := [1, 2, -4, 0, 1, -1, 0, -1, 2]
def label4082 : Mat3 := [1, 2, -3, 0, 1, 0, 0, -1, 1]
def label4087 : Mat3 := [1, 2, -2, -1, 1, 0, 0, -1, 1]
def label4088 : Mat3 := [1, 2, -2, 0, 0, 1, 0, -1, 1]
def label4101 : Mat3 := [1, 2, -2, 0, 1, 0, 0, -1, 1]
def label4102 : Mat3 := [1, 2, -2, 0, 1, 0, 0, 0, 1]
def label4104 : Mat3 := [1, 2, -2, 0, 2, -1, 0, -1, 1]
def label4105 : Mat3 := [1, 2, -2, 1, 1, 0, 0, -1, 1]
def label4133 : Mat3 := [1, 2, -1, 0, 1, 0, 0, -1, 1]
def label4195 : Mat3 := [1, 2, 0, 0, 1, 0, 0, 0, 1]
def label4209 : Mat3 := [1, 2, 0, 0, 1, 1, 0, -1, 0]
def label4318 : Mat3 := [1, 3, -3, 0, 1, 0, 0, -1, 1]
def label4321 : Mat3 := [1, 3, -2, 0, 1, 0, 0, -1, 1]
def label4362 : Mat3 := [1, 4, -2, 0, 1, 0, 0, -2, 1]
def label4394 : Mat3 := [2, -3, 0, 1, -1, 0, 0, 0, 1]
def label4454 : Mat3 := [2, -1, -2, -1, 1, 0, 0, 0, 1]
def label4468 : Mat3 := [2, -1, -2, 1, 0, -1, 0, 0, 1]
def label4469 : Mat3 := [2, -1, -2, 1, 0, -1, 0, 1, 1]
def label4515 : Mat3 := [2, -1, -1, 1, 0, -1, 0, 0, 1]
def label4517 : Mat3 := [2, -1, -1, 1, 0, 0, 0, 0, 1]
def label4562 : Mat3 := [2, -1, 0, -1, 1, 0, 0, 0, 1]
def label4592 : Mat3 := [2, -1, 0, 1, 0, 0, -1, 0, 1]
def label4593 : Mat3 := [2, -1, 0, 1, 0, 0, -1, 1, 1]
def label4594 : Mat3 := [2, -1, 0, 1, 0, 0, 0, -1, 1]
def label4595 : Mat3 := [2, -1, 0, 1, 0, 0, 0, 0, 1]
def label4596 : Mat3 := [2, -1, 0, 1, 0, 0, 0, 1, 1]
def label4597 : Mat3 := [2, -1, 0, 1, 0, 0, 1, -1, 1]
def label4598 : Mat3 := [2, -1, 0, 1, 0, 0, 1, 0, 1]
def label4647 : Mat3 := [2, -1, 1, 1, 0, 0, 0, 0, 1]
def label4649 : Mat3 := [2, -1, 1, 1, 0, 1, 0, 0, 1]
def label4671 : Mat3 := [2, -1, 2, 1, 0, 1, 0, -1, 1]
def label4672 : Mat3 := [2, -1, 2, 1, 0, 1, 0, 0, 1]
def label4736 : Mat3 := [2, 0, -1, 0, 1, 0, -1, 0, 1]
def label4750 : Mat3 := [2, 0, -1, 1, 0, -1, 0, 1, 1]
def label4817 : Mat3 := [2, 0, 1, 0, 1, 0, 1, 0, 1]
def label4830 : Mat3 := [2, 0, 1, 1, 0, 1, 0, -1, 1]
def label4874 : Mat3 := [2, 1, -4, 1, 1, -2, 0, 0, 1]
def label4878 : Mat3 := [2, 1, -3, 1, 1, -2, 0, 0, 1]
def label4886 : Mat3 := [2, 1, -2, 1, 1, -2, 0, 0, 1]
def label4889 : Mat3 := [2, 1, -2, 1, 1, -1, -1, 0, 2]
def label4890 : Mat3 := [2, 1, -2, 1, 1, -1, 0, -1, 1]
def label4891 : Mat3 := [2, 1, -2, 1, 1, -1, 0, 0, 1]
def label4892 : Mat3 := [2, 1, -2, 1, 1, -1, 0, 1, 1]
def label4893 : Mat3 := [2, 1, -2, 1, 1, -1, 1, 0, 0]
def label4897 : Mat3 := [2, 1, -2, 1, 1, 0, 0, 0, 1]
def label4923 : Mat3 := [2, 1, -1, 1, 1, -1, -1, 0, 1]
def label4924 : Mat3 := [2, 1, -1, 1, 1, -1, 0, -1, 2]
def label4925 : Mat3 := [2, 1, -1, 1, 1, -1, 0, 0, 1]
def label4926 : Mat3 := [2, 1, -1, 1, 1, -1, 0, 1, 0]
def label4927 : Mat3 := [2, 1, -1, 1, 1, -1, 1, 0, 1]
def label4935 : Mat3 := [2, 1, -1, 1, 1, 0, 0, 0, 1]
def label4984 : Mat3 := [2, 1, 0, 1, 1, 0, -2, 0, 1]
def label4986 : Mat3 := [2, 1, 0, 1, 1, 0, -1, -1, 1]
def label4987 : Mat3 := [2, 1, 0, 1, 1, 0, -1, 0, 1]
def label4988 : Mat3 := [2, 1, 0, 1, 1, 0, -1, 1, 1]
def label4989 : Mat3 := [2, 1, 0, 1, 1, 0, 0, -2, 1]
def label4990 : Mat3 := [2, 1, 0, 1, 1, 0, 0, -1, 1]
def label4991 : Mat3 := [2, 1, 0, 1, 1, 0, 0, 0, 1]
def label4992 : Mat3 := [2, 1, 0, 1, 1, 0, 0, 1, 1]
def label4993 : Mat3 := [2, 1, 0, 1, 1, 0, 0, 2, 1]
def label4994 : Mat3 := [2, 1, 0, 1, 1, 0, 1, -1, 1]
def label4995 : Mat3 := [2, 1, 0, 1, 1, 0, 1, 0, 1]
def label4996 : Mat3 := [2, 1, 0, 1, 1, 0, 1, 1, 1]
def label4998 : Mat3 := [2, 1, 0, 1, 1, 0, 2, 0, 1]
def label5055 : Mat3 := [2, 1, 1, 1, 1, 0, 0, 0, 1]
def label5063 : Mat3 := [2, 1, 1, 1, 1, 1, -1, 0, 1]
def label5064 : Mat3 := [2, 1, 1, 1, 1, 1, 0, -1, 0]
def label5065 : Mat3 := [2, 1, 1, 1, 1, 1, 0, 0, 1]
def label5066 : Mat3 := [2, 1, 1, 1, 1, 1, 0, 1, 2]
def label5067 : Mat3 := [2, 1, 1, 1, 1, 1, 1, 0, 1]
def label5092 : Mat3 := [2, 1, 2, 1, 1, 1, -1, 0, 0]
def label5093 : Mat3 := [2, 1, 2, 1, 1, 1, 0, -1, 1]
def label5094 : Mat3 := [2, 1, 2, 1, 1, 1, 0, 0, 1]
def label5095 : Mat3 := [2, 1, 2, 1, 1, 1, 0, 1, 1]
def label5096 : Mat3 := [2, 1, 2, 1, 1, 1, 1, 0, 2]
def label5099 : Mat3 := [2, 1, 2, 1, 1, 2, 0, 0, 1]
def label5106 : Mat3 := [2, 1, 3, 1, 1, 2, 0, 0, 1]
def label5108 : Mat3 := [2, 1, 4, 1, 1, 2, 0, 0, 1]
def label5126 : Mat3 := [2, 2, -1, 1, 2, -1, 0, -1, 1]
def label5144 : Mat3 := [2, 2, 1, 1, 2, 1, 0, 1, 1]
def label5150 : Mat3 := [2, 3, -3, 1, 2, -2, 0, 0, 1]
def label5151 : Mat3 := [2, 3, -2, 1, 2, -1, 0, -1, 1]
def label5152 : Mat3 := [2, 3, -2, 1, 2, -1, 0, 0, 1]
def label5156 : Mat3 := [2, 3, -1, 1, 2, -1, 0, 0, 1]
def label5163 : Mat3 := [2, 3, 0, 1, 2, 0, -1, -1, 1]
def label5164 : Mat3 := [2, 3, 0, 1, 2, 0, -1, 0, 1]
def label5165 : Mat3 := [2, 3, 0, 1, 2, 0, 0, -1, 1]
def label5166 : Mat3 := [2, 3, 0, 1, 2, 0, 0, 0, 1]
def label5167 : Mat3 := [2, 3, 0, 1, 2, 0, 0, 1, 1]
def label5168 : Mat3 := [2, 3, 0, 1, 2, 0, 1, 0, 1]
def label5169 : Mat3 := [2, 3, 0, 1, 2, 0, 1, 1, 1]
def label5178 : Mat3 := [2, 3, 1, 1, 2, 1, 0, 0, 1]
def label5180 : Mat3 := [2, 3, 2, 1, 2, 1, 0, 0, 1]
def label5181 : Mat3 := [2, 3, 2, 1, 2, 1, 0, 1, 1]
def label5183 : Mat3 := [2, 3, 3, 1, 2, 2, 0, 0, 1]
def label5186 : Mat3 := [2, 5, 0, 1, 3, 0, 0, 0, 1]
def label5189 : Mat3 := [3, -3, -2, 0, 1, 0, -1, 1, 1]
def label5194 : Mat3 := [3, -2, -2, -1, 1, 0, -1, 1, 1]
def label5197 : Mat3 := [3, -2, -2, 0, 1, 0, -1, 1, 1]
def label5218 : Mat3 := [3, -2, 0, 2, -1, 0, 0, 0, 1]
def label5235 : Mat3 := [3, -1, -2, 0, 1, 0, -1, 0, 1]
def label5260 : Mat3 := [3, -1, 0, 1, 0, 0, 0, 0, 1]
def label5277 : Mat3 := [3, 0, -5, 0, 1, 0, -1, 0, 2]
def label5281 : Mat3 := [3, 0, -2, -1, 1, 0, -1, 0, 1]
def label5282 : Mat3 := [3, 0, -2, -1, 1, 1, -1, 0, 1]
def label5283 : Mat3 := [3, 0, -2, 0, 1, -1, -1, 0, 1]
def label5286 : Mat3 := [3, 0, -2, 0, 1, 0, -1, 0, 1]
def label5289 : Mat3 := [3, 0, -2, 0, 1, 1, -1, 0, 1]
def label5290 : Mat3 := [3, 0, -2, 1, 1, -1, -1, 0, 1]
def label5291 : Mat3 := [3, 0, -2, 1, 1, 0, -1, 0, 1]
def label5314 : Mat3 := [3, 0, 1, 0, 1, 0, -1, 0, 0]
def label5341 : Mat3 := [3, 1, -3, 2, 1, -2, 0, 0, 1]
def label5343 : Mat3 := [3, 1, -2, 0, 1, 0, -1, 0, 1]
def label5347 : Mat3 := [3, 1, -2, 2, 1, -1, 0, 0, 1]
def label5353 : Mat3 := [3, 1, -1, 2, 1, -1, -1, 0, 1]
def label5354 : Mat3 := [3, 1, -1, 2, 1, -1, 0, 0, 1]
def label5361 : Mat3 := [3, 1, 0, 2, 1, 0, -1, -1, 1]
def label5362 : Mat3 := [3, 1, 0, 2, 1, 0, -1, 0, 1]
def label5363 : Mat3 := [3, 1, 0, 2, 1, 0, 0, -1, 1]
def label5364 : Mat3 := [3, 1, 0, 2, 1, 0, 0, 0, 1]
def label5365 : Mat3 := [3, 1, 0, 2, 1, 0, 0, 1, 1]
def label5366 : Mat3 := [3, 1, 0, 2, 1, 0, 1, 0, 1]
def label5367 : Mat3 := [3, 1, 0, 2, 1, 0, 1, 1, 1]
def label5378 : Mat3 := [3, 1, 1, 2, 1, 1, 0, 0, 1]
def label5379 : Mat3 := [3, 1, 1, 2, 1, 1, 1, 0, 1]
def label5385 : Mat3 := [3, 1, 2, 2, 1, 1, 0, 0, 1]
def label5387 : Mat3 := [3, 1, 3, 2, 1, 2, 0, 0, 1]
def label5389 : Mat3 := [3, 2, -2, 0, 1, 0, -1, -1, 1]
def label5392 : Mat3 := [3, 2, -2, 1, 1, 0, -1, -1, 1]
def label5425 : Mat3 := [3, 3, -2, 0, 1, 0, -1, -1, 1]
def label5429 : Mat3 := [3, 4, 0, 2, 3, 0, 0, 0, 1]
def label5437 : Mat3 := [4, 0, -3, 0, 1, 0, -1, 0, 1]
def label5441 : Mat3 := [4, 1, -2, 2, 1, -1, -1, 0, 1]
def label5442 : Mat3 := [4, 1, 0, 3, 1, 0, 0, 0, 1]
def label5443 : Mat3 := [4, 1, 2, 2, 1, 1, 1, 0, 1]
def label5450 : Mat3 := [5, 0, -2, 0, 1, 0, -2, 0, 1]
def label5454 : Mat3 := [5, 3, 0, 3, 2, 0, 0, 0, 1]
def generators : List Mat3 := [[1, -1, 0, 0, 1, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0, 0, 1], [1, 0, -1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0, 0, 1], [1, 0, 0, -1, 1, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0, 0, 0, 1], [1, 0, 0, 0, 1, -1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 1, 0, -1, 0, 1], [1, 0, 0, 0, 1, 0, 1, 0, 1], [1, 0, 0, 0, 1, 0, 0, -1, 1], [1, 0, 0, 0, 1, 0, 0, 1, 1]]
def rowBuckets0 : List (Poly Mat3) := [[(label2376, -120000000000000), (label2376, -120000000000000)], [(label3722, 10000000000000), (label2822, 10000000000000), (label2822, 10000000000000), (label3722, 10000000000000)], [], [(label2377, 10000000000000), (label1472, 10000000000000)], [], [(label2605, 10000000000000), (label2592, 10000000000000)], [(label2382, 10000000000000)], [(label3727, 10000000000000)], [], [(label4195, 10000000000000), (label2383, 10000000000000), (label2383, 10000000000000)], [(label3495, 10000000000000), (label1525, 10000000000000), (label2494, 10000000000000), (label2826, 10000000000000), (label3728, 10000000000000), (label2610, 10000000000000)], [], [], [(label2116, 10000000000000), (label2247, 10000000000000)], [(label2611, -120000000000000), (label2611, -120000000000000)], [(label1221, 10000000000000), (label1221, 10000000000000)], [], [], [(label4991, 10000000000000), (label1222, 10000000000000), (label2402, 10000000000000), (label2022, 10000000000000), (label2612, 10000000000000)], [], [], [], [(label4562, 10000000000000)], [(label2617, 10000000000000), (label2027, 10000000000000)], [], [(label3746, 10000000000000)], [(label2028, -120000000000000), (label2028, -120000000000000)], [(label2407, 10000000000000), (label2407, 10000000000000)], [], [(label2029, 10000000000000)], [], [], [], [], [(label3516, 10000000000000), (label550, 10000000000000), (label2034, 10000000000000)], [], [], [(label3517, 10000000000000), (label3517, 10000000000000), (label3323, 10000000000000)], [(label1653, 10000000000000), (label2655, 10000000000000)], [(label1938, 10000000000000)], [], [(label2630, 10000000000000)], [(label1241, 10000000000000)], [], [], [], [], [], [], [(label3125, 10000000000000), (label3125, 10000000000000)], [(label4736, 10000000000000)], [], [], [(label2047, 10000000000000), (label2047, 10000000000000)], [], [], [], [], [(label3637, 10000000000000), (label2507, 10000000000000)], [], [], [(label2526, 10000000000000)], [(label1672, 10000000000000), (label3062, 10000000000000)], [(label3208, 10000000000000)], [], [(label1673, 10000000000000), (label1847, 10000000000000), (label1673, 10000000000000)], [(label1954, 10000000000000), (label3810, 10000000000000), (label2762, 10000000000000), (label3138, 10000000000000)], [], [], [], [(label341, 10000000000000), (label1368, 10000000000000)], [], [], [(label3143, 10000000000000)], [], [(label2766, 10000000000000), (label2766, 10000000000000)], [(label3144, -120000000000000), (label3144, -120000000000000)], [(label1422, 10000000000000)], [], [(label2539, 10000000000000), (label3145, 10000000000000)], [], [], [], [], [], [], [(label3150, 10000000000000), (label2544, 10000000000000)], [(label3929, 10000000000000), (label3929, 10000000000000)], [(label2545, -120000000000000), (label2545, -120000000000000)], [(label3078, 10000000000000), (label2915, 10000000000000)], [(label3930, 10000000000000), (label3224, 10000000000000), (label2787, 10000000000000), (label2546, 10000000000000)], [], [], [(label975, 10000000000000), (label2788, 10000000000000), (label2788, 10000000000000)], [], [(label1440, 10000000000000)], [], [(label2564, 10000000000000), (label2551, 10000000000000)], [(label2668, 10000000000000), (label1441, 10000000000000)], [(label2793, 10000000000000), (label3696, 10000000000000)], [], [(label1446, 10000000000000), (label2345, 10000000000000), (label2345, 10000000000000), (label1446, 10000000000000)], [(label2794, -120000000000000), (label2794, -120000000000000)], [(label3163, 10000000000000), (label3163, 10000000000000), (label2569, 10000000000000), (label2569, 10000000000000)], [(label1447, -120000000000000), (label1447, -120000000000000)], [(label2795, 10000000000000)], [(label2570, -120000000000000), (label686, 10000000000000), (label2570, -120000000000000)], [(label1448, 10000000000000), (label1448, 10000000000000)], [], [(label2571, 10000000000000), (label2576, 10000000000000), (label2571, 10000000000000)], [(label2350, 10000000000000), (label1453, 10000000000000)], [(label2800, 10000000000000), (label2800, 10000000000000)], [(label2577, -120000000000000), (label2577, -120000000000000)], [(label1454, 10000000000000)], [(label3951, 10000000000000), (label2100, 10000000000000), (label3714, 10000000000000), (label2801, 10000000000000)], [(label2578, 1440000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000), (label2578, 10000000000000)], [], [(label3715, 10000000000000)], [(label2579, -120000000000000), (label4817, 10000000000000), (label2579, -120000000000000)], [(label2369, 10000000000000), (label2369, 10000000000000)], [], [(label2585, 10000000000000), (label2585, 10000000000000), (label2580, 10000000000000)], [(label2370, 10000000000000)], [(label3720, 10000000000000), (label3720, 10000000000000)], [(label2586, -120000000000000), (label2586, -120000000000000)], [(label2375, 10000000000000)], [(label3721, -120000000000000), (label3721, -120000000000000), (label477, 10000000000000)], [(label2009, 10000000000000), (label2009, 10000000000000), (label2587, 10000000000000), (label2587, 10000000000000)]]
def rowBuckets1 : List (Poly Mat3) := [[(label2376, 1000000000000)], [], [], [], [], [], [], [], [], [], [], [], [], [], [(label2611, 1000000000000)], [], [], [], [], [], [], [], [], [], [], [], [(label2028, 1000000000000)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [(label3144, 1000000000000)], [], [], [], [], [], [], [], [], [], [], [], [(label2545, 1000000000000)], [], [], [], [], [], [], [], [], [], [], [], [], [], [(label2794, 1000000000000)], [], [(label1447, 1000000000000)], [], [(label2570, 1000000000000)], [], [], [], [], [], [(label2577, 1000000000000)], [], [], [(label2578, -12000000000000)], [], [], [(label2579, 1000000000000)], [], [], [], [], [], [(label2586, 1000000000000)], [], [(label3721, 1000000000000)], []]
def rowBuckets10 : List (Poly Mat3) := [[(label4984, 47774511150)], [(label3722, 752131231670)], [(label5064, 157101550460), (label5168, 921360)], [], [(label4647, -250726251320), (label3726, -174411380230)], [(label5156, -619910), (label5169, 599640)], [(label4986, 135386459000), (label5065, -1312797185470)], [(label3727, 867311081290)], [], [(label4987, -1312796965910), (label4195, -1550820877490)], [(label1525, 101737112330), (label3495, 867314183540), (label5066, 1964690)], [], [(label4988, 23372686820), (label4989, 5720180)], [], [], [(label4990, -130995085810), (label5067, -451940702060)], [], [], [(label4991, 1064097815460)], [(label3499, -451934735920)], [], [(label4923, -451935201950), (label4992, -130986916150)], [], [], [(label4993, -1816560), (label4994, 23366334090)], [(label594, 157098279000)], [(label5361, -539980), (label5378, 144274155300)], [(label4995, -1312787680830)], [(label4924, 2993130)], [(label5362, 144271392660), (label5443, 250330)], [(label4925, -1312796462130), (label4996, 135383401990)], [(label4649, 327708735360)], [(label4926, 157100193380)], [(label786, 157099908280)], [(label4592, -250724768870)], [(label5363, -1747720), (label5379, 410684357030)], [(label4998, 47774468250)], [(label4593, 327711364860), (label3517, 752128479320)], [(label5364, -524600476830)], [(label4830, 219971394780), (label4927, 410678567190)], [(label4594, -47153632160)], [(label5353, 410680398660), (label5365, -3282160), (label5151, 645720)], [(label4886, 47773282540)], [(label4595, -9482878430)], [(label5108, -2422270), (label5152, -3494530)], [], [(label4596, -47152852130)], [(label5366, 144269621800)], [], [(label4597, 327705212320), (label3409, -174410818340)], [(label5354, 144273270190), (label5367, 1949280)], [], [(label4598, -250721559930)], [], [], [(label4515, 327705698480)], [(label5150, -663910)], [(label4935, 135389501510)], [(label5442, -917140), (label5183, -3970050)], [], [], [(label4889, -71082440900)], [], [], [], [], [(label4890, 873790), (label5454, -128630)], [], [(label4394, 20865269080)], [(label4891, -130993127490), (label4750, 219973679340)], [(label5180, -2941930)], [], [(label4892, -591840)], [(label5181, 589030)], [], [(label4044, -174415043920)], [(label5260, 121430564430)], [(label4893, 219970968180)], [], [], [(label223, -20870381590)], [(label4878, 23372620810)], [(label4517, -250728916460)], [(label5106, 23376597360)], [], [(label5092, 219969542660)], [], [(label3929, 752133157190)], [], [(label5347, 1595800)], [], [], [(label5093, 2225760)], [], [(label4468, -47151330140)], [(label5094, -130988818170)], [(label5186, -2113220)], [(label4469, -1361470)], [(label5095, -130080)], [(label5218, 1694350)], [], [(label5341, -1232670), (label5144, -71080922070)], [], [(label5387, -3478390)], [], [(label3947, -451936024140), (label5096, -71076953480), (label5429, 3550240)], [(label686, -1238410116000)], [(label5055, 135390556740)], [], [(label5163, 3928280), (label5178, 5974790)], [], [], [(label5164, -457330)], [(label5441, 1381790)], [(label3951, 867318187240)], [(label2578, -1773154728580), (label5385, 3148440)], [], [(label4671, -2619820), (label3715, 867312105150)], [(label5165, -6464620)], [(label5126, -71079372030)], [(label4672, -47151524540), (label4874, 175670), (label3716, -174416642590)], [(label5166, 7112310)], [(label5099, 47770856040)], [(label3720, 752127719070)], [(label5167, -2566000)], [(label5063, 410681241400)], [(label3721, 1222741326310)], []]
def rowBuckets100 : List (Poly Mat3) := [[(label5392, 2680070), (label45, -316106956910)], [], [], [(label44, 468088572380), (label1803, 5752550)], [(label5314, -60716414120)], [(label100, -2585940), (label5343, -144274525170)], [(label91, 468086575460), (label4318, 855110)], [(label5281, 643370), (label905, 633970898380)], [(label4077, -661280), (label3386, 266884838390)], [], [(label4104, 47774313300)], [(label1835, 387047107410), (label13, 5311810)], [(label1929, 633974173290)], [(label5389, 2438270), (label2116, -635243784750)], [], [(label1221, 988343910570), (label1792, -5467600)], [(label1794, -1170730), (label3433, 175670)], [], [(label1222, -635243616440)], [(label93, -316105050150)], [(label1104, -2422270)], [(label5289, 1109320)], [], [], [(label14, -290070), (label5425, -494460)], [(label1873, 490738553450)], [(label882, 47772519780), (label2028, 4442423329010)], [(label1114, -115337645770)], [], [], [(label4088, 311468436090)], [], [(label107, 231545327360), (label4209, 266882289350)], [(label886, 124120)], [(label3516, -635241908840), (label5282, -144276149030)], [], [], [(label3517, 988346484230)], [(label1838, -1502448208590)], [(label1886, 47010), (label1938, -635246311040)], [(label2125, 633971631830)], [], [], [(label868, 387048041630)], [], [(label4133, 633973455730)], [(label869, -948849909390)], [], [], [(label1, -2773680), (label3409, -135304480020)], [(label4736, -1436830319400)], [(label1813, 183119089930), (label5450, -5985160)], [(label1878, -948852430190)], [(label2047, 988348157030)], [(label809, 1162310), (label1119, -1502442145530)], [], [(label591, 311468531370)], [(label1120, 490743474710)], [], [(label862, 991230)], [], [], [], [], [(label1806, -1673320), (label3529, -135306370140)], [(label1847, 809289768800)], [(label866, 311464641830), (label5437, 152010)], [], [(label961, 266885688890)], [], [], [(label4105, 1102910)], [], [(label3417, 490736980820)], [], [], [(label3418, -1502451810570)], [(label1797, 4619970)], [(label1816, -948870138750)], [(label1881, 183118516740)], [(label89, 20867985900)], [(label1128, -135305589670)], [(label5290, -144275674040)], [], [(label4101, -948861878910)], [(label856, -4654040)], [], [(label4102, 387051248510)], [(label1147, 266885943890), (label194, 4412920), (label3383, -115337742810)], [], [], [(label1807, 1119030), (label1808, 2824610)], [(label5189, 1616510), (label1856, -1502448974390)], [(label1095, 2496700), (label811, 183117405350), (label99, -316111523970)], [], [(label5283, -900520), (label4321, 183116518040)], [(label4897, 47774478540)], [(label4087, 4042260)], [], [], [(label4454, 47774435640)], [(label804, -2216250), (label195, 499570)], [], [(label5197, 6163610), (label4362, -1390830), (label3422, -115336803640)], [(label1800, -4432090), (label854, -132800)], [(label1821, 490745585360)], [(label101, 468087951250)], [(label92, 1240490)], [], [(label5291, -2399110), (label151, 468089365610)], [], [(label5235, -144273741430)], [(label150, -316106381030), (label5277, -2649180)], [], [(label6, -596800)], [(label2578, -2779302786760), (label3385, 4286410)], [(label1207, -135305061440), (label5194, -616460)], [(label1793, 4072650)], [], [(label1859, 387048352430)], [(label242, 311464780550), (label1097, -115338279510), (label96, -432942837430)], [], [(label5286, 524601567950)], [(label4082, -524450)], [], [], [(label477, -1238409491750)], [(label2009, 988348111350)]]
end NuclearUltrapower.SOS
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
section BucketSemantics
variable {α A β γ : Type*} [DecidableEq α] [AddCommGroup A]

omit [DecidableEq α] in
@[simp] theorem eval_append (f : α → A) (p q : Poly α) :
    eval f (p ++ q) = eval f p + eval f q := by
  simp only [eval, List.map_append, List.sum_append]

end BucketSemantics
end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS
def toMatrix (a : Mat3) : Matrix (Fin 3) (Fin 3) ℤ := fun i j => entry a i j

abbrev SL := Matrix.SpecialLinearGroup (Fin 3) ℤ

/-- Total interpretation of a label; the certificate will establish det=1 at every label used. -/
def interpret (m : Mat3) : SL :=
  if h : (toMatrix m).det = 1 then ⟨toMatrix m,h⟩ else 1

end NuclearUltrapower.SOS

end

end OAI
end


