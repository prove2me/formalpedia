-- Prove2me | Definitions.Def_OAIQ229C012
-- name    : OAIQ229C012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T06:22:31.998144+00:00
-- url     : https://prove2.me/theorems/6b392d70-4af1-4e41-8aa3-e10f60a370b3
-- title:
--   Definitions bundle OAIQ229C012 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 314 declarations of OpenAI's Lean: 298 definitions and 16 theorems. The definitions and types are `OAI.CoarseAssembly.circleDegree`, `OAI.CoarseAssembly.circleUnitary`, `OAI.CoarseAssembly.windingInterpolation`, `OAI.NuclearUltrapower.SOS.label1040`, `OAI.NuclearUltrapower.SOS.label1051`, `OAI.NuclearUltrapower.SOS.label1072`, `OAI.NuclearUltrapower.SOS.label1079`, `OAI.NuclearUltrapower.SOS.label1089`, `OAI.NuclearUltrapower.SOS.label1090`, `OAI.NuclearUltrapower.SOS.label1099`, `OAI.NuclearUltrapower.SOS.label1101`, `OAI.NuclearUltrapower.SOS.label119`, `OAI.NuclearUltrapower.SOS.label1236`, `OAI.NuclearUltrapower.SOS.label1246`, `OAI.NuclearUltrapower.SOS.label127`, `OAI.NuclearUltrapower.SOS.label140`, `OAI.NuclearUltrapower.SOS.label1473`, `OAI.NuclearUltrapower.SOS.label1622`, `OAI.NuclearUltrapower.SOS.label1654`, `OAI.NuclearUltrapower.SOS.label1658`, `OAI.NuclearUltrapower.SOS.label1674`, `OAI.NuclearUltrapower.SOS.label1688`, `OAI.NuclearUltrapower.SOS.label1710`, `OAI.NuclearUltrapower.SOS.label1729`, `OAI.NuclearUltrapower.SOS.label1761`, `OAI.NuclearUltrapower.SOS.label1762`, `OAI.NuclearUltrapower.SOS.label1770`, `OAI.NuclearUltrapower.SOS.label1771`, `OAI.NuclearUltrapower.SOS.label1775`, `OAI.NuclearUltrapower.SOS.label1787`, `OAI.NuclearUltrapower.SOS.label1789`, `OAI.NuclearUltrapower.SOS.label1791`, `OAI.NuclearUltrapower.SOS.label1834`, `OAI.NuclearUltrapower.SOS.label1982`, `OAI.NuclearUltrapower.SOS.label1993`, `OAI.NuclearUltrapower.SOS.label2056`, `OAI.NuclearUltrapower.SOS.label230`, `OAI.NuclearUltrapower.SOS.label2318`, `OAI.NuclearUltrapower.SOS.label233`, `OAI.NuclearUltrapower.SOS.label234` and 258 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_CirclePairing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/CirclePairing.lean), [`CoarseAssembly_FilledDisc`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FilledDisc.lean), [`CoarseAssembly_LatticeHat`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/LatticeHat.lean), [`CoarseAssembly_LoopCircle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/LoopCircle.lean), [`CoarseAssembly_ProjectionBlocks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ProjectionBlocks.lean), [`CoarseAssembly_SpatialBlocks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SpatialBlocks.lean), [`CoarseAssembly_TransferLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/TransferLift.lean), [`CoarseAssembly_WindingHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/WindingHomotopy.lean), [`CoarseAssembly_WindingIndexEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/WindingIndexEvaluation.lean), `NuclearUltrapower_SOSResidual`, `NuclearUltrapower_SOSSemantics`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C000`, `OAIQ229C001`, `OAIQ229C002` and `OAIQ229C003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C020`, `OAIQ229C021`, `OAIQ229C022` and `OAIQ229C023`; the statements `OAI_NuclearUltrapower_SOS_row_length_10` and `OAI_NuclearUltrapower_SOS_row_partition_10`; the proofs of `OAI_NuclearUltrapower_SOS_eval_buckets`, `OAI.NuclearUltrapower.SOS.eval_buckets_ca`, `OAI_NuclearUltrapower_SOS_eval_mul`, `OAI.NuclearUltrapower.SOS.eval_mul_ca`, `OAI_NuclearUltrapower_SOS_intL1_flatten`, `OAI.NuclearUltrapower.SOS.intL1_flatten_ca`, `OAI_NuclearUltrapower_SOS_row_length_10`, `OAI_NuclearUltrapower_SOS_row_partition_10`, `OAI_NuclearUltrapower_SOS_support_compress_iff` and `OAI.NuclearUltrapower.SOS.support_compress_iff_ca`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
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
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.TransferInstance
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C000
import Definitions.Def_OAIQ229C001
import Definitions.Def_OAIQ229C002
import Definitions.Def_OAIQ229C003

section
-- module Solutions.Q229_CA.CoarseAssembly_LoopCircle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parametrizing a closed path by the circle

The interval endpoints are identified using Mathlib's quotient-circle
construction. The resulting continuous map agrees with the path on the
entire closed interval, including its identified endpoint.
-/

noncomputable section

namespace CoarseAssembly

open unitInterval

variable {Y : Type*} [TopologicalSpace Y] {y : Y}

theorem circle_parameter_surjective : Function.Surjective
    (fun t : unitInterval => ((t : ℝ) : WindingCircle)) := by
  intro z
  have hz : z ∈ (Set.univ : Set WindingCircle) := Set.mem_univ _
  rw [← AddCircle.coe_image_Icc_eq (1 : ℝ) 0] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact ⟨⟨t, by simpa using ht⟩, rfl⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CirclePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise published circle-index input

Only the scalar-unitary index pairing, its naturality for a parametrized
loop, and the classical winding formula are assumed. The domain groups
are the Fredholm-module groups.

References: Blackadar, *K-Theory for Operator Algebras*, 2nd ed. (1998),
Proposition 18.7.1 and Corollary 18.10.3; Khalkhali, *Basic Noncommutative
Geometry* (2009), Example 4.2.4, with the sign convention of manuscript §2.3.
-/

noncomputable section

namespace CoarseAssembly

open Analytic unitInterval

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The scalar unitary represented by a circle-valued map. -/
def circleUnitary (f : C(X, WindingCircle)) : C(X, Circle) :=
  ⟨fun x => AddCircle.toCircle (f x), AddCircle.continuous_toCircle.comp f.continuous⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SpatialBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled block matrices on the spatial vertex module

The bounded block-matrix construction is transported through the explicit
Hilbert-sum equivalence. Its vertex entries are the entries of the original
blocks, which allows propagation and local compactness to be checked there.
-/

noncomputable section

namespace CoarseAssembly

variable {I : Type*} {Q : I → Type*} {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

variable [DecidableEq I] [∀ i, DecidableEq (Q i)]

section Matrix

variable (rows cols : I → Finset I) (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j)
variable (B : ∀ i j, lp (fun _ : Q j => H) 2 →L[ℂ] lp (fun _ : Q i => H) 2)
variable (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
variable (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
variable (hB : ∀ i j, j ∈ rows i → ‖B i j‖ ≤ C)

theorem spatialBlocks_single (i j : I) (q : Q i) (r : Q j) (h : H) :
    spatialBlocks rows cols hdual B N C hC hr hc hB (lp.single 2 ⟨j, r⟩ h) ⟨i, q⟩ =
      if j ∈ rows i then B i j (lp.single 2 r h) q else 0 := by
  rw [spatialBlocks_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply]
  by_cases hj : j ∈ rows i
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · rw [rowVector_single_same]
    · intro k hk hkj
      rw [rowVector_single_ne hkj, map_zero]
      rfl
    · exact fun hn => (hn hj).elim
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := fun h => hj (h ▸ hk)
    rw [rowVector_single_ne hkj, map_zero]
    rfl

end Matrix

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

variable (rows cols : I → Finset I) (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j)
variable (B : ∀ i j, lp (fun _ : Q j => H) 2 →L[ℂ] lp (fun _ : Q i => H) 2)
variable (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
variable (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
variable (hB : ∀ i j, j ∈ rows i → ‖B i j‖ ≤ C)

local notation "Aₗ" => spatialBlocks rows cols hdual B N C hC hr hc hB

omit [CompleteSpace H] in
theorem spatialBlocks_entry (i j : I) (q : Q i) (r : Q j) :
    entry Aₗ ⟨i, q⟩ ⟨j, r⟩ = if j ∈ rows i then fiberBlockEntry (B i j) q r else 0 := by
  apply ContinuousLinearMap.ext
  intro h
  rw [entry_apply]
  rw [spatialBlocks_single]
  split_ifs <;> rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LatticeHat
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.CoarseAssembly.discHatWeights_apply _root_.OAI.CoarseAssembly.latticeCharge_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Piecewise linear hat functions of the triangular lattice

The nodal function at a lattice vertex is `max (0, 1 - ρ(p-v))`, where
`ρ(x,y) = max(|x|, |y|, |x+y|)`. These are the barycentric coordinate
functions for the filled triangular lattice. Their partition of unity
maps the filled hexagons into Rips space.
-/

noncomputable section

namespace CoarseAssembly

theorem realLatticeRadius_le_iff {p : ℝ × ℝ} {a : ℝ} :
    realLatticeRadius p ≤ a ↔ |p.1| ≤ a ∧ |p.2| ≤ a ∧ |p.1 + p.2| ≤ a := by
  simp only [realLatticeRadius, max_le_iff, and_assoc]

/-- The four cell functions sum to one; at most three of them are positive. -/
theorem hatKernel_partition {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hs₁ : s ≤ 1) (ht₁ : t ≤ 1) :
    hatKernel s t + hatKernel (s - 1) t + hatKernel s (t - 1) +
      hatKernel (s - 1) (t - 1) = 1 := by
  have r00 : realLatticeRadius (s, t) = s + t := by
    simp only [realLatticeRadius, abs_of_nonneg hs, abs_of_nonneg ht,
      abs_of_nonneg (add_nonneg hs ht)]
    rw [max_eq_right (max_le (by linarith) (by linarith))]
  have r11 : realLatticeRadius (s - 1, t - 1) = 2 - s - t := by
    rw [realLatticeRadius, abs_of_nonpos (by linarith : s - 1 ≤ 0),
      abs_of_nonpos (by linarith : t - 1 ≤ 0),
      abs_of_nonpos (by linarith : s - 1 + (t - 1) ≤ 0)]
    rw [max_eq_right (max_le (by linarith) (by linarith))]
    ring
  by_cases hst : s + t ≤ 1
  · have r10 : realLatticeRadius (s - 1, t) = 1 - s := by
      rw [realLatticeRadius, abs_of_nonpos (by linarith : s - 1 ≤ 0),
        abs_of_nonneg ht, abs_of_nonpos (by linarith : s - 1 + t ≤ 0)]
      rw [show max (-(s - 1)) t = -(s - 1) from max_eq_left (by linarith),
        max_eq_left (by linarith)]
      ring
    have r01 : realLatticeRadius (s, t - 1) = 1 - t := by
      rw [realLatticeRadius, abs_of_nonneg hs,
        abs_of_nonpos (by linarith : t - 1 ≤ 0),
        abs_of_nonpos (by linarith : s + (t - 1) ≤ 0)]
      rw [show max s (-(t - 1)) = -(t - 1) from max_eq_right (by linarith),
        max_eq_left (by linarith)]
      ring
    simp only [hatKernel, r00, r10, r01, r11]
    rw [max_eq_right (by linarith : 0 ≤ 1 - (s + t)),
      max_eq_right (by linarith : 0 ≤ 1 - (1 - s)),
      max_eq_right (by linarith : 0 ≤ 1 - (1 - t)),
      max_eq_left (by linarith : 1 - (2 - s - t) ≤ 0)]
    ring
  · have r10 : realLatticeRadius (s - 1, t) = t := by
      rw [realLatticeRadius, abs_of_nonpos (by linarith : s - 1 ≤ 0),
        abs_of_nonneg ht, abs_of_nonneg (by linarith : 0 ≤ s - 1 + t)]
      rw [show max (-(s - 1)) t = t from max_eq_right (by linarith),
        max_eq_left (by linarith)]
    have r01 : realLatticeRadius (s, t - 1) = s := by
      rw [realLatticeRadius, abs_of_nonneg hs,
        abs_of_nonpos (by linarith : t - 1 ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ s + (t - 1))]
      rw [show max s (-(t - 1)) = s from max_eq_left (by linarith),
        max_eq_left (by linarith)]
    simp only [hatKernel, r00, r10, r01, r11]
    rw [max_eq_left (by linarith : 1 - (s + t) ≤ 0),
      max_eq_right (by linarith : 0 ≤ 1 - t), max_eq_right (by linarith : 0 ≤ 1 - s),
      max_eq_right (by linarith : 0 ≤ 1 - (2 - s - t))]
    ring

theorem latticeHatWeights_total (p : ℝ × ℝ) :
    (latticeHatWeights p).sum (fun _ t => t) = 1 := by
  classical
  rw [latticeHatWeights, Finsupp.onFinset_sum (latticeHat_support_cell p) (by simp)]
  have hx : (⌊p.1⌋ : ℤ) ≠ ⌊p.1⌋ + 1 := by omega
  have hy : (⌊p.2⌋ : ℤ) ≠ ⌊p.2⌋ + 1 := by omega
  have hs : 0 ≤ p.1 - (⌊p.1⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le p.1)
  have ht : 0 ≤ p.2 - (⌊p.2⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le p.2)
  have hs₁ : p.1 - (⌊p.1⌋ : ℝ) ≤ 1 := by linarith [Int.lt_floor_add_one p.1]
  have ht₁ : p.2 - (⌊p.2⌋ : ℝ) ≤ 1 := by linarith [Int.lt_floor_add_one p.2]
  have h := hatKernel_partition hs ht hs₁ ht₁
  simp only [latticeCell, Finset.sum_product, Finset.sum_insert (Finset.notMem_singleton.mpr hx),
    Finset.sum_insert (Finset.notMem_singleton.mpr hy), Finset.sum_singleton, latticeHat,
    Int.cast_add, Int.cast_one, sub_add_eq_sub_sub]
  linarith

theorem latticeHat_in_disc {j : ℕ} {p : ℝ × ℝ}
    (hp : realLatticeRadius p ≤ j) {v : LatticeVertex} (hv : 0 < latticeHat p v) :
    latticeRadius v ≤ j := by
  have hp' := realLatticeRadius_le_iff.mp hp
  have hv' := (latticeHat_pos_iff p v).mp hv
  have bound (x n : ℝ) (hx : |x| ≤ j) (hn : |x - n| < 1) : |n| < (j : ℝ) + 1 := by
    rw [abs_le] at hx
    rw [abs_lt] at hn ⊢
    constructor <;> linarith
  have ha : |v.1| < (j : ℤ) + 1 := by exact_mod_cast bound p.1 v.1 hp'.1 hv'.1
  have hb : |v.2| < (j : ℤ) + 1 := by exact_mod_cast bound p.2 v.2 hp'.2.1 hv'.2.1
  have hc : |v.1 + v.2| < (j : ℤ) + 1 := by
    have hsum : |(p.1 + p.2) - ((v.1 : ℝ) + v.2)| < 1 := by
      convert hv'.2.2 using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    exact_mod_cast bound (p.1 + p.2) ((v.1 : ℝ) + v.2) hp'.2.2 hsum
  simp only [latticeRadius, max_le_iff]
  omega

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FilledDisc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual filled hexagonal discs

The compact polygon is contracted by radial scaling. The triangular-lattice
hat functions give a continuous map of this polygon into the scale-one Rips
realization of its lattice vertices. Thus the filling is constructed, not
assumed as an analytic vanishing premise.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips Analytic

theorem latticeHatWeights_disc_support (j : ℕ) (p : FilledDisc j) :
    ↑(latticeHatWeights p.val).support ⊆ Set.range (@Subtype.val LatticeVertex
      (fun v => latticeRadius v ≤ (j : ℤ))) := by
  intro v hv
  have hpos : 0 < latticeHat p.val v := lt_of_le_of_ne (latticeHat_nonneg _ _)
    (Finsupp.mem_support_iff.mp hv).symm
  exact ⟨⟨v, latticeHat_in_disc p.property hpos⟩, rfl⟩

theorem discHatWeights_total (j : ℕ) (p : FilledDisc j) :
    (discHatWeights j p).sum (fun _ t => t) = 1 := by
  have hm := Finsupp.embDomain_comapDomain
    (f := (⟨Subtype.val, Subtype.val_injective⟩ : Disc j ↪ LatticeVertex))
    (latticeHatWeights_disc_support j p)
  have hs := congrArg (fun f : LatticeVertex →₀ ℝ => f.sum (fun _ t => t)) hm
  simp only [Finsupp.sum_embDomain, latticeHatWeights_total] at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (fun f : Disc j →₀ ℝ => f.sum (fun _ t => t))
  apply Finsupp.ext
  intro v
  rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ProjectionBlocks
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

omit [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)] [CompleteSpace H] in
theorem flattenOperator_sub
    (A B : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    flattenOperator (A - B) = flattenOperator A - flattenOperator B := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext z
  rfl

omit [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)] in
theorem flattenOperator_mul
    (A B : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    flattenOperator (A * B) = flattenOperator A * flattenOperator B := by
  rw [flattenOperator_eq_conjugation, flattenOperator_eq_conjugation,
    flattenOperator_eq_conjugation, operatorConjugation_mul]

omit [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)] in
theorem flattenOperator_tendsto
    (A : ℕ → (lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2))
    (B : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2)
    (h : Filter.Tendsto A Filter.atTop (nhds B)) :
    Filter.Tendsto (fun n => flattenOperator (Q := Q) (H := H) (A n))
      Filter.atTop (nhds (flattenOperator B)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_iff_norm_sub_tendsto_zero.mp h)
  rw [← flattenOperator_sub]
  exact flattenOperator_norm_le _

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_WindingHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit homotopy from a lifted loop to its winding power -/

noncomputable section

namespace CoarseAssembly

open unitInterval

/-- The degree-`n` self-map of the additive circle. -/
def circleDegree (n : ℤ) : C(WindingCircle, WindingCircle) :=
  ⟨fun z => n • z, continuous_id.zsmul n⟩

theorem windingCircle_intCast (n : ℤ) : ((n : ℝ) : WindingCircle) = 0 := by
  have h : ((n • (1 : ℝ) : ℝ) : WindingCircle) = 0 := by
    rw [AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  simpa only [zsmul_eq_mul, mul_one] using h

/-- Straight-line interpolation of the real lift with `t ↦ n*t`. -/
def windingInterpolation (n : ℤ) (L : Path (0 : ℝ) (n : ℝ)) (s : unitInterval) :
    Path (0 : WindingCircle) 0 where
  toFun t := (((1 - (s : ℝ)) * L t + (s : ℝ) * n * (t : ℝ) : ℝ) : WindingCircle)
  continuous_toFun := (AddCircle.continuous_mk' 1).comp
    ((L.continuous.const_mul _).add (continuous_subtype_val.const_mul _))
  source' := by simp
  target' := by
    have he : (1 - (s : ℝ)) * (n : ℝ) + (s : ℝ) * n * 1 = n := by ring
    simp only [Path.target, Set.Icc.coe_one, he]
    exact windingCircle_intCast n

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_WindingIndexEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing the winding index formula to one generator evaluation

The pairing, its naturality, homotopy invariance and power law are proved.
Only an actual circle class with coordinate index one remains to construct.
-/

noncomputable section

namespace CoarseAssembly

open Analytic unitInterval

theorem circleUnitary_degree (n : ℤ) : circleUnitary (circleDegree n) =
    circleUnitary (ContinuousMap.id WindingCircle) ^ n := by
  apply ContinuousMap.ext
  intro z
  exact AddCircle.toCircle_zsmul z n

end CoarseAssembly

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
def label5 : Mat3 := [-2, -1, 0, 3, 1, 0, 0, 0, 1]
def label33 : Mat3 := [-1, -2, 0, 1, 1, 1, 0, 0, 1]
def label34 : Mat3 := [-1, -2, 0, 2, 3, 0, 0, 0, 1]
def label37 : Mat3 := [-1, -2, 1, 1, 1, 0, -1, -1, 1]
def label38 : Mat3 := [-1, -2, 1, 1, 1, 0, 0, 0, 1]
def label56 : Mat3 := [-1, -1, -1, 2, 1, 1, 0, 0, 1]
def label57 : Mat3 := [-1, -1, -1, 2, 1, 1, 1, 0, 1]
def label59 : Mat3 := [-1, -1, -1, 2, 1, 2, 0, 0, 1]
def label60 : Mat3 := [-1, -1, 0, 1, 0, 0, 0, 0, 1]
def label61 : Mat3 := [-1, -1, 0, 2, 1, -1, 0, 0, 1]
def label63 : Mat3 := [-1, -1, 0, 2, 1, 0, -1, -1, 1]
def label64 : Mat3 := [-1, -1, 0, 2, 1, 0, -1, 0, 1]
def label65 : Mat3 := [-1, -1, 0, 2, 1, 0, 0, -1, 1]
def label66 : Mat3 := [-1, -1, 0, 2, 1, 0, 0, 0, 1]
def label67 : Mat3 := [-1, -1, 0, 2, 1, 0, 0, 1, 1]
def label68 : Mat3 := [-1, -1, 0, 2, 1, 0, 1, 0, 1]
def label69 : Mat3 := [-1, -1, 0, 2, 1, 0, 1, 1, 1]
def label71 : Mat3 := [-1, -1, 0, 2, 1, 1, 0, 0, 1]
def label72 : Mat3 := [-1, -1, 0, 3, 2, 0, 0, 0, 1]
def label75 : Mat3 := [-1, -1, 1, 0, 1, 0, -2, 0, 1]
def label77 : Mat3 := [-1, -1, 1, 1, 1, 0, -1, 0, 1]
def label78 : Mat3 := [-1, -1, 1, 2, 1, -2, 0, 0, 1]
def label80 : Mat3 := [-1, -1, 1, 2, 1, -1, -1, 0, 1]
def label81 : Mat3 := [-1, -1, 1, 2, 1, -1, 0, 0, 1]
def label83 : Mat3 := [-1, -1, 1, 2, 1, 0, 0, 0, 1]
def label85 : Mat3 := [-1, -1, 2, 0, 1, 0, -1, 0, 1]
def label87 : Mat3 := [-1, -1, 2, 1, 1, -1, -1, 0, 1]
def label119 : Mat3 := [-1, 0, 0, 2, -1, 0, 0, 0, 1]
def label127 : Mat3 := [-1, 0, 1, 0, 1, 0, -2, 1, 1]
def label140 : Mat3 := [-1, 0, 2, 0, 1, 0, -1, 1, 1]
def label230 : Mat3 := [0, -2, -1, 1, 2, 1, 0, 1, 1]
def label233 : Mat3 := [0, -2, 1, 0, 1, 0, -1, -1, 1]
def label234 : Mat3 := [0, -2, 1, 0, 1, 0, -1, 0, 1]
def label237 : Mat3 := [0, -2, 1, 1, 1, 0, 0, -1, 1]
def label239 : Mat3 := [0, -2, 1, 1, 2, -1, 0, -1, 1]
def label246 : Mat3 := [0, -1, -2, 1, 1, 2, 0, 0, 1]
def label268 : Mat3 := [0, -1, -1, 1, 0, 0, 0, 0, 1]
def label270 : Mat3 := [0, -1, -1, 1, 0, 1, 0, 0, 1]
def label277 : Mat3 := [0, -1, -1, 1, 1, 0, 0, 0, 1]
def label284 : Mat3 := [0, -1, -1, 1, 1, 1, -1, 0, 1]
def label285 : Mat3 := [0, -1, -1, 1, 1, 1, 0, -1, 0]
def label286 : Mat3 := [0, -1, -1, 1, 1, 1, 0, 0, 1]
def label287 : Mat3 := [0, -1, -1, 1, 1, 1, 0, 1, 2]
def label289 : Mat3 := [0, -1, -1, 1, 1, 1, 1, 0, 1]
def label293 : Mat3 := [0, -1, -1, 1, 1, 2, 0, 0, 1]
def label297 : Mat3 := [0, -1, -1, 1, 2, 1, 0, 0, 1]
def label299 : Mat3 := [0, -1, -1, 1, 2, 2, 0, 0, 1]
def label302 : Mat3 := [0, -1, -1, 2, 1, 2, 1, 0, 1]
def label305 : Mat3 := [0, -1, 0, 0, 0, 1, -1, -1, 1]
def label306 : Mat3 := [0, -1, 0, 0, 1, -1, 1, 0, 1]
def label309 : Mat3 := [0, -1, 0, 0, 1, 1, -1, 0, 1]
def label310 : Mat3 := [0, -1, 0, 1, -1, 0, 0, 0, 1]
def label311 : Mat3 := [0, -1, 0, 1, 0, -1, 0, 0, 1]
def label312 : Mat3 := [0, -1, 0, 1, 0, -1, 0, 1, 1]
def label314 : Mat3 := [0, -1, 0, 1, 0, 0, -1, 0, 1]
def label315 : Mat3 := [0, -1, 0, 1, 0, 0, -1, 1, 1]
def label316 : Mat3 := [0, -1, 0, 1, 0, 0, 0, -1, 1]
def label317 : Mat3 := [0, -1, 0, 1, 0, 0, 0, 0, 1]
def label318 : Mat3 := [0, -1, 0, 1, 0, 0, 0, 1, 1]
def label319 : Mat3 := [0, -1, 0, 1, 0, 0, 1, -1, 1]
def label320 : Mat3 := [0, -1, 0, 1, 0, 0, 1, 0, 1]
def label322 : Mat3 := [0, -1, 0, 1, 0, 1, 0, -1, 1]
def label323 : Mat3 := [0, -1, 0, 1, 0, 1, 0, 0, 1]
def label324 : Mat3 := [0, -1, 0, 1, 1, -2, 0, 0, 1]
def label326 : Mat3 := [0, -1, 0, 1, 1, -1, -1, 0, 2]
def label327 : Mat3 := [0, -1, 0, 1, 1, -1, 0, -1, 1]
def label328 : Mat3 := [0, -1, 0, 1, 1, -1, 0, 0, 1]
def label329 : Mat3 := [0, -1, 0, 1, 1, -1, 0, 1, 1]
def label330 : Mat3 := [0, -1, 0, 1, 1, -1, 1, 0, 0]
def label334 : Mat3 := [0, -1, 0, 1, 1, 0, -2, 0, 1]
def label336 : Mat3 := [0, -1, 0, 1, 1, 0, -1, -1, 1]
def label337 : Mat3 := [0, -1, 0, 1, 1, 0, -1, 0, 1]
def label338 : Mat3 := [0, -1, 0, 1, 1, 0, -1, 1, 1]
def label339 : Mat3 := [0, -1, 0, 1, 1, 0, 0, -2, 1]
def label340 : Mat3 := [0, -1, 0, 1, 1, 0, 0, -1, 1]
def label342 : Mat3 := [0, -1, 0, 1, 1, 0, 0, 1, 1]
def label343 : Mat3 := [0, -1, 0, 1, 1, 0, 0, 2, 1]
def label344 : Mat3 := [0, -1, 0, 1, 1, 0, 1, -1, 1]
def label345 : Mat3 := [0, -1, 0, 1, 1, 0, 1, 0, 1]
def label346 : Mat3 := [0, -1, 0, 1, 1, 0, 1, 1, 1]
def label348 : Mat3 := [0, -1, 0, 1, 1, 0, 2, 0, 1]
def label352 : Mat3 := [0, -1, 0, 1, 1, 1, -1, 0, 0]
def label353 : Mat3 := [0, -1, 0, 1, 1, 1, 0, -1, 1]
def label354 : Mat3 := [0, -1, 0, 1, 1, 1, 0, 0, 1]
def label355 : Mat3 := [0, -1, 0, 1, 1, 1, 0, 1, 1]
def label356 : Mat3 := [0, -1, 0, 1, 1, 1, 1, 0, 2]
def label358 : Mat3 := [0, -1, 0, 1, 1, 2, 0, 0, 1]
def label359 : Mat3 := [0, -1, 0, 1, 2, -1, 0, -1, 1]
def label360 : Mat3 := [0, -1, 0, 1, 2, -1, 0, 0, 1]
def label362 : Mat3 := [0, -1, 0, 1, 2, 0, -1, -1, 1]
def label363 : Mat3 := [0, -1, 0, 1, 2, 0, -1, 0, 1]
def label364 : Mat3 := [0, -1, 0, 1, 2, 0, 0, -1, 1]
def label365 : Mat3 := [0, -1, 0, 1, 2, 0, 0, 0, 1]
def label366 : Mat3 := [0, -1, 0, 1, 2, 0, 0, 1, 1]
def label367 : Mat3 := [0, -1, 0, 1, 2, 0, 1, 0, 1]
def label368 : Mat3 := [0, -1, 0, 1, 2, 0, 1, 1, 1]
def label370 : Mat3 := [0, -1, 0, 1, 2, 1, 0, 0, 1]
def label371 : Mat3 := [0, -1, 0, 1, 2, 1, 0, 1, 1]
def label372 : Mat3 := [0, -1, 0, 1, 3, 0, 0, 0, 1]
def label373 : Mat3 := [0, -1, 0, 2, 1, -1, -1, 0, 1]
def label374 : Mat3 := [0, -1, 0, 2, 1, 1, 1, 0, 1]
def label376 : Mat3 := [0, -1, 0, 2, 2, 1, 1, 1, 1]
def label379 : Mat3 := [0, -1, 1, -1, 1, 1, -1, 0, 1]
def label386 : Mat3 := [0, -1, 1, 0, 1, 0, -1, -1, 1]
def label388 : Mat3 := [0, -1, 1, 0, 1, 0, -1, 0, 0]
def label389 : Mat3 := [0, -1, 1, 0, 1, 0, -1, 0, 1]
def label390 : Mat3 := [0, -1, 1, 0, 1, 0, -1, 0, 2]
def label392 : Mat3 := [0, -1, 1, 0, 1, 0, -1, 1, 1]
def label396 : Mat3 := [0, -1, 1, 1, 0, -1, 0, 0, 1]
def label398 : Mat3 := [0, -1, 1, 1, 0, 0, 0, 0, 1]
def label402 : Mat3 := [0, -1, 1, 1, 1, -2, 0, 0, 1]
def label406 : Mat3 := [0, -1, 1, 1, 1, -1, -1, 0, 1]
def label408 : Mat3 := [0, -1, 1, 1, 1, -1, 0, -1, 2]
def label409 : Mat3 := [0, -1, 1, 1, 1, -1, 0, 0, 1]
def label410 : Mat3 := [0, -1, 1, 1, 1, -1, 0, 1, 0]
def label411 : Mat3 := [0, -1, 1, 1, 1, -1, 1, 0, 1]
def label418 : Mat3 := [0, -1, 1, 1, 1, 0, 0, 0, 1]
def label421 : Mat3 := [0, -1, 1, 1, 1, 0, 1, 1, 1]
def label423 : Mat3 := [0, -1, 1, 1, 1, 1, 0, 0, 1]
def label425 : Mat3 := [0, -1, 1, 1, 2, -2, 0, 0, 1]
def label427 : Mat3 := [0, -1, 1, 1, 2, -1, 0, 0, 1]
def label429 : Mat3 := [0, -1, 1, 1, 2, 0, 0, 0, 1]
def label434 : Mat3 := [0, -1, 2, 0, 1, -1, -1, 0, 1]
def label436 : Mat3 := [0, -1, 2, 1, 1, -2, 0, 0, 1]
def label438 : Mat3 := [0, -1, 2, 1, 1, -1, 0, 0, 1]
def label440 : Mat3 := [0, -1, 2, 1, 1, 0, 0, 0, 1]
def label493 : Mat3 := [0, 0, -1, 1, 0, 1, 0, -1, 1]
def label522 : Mat3 := [0, 0, 1, -1, 1, 0, -2, 1, 1]
def label527 : Mat3 := [0, 0, 1, -1, 1, 1, -2, 1, 2]
def label542 : Mat3 := [0, 0, 1, 0, 1, -1, -1, 1, 0]
def label553 : Mat3 := [0, 0, 1, 0, 1, 0, -1, 1, 0]
def label554 : Mat3 := [0, 0, 1, 0, 1, 0, -1, 1, 1]
def label555 : Mat3 := [0, 0, 1, 0, 1, 0, -1, 1, 2]
def label556 : Mat3 := [0, 0, 1, 0, 1, 0, -1, 2, 1]
def label563 : Mat3 := [0, 0, 1, 0, 1, 1, -1, 1, 2]
def label566 : Mat3 := [0, 0, 1, 1, 0, -1, 0, 1, 1]
def label574 : Mat3 := [0, 0, 1, 1, 1, -1, 0, 1, 0]
def label579 : Mat3 := [0, 0, 1, 1, 1, 0, 0, 1, 1]
def label735 : Mat3 := [0, 1, 1, -1, 1, 0, -2, 2, 1]
def label737 : Mat3 := [0, 1, 1, -1, 1, 0, -1, 1, 1]
def label770 : Mat3 := [0, 1, 1, 0, 1, 0, -1, 1, 1]
def label772 : Mat3 := [0, 1, 1, 0, 1, 0, -1, 2, 1]
def label837 : Mat3 := [1, -3, 0, 0, 1, 1, 0, 0, 1]
def label841 : Mat3 := [1, -3, 1, 0, 1, 0, 0, -2, 1]
def label842 : Mat3 := [1, -3, 1, 0, 1, 0, 0, -1, 1]
def label843 : Mat3 := [1, -3, 1, 0, 1, 0, 0, 0, 1]
def label848 : Mat3 := [1, -3, 2, 0, 1, 0, 0, -1, 1]
def label850 : Mat3 := [1, -3, 2, 0, 2, -1, 0, -1, 1]
def label881 : Mat3 := [1, -2, -2, 0, 1, 2, 0, 0, 1]
def label914 : Mat3 := [1, -2, -1, 0, 1, 1, 0, -1, 0]
def label915 : Mat3 := [1, -2, -1, 0, 1, 1, 0, 0, 1]
def label919 : Mat3 := [1, -2, -1, 0, 1, 2, 0, 0, 1]
def label923 : Mat3 := [1, -2, -1, 0, 2, 1, 0, 1, 1]
def label928 : Mat3 := [1, -2, -1, 0, 3, 2, 0, 1, 1]
def label937 : Mat3 := [1, -2, 0, -1, 1, 1, -1, 0, 1]
def label939 : Mat3 := [1, -2, 0, -1, 2, 1, -1, 1, 1]
def label956 : Mat3 := [1, -2, 0, 0, 0, 1, 0, -1, 1]
def label974 : Mat3 := [1, -2, 0, 0, 1, 0, 0, -1, 1]
def label990 : Mat3 := [1, -2, 0, 0, 1, 1, 0, 0, 1]
def label995 : Mat3 := [1, -2, 0, 0, 2, 1, 0, 1, 1]
def label1040 : Mat3 := [1, -2, 1, 0, 1, 0, 0, 1, 1]
def label1051 : Mat3 := [1, -2, 1, 0, 2, -1, 0, 1, 0]
def label1072 : Mat3 := [1, -2, 2, 0, 1, -1, 0, 0, 1]
def label1079 : Mat3 := [1, -2, 2, 0, 1, 0, 0, -1, 1]
def label1089 : Mat3 := [1, -2, 3, 0, 1, -1, 0, -1, 2]
def label1090 : Mat3 := [1, -2, 3, 0, 1, -1, 0, 0, 1]
def label1099 : Mat3 := [1, -1, -3, 0, 1, 2, 0, 0, 1]
def label1101 : Mat3 := [1, -1, -3, 0, 1, 3, 0, 0, 1]
def label1236 : Mat3 := [1, -1, -1, 0, 1, 1, -1, 0, 1]
def label1246 : Mat3 := [1, -1, -1, 0, 1, 1, 1, 0, 1]
def label1473 : Mat3 := [1, -1, 0, 0, 1, 1, 0, 1, 2]
def label1622 : Mat3 := [1, -1, 1, -1, 2, 0, -1, 2, 1]
def label1654 : Mat3 := [1, -1, 1, 0, 1, -1, 0, 1, 0]
def label1658 : Mat3 := [1, -1, 1, 0, 1, -1, 1, 0, 1]
def label1674 : Mat3 := [1, -1, 1, 0, 1, 0, 0, 1, 1]
def label1688 : Mat3 := [1, -1, 1, 0, 1, 1, 0, 1, 2]
def label1710 : Mat3 := [1, -1, 1, 1, 0, 0, 1, 0, 1]
def label1729 : Mat3 := [1, -1, 1, 1, 1, 2, 1, 0, 2]
def label1761 : Mat3 := [1, -1, 2, 0, 1, -1, 0, 0, 1]
def label1762 : Mat3 := [1, -1, 2, 0, 1, -1, 0, 1, 0]
def label1770 : Mat3 := [1, -1, 2, 0, 1, 0, 0, 0, 1]
def label1771 : Mat3 := [1, -1, 2, 0, 1, 0, 0, 1, 1]
def label1775 : Mat3 := [1, -1, 2, 0, 1, 1, 0, 0, 1]
def label1787 : Mat3 := [1, -1, 3, 0, 1, -2, 0, 0, 1]
def label1789 : Mat3 := [1, -1, 3, 0, 1, -1, 0, 0, 1]
def label1791 : Mat3 := [1, -1, 3, 0, 1, 0, 0, 0, 1]
def label1834 : Mat3 := [1, 0, -2, 0, 0, 1, 0, -1, 1]
def label1982 : Mat3 := [1, 0, -1, 0, -1, 2, 0, -1, 1]
def label1993 : Mat3 := [1, 0, -1, 0, 0, 1, 0, -1, 1]
def label2056 : Mat3 := [1, 0, -1, 0, 1, 2, 0, 0, 1]
def label2318 : Mat3 := [1, 0, 0, -1, 0, 1, -1, -1, 1]
def label2403 : Mat3 := [1, 0, 0, -1, 1, 1, -1, 1, 2]
def label2771 : Mat3 := [1, 0, 0, 1, 1, -1, 1, 1, 0]
def label2862 : Mat3 := [1, 0, 0, 1, 2, 1, 1, 1, 1]
def label3028 : Mat3 := [1, 0, 1, -2, 1, 0, -2, 1, 1]
def label3058 : Mat3 := [1, 0, 1, -1, 1, -1, -1, 1, 0]
def label3076 : Mat3 := [1, 0, 1, -1, 1, 0, -1, 1, 1]
def label3086 : Mat3 := [1, 0, 1, -1, 1, 1, -1, 1, 2]
def label3117 : Mat3 := [1, 0, 1, 0, 1, -2, 0, 1, -1]
def label3126 : Mat3 := [1, 0, 1, 0, 1, -1, 0, 1, 0]
def label3146 : Mat3 := [1, 0, 1, 0, 1, 0, 0, 2, 1]
def label3164 : Mat3 := [1, 0, 1, 0, 1, 1, 0, 1, 2]
def label3173 : Mat3 := [1, 0, 1, 0, 1, 2, 0, 1, 3]
def label3184 : Mat3 := [1, 0, 1, 0, 2, 1, 0, 1, 1]
def label3201 : Mat3 := [1, 0, 1, 1, 1, -1, 1, 1, 0]
def label3211 : Mat3 := [1, 0, 1, 1, 1, 0, 1, 1, 1]
def label3229 : Mat3 := [1, 0, 1, 1, 1, 1, 1, 1, 2]
def label3254 : Mat3 := [1, 0, 1, 2, 1, 0, 2, 1, 1]
def label3299 : Mat3 := [1, 0, 2, -1, 1, -1, -1, 1, 0]
def label3304 : Mat3 := [1, 0, 2, -1, 1, 0, -1, 1, 1]
def label3314 : Mat3 := [1, 0, 2, 0, 1, -1, 0, 0, 1]
def label3315 : Mat3 := [1, 0, 2, 0, 1, -1, 0, 1, 0]
def label3324 : Mat3 := [1, 0, 2, 0, 1, 0, 0, 1, 1]
def label3333 : Mat3 := [1, 0, 2, 0, 1, 1, 0, 1, 2]
def label3343 : Mat3 := [1, 0, 2, 1, 1, 0, 1, 1, 1]
def label3348 : Mat3 := [1, 0, 2, 1, 1, 1, 1, 1, 2]
def label3371 : Mat3 := [1, 0, 3, 0, 1, 0, 0, 1, 1]
def label3697 : Mat3 := [1, 1, 0, 0, 1, -1, 0, 1, 0]
def label3698 : Mat3 := [1, 1, 0, 0, 1, -1, 0, 2, -1]
def label3723 : Mat3 := [1, 1, 0, 0, 1, 0, 0, 2, 1]
def label3889 : Mat3 := [1, 1, 1, -1, 0, 0, -1, 0, 1]
def label3899 : Mat3 := [1, 1, 1, -1, 1, 0, -1, 2, 1]
def label3908 : Mat3 := [1, 1, 1, 0, 0, -1, 0, 1, 0]
def label3918 : Mat3 := [1, 1, 1, 0, 1, -1, 0, 1, 0]
def label3931 : Mat3 := [1, 1, 1, 0, 1, 0, 0, 2, 1]
def label3952 : Mat3 := [1, 1, 1, 0, 1, 1, 0, 1, 2]
def label3971 : Mat3 := [1, 1, 1, 0, 2, 1, 0, 3, 2]
def label3980 : Mat3 := [1, 1, 1, 1, 1, 0, 1, 2, 1]
def label3989 : Mat3 := [1, 1, 1, 1, 2, 0, 1, 2, 1]
def label4029 : Mat3 := [1, 1, 2, 0, 0, -1, 0, 1, 1]
def label4036 : Mat3 := [1, 1, 2, 0, 1, 0, 0, 1, 1]
def label4037 : Mat3 := [1, 1, 2, 0, 1, 0, 0, 2, 1]
def label4045 : Mat3 := [1, 1, 2, 0, 1, 1, 0, 1, 2]
def label4046 : Mat3 := [1, 1, 2, 0, 1, 1, 0, 2, 3]
def label4250 : Mat3 := [1, 2, 1, 0, 1, 0, 0, 1, 1]
def label4251 : Mat3 := [1, 2, 1, 0, 1, 0, 0, 2, 1]
def label4252 : Mat3 := [1, 2, 1, 0, 1, 0, 0, 3, 1]
def label4292 : Mat3 := [1, 2, 2, 0, 1, 0, 0, 2, 1]
def label4393 : Mat3 := [2, -3, 0, -1, 2, 1, 0, 0, 1]
def label4397 : Mat3 := [2, -3, 1, -1, 2, 0, 0, 0, 1]
def label4400 : Mat3 := [2, -3, 1, 0, 1, 0, 1, -1, 1]
def label4427 : Mat3 := [2, -2, 1, -1, 1, 0, 0, -1, 1]
def label4436 : Mat3 := [2, -2, 1, 0, 1, 0, 1, -1, 1]
def label4437 : Mat3 := [2, -2, 1, 0, 1, 0, 1, 0, 1]
def label4465 : Mat3 := [2, -1, -2, -1, 1, 2, 0, 0, 1]
def label4476 : Mat3 := [2, -1, -1, -2, 1, 2, -1, 0, 1]
def label4492 : Mat3 := [2, -1, -1, -1, 1, 1, -1, 0, 1]
def label4495 : Mat3 := [2, -1, -1, -1, 1, 1, 0, 0, 1]
def label4500 : Mat3 := [2, -1, -1, -1, 1, 2, 0, 0, 1]
def label4512 : Mat3 := [2, -1, -1, 0, 1, 0, 1, 0, 0]
def label4539 : Mat3 := [2, -1, 0, -2, 1, 1, -1, 0, 1]
def label4541 : Mat3 := [2, -1, 0, -2, 2, 1, -1, 1, 1]
def label4543 : Mat3 := [2, -1, 0, -1, 0, 1, 0, -1, 1]
def label4577 : Mat3 := [2, -1, 0, -1, 1, 1, 0, 0, 1]
def label4582 : Mat3 := [2, -1, 0, -1, 2, 1, 0, 1, 1]
def label4584 : Mat3 := [2, -1, 0, 0, 0, 1, 1, -1, 1]
def label4588 : Mat3 := [2, -1, 0, 0, 1, 1, 1, 0, 1]
def label4626 : Mat3 := [2, -1, 1, -1, 1, 0, -1, 1, 1]
def label4627 : Mat3 := [2, -1, 1, -1, 1, 0, 0, 0, 1]
def label4633 : Mat3 := [2, -1, 1, -1, 1, 1, 0, 0, 1]
def label4641 : Mat3 := [2, -1, 1, 0, 1, 0, 1, 0, 1]
def label4642 : Mat3 := [2, -1, 1, 0, 1, 0, 1, 1, 1]
def label4652 : Mat3 := [2, -1, 1, 1, 1, 1, 1, 0, 1]
def label4662 : Mat3 := [2, -1, 2, -1, 1, -1, 0, 0, 1]
def label4667 : Mat3 := [2, -1, 2, -1, 1, 0, 0, 0, 1]
def label4670 : Mat3 := [2, -1, 2, 0, 1, -1, 1, 0, 1]
def label4675 : Mat3 := [2, -1, 3, -1, 1, -1, 0, 0, 1]
def label4678 : Mat3 := [2, -1, 3, 0, 1, 0, 1, 0, 2]
def label4741 : Mat3 := [2, 0, -1, 0, 1, 0, 1, 1, 0]
def label4794 : Mat3 := [2, 0, 1, -1, 1, -1, 0, 1, 0]
def label4799 : Mat3 := [2, 0, 1, -1, 1, 0, 0, 1, 1]
def label4809 : Mat3 := [2, 0, 1, 0, 1, -1, 1, 1, 0]
def label4818 : Mat3 := [2, 0, 1, 0, 1, 0, 1, 1, 1]
def label4827 : Mat3 := [2, 0, 1, 0, 1, 1, 1, 1, 2]
def label4836 : Mat3 := [2, 0, 1, 1, 1, 0, 2, 1, 1]
def label4841 : Mat3 := [2, 0, 1, 1, 1, 1, 2, 1, 2]
def label4866 : Mat3 := [2, 0, 3, 0, 1, 0, 1, 1, 2]
def label4964 : Mat3 := [2, 1, 0, -1, 0, 1, 0, 0, 1]
def label5036 : Mat3 := [2, 1, 1, -1, 0, 0, 0, 0, 1]
def label5045 : Mat3 := [2, 1, 1, 0, 1, 0, 1, 1, 1]
def label5046 : Mat3 := [2, 1, 1, 0, 1, 0, 1, 2, 1]
def label5057 : Mat3 := [2, 1, 1, 1, 1, 0, 1, 1, 1]
def label5059 : Mat3 := [2, 1, 1, 1, 1, 0, 2, 2, 1]
def label5136 : Mat3 := [2, 2, 1, 0, 1, 0, 1, 2, 1]
def label5217 : Mat3 := [3, -2, 0, -1, 1, 1, 0, 0, 1]
def label5221 : Mat3 := [3, -2, 1, -1, 1, 0, 0, 0, 1]
def label5222 : Mat3 := [3, -2, 1, -1, 1, 0, 1, -1, 1]
def label5259 : Mat3 := [3, -1, 0, -2, 1, 1, 0, 0, 1]
def label5264 : Mat3 := [3, -1, 1, -2, 1, 0, 0, 0, 1]
def label5266 : Mat3 := [3, -1, 1, -1, 1, 0, 1, 0, 1]
def label5269 : Mat3 := [3, -1, 1, 0, 1, 0, 2, 0, 1]
def label5272 : Mat3 := [3, -1, 2, -1, 1, -1, 1, 0, 1]
def label5275 : Mat3 := [3, -1, 2, 0, 1, 0, 1, 0, 1]
def label5317 : Mat3 := [3, 0, 1, 0, 1, 0, 2, 1, 1]
def label5332 : Mat3 := [3, 0, 2, 0, 1, 0, 1, 1, 1]
end NuclearUltrapower.SOS
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
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
@[simp] theorem eval_flatMap (f : α → A) (xs : List β) (p : β → Poly α) :
    eval f (xs.flatMap p) = (xs.map (fun x => eval f (p x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, eval_append, ih, List.map_cons, List.sum_cons]

omit [DecidableEq α] in
@[simp] theorem eval_flatten (f : α → A) (xs : List (Poly α)) :
    eval f xs.flatten = (xs.map (eval f)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatten_cons, eval_append, ih, List.map_cons, List.sum_cons]

end BucketSemantics
end NuclearUltrapower.SOS

end

end OAI
end


