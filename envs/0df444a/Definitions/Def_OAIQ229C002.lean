-- Prove2me | Definitions.Def_OAIQ229C002
-- name    : OAIQ229C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T02:19:26.224395+00:00
-- url     : https://prove2.me/theorems/bfba9338-e2b2-4a9b-82f6-38cdeaf9cc41
-- title:
--   Definitions bundle OAIQ229C002 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 162 declarations of OpenAI's Lean: 37 definitions, 3 inductive types or structures and 122 theorems. The definitions and types are `OAI.CoarseAssembly.Congruence.wordBall`, `OAI.CoarseAssembly.DiscreteRoe.finiteHeadRadius`, `OAI.CoarseAssembly.HexDirection`, `OAI.CoarseAssembly.IntegerPathLift`, `OAI.CoarseAssembly.IntegerPathLift.refl`, `OAI.CoarseAssembly.IntegerPathLift.trans`, `OAI.CoarseAssembly.OperatorKTheory.conjugatedTwoUnitary`, `OAI.CoarseAssembly.OperatorKTheory.diagonalTwoUnitary`, `OAI.CoarseAssembly.OperatorKTheory.mapTwoUnitary`, `OAI.CoarseAssembly.OperatorKTheory.matrixTwoStarHom`, `OAI.CoarseAssembly.OperatorKTheory.matrixTwoUnitalStarHom`, `OAI.CoarseAssembly.OperatorKTheory.relativeTwoPart`, `OAI.CoarseAssembly.OperatorKTheory.relativeTwoUnitary`, `OAI.CoarseAssembly.Rips.IntegralCocycle`, `OAI.CoarseAssembly.Rips.IntegralCocycle.circleMap`, `OAI.CoarseAssembly.Rips.IntegralCocycle.edgeLift`, `OAI.CoarseAssembly.Rips.IntegralCocycle.localAngle`, `OAI.CoarseAssembly.Rips.IntegralCocycle.toContinuousMap`, `OAI.CoarseAssembly.Rips.IntegralCocycle.walkLift`, `OAI.CoarseAssembly.Rips.Point.supportVertex`, `OAI.CoarseAssembly.Rips.edgePath`, `OAI.CoarseAssembly.Rips.inclusionFunctionHom`, `OAI.CoarseAssembly.Rips.interpolate`, `OAI.CoarseAssembly.Rips.scaleFunctionHom`, `OAI.CoarseAssembly.Rips.simplexPath`, `OAI.CoarseAssembly.Rips.walkPath`, `OAI.CoarseAssembly.componentEmbedding`, `OAI.CoarseAssembly.controlledMatrix`, `OAI.CoarseAssembly.controlledMatrixLinear`, `OAI.CoarseAssembly.discOrigin`, `OAI.CoarseAssembly.discRank`, `OAI.CoarseAssembly.embeddingTransition`, `OAI.CoarseAssembly.matrixRow`, `OAI.CoarseAssembly.operatorSandwich`, `OAI.CoarseAssembly.quotientSection`, `OAI.CoarseAssembly.reindexFiberVector`, `OAI.CoarseAssembly.shiftedRealPath`, `OAI.CoarseAssembly.spatialBlocks`, `OAI.CoarseAssembly.walkCharge`, `OAI.NuclearUltrapower.Elementary.Residue3`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BoundaryGeometry`, `CoarseAssembly_CocycleCircleMap`, `CoarseAssembly_CocyclePathLifting`, `CoarseAssembly_ComponentHilbertInclusion`, `CoarseAssembly_ComponentInclusion`, `CoarseAssembly_CongruenceQuotients`, `CoarseAssembly_Conjugation`, `CoarseAssembly_ControlledMatrices`, `CoarseAssembly_DiagonalMultiplier`, `CoarseAssembly_DiscConnected`, `CoarseAssembly_EmbeddingTransition`, `CoarseAssembly_FiniteFiberMaps`, `CoarseAssembly_FiniteHeadNormalization`, `CoarseAssembly_FiniteWords`, `CoarseAssembly_GraphFiberOperators`, `CoarseAssembly_GraphMetric`, `CoarseAssembly_HilbertSum`, `CoarseAssembly_InclusionFunctoriality`, `CoarseAssembly_InclusionModule`, `CoarseAssembly_IsometricExtension`, `CoarseAssembly_Lattice`, `CoarseAssembly_LatticeCharge`, `CoarseAssembly_MultiplierOrthogonalEmbeddings`, `CoarseAssembly_PartitionCompactPerturbation`, `CoarseAssembly_PathFiberOperators`, `CoarseAssembly_ProjectionBlocks`, `CoarseAssembly_RelativeHomotopy`, `CoarseAssembly_RelativeMultiplication`, `CoarseAssembly_RelativeNearby`, `CoarseAssembly_RelativeTwoByTwo`, `CoarseAssembly_RelativeTwoConjugation`, `CoarseAssembly_RelativeTwoDiagonal`, `CoarseAssembly_RelativeTwoHomotopy`, `CoarseAssembly_RelativeUnitary`, `CoarseAssembly_RipsEmbedding`, `CoarseAssembly_RipsFamilyMap`, `CoarseAssembly_RipsInclusionNaturality`, `CoarseAssembly_RipsMapCalculus`, `CoarseAssembly_RipsPartition`, `CoarseAssembly_RipsPaths`, `CoarseAssembly_RipsRealization`, `CoarseAssembly_RipsReindex`, `CoarseAssembly_RipsScaleCompatibility`, `CoarseAssembly_RoeCalculus`, `CoarseAssembly_Sandwich`, `CoarseAssembly_SandwichNormControl`, `CoarseAssembly_SeparatedFamilyBoundary`, `CoarseAssembly_SeparatedRips`, `CoarseAssembly_SeparatedUnion`, `CoarseAssembly_ShortLoops`, `CoarseAssembly_SpatialBlocks`, `NuclearUltrapower_Kazhdan`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C010`, `OAIQ229C011`, `OAIQ229C012` and `OAIQ229C015`.
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

section
-- module Solutions.Q229_CA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
end OAICompat434

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

/-- Radius changes by at most one across a lattice edge. -/
theorem latticeRadius_adj {u v : LatticeVertex} (h : triangularGraph.Adj u v) :
    |latticeRadius u - latticeRadius v| ≤ 1 := by
  unfold latticeRadius
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le
  · apply (abs_max_sub_max_le_max _ _ _ _).trans
    exact max_le ((abs_abs_sub_abs_le_abs_sub _ _).trans h.1)
      ((abs_abs_sub_abs_le_abs_sub _ _).trans h.2.1)
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans h.2.2.1

theorem discDepth_int (j : ℕ) (u : Disc j) :
    (discDepth j u : ℤ) = (j : ℤ) - latticeRadius u.val := by
  exact Int.toNat_of_nonneg (sub_nonneg.mpr u.property)

theorem discDepth_adj {j : ℕ} {u v : Disc j} (h : (discGraph j).Adj u v) :
    |(discDepth j u : ℤ) - (discDepth j v : ℤ)| ≤ 1 := by
  rw [discDepth_int, discDepth_int]
  have hr := latticeRadius_adj h
  rw [abs_le] at hr ⊢
  omega

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiscConnected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connectivity of the triangular lattice discs

Moving a nonzero coordinate one step toward zero stays in the hexagonal
disc and decreases the sum of absolute coordinates. This gives paths to
the origin within each finite base disc.
-/

namespace CoarseAssembly

def discOrigin (j : ℕ) : Disc j := ⟨(0, 0), by simp [latticeRadius]⟩

def discRank {j : ℕ} (u : Disc j) : ℕ := u.val.1.natAbs + u.val.2.natAbs

theorem disc_lower_neighbor {j : ℕ} (u : Disc j) (hu : u ≠ discOrigin j) :
    ∃ v : Disc j, (discGraph j).Adj u v ∧ discRank v < discRank u := by
  rcases u with ⟨⟨a, b⟩, huj⟩
  have hh := huj
  simp only [latticeRadius, max_le_iff, abs_le] at hh
  have hstep (c d : ℤ) (hc : |c| ≤ (j : ℤ)) (hd : |d| ≤ (j : ℤ))
      (hcd : |c + d| ≤ (j : ℤ)) (ha : |a - c| ≤ 1) (hb : |b - d| ≤ 1)
      (hs : |(a + b) - (c + d)| ≤ 1) (hne : (a, b) ≠ (c, d))
      (hr : c.natAbs + d.natAbs < a.natAbs + b.natAbs) :
      ∃ v : Disc j, (discGraph j).Adj ⟨(a, b), huj⟩ v ∧
        discRank v < discRank ⟨(a, b), huj⟩ := by
    exact ⟨⟨(c, d), by simp only [latticeRadius, max_le_iff]; exact ⟨⟨hc, hd⟩, hcd⟩⟩,
      ⟨ha, hb, hs, hne⟩, hr⟩
  by_cases ha : 0 < a
  · apply hstep (a - 1) b
    · rw [abs_le]; omega
    · rw [abs_le]; omega
    · rw [abs_le]; omega
    · norm_num
    · simp
    · norm_num
    · intro he; have := congrArg Prod.fst he; omega
    · have h1 : (a.natAbs : ℤ) = a := by omega
      have h2 : ((a - 1).natAbs : ℤ) = a - 1 := by omega
      omega
  · by_cases ha' : a < 0
    · apply hstep (a + 1) b
      · rw [abs_le]; omega
      · rw [abs_le]; omega
      · rw [abs_le]; omega
      · norm_num
      · simp
      · norm_num
      · intro he; have := congrArg Prod.fst he; omega
      · have h1 : (a.natAbs : ℤ) = -a := by omega
        have h2 : ((a + 1).natAbs : ℤ) = -(a + 1) := by omega
        omega
    · have ha0 : a = 0 := by omega
      subst a
      have hb0 : b ≠ 0 := by
        intro hb
        apply hu
        subst b
        rfl
      by_cases hb : 0 < b
      · apply hstep 0 (b - 1)
        · simp
        · rw [abs_le]; omega
        · rw [abs_le]; omega
        · simp
        · norm_num
        · norm_num
        · intro he; have := congrArg Prod.snd he; omega
        · have h1 : (b.natAbs : ℤ) = b := by omega
          have h2 : ((b - 1).natAbs : ℤ) = b - 1 := by omega
          omega
      · have hb' : b < 0 := by omega
        apply hstep 0 (b + 1)
        · simp
        · rw [abs_le]; omega
        · rw [abs_le]; omega
        · simp
        · norm_num
        · norm_num
        · intro he; have := congrArg Prod.snd he; omega
        · have h1 : (b.natAbs : ℤ) = -b := by omega
          have h2 : ((b + 1).natAbs : ℤ) = -(b + 1) := by omega
          omega

theorem disc_reachable_origin {j : ℕ} (u : Disc j) :
    (discGraph j).Reachable u (discOrigin j) := by
  induction hn : discRank u using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hu : u = discOrigin j
    · subst u; exact SimpleGraph.Reachable.refl _
    · obtain ⟨v, huv, hv⟩ := disc_lower_neighbor u hu
      have hvo := ih (discRank v) (by omega) v rfl
      exact huv.reachable.trans hvo

theorem discGraph_connected (j : ℕ) : (discGraph j).Connected where
  preconnected u v := (disc_reachable_origin u).trans (disc_reachable_origin v).symm
  nonempty := ⟨discOrigin j⟩

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual congruence quotients and diagonal holonomies

The congruence quotient is `SL₃(ℤ/2^kℤ)`, including the singleton quotient
for `k = 0`.
Its diagonal matrices have entries `t,t⁻¹,1`, and the finite-level matrices
are obtained by the genuine 2-adic reduction maps.
-/

namespace CoarseAssembly.Congruence

theorem diagonal_mul {R : Type*} [CommRing R] (s t : Rˣ) :
    diagonal (s * t) = diagonal s * diagonal t := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conjugation by an isometry

The spatial operator homomorphism and exact boundary factorization used in
§§5--6 of the coarse Novikov manuscript. Restriction of this homomorphism to
the Roe algebras is a separate range-membership obligation.
-/

namespace CoarseAssembly

variable {E F H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorConjugation_comp (V : F →ₗᵢ[ℂ] H) (W : E →ₗᵢ[ℂ] F)
    (T : E →L[ℂ] E) :
    operatorConjugation V (operatorConjugation W T) = operatorConjugation (V.comp W) T := by
  have hcomp : (V.comp W).toContinuousLinearMap =
      V.toContinuousLinearMap.comp W.toContinuousLinearMap := rfl
  simp [operatorConjugation, hcomp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc]

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HilbertSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the Hilbert sum of the finite fibers

The transfer is naturally constructed as a block operator. Flattening its
Hilbert sum identifies it isometrically with the ordinary Roe module on
the sigma type of vertices. Both directions and the norm identity are
constructed from summability of squared norms.
-/

noncomputable section

namespace CoarseAssembly

variable {ι : Type*} {Q : ι → Type*} {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [NormedSpace ℂ H] in
@[simp] theorem flatten_unflatten (x : lp (fun _ : Sigma Q => H) 2) :
    flattenVector (unflattenVector x) = x := by
  apply lp.ext
  rfl

omit [NormedSpace ℂ H] in
@[simp] theorem unflatten_flatten (x : lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    unflattenVector (flattenVector x) = x := by
  apply lp.ext
  funext i
  apply lp.ext
  rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteFiberMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permutations and normalized quotient-copying maps

These are the two types of edge operator in the graph construction:
permutations at equal depth, and normalized copying along a surjective
finite-group quotient. Their norm and constant-vector properties are
proved on the actual finite-fiber Hilbert spaces.
-/

noncomputable section

namespace CoarseAssembly

variable {Q R H : Type*} [Fintype Q] [Fintype R]
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

def reindexFiberVector (e : Q ≃ R) (x : lp (fun _ : Q => H) 2) :
    lp (fun _ : R => H) 2 := ⟨fun r => x (e.symm r), Memℓp.all _⟩

section GroupQuotient

variable {G K : Type*} [Group G] [Group K] [Fintype G] [Fintype K]

def quotientSection (f : G →* K) (hf : Function.Surjective f) (k : K) : G := (hf k).choose

end GroupQuotient

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform exclusion of short charged closed words

This is the algebraic part of the small-loop lemma in §3, specialized to
`SL₃(ℤ)` and its actual congruence quotients. The finite family of possible
word traces is constructed, rather than postulated as an extra input.
-/

namespace CoarseAssembly.Congruence

/-- Words of length at most `n` in a finite set of left moves. -/
def wordBall (S : Finset ArithmeticGroup) : ℕ → Finset ArithmeticGroup
  | 0 => {1}
  | n + 1 => wordBall S n ∪ (wordBall S n).biUnion (fun w => S.image (w * ·))

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ShortLoops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Short loops and the Rips edge cocycle

The combinatorial step in §4 of the coarse Novikov manuscript. The only
hypothesis on the charge is vanishing on short closed graph walks, exactly
the output required from the manuscript's small-loop lemma. This is a
conditional combinatorial result, not an assumption about analytic K-homology.
-/

namespace CoarseAssembly

variable {V : Type*} {G : SimpleGraph V}

/-- Sum an integer edge charge along an actual graph walk. -/
def walkCharge (a : V → V → ℤ) : {u v : V} → G.Walk u v → ℤ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => a u v + walkCharge a p

@[simp] theorem walkCharge_nil (a : V → V → ℤ) (u : V) :
    walkCharge a (.nil : G.Walk u u) = 0 := rfl

@[simp] theorem walkCharge_cons (a : V → V → ℤ) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkCharge a (.cons h p) = a u v + walkCharge a p := rfl

@[simp] theorem walkCharge_append (a : V → V → ℤ) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkCharge a (p.append q) = walkCharge a p + walkCharge a q := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, add_assoc]

@[simp] theorem walkCharge_reverse (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) {u v : V} (p : G.Walk u v) :
    walkCharge a p.reverse = -walkCharge a p := by
  induction p with
  | nil => simp
  | cons h p ih => simp [SimpleGraph.Walk.reverse_cons, ih, ha _ _ h]

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LatticeCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A combinatorial ray charge and the half-plane argument

We use a half-open cut along the positive horizontal ray: an edge entering
height zero from below has charge one exactly when its endpoint has positive
first coordinate. This is a combinatorial convention at ray vertices; edges
incident to the origin have charge zero. Its restriction to any of the six
open lattice half-planes is an exact difference of vertex potentials.
-/

namespace CoarseAssembly

inductive HexDirection
  | a | negA | b | negB | sum | negSum

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_GraphFiberOperators
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

theorem isometry_norm_le_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (V : E →ₗᵢ[ℂ] F) :
    ‖V.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [LinearIsometry.coe_toContinuousLinearMap, V.norm_map, one_mul] using le_rfl (a := ‖x‖)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PathFiberOperators
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

section FiniteMatrices

variable {Q R T : Type*} [Fintype Q] [Fintype R] [Fintype T]
variable [DecidableEq Q] [DecidableEq R] [DecidableEq T]

theorem scalarFiber_expansion (x : lp (fun _ : Q => ℂ) 2) :
    x = ∑ q : Q, (x q) • lp.single 2 q (1 : ℂ) := by
  apply lp.ext
  funext r
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, smul_eq_mul]
  simp [Pi.single_apply, mul_ite]

omit [Fintype R] [DecidableEq R] in
theorem scalarFiber_apply_sum
    (A : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (x : lp (fun _ : Q => ℂ) 2) (r : R) :
    A x r = ∑ q : Q, x q * A (lp.single 2 q 1) r := by
  conv_lhs => rw [scalarFiber_expansion x]
  simp only [map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

omit [Fintype Q] [Fintype T] [DecidableEq T] in
theorem scalarFiber_comp_nonzero
    (A : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (B : lp (fun _ : R => ℂ) 2 →L[ℂ] lp (fun _ : T => ℂ) 2)
    (q : Q) (t : T) (h : (B.comp A) (lp.single 2 q 1) t ≠ 0) :
    ∃ r : R, A (lp.single 2 q 1) r ≠ 0 ∧ B (lp.single 2 r 1) t ≠ 0 := by
  classical
  by_contra! hn
  apply h
  rw [ContinuousLinearMap.comp_apply, scalarFiber_apply_sum]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : A (lp.single 2 q 1) r = 0
  · rw [hr, zero_mul]
  · rw [hn r hr, mul_zero]

end FiniteMatrices

end CoarseAssembly

end

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

theorem graphMetricOrDiscrete_eq (hG : G.Connected) :
    graphMetricOrDiscrete G = connectedGraphMetric G hG := by
  classical
  simp only [graphMetricOrDiscrete, dite_eq_left hG]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A separated metric union

Components embed isometrically. Paths between different components go
through chosen roots, with bridge length `i + j + 2`; thus bounded-distance
cross-component pairs lie in finitely many finite components.
-/

noncomputable section

namespace CoarseAssembly

variable {V : ℕ → Type*} [∀ i, MetricSpace (V i)]

@[simp] theorem separatedDist_same (o : ∀ i, V i) (i : ℕ) (x y : V i) :
    separatedDist o ⟨i, x⟩ ⟨i, y⟩ = dist x y := dite_eq_left rfl

theorem separatedDist_different (o : ∀ i, V i) {i j : ℕ} (h : i ≠ j)
    (x : V i) (y : V j) :
    separatedDist o ⟨i, x⟩ ⟨j, y⟩ =
      dist x (o i) + ((i : ℝ) + (j : ℝ) + 2) + dist (o j) y := dite_eq_right h

theorem separatedDist_indices (o : ∀ i, V i) (x y : Sigma V) (hxy : x.1 ≠ y.1)
    {R : ℝ} (hR : separatedDist o x y ≤ R) : (x.1 : ℝ) ≤ R ∧ (y.1 : ℝ) ≤ R := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rw [separatedDist_different o hxy] at hR
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor <;> linarith [dist_nonneg (x := x) (y := o i), dist_nonneg (x := o j) (y := y)]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Sandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The operator-norm sandwich estimate

The norm estimate and closure step do not require an amplified
constant-fiber projection to be locally compact.
Membership of the approximating sandwiches in the closed algebra is explicit.
-/

namespace CoarseAssembly

section ClosedRange

variable {A : Type*} [NormedRing A]

/-- Norm convergence of the finite-propagation projections passes their
sandwiches into any norm-closed algebra. The hypothesis concerns the
sandwiches themselves, as required for local compactness in the paper. -/
theorem sandwich_mem_of_tendsto (S : Set A) (hS : IsClosed S) (P : A)
    (Pn : ℕ → A) (hlim : Filter.Tendsto Pn Filter.atTop (nhds P)) (T : A)
    (hmem : ∀ n, Pn n * T * Pn n ∈ S) : P * T * P ∈ S := by
  apply hS.mem_of_tendsto ((hlim.mul tendsto_const_nhds).mul hlim)
  exact Filter.Eventually.of_forall hmem

end ClosedRange

end CoarseAssembly

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

omit [CompleteSpace H] in
theorem compact_sum {ι : Type*} (s : Finset ι) (A : ι → H →L[ℂ] H)
    (hA : ∀ i ∈ s, IsCompactOperator (A i)) :
    IsCompactOperator (∑ i ∈ s, A i : H →L[ℂ] H) := by
  exact (compactOperator (RingHom.id ℂ) H H).sum_mem hA

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ControlledMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded operators from controlled block matrices

A finite-propagation matrix has uniformly bounded row and column supports.
Cauchy--Schwarz and finite double counting construct its bounded operator
directly. This supplies the boundedness step of the transfer lift without
an auxiliary edge colouring.
-/

noncomputable section

namespace CoarseAssembly

open scoped BigOperators

theorem norm_sum_sq_le_card {J E : Type*} [NormedAddCommGroup E]
    (s : Finset J) (x : J → E) :
    ‖∑ j ∈ s, x j‖ ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖x j‖ ^ 2 := by
  have hn := norm_sum_le s x
  have hs := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖x j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hnon : 0 ≤ ∑ j ∈ s, ‖x j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ (∑ j ∈ s, ‖x j‖) ^ 2 := by nlinarith [norm_nonneg (∑ j ∈ s, x j)]
    _ ≤ _ := by simpa only [mul_comm] using hs

variable {I : Type*} [DecidableEq I]

theorem sum_neighbors_le (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (N : ℕ)
    (hc : ∀ j, (cols j).card ≤ N) (S : Finset I) (f : I → ℝ)
    (hf : ∀ j, 0 ≤ f j) :
    ∑ i ∈ S, ∑ j ∈ rows i, f j ≤ (N : ℝ) * ∑ j ∈ S.biUnion rows, f j := by
  let T := S.biUnion rows
  have heq : (∑ i ∈ S, ∑ j ∈ rows i, f j) =
      ∑ j ∈ T, ((S.filter (fun i => j ∈ rows i)).card : ℝ) * f j := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ T, if j ∈ rows i then f j else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∑ j ∈ rows i, if j ∈ rows i then f j else 0 := by simp
          _ = _ := Finset.sum_subset
            (fun j hj => Finset.mem_biUnion.mpr ⟨i, hi, hj⟩)
            (by intro j hj hjnot; simp [hjnot])
      _ = ∑ j ∈ T, ∑ i ∈ S, if j ∈ rows i then f j else 0 := Finset.sum_comm
      _ = _ := by simp [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [heq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right _ (hf j)
  exact_mod_cast (Finset.card_le_card (show S.filter (fun i => j ∈ rows i) ⊆ cols j from
    fun i hi => (hdual i j).mp (Finset.mem_filter.mp hi).2)).trans (hc j)

variable {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]

def matrixRow (rows : I → Finset I) (A : ∀ i j, E j →L[ℂ] E i)
    (x : lp E 2) (i : I) : E i := ∑ j ∈ rows i, A i j (x j)

omit [DecidableEq I] in
theorem matrixRow_norm_sq (rows : I → Finset I) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (_hC : 0 ≤ C) (hr : ∀ i, (rows i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) (x : lp E 2) (i : I) :
    ‖matrixRow rows A x i‖ ^ 2 ≤ (N : ℝ) * C ^ 2 * ∑ j ∈ rows i, ‖x j‖ ^ 2 := by
  have hentry (j : I) (hj : j ∈ rows i) : ‖A i j (x j)‖ ≤ C * ‖x j‖ :=
    (A i j).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hA i j hj) (norm_nonneg _))
  calc
    _ ≤ ((rows i).card : ℝ) * ∑ j ∈ rows i, ‖A i j (x j)‖ ^ 2 :=
      norm_sum_sq_le_card _ _
    _ ≤ (N : ℝ) * ∑ j ∈ rows i, (C * ‖x j‖) ^ 2 := by
      refine mul_le_mul (by exact_mod_cast hr i) ?_
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      exact hentry j hj
    _ = _ := by simp only [mul_pow, ← Finset.mul_sum] <;> ring

theorem matrix_finite_norm_sq (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) (x : lp E 2) (S : Finset I) :
    ∑ i ∈ S, ‖matrixRow rows A x i‖ ^ 2 ≤ ((N : ℝ) * C * ‖x‖) ^ 2 := by
  calc
    _ ≤ ∑ i ∈ S, (N : ℝ) * C ^ 2 * ∑ j ∈ rows i, ‖x j‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => matrixRow_norm_sq rows A N C hC hr hA x i)
    _ = (N : ℝ) * C ^ 2 * ∑ i ∈ S, ∑ j ∈ rows i, ‖x j‖ ^ 2 :=
      (Finset.mul_sum ..).symm
    _ ≤ (N : ℝ) * C ^ 2 * ((N : ℝ) * ∑ j ∈ S.biUnion rows, ‖x j‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (sum_neighbors_le rows cols hdual N hc S
        (fun j => ‖x j‖ ^ 2) (fun _ => sq_nonneg _)) (by positivity)
    _ ≤ (N : ℝ) * C ^ 2 * ((N : ℝ) * ‖x‖ ^ 2) := by
      gcongr
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) x (S.biUnion rows)
    _ = _ := by ring

def controlledMatrixLinear (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) : lp E 2 →ₗ[ℂ] lp E 2 where
  toFun x := ⟨matrixRow rows A x, by
    apply memℓp_gen'
    intro S
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      matrix_finite_norm_sq rows cols hdual A N C hC hr hc hA x S⟩
  map_add' x y := by
    apply lp.ext
    funext i
    change (∑ j ∈ rows i, A i j (x j + y j)) =
      (∑ j ∈ rows i, A i j (x j)) + ∑ j ∈ rows i, A i j (y j)
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp [matrixRow, map_smul, Finset.smul_sum]

theorem controlledMatrixLinear_norm_le (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) (x : lp E 2) :
    ‖controlledMatrixLinear rows cols hdual A N C hC hr hc hA x‖ ≤ (N : ℝ) * C * ‖x‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (by positivity)
  intro S
  change (∑ i ∈ S, ‖matrixRow rows A x i‖ ^ (2 : ENNReal).toReal) ≤
    ((N : ℝ) * C * ‖x‖) ^ (2 : ENNReal).toReal
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    matrix_finite_norm_sq rows cols hdual A N C hC hr hc hA x S

def controlledMatrix (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) : lp E 2 →L[ℂ] lp E 2 :=
  (controlledMatrixLinear rows cols hdual A N C hC hr hc hA).mkContinuous ((N : ℝ) * C)
    (controlledMatrixLinear_norm_le rows cols hdual A N C hC hr hc hA)

@[simp] theorem controlledMatrix_apply (rows cols : I → Finset I)
    (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j) (A : ∀ i j, E j →L[ℂ] E i)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
    (hA : ∀ i j, j ∈ rows i → ‖A i j‖ ≤ C) (x : lp E 2) (i : I) :
    controlledMatrix rows cols hdual A N C hC hr hc hA x i = ∑ j ∈ rows i, A i j (x j) := rfl

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

@[simp] theorem flattenOperator_apply
    (A : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2)
    (x : lp (fun _ : Sigma Q => H) 2) (i : I) (q : Q i) :
    flattenOperator A x ⟨i, q⟩ = A (unflattenVector x) i q := rfl

theorem flattenOperator_norm_le
    (A : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2) : ‖flattenOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  change ‖flattenEquiv (A ((flattenEquiv (Q := Q) (H := H)).symm x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    A.le_opNorm ((flattenEquiv (Q := Q) (H := H)).symm x)

variable [DecidableEq I] [∀ i, DecidableEq (Q i)]

omit [NormedSpace ℂ H] in
theorem rowVector_single_same (i : I) (q : Q i) (h : H) :
    rowVector (lp.single 2 ⟨i, q⟩ h) i = lp.single 2 q h := by
  apply lp.ext
  funext r
  change lp.single (E := fun _ : Sigma Q => H) 2 ⟨i, q⟩ h ⟨i, r⟩ =
    lp.single (E := fun _ : Q i => H) 2 q h r
  by_cases hr : r = q
  · subst r; simp
  · have hn : (⟨i, r⟩ : Sigma Q) ≠ ⟨i, q⟩ := by
      intro he
      cases he
      exact hr rfl
    simp [hr, hn]

omit [NormedSpace ℂ H] in
theorem rowVector_single_ne {i j : I} (hji : j ≠ i) (q : Q i) (h : H) :
    rowVector (lp.single 2 ⟨i, q⟩ h) j = 0 := by
  apply lp.ext
  funext r
  have hn : (⟨j, r⟩ : Sigma Q) ≠ ⟨i, q⟩ := fun he => hji (congrArg Sigma.fst he)
  change lp.single (E := fun _ : Sigma Q => H) 2 ⟨i, q⟩ h ⟨j, r⟩ = 0
  exact lp.single_apply_ne (E := fun _ : Sigma Q => H) 2 ⟨i, q⟩ h hn

section Matrix

variable (rows cols : I → Finset I) (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j)
variable (B : ∀ i j, lp (fun _ : Q j => H) 2 →L[ℂ] lp (fun _ : Q i => H) 2)
variable (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
variable (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
variable (hB : ∀ i j, j ∈ rows i → ‖B i j‖ ≤ C)

def spatialBlocks : lp (fun _ : Sigma Q => H) 2 →L[ℂ] lp (fun _ : Sigma Q => H) 2 :=
  flattenOperator (controlledMatrix rows cols hdual B N C hC hr hc hB)

omit [∀ i, DecidableEq (Q i)] in
@[simp] theorem spatialBlocks_apply (x : lp (fun _ : Sigma Q => H) 2) (i : I) (q : Q i) :
    spatialBlocks rows cols hdual B N C hC hr hc hB x ⟨i, q⟩ =
      (∑ j ∈ rows i, B i j (rowVector x j)) q := rfl

end Matrix

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_InclusionModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial module maps for inclusions

Extension by zero along an injection is an actual Hilbert-space isometry,
with the exact basis formula used for the boundary inclusions.
-/

noncomputable section

namespace CoarseAssembly

variable {X Y H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [NormedSpace ℂ H] in
theorem extendedFunction_apply (e : X ↪ Y) (x : lp (fun _ : X => H) 2) (a : X) :
    extendedFunction e x (e a) = x a := e.injective.extend_apply _ _ _

omit [NormedSpace ℂ H] in
theorem extendedFunction_zero (e : X ↪ Y) (x : lp (fun _ : X => H) 2)
    (y : Y) (hy : y ∉ Set.range e) : extendedFunction e x y = 0 :=
  Function.extend_apply' _ _ _ hy

omit [NormedSpace ℂ H] in
@[simp] theorem inclusionVector_apply (e : X ↪ Y) (x : lp (fun _ : X => H) 2) (a : X) :
    inclusionVector e x (e a) = x a := extendedFunction_apply e x a

omit [NormedSpace ℂ H] in
theorem inclusionVector_zero (e : X ↪ Y) (x : lp (fun _ : X => H) 2) (y : Y)
    (hy : y ∉ Set.range e) : inclusionVector e x y = 0 := extendedFunction_zero e x y hy

theorem inclusionIsometry_single [DecidableEq X] [DecidableEq Y]
    (e : X ↪ Y) (a : X) (h : H) :
    inclusionIsometry e (lp.single 2 a h) = lp.single 2 (e a) h := by
  apply lp.ext
  funext y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨b, rfl⟩ := hy
    change inclusionVector e (lp.single 2 a h) (e b) = _
    rw [inclusionVector_apply]
    simp only [lp.single_apply, Pi.single_apply, e.injective.eq_iff]
  · have hne : y ≠ e a := fun h => hy ⟨a, h.symm⟩
    change inclusionVector e (lp.single 2 a h) y = _
    rw [inclusionVector_zero e _ y hy, lp.single_apply_ne (E := fun _ : Y => H) 2 (e a) h hne]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Barycentric Rips realization and proper coarsening

Points are actual finitely supported probability weights with support of
bounded diameter. The topology is induced by the barycentric coordinates.
For a locally finite Rips complex this is its usual simplicial topology.
Increasing-scale inclusions are proved to be closed embeddings and therefore
proper, providing the continuous coarsening maps for analytic K-homology.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable (X : Type*) [PseudoMetricSpace X]

variable {X}

theorem coordinates_continuous {r : ℝ} : Continuous (coordinates (X := X) (r := r)) :=
  continuous_induced_dom

theorem coordinate_continuous {r : ℝ} (x : X) :
    Continuous (fun p : Point X r => p.weight x) :=
  (continuous_apply x).comp coordinates_continuous

@[simp] theorem coarsen_weight {r s : ℝ} (h : r ≤ s) (p : Point X r) :
    (coarsen h p).weight = p.weight := rfl

theorem coarsen_embedding {r s : ℝ} (h : r ≤ s) : IsEmbedding (coarsen (X := X) h) where
  eq_induced := by
    change TopologicalSpace.induced coordinates _ =
      TopologicalSpace.induced (coarsen h) (TopologicalSpace.induced coordinates _)
    rw [induced_compose]
    rfl
  injective := by
    intro p q heq
    apply Point.ext
    exact congrArg (fun p : Point X s => p.weight) heq

theorem range_coarsen {r s : ℝ} (h : r ≤ s) :
    Set.range (coarsen (X := X) h) =
      {p : Point X s | ∀ x y, r < dist x y → p.weight x = 0 ∨ p.weight y = 0} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ x y hxy
    by_cases hx : q.weight x = 0
    · exact Or.inl hx
    by_cases hy : q.weight y = 0
    · exact Or.inr hy
    exact False.elim ((not_le_of_gt hxy)
      (q.diameter x (Finsupp.mem_support_iff.mpr hx) y (Finsupp.mem_support_iff.mpr hy)))
  · intro hp
    let q : Point X r :=
      { weight := p.weight
        nonneg := p.nonneg
        total := p.total
        diameter := by
          intro x hx y hy
          by_contra hxy
          rcases hp x y (lt_of_not_ge hxy) with hx' | hy'
          · exact Finsupp.mem_support_iff.mp hx hx'
          · exact Finsupp.mem_support_iff.mp hy hy' }
    exact ⟨q, by apply Point.ext; rfl⟩

theorem coarsen_closedEmbedding {r s : ℝ} (h : r ≤ s) :
    IsClosedEmbedding (coarsen (X := X) h) := by
  refine ⟨coarsen_embedding h, ?_⟩
  rw [range_coarsen h]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter (fun x => isClosed_iInter (fun y => isClosed_iInter (fun _ => ?_)))
  exact (isClosed_eq (coordinate_continuous x) continuous_const).union
    (isClosed_eq (coordinate_continuous y) continuous_const)

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CocycleCircleMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The circle map of an integral Rips cocycle

On each finite component, barycentric interpolation of an integral edge
cocycle defines a genuine continuous map to `ℝ / ℤ`. The local real lifts
differ by the integral edge charge. This constructs the winding test in
the manuscript, rather than assuming its topological extension.
-/

noncomputable section

namespace CoarseAssembly.Rips

open scoped BigOperators
open Topology

variable {X : Type*} [PseudoMetricSpace X] {r : ℝ}

/-- Integral charges with the two identities required on a Rips simplex. -/
structure IntegralCocycle (X : Type*) [PseudoMetricSpace X] (r : ℝ) where
  charge : X → X → ℤ
  antisymm : ∀ x y, dist x y ≤ r → charge y x = -charge x y
  triangle : ∀ x y z, dist x y ≤ r → dist y z ≤ r → dist z x ≤ r →
    charge x y + charge y z + charge z x = 0

theorem IntegralCocycle.difference (c : IntegralCocycle X r) {x y z : X}
    (hxy : dist x y ≤ r) (hyz : dist y z ≤ r) (hzx : dist z x ≤ r) :
    c.charge x z - c.charge y z = c.charge x y := by
  have h := c.triangle x y z hxy hyz hzx
  rw [c.antisymm x z (by simpa only [dist_comm] using hzx)] at h
  omega

theorem Point.exists_positive (p : Point X r) : ∃ x, 0 < p.weight x := by
  classical
  by_contra! h
  have hz : p.weight = 0 := by
    ext x
    exact le_antisymm (h x) (p.nonneg x)
  have ht := p.total
  simp [hz] at ht

def Point.supportVertex (p : Point X r) : X := p.exists_positive.choose

theorem Point.supportVertex_positive (p : Point X r) :
    0 < p.weight p.supportVertex := p.exists_positive.choose_spec

theorem Point.supportVertex_mem (p : Point X r) :
    p.supportVertex ∈ p.weight.support :=
  Finsupp.mem_support_iff.mpr (ne_of_gt p.supportVertex_positive)

variable [Fintype X]

/-- Local real lift based at a vertex of the supporting simplex. -/
def IntegralCocycle.localAngle (c : IntegralCocycle X r) (x : X) (p : Point X r) : ℝ :=
  ∑ z : X, p.weight z * (c.charge x z : ℝ)

theorem IntegralCocycle.localAngle_continuous (c : IntegralCocycle X r) (x : X) :
    Continuous (c.localAngle x) := by
  unfold localAngle
  exact continuous_finsetSum _ (fun z _ => (coordinate_continuous z).mul continuous_const)

theorem Point.sum_weight (p : Point X r) : ∑ x : X, p.weight x = 1 := by
  rw [← p.total]
  exact (p.weight.sum_fintype (fun _ t => t) (by simp)).symm

/-- Changes of local lift are exactly the prescribed integral charges. -/
theorem IntegralCocycle.localAngle_sub (c : IntegralCocycle X r) (p : Point X r)
    {x y : X} (hx : x ∈ p.weight.support) (hy : y ∈ p.weight.support) :
    c.localAngle x p - c.localAngle y p = (c.charge x y : ℝ) := by
  classical
  unfold localAngle
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ z : X, (p.weight z * (c.charge x z : ℝ) -
        p.weight z * (c.charge y z : ℝ))) =
        ∑ z : X, p.weight z * (c.charge x y : ℝ) := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ p.weight.support
      · rw [← mul_sub]
        congr 1
        exact_mod_cast c.difference (p.diameter x hx y hy)
          (p.diameter y hy z hz) (p.diameter z hz x hx)
      · have hz' : p.weight z = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hz
        simp only [hz', zero_mul, sub_self]
    _ = (c.charge x y : ℝ) := by rw [← Finset.sum_mul, p.sum_weight, one_mul]

theorem IntegralCocycle.localAngle_coe_eq (c : IntegralCocycle X r) (p : Point X r)
    {x y : X} (hx : x ∈ p.weight.support) (hy : y ∈ p.weight.support) :
    (c.localAngle x p : AddCircle (1 : ℝ)) = c.localAngle y p := by
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, c.localAngle_sub p hx hy]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨c.charge x y, by simp⟩

/-- Barycentric interpolation of the cocycle, with values in the unit circle. -/
def IntegralCocycle.circleMap (c : IntegralCocycle X r) (p : Point X r) :
    AddCircle (1 : ℝ) := c.localAngle p.supportVertex p

theorem IntegralCocycle.circleMap_eq (c : IntegralCocycle X r) (p : Point X r)
    {x : X} (hx : x ∈ p.weight.support) :
    c.circleMap p = (c.localAngle x p : AddCircle (1 : ℝ)) :=
  c.localAngle_coe_eq p p.supportVertex_mem hx

theorem IntegralCocycle.circleMap_continuous (c : IntegralCocycle X r) :
    Continuous c.circleMap := by
  rw [continuous_iff_continuousAt]
  intro p
  let x := p.supportVertex
  have hx : {q : Point X r | 0 < q.weight x} ∈ 𝓝 p :=
    (isOpen_lt continuous_const (coordinate_continuous x)).mem_nhds
      p.supportVertex_positive
  have hc := ((AddCircle.continuous_mk' (1 : ℝ)).comp
    (c.localAngle_continuous x)).continuousAt (x := p)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hx] with q hq
  exact c.circleMap_eq q (Finsupp.mem_support_iff.mpr (ne_of_gt hq))

def IntegralCocycle.toContinuousMap (c : IntegralCocycle X r) :
    C(Point X r, AddCircle (1 : ℝ)) := ⟨c.circleMap, c.circleMap_continuous⟩

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paths in a finite Rips realization

Straight barycentric interpolation in a simplex, including its endpoint
and cocycle-lift formulas. These are paths in the actual realization.+-/

noncomputable section

namespace CoarseAssembly.Rips

open scoped BigOperators
open unitInterval

variable {X : Type*} [PseudoMetricSpace X] {r : ℝ}

@[simp] theorem vertex_weight (x : X) (hr : 0 ≤ r) :
    (vertex x hr).weight = Finsupp.single x 1 := rfl

def interpolate (p q : Point X r)
    (hpq : ∀ x ∈ p.weight.support, ∀ y ∈ q.weight.support, dist x y ≤ r)
    (t : unitInterval) : Point X r where
  weight := (1 - (t : ℝ)) • p.weight + (t : ℝ) • q.weight
  nonneg x := add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (p.nonneg x))
    (mul_nonneg t.2.1 (q.nonneg x))
  total := by
    rw [Finsupp.sum_add_index' (by simp) (by simp),
      Finsupp.sum_smul_index' (by simp), Finsupp.sum_smul_index' (by simp)]
    simp only [smul_eq_mul]
    rw [← Finsupp.mul_sum, ← Finsupp.mul_sum, p.total, q.total]
    ring
  diameter x hx y hy := by
    have support : ∀ z, z ∈ ((1 - (t : ℝ)) • p.weight + (t : ℝ) • q.weight).support →
        z ∈ p.weight.support ∨ z ∈ q.weight.support := by
      intro z hz
      by_contra! h
      have hpz := Finsupp.notMem_support_iff.mp h.1
      have hqz := Finsupp.notMem_support_iff.mp h.2
      simp [Finsupp.mem_support_iff, hpz, hqz] at hz
    rcases support x hx with hx | hx <;> rcases support y hy with hy | hy
    · exact p.diameter x hx y hy
    · exact hpq x hx y hy
    · simpa only [dist_comm] using hpq y hy x hx
    · exact q.diameter x hx y hy

theorem interpolate_continuous (p q : Point X r) (hpq) :
    Continuous (interpolate p q hpq) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  change Continuous (fun t : unitInterval => (1 - (t : ℝ)) * p.weight x + (t : ℝ) * q.weight x)
  fun_prop

@[simp] theorem interpolate_zero (p q : Point X r) (hpq) :
    interpolate p q hpq 0 = p := by
  apply Point.ext
  simp [interpolate]

@[simp] theorem interpolate_one (p q : Point X r) (hpq) :
    interpolate p q hpq 1 = q := by
  apply Point.ext
  simp [interpolate]

def simplexPath (p q : Point X r)
    (hpq : ∀ x ∈ p.weight.support, ∀ y ∈ q.weight.support, dist x y ≤ r) : Path p q where
  toFun := interpolate p q hpq
  continuous_toFun := interpolate_continuous p q hpq
  source' := interpolate_zero p q hpq
  target' := interpolate_one p q hpq

def edgePath {x y : X} (hxy : dist x y ≤ r) :
    Path (vertex x (dist_nonneg.trans hxy)) (vertex y (dist_nonneg.trans hxy)) :=
  simplexPath _ _ (by
    intro u hu v hv
    have hu' : u = x := by simpa using hu
    have hv' : v = y := by simpa using hv
    simpa [hu', hv'] using hxy)

variable [Fintype X]

omit [Fintype X] in
theorem IntegralCocycle.charge_self (c : IntegralCocycle X r) (hr : 0 ≤ r) (x : X) :
    c.charge x x = 0 := by
  have h := c.antisymm x x (by simpa using hr)
  omega

theorem IntegralCocycle.localAngle_vertex (c : IntegralCocycle X r)
    (hr : 0 ≤ r) (x y : X) : c.localAngle x (vertex y hr) = (c.charge x y : ℝ) := by
  classical
  simp [localAngle, Finsupp.single_apply]

@[simp] theorem IntegralCocycle.circleMap_vertex (c : IntegralCocycle X r)
    (hr : 0 ≤ r) (x : X) : c.circleMap (vertex x hr) = 0 := by
  rw [c.circleMap_eq _ (x := x) (by simp)]
  simp [c.localAngle_vertex, c.charge_self hr]

theorem IntegralCocycle.localAngle_interpolate (c : IntegralCocycle X r)
    (x : X) (p q : Point X r) (hpq) (t : unitInterval) :
    c.localAngle x (interpolate p q hpq t) =
      (1 - (t : ℝ)) * c.localAngle x p + (t : ℝ) * c.localAngle x q := by
  simp only [localAngle, interpolate, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- The edge has the real lift `t ↦ t * charge x y`. -/
theorem IntegralCocycle.circleMap_edgePath (c : IntegralCocycle X r)
    {x y : X} (hxy : dist x y ≤ r) (t : unitInterval) :
    c.circleMap (edgePath hxy t) = ((t : ℝ) * (c.charge x y : ℝ) : ℝ) := by
  have hr : 0 ≤ r := dist_nonneg.trans hxy
  by_cases ht : (t : ℝ) = 1
  · have ht' : t = 1 := Subtype.ext ht
    subst t
    simp only [Path.target, c.circleMap_vertex]
    exact ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨c.charge x y, by simp⟩).symm
  · have hx : x ∈ (edgePath hxy t).weight.support := by
      apply Finsupp.mem_support_iff.mpr
      change (1 - (t : ℝ)) * (Finsupp.single x 1 x) +
        (t : ℝ) * (Finsupp.single y 1 x) ≠ 0
      have hpos : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.2.2 ht)
      have hnn : 0 ≤ (Finsupp.single y (1 : ℝ) x) := (vertex y hr).nonneg x
      simpa only [Finsupp.single_eq_same, mul_one] using
        ne_of_gt (add_pos_of_pos_of_nonneg hpos (mul_nonneg t.2.1 hnn))
    rw [c.circleMap_eq _ hx]
    dsimp only [edgePath, simplexPath]
    simp only [Path.coe_mk_mk]
    rw [c.localAngle_interpolate, c.localAngle_vertex, c.localAngle_vertex,
      c.charge_self hr]
    simp

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CocyclePathLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer lifts and winding along graph walks

The real lift of the constructed circle map along an actual graph walk
ends at the sum of its edge charges. This is the topological degree
calculation used before applying the published circle index formula.
-/

noncomputable section

namespace CoarseAssembly

open unitInterval

section Lifts

variable {Y : Type*} [TopologicalSpace Y] (f : Y → AddCircle (1 : ℝ))
  {x y z : Y}

/-- A real path lift normalized to start at zero, with integral endpoint. -/
structure IntegerPathLift (p : Path x y) (n : ℤ) where
  path : Path (0 : ℝ) (n : ℝ)
  commutes : ∀ t, f (p t) = (path t : AddCircle (1 : ℝ))

def shiftedRealPath (a b : ℤ) (p : Path (0 : ℝ) (b : ℝ)) :
    Path (a : ℝ) ((a + b : ℤ) : ℝ) where
  toFun t := (a : ℝ) + p t
  continuous_toFun := continuous_const.add p.continuous
  source' := by simp
  target' := by simp

def IntegerPathLift.refl (hfx : f x = 0) :
    IntegerPathLift f (Path.refl x) 0 where
  path := (Path.refl (0 : ℝ)).cast rfl (by simp)
  commutes t := by simpa [Path.cast] using hfx

def IntegerPathLift.trans {p : Path x y} {q : Path y z} {a b : ℤ}
    (hp : IntegerPathLift f p a) (hq : IntegerPathLift f q b) :
    IntegerPathLift f (p.trans q) (a + b) where
  path := hp.path.trans (shiftedRealPath a b hq.path)
  commutes t := by
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with ht
    · exact hp.commutes _
    · change f (q _) = ((a : ℝ) + hq.path _ : ℝ)
      rw [hq.commutes, AddCircle.coe_add]
      have ha : ((a : ℝ) : AddCircle (1 : ℝ)) = 0 :=
        (AddCircle.coe_eq_zero_iff _).mpr ⟨a, by simp⟩
      rw [ha, zero_add]

end Lifts

namespace Rips

variable {X : Type*} [PseudoMetricSpace X] {r : ℝ}

/-- Follow the barycentric unit edges of a graph walk. -/
def walkPath {G : SimpleGraph X} (hr : 0 ≤ r)
    (hE : ∀ x y, G.Adj x y → dist x y ≤ r) :
    {x y : X} → G.Walk x y → Path (vertex x hr) (vertex y hr)
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (edgePath (hE _ _ h)).trans (walkPath hr hE p)

variable [Fintype X]

def IntegralCocycle.edgeLift (c : IntegralCocycle X r)
    {x y : X} (hxy : dist x y ≤ r) :
    IntegerPathLift c.circleMap (edgePath hxy) (c.charge x y) where
  path := Path.segment 0 (c.charge x y : ℝ)
  commutes t := by
    rw [c.circleMap_edgePath]
    simp only [Path.segment_apply, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      sub_zero, smul_eq_mul, add_zero]

def IntegralCocycle.walkLift (c : IntegralCocycle X r) {G : SimpleGraph X}
    (hr : 0 ≤ r) (hE : ∀ x y, G.Adj x y → dist x y ≤ r)
    {x y : X} (p : G.Walk x y) :
    IntegerPathLift c.circleMap (walkPath hr hE p) (walkCharge c.charge p) := by
  induction p with
  | nil => exact IntegerPathLift.refl _ (c.circleMap_vertex hr _)
  | cons h p ih => exact (c.edgeLift (hE _ _ h)).trans _ ih

end Rips

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simplicial embeddings and isolated Rips components

An injective nonexpanding vertex map induces the actual barycentric map.
For an isometric component separated from its complement at the Rips scale,
its realization is a clopen subspace. Finite components are compact, so the
inclusion is proper.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {r : ℝ}

@[simp] theorem mapPoint_weight_self (e : X ↪ Y) (he) (p : Point X r) (x : X) :
    (mapPoint e he p).weight (e x) = p.weight x :=
  Finsupp.embDomain_apply_self e p.weight x

theorem mapPoint_continuous (e : X ↪ Y) (he) : Continuous (mapPoint (r := r) e he) := by
  classical
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro y
  change Continuous (fun p : Point X r => coordinates (mapPoint e he p) y)
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    simpa only [coordinates, mapPoint, Finsupp.embDomain_apply_self] using
      coordinate_continuous (r := r) x
  · have hz : (fun p : Point X r => coordinates (mapPoint e he p) y) = fun _ => 0 := by
      funext p
      exact Finsupp.embDomain_of_notMem_range e p.weight y hy
    rw [hz]
    exact continuous_const

theorem mapPoint_injective (e : X ↪ Y) (he) : Function.Injective (mapPoint (r := r) e he) := by
  intro p q h
  apply Point.ext
  apply Finsupp.ext
  intro x
  have hx := congrArg (fun p : Point Y r => p.weight (e x)) h
  simpa only [mapPoint_weight_self] using hx

theorem coarsen_mapPoint {s : ℝ} (hrs : r ≤ s) (e : X ↪ Y) (he)
    (p : Point X r) : coarsen hrs (mapPoint e he p) = mapPoint e he (coarsen hrs p) := by
  apply Point.ext
  rfl

theorem mapPoint_range (e : X ↪ Y) (he : Isometry e) :
    Set.range (mapPoint (r := r) e (fun x y => (he.dist_eq x y).le)) =
      {q : Point Y r | ↑q.weight.support ⊆ Set.range e} := by
  classical
  ext q
  constructor
  · rintro ⟨p, rfl⟩ y hy
    rw [mapPoint, Finsupp.support_embDomain, Finset.mem_coe, Finset.mem_map] at hy
    obtain ⟨x, _, rfl⟩ := hy
    exact ⟨x, rfl⟩
  · intro hq
    refine ⟨unmapPoint e he q hq, ?_⟩
    apply Point.ext
    exact Finsupp.embDomain_comapDomain hq

theorem mapPoint_range_open (e : X ↪ Y) (he : Isometry e)
    (hsep : ∀ x y, y ∉ Set.range e → r < dist (e x) y) :
    IsOpen (Set.range (mapPoint (r := r) e (fun x y => (he.dist_eq x y).le))) := by
  rw [mapPoint_range e he]
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨y, hy⟩ := q.exists_positive
  obtain ⟨x, rfl⟩ := hq (Finsupp.mem_support_iff.mpr (ne_of_gt hy))
  have hnhds : {p : Point Y r | 0 < p.weight (e x)} ∈ 𝓝 q :=
    (isOpen_lt continuous_const (coordinate_continuous (e x))).mem_nhds hy
  apply Filter.mem_of_superset hnhds
  intro p hp y hy
  by_contra hnot
  exact (not_le_of_gt (hsep x y hnot))
    (p.diameter (e x) (Finsupp.mem_support_iff.mpr (ne_of_gt hp)) y hy)

theorem mapPoint_closedEmbedding [Fintype X] (e : X ↪ Y) (he) :
    IsClosedEmbedding (mapPoint (r := r) e he) :=
  (mapPoint_continuous e he).isClosedEmbedding (mapPoint_injective e he)

end CoarseAssembly.Rips

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

theorem walk_image_dist_le {V Z : Type*} (G : SimpleGraph V)
    [PseudoMetricSpace Z] (f : V → Z)
    (hedge : ∀ x y, G.Adj x y → dist (f x) (f y) ≤ 1)
    {x y : V} (p : G.Walk x y) : dist (f x) (f y) ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    calc
      dist (f x) (f z) ≤ dist (f x) (f y) + dist (f y) (f z) := dist_triangle _ _ _
      _ ≤ 1 + (p.length : ℝ) := add_le_add (hedge x y h) ih
      _ = ((SimpleGraph.Walk.cons h p).length : ℝ) := by simp <;> ring

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedRips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Late components are clopen at a fixed Rips scale

This proves the topological component separation required for the changing
finite-component winding test in the actual separated coarse union.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips

variable {V : ℕ → Type} [∀ j, MetricSpace (V j)]

theorem separatedComponent_isometry (o : ∀ j, V j) (j : ℕ) :
    letI := separatedMetric o
    Isometry (separatedComponent (V := V) j) := by
  let := separatedMetric o
  apply Isometry.of_dist_eq
  intro x y
  exact separatedDist_same o j x y

theorem separated_closedBall_finite [∀ j, Fintype (V j)]
    (o : ∀ j, V j) (x : Sigma V) (r : ℝ) :
    letI := separatedMetric o
    Set.Finite {y : Sigma V | dist x y ≤ r} := by
  classical
  let := separatedMetric o
  let m := max (x.1 + 1) (⌈r⌉₊ + 1)
  let s : Finset (Sigma V) := (Finset.range m).sigma (fun _ => Finset.univ)
  apply s.finite_toSet.subset
  intro y hy
  have hm : y.1 < m := by
    by_cases hxy : x.1 = y.1
    · dsimp [m]
      omega
    · have hb := (separatedDist_indices o x y hxy hy).2
      have hc : y.1 ≤ ⌈r⌉₊ := by exact_mod_cast hb.trans (Nat.le_ceil r)
      dsimp [m]
      omega
  exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hm, Finset.mem_univ _⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsFamilyMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proper maps from componentwise compact families into Rips realizations

The boundary family will be a countable family of parametrized circles.
Compact subsets of the target use finitely many vertices, hence meet only
finitely many members of this family. This proves properness directly.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips

variable {V : ℕ → Type} [∀ j, MetricSpace (V j)]
  {Z : ℕ → Type} [∀ j, TopologicalSpace (Z j)] [∀ j, CompactSpace (Z j)]

@[simp] theorem separatedRipsMap_weight (o : ∀ j, V j) (r : ℝ) (j : ℕ)
    (p : Point (V j) r) (x : V j) :
    letI := separatedMetric o
    (separatedRipsMap o r j p).weight ⟨j, x⟩ = p.weight x := by
  let := separatedMetric o
  exact mapPoint_weight_self (separatedComponent j)
    (fun x y => ((separatedComponent_isometry o j).dist_eq x y).le) p x

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ComponentInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Component-preserving inclusions of the separated graph unions -/

noncomputable section

namespace CoarseAssembly

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]

def componentEmbedding (e : ∀ i, Q i ↪ P i) : Sigma Q ↪ Sigma P where
  toFun x := ⟨x.1, e x.1 x.2⟩
  inj' := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hij : i = j := congrArg Sigma.fst h
    subst j
    have hxy : e i x = e i y := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
    exact congrArg (Sigma.mk i) ((e i).injective hxy)

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

omit [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)] in
theorem flattenOperator_eq_conjugation
    (A : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    flattenOperator A = operatorConjugation
      (flattenEquiv (Q := Q) (H := H)).toLinearIsometry A := by
  let e := flattenEquiv (Q := Q) (H := H)
  have he : e.toLinearIsometry.toContinuousLinearMap.adjoint =
      e.symm.toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.apply_symm_apply] using e.inner_map_map (e.symm x) y
  unfold flattenOperator operatorConjugation
  rw [he]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_IsometricExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a Fredholm operator by the identity off an isometric image -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricExtension_selfAdjoint (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E)
    (hF : IsSelfAdjoint F) : IsSelfAdjoint (isometricExtension V F) :=
  (IsSelfAdjoint.one (H →L[ℂ] H)).add
    ((hF.sub (IsSelfAdjoint.one (E →L[ℂ] E))).map
      (operatorConjugationHom V))

theorem isometricExtension_square_defect (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E) :
    isometricExtension V F * isometricExtension V F - 1 =
      operatorConjugation V (F * F - 1) := by
  let φ := operatorConjugationHom V
  have he : (F - 1) * (F - 1) + (F - 1) + (F - 1) = F * F - 1 := by noncomm_ring
  calc
    isometricExtension V F * isometricExtension V F - 1 =
        φ (F - 1) * φ (F - 1) + φ (F - 1) + φ (F - 1) := by
      change (1 + φ (F - 1)) * (1 + φ (F - 1)) - 1 = _
      noncomm_ring
    _ = φ ((F - 1) * (F - 1) + (F - 1) + (F - 1)) := by
      rw [map_add, map_add, map_mul]
    _ = operatorConjugation V (F * F - 1) := by rw [he]; rfl

theorem isometricExtension_square_compact (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E)
    (hF : IsCompactOperator (F * F - (1 : E →L[ℂ] E))) :
    IsCompactOperator (isometricExtension V F * isometricExtension V F -
      (1 : H →L[ℂ] H)) := by
  rw [isometricExtension_square_defect]
  exact (hF.comp_clm V.toContinuousLinearMap.adjoint).clm_comp V.toContinuousLinearMap

theorem operatorConjugation_norm_le (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E) :
    ‖operatorConjugation V F‖ ≤ ‖F‖ := by
  have hV := V.norm_toContinuousLinearMap_le
  have hVs : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hV
  have h1 : ‖V.toContinuousLinearMap.comp F‖ ≤ ‖V.toContinuousLinearMap‖ * ‖F‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h2 : ‖(V.toContinuousLinearMap.comp F).comp V.toContinuousLinearMap.adjoint‖ ≤
      ‖V.toContinuousLinearMap.comp F‖ * ‖V.toContinuousLinearMap.adjoint‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖operatorConjugation V F‖ ≤
        ‖V.toContinuousLinearMap‖ * ‖F‖ * ‖V.toContinuousLinearMap.adjoint‖ :=
      h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    _ ≤ 1 * ‖F‖ * 1 := by gcongr
    _ = ‖F‖ := by ring

theorem isometricExtension_norm_le (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E) :
    ‖isometricExtension V F‖ ≤ ‖F‖ + 2 := by
  have h1 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hd : ‖F - 1‖ ≤ ‖F‖ + 1 := (norm_sub_le _ _).trans (add_le_add le_rfl h1)
  calc
    ‖isometricExtension V F‖ ≤ ‖(1 : H →L[ℂ] H)‖ + ‖operatorConjugation V (F - 1)‖ :=
      norm_add_le _ _
    _ ≤ 1 + ‖F - 1‖ := add_le_add ContinuousLinearMap.norm_id_le
      (operatorConjugation_norm_le V _)
    _ ≤ 1 + (‖F‖ + 1) := add_le_add le_rfl hd
    _ = ‖F‖ + 2 := by ring

end CoarseAssembly

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

omit [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem componentEmbedding_range (e : ∀ i, Q i ↪ P i) (i : ℕ) (y : P i) :
    (⟨i, y⟩ : Sigma P) ∈ Set.range (componentEmbedding e) ↔ y ∈ Set.range (e i) := by
  constructor
  · rintro ⟨⟨j, x⟩, h⟩
    have hij : j = i := congrArg Sigma.fst h
    subst j
    refine ⟨x, ?_⟩
    change (⟨i, e i x⟩ : Sigma P) = ⟨i, y⟩ at h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  · rintro ⟨x, rfl⟩
    exact ⟨⟨i, x⟩, rfl⟩

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete multiplication representation on a discrete ample module -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped ZeroAtInfty

variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem scalarBlock_norm_le (z : ℂ) : ‖z • (1 : H →L[ℂ] H)‖ ≤ ‖z‖ := by
  exact (norm_smul_le z (1 : H →L[ℂ] H)).trans
    (mul_le_of_le_one_right (norm_nonneg z) ContinuousLinearMap.norm_id_le)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_EmbeddingTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The partial isometry comparing two Hilbert-space embeddings -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def embeddingTransition (V W : E →ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  W.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unitaries equal to one modulo a nonunital subalgebra

The scalar part is kept explicit, so no faithfulness assumption on a
unitization representation is needed to obtain its K₁ class.
-/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A : Type*} [CStarAlgebra A] (S : NonUnitalStarSubalgebra ℂ A)

@[simp] theorem relativeUnitary_val (u : unitary A) (hu : (u : A) - 1 ∈ S) :
    (relativeUnitary S u hu : Unitization ℂ S) =
      1 + (relativePart S u hu : Unitization ℂ S) := rfl

@[simp] theorem relativeUnitary_scalar (u : unitary A) (hu : (u : A) - 1 ∈ S) :
    (relativeUnitary S u hu : Unitization ℂ S).fst = 1 := by
  simp

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedFamilyBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Roe boundary class from a uniformly controlled separated family

The compact component defects need not decay in norm. Their direct sum is
nevertheless a finite-propagation operator with compact matrix entries,
which is the local compactness needed for the whole-union Roe algebra.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, DecidableEq (V i)] in
theorem separatedMetric_closedBall_finite (o : ∀ i, V i) (x : Sigma V) (r : ℝ) :
    letI := separatedMetric o
    (Metric.closedBall x r).Finite := by
  let := separatedMetric o
  simpa only [Metric.closedBall, dist_comm] using separated_closedBall_finite o x r

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homotopy invariance of relative unitary classes -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open Analytic

variable {A P : Type*} [CStarAlgebra A] [TopologicalSpace P]
variable (S : NonUnitalStarSubalgebra ℂ A) [hS : IsClosed (S : Set A)]

theorem continuous_relativeUnitary (u : P → unitary A)
    (hu : ∀ p, (u p : A) - 1 ∈ S) (hcont : Continuous (fun p => (u p : A))) :
    Continuous (fun p => (relativeUnitary S (u p) (hu p) : Unitization ℂ S)) := by
  have hr : Continuous (fun p => relativePart S (u p) (hu p)) :=
    (hcont.sub continuous_const).subtype_mk hu
  exact continuous_const.add (Unitization.continuous_inr.comp hr)

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteHeadNormalization
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

def finiteHeadRadius (J : Finset ℕ) : ℝ := ∑ i ∈ J, ∑ x : V i, ∑ y : V i, dist x y

omit [∀ i, DecidableEq (V i)] in
theorem finiteHeadRadius_diam (J : Finset ℕ) {i : ℕ} (hi : i ∈ J) (x y : V i) :
    dist x y ≤ finiteHeadRadius (V := V) J := by
  have h1 : dist x y ≤ ∑ z : V i, dist x z :=
    Finset.single_le_sum (f := fun z : V i => dist x z) (fun _ _ => dist_nonneg) (Finset.mem_univ y)
  have h2 : (∑ z : V i, dist x z) ≤ ∑ z : V i, ∑ w : V i, dist z w :=
    Finset.single_le_sum (f := fun z : V i => ∑ w : V i, dist z w)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)) (Finset.mem_univ x)
  have h3 : (∑ z : V i, ∑ w : V i, dist z w) ≤ finiteHeadRadius (V := V) J :=
    Finset.single_le_sum (f := fun j => ∑ z : V j, ∑ w : V j, dist z w)
      (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => dist_nonneg))) hi
  exact h1.trans (h2.trans h3)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsMapCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact naturality of the parametrized Rips paths

Injective nonexpanding vertex maps commute with barycentric interpolation,
edge paths and concatenated graph walks, including their parametrizations.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  {r : ℝ}

theorem mapPoint_comp (e : X ↪ Y) (f : Y ↪ Z) (he) (hf) (p : Point X r) :
    mapPoint f hf (mapPoint e he p) =
      mapPoint (e.trans f) (fun x y => (hf (e x) (e y)).trans (he x y)) p := by
  apply Point.ext
  exact (Finsupp.embDomain_trans_apply p.weight e f).symm

theorem mapPoint_vertex (e : X ↪ Y) (he) (x : X) (hr : 0 ≤ r) :
    mapPoint e he (vertex x hr) = vertex (e x) hr := by
  apply Point.ext
  exact Finsupp.embDomain_single e x 1

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_InclusionFunctoriality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composition of the actual geometric and spatial inclusion maps -/

noncomputable section

namespace CoarseAssembly

variable {X Y Z H : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem inclusionIsometry_comp (e : X ↪ Y) (f : Y ↪ Z) :
    (inclusionIsometry (H := H) f).comp (inclusionIsometry (H := H) e) =
      inclusionIsometry (H := H) (e.trans f) := by
  have hc : ((inclusionIsometry (H := H) f).comp (inclusionIsometry (H := H) e)).toContinuousLinearMap =
      (inclusionIsometry (H := H) (e.trans f)).toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
    intro x
    apply ContinuousLinearMap.ext
    intro h
    change inclusionIsometry f (inclusionIsometry e (lp.single 2 x h)) =
      inclusionIsometry (e.trans f) (lp.single 2 x h)
    rw [inclusionIsometry_single, inclusionIsometry_single, inclusionIsometry_single]
    rfl
  apply DFunLike.ext
  intro v
  exact DFunLike.congr_fun hc v

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeTwoByTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two-by-two relative unitaries for the spatial stabilization argument -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def matrixTwoStarHom (φ : A →⋆ₙₐ[ℂ] B) :
    Matrix (Fin 2) (Fin 2) A →⋆ₙₐ[ℂ] Matrix (Fin 2) (Fin 2) B where
  toFun T := T.map φ
  map_zero' := by ext i j; exact map_zero φ
  map_add' T U := by ext i j; exact map_add φ _ _
  map_mul' T U := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  map_smul' z T := by ext i j; exact map_smul φ z _
  map_star' T := by ext i j; exact map_star φ _

theorem matrixTwoStarHom_injective (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) :
    Function.Injective (matrixTwoStarHom φ) := by
  intro T U h
  ext i j
  apply hφ
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M i j) h

theorem matrixTwoStarHom_continuous (φ : A →⋆ₙₐ[ℂ] B) (hφ : Continuous φ) :
    Continuous (matrixTwoStarHom φ) := by
  exact continuous_pi (fun i => continuous_pi (fun j =>
    hφ.comp ((continuous_apply j).comp (continuous_apply i))))

section Relative

variable {R : Type*} [CStarAlgebra R] (S : NonUnitalStarSubalgebra ℂ R)

def relativeTwoPart (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    Matrix (Fin 2) (Fin 2) S :=
  fun i j => ⟨((u : Matrix (Fin 2) (Fin 2) R) - 1) i j, hu i j⟩

variable [hS : IsClosed (S : Set R)]

theorem relativeTwoPart_coe (u : unitary (Matrix (Fin 2) (Fin 2) R)) (hu) :
    matrixTwoStarHom (NonUnitalStarSubalgebraClass.subtype S) (relativeTwoPart S u hu) =
      (u : Matrix (Fin 2) (Fin 2) R) - 1 := rfl

theorem relativeTwoPart_star_mul (u : unitary (Matrix (Fin 2) (Fin 2) R)) (hu) :
    relativeTwoPart S u hu + star (relativeTwoPart S u hu) +
      star (relativeTwoPart S u hu) * relativeTwoPart S u hu = 0 := by
  apply matrixTwoStarHom_injective (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective
  simp only [map_add, map_mul, map_star, map_zero, relativeTwoPart_coe]
  rw [star_sub, star_one]
  have h := Unitary.coe_star_mul_self u
  change star (u : Matrix (Fin 2) (Fin 2) R) * (u : Matrix (Fin 2) (Fin 2) R) = 1 at h
  noncomm_ring [h]

theorem relativeTwoPart_mul_star (u : unitary (Matrix (Fin 2) (Fin 2) R)) (hu) :
    star (relativeTwoPart S u hu) + relativeTwoPart S u hu +
      relativeTwoPart S u hu * star (relativeTwoPart S u hu) = 0 := by
  apply matrixTwoStarHom_injective (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective
  simp only [map_add, map_mul, map_star, map_zero, relativeTwoPart_coe]
  rw [star_sub, star_one]
  have h := Unitary.coe_mul_star_self u
  change (u : Matrix (Fin 2) (Fin 2) R) * star (u : Matrix (Fin 2) (Fin 2) R) = 1 at h
  noncomm_ring [h]

def relativeTwoUnitary (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    unitary (Matrix (Fin 2) (Fin 2) (Unitization ℂ S)) := by
  let φ := matrixTwoStarHom (Unitization.inrNonUnitalStarAlgHom ℂ S)
  let P := relativeTwoPart S u hu
  refine ⟨1 + φ P, ?_, ?_⟩
  · change star (1 + φ P) * (1 + φ P) = 1
    calc
      _ = 1 + (φ P + star (φ P) + star (φ P) * φ P) := by
        rw [star_add, star_one]
        noncomm_ring
      _ = 1 + φ (P + star P + star P * P) := by rw [map_add, map_add, map_mul, map_star]
      _ = 1 := by rw [relativeTwoPart_star_mul, map_zero, add_zero]
  · change (1 + φ P) * star (1 + φ P) = 1
    calc
      _ = 1 + (star (φ P) + φ P + φ P * star (φ P)) := by
        rw [star_add, star_one]
        noncomm_ring
      _ = 1 + φ (star P + P + P * star P) := by rw [map_add, map_add, map_mul, map_star]
      _ = 1 := by rw [relativeTwoPart_mul_star, map_zero, add_zero]

end Relative

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeTwoHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative two-by-two classes and their actual norm homotopies -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open Analytic

variable {R : Type*} [CStarAlgebra R]
variable (S : NonUnitalStarSubalgebra ℂ R) [hS : IsClosed (S : Set R)]

variable {P : Type*} [TopologicalSpace P]

theorem continuous_relativeTwoUnitary (u : P → unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ p i j, ((u p : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S)
    (hc : Continuous (fun p => (u p : Matrix (Fin 2) (Fin 2) R))) :
    Continuous (fun p => (relativeTwoUnitary S (u p) (hu p)).val) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hp : Continuous (fun p => relativeTwoPart S (u p) (hu p) i j) :=
    (((continuous_apply j).comp ((continuous_apply i).comp hc)).sub continuous_const).subtype_mk
      (fun p => hu p i j)
  exact continuous_const.add (Unitization.continuous_inr.comp hp)

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeTwoDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal relative matrices and addition in Roe K₁ -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {R : Type*} [CStarAlgebra R]

def diagonalTwoUnitary (u v : unitary R) : unitary (Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨Matrix.diagonal (fun i => if i = 0 then (u : R) else (v : R)), ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal]
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal]

variable (S : NonUnitalStarSubalgebra ℂ R) [hS : IsClosed (S : Set R)]

omit hS in
theorem diagonalTwoUnitary_relative (u v : unitary R)
    (hu : (u : R) - 1 ∈ S) (hv : (v : R) - 1 ∈ S) :
    ∀ i j, ((diagonalTwoUnitary u v : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [diagonalTwoUnitary, Matrix.diagonal] using hu
  · simp [diagonalTwoUnitary, Matrix.diagonal]
  · simp [diagonalTwoUnitary, Matrix.diagonal]
  · simpa [diagonalTwoUnitary, Matrix.diagonal] using hv

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeTwoConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative two-by-two conjugation by idealizing operators -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A R : Type*} [CStarAlgebra A] [CStarAlgebra R]

def matrixTwoUnitalStarHom (φ : A →⋆ₐ[ℂ] R) :
    Matrix (Fin 2) (Fin 2) A →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) R :=
  { matrixTwoStarHom φ.toNonUnitalStarAlgHom with
    map_one' := by
      ext i j
      by_cases h : i = j <;> simp [matrixTwoStarHom, Matrix.one_apply, h]
    commutes' := by
      intro z
      ext i j
      by_cases h : i = j <;>
        simp [matrixTwoStarHom, Algebra.algebraMap_eq_smul_one, h] }

@[simp] theorem matrixTwoUnitalStarHom_apply (φ : A →⋆ₐ[ℂ] R)
    (M : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    matrixTwoUnitalStarHom φ M i j = φ (M i j) := rfl

theorem matrixTwoUnitalStarHom_continuous (φ : A →⋆ₐ[ℂ] R) (hc : Continuous φ) :
    Continuous (matrixTwoUnitalStarHom φ) :=
  matrixTwoStarHom_continuous φ.toNonUnitalStarAlgHom hc

def mapTwoUnitary (φ : A →⋆ₐ[ℂ] R)
    (u : unitary (Matrix (Fin 2) (Fin 2) A)) :
    unitary (Matrix (Fin 2) (Fin 2) R) :=
  Unitary.map (StarMonoidHom.ofClass (matrixTwoUnitalStarHom φ)) u

@[simp] theorem mapTwoUnitary_diagonal (φ : A →⋆ₐ[ℂ] R) (u v : unitary A) :
    mapTwoUnitary φ (diagonalTwoUnitary u v) =
      diagonalTwoUnitary (Unitary.map (StarMonoidHom.ofClass φ) u) (Unitary.map (StarMonoidHom.ofClass φ) v) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mapTwoUnitary, diagonalTwoUnitary, Matrix.diagonal, matrixTwoUnitalStarHom, matrixTwoStarHom]

def conjugatedTwoUnitary (w u : unitary (Matrix (Fin 2) (Fin 2) R)) :
    unitary (Matrix (Fin 2) (Fin 2) R) := w * u * star w

theorem conjugatedTwoUnitary_defect (w u : unitary (Matrix (Fin 2) (Fin 2) R)) :
    (conjugatedTwoUnitary w u : Matrix (Fin 2) (Fin 2) R) - 1 =
      (w : Matrix (Fin 2) (Fin 2) R) * ((u : Matrix (Fin 2) (Fin 2) R) - 1) *
        star (w : Matrix (Fin 2) (Fin 2) R) := by
  change w.val * u.val * star w.val - 1 = w.val * (u.val - 1) * star w.val
  have hw : w.val * star w.val = 1 := by
    have h := Unitary.coe_mul_star_self w
    change w.val * star w.val = 1 at h
    exact h
  rw [mul_sub, mul_one, sub_mul, hw]

@[simp] theorem mapTwoUnitary_one (φ : A →⋆ₐ[ℂ] R) : mapTwoUnitary φ 1 = 1 := by
  apply Subtype.ext
  exact map_one (matrixTwoUnitalStarHom φ)

theorem mapTwoUnitary_conjugate (φ : A →⋆ₐ[ℂ] R)
    (w u : unitary (Matrix (Fin 2) (Fin 2) A)) :
    mapTwoUnitary φ (conjugatedTwoUnitary w u) =
      conjugatedTwoUnitary (mapTwoUnitary φ w) (mapTwoUnitary φ u) := by
  apply Subtype.ext
  change matrixTwoUnitalStarHom φ (w.val * u.val * star w.val) =
    matrixTwoUnitalStarHom φ w.val * matrixTwoUnitalStarHom φ u.val *
      star (matrixTwoUnitalStarHom φ w.val)
  rw [map_mul, map_mul, map_star]

variable (S : NonUnitalStarSubalgebra ℂ R)

/-- The entries of the conjugation defect remain in the idealized algebra. -/
theorem conjugatedTwoUnitary_relative (φ : A →⋆ₐ[ℂ] R)
    (hφ : ∀ a b, b ∈ S → φ a * b ∈ S ∧ b * φ a ∈ S)
    (w : unitary (Matrix (Fin 2) (Fin 2) A))
    (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    ∀ i j, ((conjugatedTwoUnitary (mapTwoUnitary φ w) u :
      Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S := by
  intro i j
  rw [conjugatedTwoUnitary_defect]
  simp only [Matrix.mul_apply]
  apply S.sum_mem
  intro k _
  rw [Finset.sum_mul]
  apply S.sum_mem
  intro l _
  rw [Matrix.star_apply]
  change φ (w.val i l) * ((u.val - 1) l k) * star (φ (w.val j k)) ∈ S
  rw [← map_star]
  exact (hφ (star (w.val j k)) _ ((hφ (w.val i l) _ (hu l k)).1)).2

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplication of relative unitaries adds their actual K₁ classes -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A : Type*} [CStarAlgebra A] (S : NonUnitalStarSubalgebra ℂ A)

theorem relative_mul_mem (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    ((u * v : unitary A) : A) - 1 ∈ S := by
  have he : (u : A) * (v : A) - 1 =
      ((u : A) - 1) + ((v : A) - 1) + ((u : A) - 1) * ((v : A) - 1) := by
    noncomm_ring
  change (u : A) * (v : A) - 1 ∈ S
  rw [he]
  exact S.add_mem (S.add_mem hu hv) (S.mul_mem hu hv)

theorem relativePart_mul (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    relativePart S (u * v) (relative_mul_mem S u v hu hv) =
      relativePart S u hu + relativePart S v hv + relativePart S u hu * relativePart S v hv := by
  apply Subtype.ext
  change (u : A) * (v : A) - 1 = _
  change (u : A) * (v : A) - 1 =
    ((u : A) - 1) + ((v : A) - 1) + ((u : A) - 1) * ((v : A) - 1)
  noncomm_ring

theorem relativeUnitary_mul (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    relativeUnitary S (u * v) (relative_mul_mem S u v hu hv) =
      relativeUnitary S u hu * relativeUnitary S v hv := by
  apply Subtype.ext
  change 1 + (relativePart S (u * v) (relative_mul_mem S u v hu hv) : Unitization ℂ S) =
    (1 + (relativePart S u hu : Unitization ℂ S)) *
      (1 + (relativePart S v hv : Unitization ℂ S))
  rw [relativePart_mul S u v hu hv, Unitization.inr_add, Unitization.inr_add, Unitization.inr_mul]
  noncomm_ring

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_MultiplierOrthogonalEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Addition of actual Roe boundaries supported in orthogonal images -/

noncomputable section

namespace CoarseAssembly

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorConjugation_orthogonal (V : E →ₗᵢ[ℂ] H) (W : F →ₗᵢ[ℂ] H)
    (hVW : V.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap = 0)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    operatorConjugation V A * operatorConjugation W B = 0 := by
  ext x
  change V (A (V.toContinuousLinearMap.adjoint (W (B (W.toContinuousLinearMap.adjoint x))))) = 0
  have hz : V.toContinuousLinearMap.adjoint (W (B (W.toContinuousLinearMap.adjoint x))) = 0 :=
    DFunLike.congr_fun hVW _
  rw [hz, map_zero, map_zero]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsPartition
attribute [-simp] _root_.OAI.CoarseAssembly.Rips.mapPoint_weight_self _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit square partition on a finite Rips realization -/

noncomputable section

namespace CoarseAssembly.Rips

variable {X : Type} [PseudoMetricSpace X] [Fintype X] (r : ℝ)

omit [Fintype X] in
@[simp] theorem sqrtCoordinate_selfAdjoint (x : X) :
    IsSelfAdjoint (sqrtCoordinate r x) := by
  ext p
  simp [sqrtCoordinate]

theorem sqrtCoordinate_square_sum :
    ∑ x : X, sqrtCoordinate r x * sqrtCoordinate r x = 1 := by
  ext p
  change (ContinuousMap.evalAlgHom ℂ ℂ p)
    (∑ x : X, sqrtCoordinate r x * sqrtCoordinate r x) = 1
  rw [map_sum]
  simp only [map_mul]
  change (∑ x : X, (Real.sqrt (p.weight x) : ℂ) * (Real.sqrt (p.weight x) : ℂ)) = 1
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt (p.nonneg _)]
  rw [← Complex.ofReal_sum, p.sum_weight, Complex.ofReal_one]

omit [Fintype X] in
theorem sqrtCoordinate_mul_eq_zero (x y : X) (hxy : r < dist x y) :
    sqrtCoordinate r x * sqrtCoordinate r y = 0 := by
  ext p
  have hz : p.weight x = 0 ∨ p.weight y = 0 := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hxy) (p.diameter x (Finsupp.mem_support_iff.mpr h.1)
      y (Finsupp.mem_support_iff.mpr h.2))
  rcases hz with hx | hy
  · simp [sqrtCoordinate, hx]
  · simp [sqrtCoordinate, hy]

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionCompactPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact perturbations through the actual localization operators -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricExtension_sub (V : E →ₗᵢ[ℂ] H) (F G : E →L[ℂ] E) :
    isometricExtension V F - isometricExtension V G = operatorConjugation V (F - G) := by
  unfold isometricExtension
  change (1 + operatorConjugationHom V (F - 1)) -
    (1 + operatorConjugationHom V (G - 1)) = operatorConjugationHom V (F - G)
  have he : (F - 1) - (G - 1) = F - G := by abel
  calc
    _ = operatorConjugationHom V (F - 1) - operatorConjugationHom V (G - 1) := by abel
    _ = operatorConjugationHom V ((F - 1) - (G - 1)) := (map_sub _ _ _).symm
    _ = _ := by rw [he]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeNearby
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nearby relative unitaries have the same actual Roe K₁ class -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A : Type*} [CStarAlgebra A]
  (S : NonUnitalStarSubalgebra ℂ A) [hS : IsClosed (S : Set A)]

theorem relativeUnitary_sub_norm (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    ‖(relativeUnitary S v hv : Unitization ℂ S) - relativeUnitary S u hu‖ = ‖(v : A) - u‖ := by
  have he : (relativeUnitary S v hv : Unitization ℂ S) - relativeUnitary S u hu =
      ((relativePart S v hv - relativePart S u hu : S) : Unitization ℂ S) := by
    rw [Unitization.inr_sub, relativeUnitary_val, relativeUnitary_val]
    abel
  rw [he, Unitization.norm_inr]
  change ‖((v : A) - 1) - ((u : A) - 1)‖ = ‖(v : A) - u‖
  congr 1
  abel

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsInclusionNaturality
attribute [-simp] _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-Rips localization respects an actual vertex inclusion -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (r : ℝ) (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) ≤ dist x y)

def inclusionFunctionHom : C(Point Y r, ℂ) →⋆ₐ[ℂ] C(Point X r, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ ⟨mapPoint e he, mapPoint_continuous e he⟩

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem inclusionFunctionHom_sqrt (x : X) :
    inclusionFunctionHom r e he (sqrtCoordinate r (e x)) = sqrtCoordinate r x := by
  ext p
  change (Real.sqrt ((mapPoint e he p).weight (e x)) : ℂ) = _
  rw [mapPoint_weight_self]
  rfl

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem inclusionFunctionHom_sqrt_zero (y : Y) (hy : y ∉ Set.range e) :
    inclusionFunctionHom r e he (sqrtCoordinate r y) = 0 := by
  ext p
  change (Real.sqrt ((mapPoint e he p).weight y) : ℂ) = 0
  rw [show (mapPoint e he p).weight y = 0 from
    Finsupp.embDomain_of_notMem_range e p.weight y hy]
  simp

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric reindexing of coarse homology

The two sigma-type presentations of the fibered vertex set give isomorphic
Rips coarsening limits. This is used to compare the graph detector with the
vertex indexing of the spatial transfer.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

universe u

variable {X Y : Type u} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem equiv_inverse_isometry (e : X ≃ Y) (he : Isometry e) : Isometry e.symm := by
  apply Isometry.of_dist_eq
  intro x y
  simpa only [Equiv.apply_symm_apply] using (he.dist_eq (e.symm x) (e.symm y)).symm

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsScaleCompatibility
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

def scaleFunctionHom : C(Point X s, ℂ) →⋆ₐ[ℂ] C(Point X r, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ ⟨coarsen hrs, (coarsen_closedEmbedding hrs).continuous⟩

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SandwichNormControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform estimates for changing localization isometries -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def operatorSandwich (P : E →L[ℂ] H) (F : E →L[ℂ] E) : H →L[ℂ] H :=
  P.comp (F.comp P.adjoint)

theorem operatorSandwich_sub_norm_le (P Q : E →L[ℂ] H)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (F G : E →L[ℂ] E) (C : ℝ) (hG : ‖G‖ ≤ C) :
    ‖operatorSandwich P F - operatorSandwich Q G‖ ≤
      ‖F - G‖ + 2 * C * ‖P - Q‖ := by
  have hC : 0 ≤ C := (norm_nonneg G).trans hG
  have hPa : ‖P.adjoint‖ ≤ 1 := by simpa only [ContinuousLinearMap.adjoint.norm_map] using hP
  have hd : ‖P.adjoint - Q.adjoint‖ = ‖P - Q‖ := by
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
  have h1 : ‖P.comp ((F - G).comp P.adjoint)‖ ≤ ‖F - G‖ := by
    calc
      _ ≤ ‖P‖ * (‖F - G‖ * ‖P.adjoint‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖F - G‖ * 1) := by gcongr
      _ = _ := by ring
  have h2 : ‖(P - Q).comp (G.comp P.adjoint)‖ ≤ C * ‖P - Q‖ := by
    calc
      _ ≤ ‖P - Q‖ * (‖G‖ * ‖P.adjoint‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖P - Q‖ * (C * 1) := by gcongr
      _ = _ := by ring
  have h3 : ‖Q.comp (G.comp (P.adjoint - Q.adjoint))‖ ≤ C * ‖P - Q‖ := by
    calc
      _ ≤ ‖Q‖ * (‖G‖ * ‖P.adjoint - Q.adjoint‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (C * ‖P - Q‖) := by rw [hd]; gcongr
      _ = _ := by ring
  have he : operatorSandwich P F - operatorSandwich Q G =
      P.comp ((F - G).comp P.adjoint) + (P - Q).comp (G.comp P.adjoint) +
        Q.comp (G.comp (P.adjoint - Q.adjoint)) := by
    simp only [operatorSandwich, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖P.comp ((F - G).comp P.adjoint)‖ + ‖(P - Q).comp (G.comp P.adjoint)‖ +
        ‖Q.comp (G.comp (P.adjoint - Q.adjoint))‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖F - G‖ + C * ‖P - Q‖ + C * ‖P - Q‖ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_Kazhdan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary

abbrev Residue3 := Fin 3 → ZMod 2

end NuclearUltrapower.Elementary
end
end

end OAI
end


