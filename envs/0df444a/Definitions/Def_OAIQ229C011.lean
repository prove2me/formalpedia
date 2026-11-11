-- Prove2me | Definitions.Def_OAIQ229C011
-- name    : OAIQ229C011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:57:30.750481+00:00
-- url     : https://prove2.me/theorems/24ebf0d3-0345-4d81-bcb9-fa655a432fbb
-- title:
--   Definitions bundle OAIQ229C011 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 145 declarations of OpenAI's Lean: 62 definitions, 2 inductive types or structures, 3 instances and 78 theorems. The definitions and types are `OAI.CoarseAssembly.HexDirection.eval`, `OAI.CoarseAssembly.HexDirection.potential`, `OAI.CoarseAssembly.HexagonalBoundaryWalks`, `OAI.CoarseAssembly.OperatorKTheory.relativeTwoClass`, `OAI.CoarseAssembly.OperatorKTheory.relativeTwoMatrix`, `OAI.CoarseAssembly.PublishedCircleInput`, `OAI.CoarseAssembly.Rips.classAt`, `OAI.CoarseAssembly.TopologicalK1.diagonalTwoUnits`, `OAI.CoarseAssembly.TopologicalK1.flipTwoUnits`, `OAI.CoarseAssembly.TopologicalK1.nearbyUnitPath`, `OAI.CoarseAssembly.TopologicalK1.scalarUnitMatrix`, `OAI.CoarseAssembly.amplifyFiber`, `OAI.CoarseAssembly.assembledDiscEq`, `OAI.CoarseAssembly.assemblyBoundaryComponentMetric`, `OAI.CoarseAssembly.assemblyBoundaryEq`, `OAI.CoarseAssembly.assemblyFiberComponentMetric`, `OAI.CoarseAssembly.assemblyFiberEq`, `OAI.CoarseAssembly.baseBoundaryLoops`, `OAI.CoarseAssembly.boundaryBaseHom`, `OAI.CoarseAssembly.boundaryBaseIsometry`, `OAI.CoarseAssembly.boundaryCharge`, `OAI.CoarseAssembly.boundaryComponentMetric`, `OAI.CoarseAssembly.boundaryComponentToBase`, `OAI.CoarseAssembly.boundaryComponentsMetric`, `OAI.CoarseAssembly.boundaryFamilyMap`, `OAI.CoarseAssembly.boundaryFiberEmbedding`, `OAI.CoarseAssembly.boundaryGraph`, `OAI.CoarseAssembly.boundaryLoopMetric1`, `OAI.CoarseAssembly.boundaryLoopMetric2`, `OAI.CoarseAssembly.boundaryLoopMetric3`, `OAI.CoarseAssembly.boundaryLoopMetric5`, `OAI.CoarseAssembly.boundaryReindex`, `OAI.CoarseAssembly.boundaryRoot`, `OAI.CoarseAssembly.boundaryToBase`, `OAI.CoarseAssembly.boundaryTotalCoarsening`, `OAI.CoarseAssembly.boundaryTotalRoeHom`, `OAI.CoarseAssembly.boundaryVertexIsometry`, `OAI.CoarseAssembly.concreteDiagramBoundaryComponentMetric`, `OAI.CoarseAssembly.concreteDiagramBoundaryEq`, `OAI.CoarseAssembly.concreteDiagramBoundaryMetric` and 24 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BoundaryAssemblyMaps`, `CoarseAssembly_BoundaryComponents`, `CoarseAssembly_BoundaryEmbedding`, `CoarseAssembly_BoundaryGeometry`, `CoarseAssembly_BoundaryLoopMaps`, `CoarseAssembly_BoundaryWalks`, `CoarseAssembly_CirclePairing`, `CoarseAssembly_ComponentInclusion`, `CoarseAssembly_ComponentRipsPreimage`, `CoarseAssembly_ConcreteIndexDiagrams`, `CoarseAssembly_ConcreteIndexFamilies`, `CoarseAssembly_ConcreteIndexSquares`, `CoarseAssembly_ConcreteSpaces`, `CoarseAssembly_ConstructedBoundaryAssembly`, `CoarseAssembly_EmbeddingTransition`, `CoarseAssembly_ExplicitBoundaryRepresentative`, `CoarseAssembly_FamilyFilling`, `CoarseAssembly_FiberDegree`, `CoarseAssembly_FilledEdges`, `CoarseAssembly_FilledWalks`, `CoarseAssembly_FiniteCompactRoe`, `CoarseAssembly_FiniteHeadBoundary`, `CoarseAssembly_HexagonSides`, `CoarseAssembly_InclusionFunctoriality`, `CoarseAssembly_IsometricDecomposition`, `CoarseAssembly_K1Nearby`, `CoarseAssembly_K1TwoByTwo`, `CoarseAssembly_Lattice`, `CoarseAssembly_LatticeCharge`, `CoarseAssembly_LoopCircle`, `CoarseAssembly_NonUnitalK1`, `CoarseAssembly_PartitionInclusion`, `CoarseAssembly_RelativeHomotopy`, `CoarseAssembly_RelativeMultiplication`, `CoarseAssembly_RelativeNaturality`, `CoarseAssembly_RelativeNearby`, `CoarseAssembly_RelativeTwoConjugation`, `CoarseAssembly_RelativeTwoDiagonal`, `CoarseAssembly_RelativeTwoHomotopy`, `CoarseAssembly_RelativeUnitary`, `CoarseAssembly_RipsBoundaryDegeneracy`, `CoarseAssembly_RipsCompactSupport`, `CoarseAssembly_RipsFamilyMap`, `CoarseAssembly_RipsFamilyRestriction`, `CoarseAssembly_RipsRealClass`, `CoarseAssembly_RipsUnitaryLocalization`, `CoarseAssembly_Roe`, `CoarseAssembly_RoeInclusion`, `CoarseAssembly_RoeRows`, `CoarseAssembly_RoeTransfer`, `CoarseAssembly_SeparatedGeometry`, `CoarseAssembly_SeparatedRips`, `CoarseAssembly_TensorFibers`, `CoarseAssembly_TopologicalK1`, `NuclearUltrapower_SOSResidual`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C000`, `OAIQ229C001`, `OAIQ229C002` and `OAIQ229C003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C017`, `OAIQ229C018`, `OAIQ229C019`, `OAIQ229C020`, `OAIQ229C021` and `OAIQ229C022`.
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
import Definitions.Def_OAIQ229C000
import Definitions.Def_OAIQ229C001
import Definitions.Def_OAIQ229C002
import Definitions.Def_OAIQ229C003

section
-- module Solutions.Q229_CA.CoarseAssembly_Lattice
attribute [-instance] _root_.OAI.CoarseAssembly.discGraphMetric
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

theorem discDepth_eq_zero_iff (j : ℕ) (u : Disc j) :
    discDepth j u = 0 ↔ latticeRadius u.val = j := by
  have hd := discDepth_int j u
  omega

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

def HexDirection.eval : HexDirection → LatticeVertex → ℤ
  | .a, u => u.1
  | .negA, u => -u.1
  | .b, u => u.2
  | .negB, u => -u.2
  | .sum, u => u.1 + u.2
  | .negSum, u => -(u.1 + u.2)

def HexDirection.potential : HexDirection → LatticeVertex → ℤ
  | .a, u | .sum, u => if 0 ≤ u.2 then 1 else 0
  | _, _ => 0

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberDegree
attribute [-instance] _root_.OAI.CoarseAssembly.discGraphMetric
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

def fiberBits : (k : ℕ) → Quotient k → FiberBits
  | 0, _ => fun _ _ => 0
  | k + 1, q => matrixTopBits k q

theorem card_baseNeighbors_le {j : ℕ} (u : Disc j) : (baseNeighbors u).card ≤ 7 := by
  classical
  have himage : (baseNeighbors u).image Subtype.val ⊆ insert u.val (latticeNeighbors u.val) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    rcases (mem_baseNeighbors u w).mp hw with hw | hw
    · subst w; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_latticeNeighbors_iff _ _).mpr hw)
  calc
    (baseNeighbors u).card = ((baseNeighbors u).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (insert u.val (latticeNeighbors u.val)).card := Finset.card_le_card himage
    _ ≤ (latticeNeighbors u.val).card + 1 := Finset.card_insert_le _ _
    _ ≤ 7 := by have := card_latticeNeighbors_le u.val; omega

def neighborMove {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    (x : FiberVertex j) (y : {y // (fiberedGraph S t j).Adj x y}) : ArithmeticGroup :=
  y.property.2.choose

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Roe
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

theorem generator_mem {T : Operator X H} (hT : Generator T) :
    T ∈ algebra (X := X) (H := H) :=
  (NonUnitalStarSubalgebra.le_topologicalClosure _)
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ hT)

end CoarseAssembly.DiscreteRoe

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

omit [DecidableEq D] [DecidableEq X] [PseudoMetricSpace D] [PseudoMetricSpace X] in
theorem conjugation_continuous (V : Module D H →ₗᵢ[ℂ] Module X H) :
    Continuous (operatorConjugation V) := by
  show Continuous (fun T : Operator D H =>
    V.toContinuousLinearMap.comp (T.comp V.toContinuousLinearMap.adjoint))
  exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TensorFibers
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
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

theorem fiberTensorMap_inner (x y : lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) :
    inner ℂ (fiberTensorMap x) (fiberTensorMap y) = inner ℂ x y := by
  induction x using OAI.tensorInductionOn with
  | tmul a h =>
    induction y using OAI.tensorInductionOn with
    | tmul b k =>
      rw [TensorProduct.inner_tmul]
      change (∑' q : Q, inner ℂ (a q • h) (b q • k)) =
        (∑' q : Q, inner ℂ (a q) (b q)) * inner ℂ h k
      simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply]
      calc
        _ = ∑' q : Q, (b q * (starRingEnd ℂ) (a q)) * inner ℂ h k :=
          tsum_congr (fun q => (mul_assoc _ _ _).symm)
        _ = _ := tsum_mul_right
    | add y z ihy ihz => simp only [map_add, inner_add_right, ihy, ihz]
  | add x z ihx ihz => simp only [map_add, inner_add_left, ihx, ihz]

def fiberTensorIsometry :
    (lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) →ₗᵢ[ℂ] lp (fun _ : Q => H) 2 where
  toLinearMap := fiberTensorMap
  norm_map' x := by
    have hs := norm_sq_eq_re_inner (𝕜 := ℂ) (fiberTensorMap x)
    rw [fiberTensorMap_inner] at hs
    have ht := norm_sq_eq_re_inner (𝕜 := ℂ) x
    nlinarith [norm_nonneg (fiberTensorMap x), norm_nonneg x]

variable [DecidableEq Q]

def fiberTensorEquiv :
    (lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) ≃ₗᵢ[ℂ] lp (fun _ : Q => H) 2 :=
  LinearIsometryEquiv.ofSurjective fiberTensorIsometry fiberTensorMap_surjective

@[simp] theorem fiberTensorEquiv_apply (x : lp (fun _ : Q => ℂ) 2 ⊗[ℂ] H) :
    fiberTensorEquiv x = fiberTensorMap x := rfl

theorem fiberTensor_single (q : Q) (h : H) :
    fiberTensorEquiv (lp.single 2 q (1 : ℂ) ⊗ₜ[ℂ] h) = lp.single 2 q h := by
  apply lp.ext
  funext r
  simp [fiberTensorMap_tmul_apply, lp.single_apply, Pi.single_apply]

variable [DecidableEq R]

def amplifyFiber (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H) : lp (fun _ : Q => H) 2 →L[ℂ] lp (fun _ : R => H) 2 :=
  (fiberTensorEquiv (Q := R) (H := H)).toLinearIsometry.toContinuousLinearMap.comp
    ((TensorProduct.mapL O T).comp
      (fiberTensorEquiv (Q := Q) (H := H)).symm.toLinearIsometry.toContinuousLinearMap)

theorem amplifyFiber_norm_le (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H) : ‖amplifyFiber O T‖ ≤ ‖O‖ * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  change ‖fiberTensorEquiv (TensorProduct.mapL O T (fiberTensorEquiv.symm x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖TensorProduct.mapL O T‖ * ‖fiberTensorEquiv.symm x‖ :=
      (TensorProduct.mapL O T).le_opNorm _
    _ ≤ (‖O‖ * ‖T‖) * ‖x‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le O T) (norm_nonneg _)

theorem amplifyFiber_tensor (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H) (a : lp (fun _ : Q => ℂ) 2) (h : H) :
    amplifyFiber O T (fiberTensorEquiv (a ⊗ₜ[ℂ] h)) =
      fiberTensorEquiv (O a ⊗ₜ[ℂ] T h) := by
  change fiberTensorEquiv (TensorProduct.mapL O T
    (fiberTensorEquiv.symm (fiberTensorEquiv (a ⊗ₜ[ℂ] h)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, TensorProduct.mapL_tmul]

theorem amplifyFiber_single (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H) (q : Q) (r : R) (h : H) :
    amplifyFiber O T (lp.single 2 q h) r = O (lp.single 2 q 1) r • T h := by
  rw [← fiberTensor_single, amplifyFiber_tensor]
  rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RoeRows
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstruction from finite operator rows

Finite propagation and finite metric balls make every row finite. The
finite-row formula extends to arbitrary Hilbert-sum vectors by density of
the single-coordinate subspaces.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem entry_norm_le (T : Operator X H) (x y : X) : ‖entry T x y‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro h
  have hsingle : ‖(lp.single 2 y h : Module X H)‖ = ‖h‖ :=
    lp.norm_single (E := fun _ : X => H) (by norm_num : (0 : ENNReal) < 2) y h
  have hop := T.le_opNorm (lp.single 2 y h : Module X H)
  rw [hsingle] at hop
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (T (lp.single 2 y h)) x).trans hop

theorem finite_row_apply (T : Operator X H) (x : X) (s : Finset X)
    (hs : ∀ y, y ∉ s → entry T x y = 0) (v : Module X H) :
    T v x = ∑ y ∈ s, entry T x y (v y) := by
  have heq : (coordinate x).comp T =
      ∑ y ∈ s, (entry T x y).comp (coordinate y) := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
    intro y
    apply ContinuousLinearMap.ext
    intro z
    change entry T x y z = _
    simp only [ContinuousLinearMap.comp_apply, sum_apply,
      coordinate_apply, lp.singleContinuousLinearMap_apply]
    by_cases hy : y ∈ s
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b hb hby
        simp [Ne.symm hby]
      · exact fun h => (h hy).elim
    · rw [hs y hy]
      simp only [zero_apply]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have hby : b ≠ y := fun h => hy (h ▸ hb)
      simp [hby]
  simpa only [ContinuousLinearMap.comp_apply, sum_apply, coordinate_apply] using
    DFunLike.congr_fun heq v

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedGeometry
attribute [-simp] _root_.OAI.CoarseAssembly.separatedRipsMap_weight
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

/-- The bounded-geometry hypothesis needed by the Roe transfer is preserved
by this separated union. -/
theorem separated_uniform_finite_balls (o : ∀ i, V i)
    (hcomp : ∀ R : ℝ, 0 ≤ R → ∃ N : ℕ, ∀ i (x : V i), ∃ b : Finset (V i),
      (∀ y, y ∈ b ↔ dist x y ≤ R) ∧ b.card ≤ N) :
    @UniformFiniteBalls (Sigma V) (separatedMetric o).toPseudoMetricSpace := by
  classical
  let := separatedMetric o
  intro R hR
  obtain ⟨N, hN⟩ := hcomp R hR
  refine ⟨N + (componentPrefix (V := V) ⌈R⌉₊).card, ?_⟩
  rintro ⟨i, x⟩
  obtain ⟨b, hb, hcard⟩ := hN i x
  let emb : V i ↪ Sigma V := ⟨Sigma.mk i, fun _ _ h => by simpa using h⟩
  let c := b.map emb ∪ componentPrefix (V := V) ⌈R⌉₊
  refine ⟨c.filter (fun y => dist (⟨i, x⟩ : Sigma V) y ≤ R), ?_, ?_⟩
  · intro y
    simp only [Finset.mem_filter]
    refine ⟨fun h => h.2, fun hy => ⟨?_, hy⟩⟩
    rcases y with ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      apply Finset.mem_union_left
      apply Finset.mem_map.mpr
      refine ⟨y, (hb y).mpr ?_, rfl⟩
      change separatedDist o ⟨i, x⟩ ⟨i, y⟩ ≤ R at hy
      simpa only [separatedDist_same] using hy
    · apply Finset.mem_union_right
      apply (mem_componentPrefix _ _).mpr
      have hi := (separatedDist_indices o ⟨i, x⟩ ⟨j, y⟩ hij hy).2
      exact_mod_cast hi.trans (Nat.le_ceil R)
  · calc
      _ ≤ c.card := Finset.card_filter_le _ _
      _ ≤ (b.map emb).card + (componentPrefix (V := V) ⌈R⌉₊).card := Finset.card_union_le _ _
      _ ≤ N + (componentPrefix (V := V) ⌈R⌉₊).card := by
        rw [Finset.card_map]
        exact Nat.add_le_add_right hcard _

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

theorem discGraphMetric_eq (j : ℕ) :
    discGraphMetric j = connectedGraphMetric (discGraph j) (discGraph_connected j) :=
  graphMetricOrDiscrete_eq _ _

theorem baseUnion_uniform_balls : UniformFiniteBalls BaseUnion := by
  classical
  apply separated_uniform_finite_balls discBoundaryBase
  intro R hR
  refine ⟨8 ^ ⌈R⌉₊, ?_⟩
  intro j u
  rw [discGraphMetric_eq]
  exact graphMetric_ball_bound (discGraph j) (discGraph_connected j) baseNeighbors 7
    (fun x y h => (mem_baseNeighbors x y).mpr (Or.inr h)) card_baseNeighbors_le R u

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact spatial boundary factorization

Boundary fibers have depth zero and are singletons. The normalized fiber
embedding therefore agrees exactly with the coordinate inclusion there,
which proves the operator factorization needed by assembly naturality.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

def boundaryToBase : BoundaryVertex ↪ BaseUnion := ⟨Subtype.val, Subtype.val_injective⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def boundaryBaseIsometry : lp (fun _ : BoundaryVertex => H) 2 →ₗᵢ[ℂ]
    lp (fun _ : BaseUnion => H) 2 := inclusionIsometry boundaryToBase

def boundaryVertexIsometry : lp (fun _ : BoundaryVertex => H) 2 →ₗᵢ[ℂ]
    lp (fun _ : VertexUnion => H) 2 := inclusionIsometry boundaryToVertex

end CoarseAssembly

end

end OAI
end

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

def loopCircle (γ : Path y y) : C(WindingCircle, Y) where
  toFun := AddCircle.liftIco 1 0 γ.extend
  continuous_toFun := AddCircle.liftIco_zero_continuous (by simp)
    γ.continuous_extend.continuousOn

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CirclePairing
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
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

/-- Minimal published analytic data needed to test loops. Each `pairing f`
is the index pairing with the scalar unitary `circleUnitary f`. -/
structure PublishedCircleInput where
  fundamental : LocallyFiniteK1 WindingCircle
  pairing : ∀ {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y],
    C(Y, WindingCircle) → (LocallyFiniteK1 Y →+ ℤ)
  loop_naturality : ∀ {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (f : C(Y, WindingCircle)) (γ : C(WindingCircle, Y)),
    pairing f (pushforward (compactMap γ) fundamental) = pairing (f.comp γ) fundamental
  winding : ∀ (g : C(WindingCircle, WindingCircle)) (n : ℤ)
    (L : Path (0 : ℝ) (n : ℝ)),
    (∀ t : unitInterval, g (t : ℝ) = (L t : WindingCircle)) →
      pairing g fundamental = n

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FilledEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear edges in the filled polygon

The polygon's straight paths map to the actual barycentric Rips edges.
These identities supply the filling factorization of the boundary walk.
-/

noncomputable section

namespace CoarseAssembly

open Rips

def realVertex (v : LatticeVertex) : ℝ × ℝ := (v.1, v.2)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FilledWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Filling the actual parametrized lattice walks

Straight segments in the compact polygon follow the same concatenation as
the barycentric graph path. Thus every closed base walk, with its original
parametrization, factors through the filled polygon.
-/

noncomputable section

namespace CoarseAssembly

open Rips

theorem discEdgeBound {j : ℕ} (u v : Disc j) (h : (discGraph j).Adj u v) :
    dist u v ≤ (1 : ℝ) := by
  rw [discGraphMetric_eq]
  change ((discGraph j).dist u v : ℝ) ≤ 1
  exact_mod_cast (show (discGraph j).dist u v ≤ 1 by
    simpa using (discGraph j).dist_le h.toWalk)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TopologicalK1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Topological K₁ from stable invertible matrices

The unital group is presented by invertible finite matrices, with the actual
matrix-product, stabilization and continuous-path relations. The nonunital
group will be the kernel of the scalar-quotient map on the unitization.
These definitions keep the analytic assembly target tied to its algebra.
-/

noncomputable section

namespace CoarseAssembly.TopologicalK1

open CoarseAssembly.Analytic (Interval start finish)

universe u v w

variable (R : Type u) [Ring R] [TopologicalSpace R]

variable {R}

theorem matrixClass_stabilize {n : ℕ} (g : InvertibleMatrix R n) (h : InvertibleMatrix R (n + 1))
    (hs : IsStabilization R g h) : matrixClass R g = matrixClass R h := by
  apply sub_eq_zero.mp
  simpa only [matrixClass, QuotientAddGroup.mk_sub] using relation_zero (.stabilize g h hs)

theorem matrixClass_homotopy {n : ℕ} (c : Interval → InvertibleMatrix R n) (hc : Continuous c) :
    matrixClass R (c start) = matrixClass R (c finish) := by
  apply sub_eq_zero.mp
  simpa only [matrixClass, QuotientAddGroup.mk_sub] using relation_zero (.homotopy c hc)

end CoarseAssembly.TopologicalK1

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_NonUnitalK1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# K₁ of nonunital C*-algebras

The group is the kernel of the scalar projection from the unitization.
Nonunital star homomorphisms induce actual maps of these kernels, preserving
composition. This is the target functor for the reduced Roe assembly map.
-/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open scoped CStarAlgebra

universe u v w

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A} {B : Type v} [NonUnitalCStarAlgebra B]
variable {C : Type w} [NonUnitalCStarAlgebra C]

theorem unitizationMap_comp (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] C) :
    unitizationMap (ψ.comp φ) = (unitizationMap ψ).comp (unitizationMap φ) := by
  apply TopologicalK1.hom_ext
  intro n g
  simp only [AddMonoidHom.comp_apply, unitizationMap_matrixClass]
  congr 1
  apply Units.ext
  apply Matrix.ext
  intro i j
  change Unitization.starMap (ψ.comp φ) ((g : Matrix (Fin n) (Fin n) (Unitization ℂ A)) i j) =
    Unitization.starMap ψ (Unitization.starMap φ ((g : Matrix (Fin n) (Fin n) (Unitization ℂ A)) i j))
  exact DFunLike.congr_fun (Unitization.starMap_comp (φ := φ) (ψ := ψ)) _

theorem map_comp (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] C) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (unitizationMap_comp φ ψ) (x : TopologicalK1.Group (Unitization ℂ A))

end CoarseAssembly.OperatorKTheory

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

theorem inclusion_entry (e : X ↪ Y) (T : Operator X H) (x y : X) :
    entry (operatorConjugation (inclusionIsometry e) T) (e x) (e y) = entry T x y := by
  ext h
  simp only [entry_apply, operatorConjugation, ContinuousLinearMap.comp_apply]
  rw [← inclusionIsometry_single e y h, adjoint_apply_isometry]
  exact inclusionVector_apply e _ x

omit [DecidableEq X] in
theorem inclusion_entry_row_zero (e : X ↪ Y) (T : Operator X H) (x y : Y)
    (hx : x ∉ Set.range e) :
    entry (operatorConjugation (inclusionIsometry e) T) x y = 0 := by
  ext h
  exact inclusionVector_zero e _ x hx

end CoarseAssembly.DiscreteRoe

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

theorem boundaryToVertex_nonexpanding (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    ∀ x y, @dist VertexUnion (vertexUnionMetric S t).toDist
      (boundaryToVertex x) (boundaryToVertex y) ≤
      @dist BoundaryVertex (boundaryMetric S t).toDist x y :=
  fun _ _ => le_rfl

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

local instance boundaryAssemblyMetric2_r824cac_1 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.boundaryAssemblyMetric3
instance instNonUnitalCStarAlgebraBoundaryRoe : NonUnitalCStarAlgebra BoundaryRoe :=
  (OAI.CoarseAssembly.DiscreteRoe.instNonUnitalCStarAlgebraSubtypeOperatorMemNonUnitalStarSubalgebraComplexAlgebra (X := BoundaryVertex) (H := AmpleSpace) : NonUnitalCStarAlgebra (algebra (X := BoundaryVertex) (H := AmpleSpace)))
instance instNonUnitalCStarAlgebraBaseRoe : NonUnitalCStarAlgebra BaseRoe :=
  (OAI.CoarseAssembly.DiscreteRoe.instNonUnitalCStarAlgebraSubtypeOperatorMemNonUnitalStarSubalgebraComplexAlgebra (X := BaseUnion) (H := AmpleSpace) : NonUnitalCStarAlgebra (algebra (X := BaseUnion) (H := AmpleSpace)))

def boundaryTotalCoarsening : CoarseningMorphism (Rips.coarsening BoundaryVertex)
    (Rips.coarsening VertexUnion) :=
  Rips.embeddingCoarsening boundaryToVertex
    (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)

def boundaryTotalRoeHom : BoundaryRoe →⋆ₙₐ[ℂ] TotalRoe :=
  inclusionHom (X := BoundaryVertex) (Y := VertexUnion) (H := AmpleSpace)
    boundaryToVertex (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)

end CoarseAssembly

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

noncomputable instance instFintypeBoundaryComponent (j : ℕ) : Fintype (BoundaryComponent j) :=
  inferInstanceAs (Fintype {u : Disc j // discDepth j u = 0})

def boundaryGraph (j : ℕ) : SimpleGraph (BoundaryComponent j) :=
  (discGraph j).induce {u | discDepth j u = 0}

def boundaryRoot (j : ℕ) : BoundaryComponent j := ⟨discBoundaryBase j, discBoundaryBase_depth j⟩

def boundaryFiberEmbedding (j : ℕ) : BoundaryComponent j ↪ FiberVertex j where
  toFun u := ⟨u.val, 1⟩
  inj' _ _ h := Subtype.ext (congrArg Sigma.fst h)

def boundaryBaseHom (j : ℕ) : boundaryGraph j →g discGraph j :=
  (SimpleGraph.Embedding.induce _).toHom

/-- Geometric data still to be constructed from the six sides of the
hexagon. These are own-paper obligations, not a published-input interface. -/
structure HexagonalBoundaryWalks where
  walk : ∀ j, (boundaryGraph j).Walk (boundaryRoot j) (boundaryRoot j)
  charge_one : ∀ j, 2 ≤ j →
    walkCharge (fun x y : Disc j => latticeCharge x.val y.val)
      ((walk j).map (boundaryBaseHom j)) = 1

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsCompactSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact subsets of a locally finite Rips complex

A compact set of probability weights has its entire support in one finite
vertex set. The proof uses a finite cover by positive-coordinate stars and
the finite metric balls around those coordinates.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable {X : Type*} [PseudoMetricSpace X] {r : ℝ}

theorem compact_support_finite
    (hballs : ∀ x : X, Set.Finite {y : X | dist x y ≤ r})
    {K : Set (Point X r)} (hK : IsCompact K) :
    ∃ s : Finset X, ∀ p ∈ K, p.weight.support ⊆ s := by
  classical
  obtain ⟨a, ha⟩ := hK.elim_finite_subcover
    (fun x : X => {p : Point X r | 0 < p.weight x})
    (fun x => isOpen_lt continuous_const (coordinate_continuous x)) (by
      intro p _
      obtain ⟨x, hx⟩ := p.exists_positive
      exact Set.mem_iUnion.mpr ⟨x, hx⟩)
  let s : Finset X := a.biUnion (fun x => (hballs x).toFinset)
  refine ⟨s, ?_⟩
  intro p hp y hy
  obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.mp (ha hp)
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, ?_⟩
  exact (hballs x).mem_toFinset.mpr
    (p.diameter x (Finsupp.mem_support_iff.mpr (ne_of_gt hpx)) y hy)

end CoarseAssembly.Rips

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

theorem separatedComponent_separation (o : ∀ j, V j) (j : ℕ) (r : ℝ) (hj : r < j) :
    letI := separatedMetric o
    ∀ x y, y ∉ Set.range (separatedComponent (V := V) j) →
      r < dist (separatedComponent j x) y := by
  let := separatedMetric o
  rintro x ⟨k, y⟩ hy
  have hjk : j ≠ k := by
    rintro rfl
    exact hy ⟨y, rfl⟩
  change r < separatedDist o ⟨j, x⟩ ⟨k, y⟩
  rw [separatedDist_different o hjk]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith [dist_nonneg (x := x) (y := o j), dist_nonneg (x := o k) (y := y)]

/-- The chosen late finite Rips component really is open and closed in
the global Rips realization; its inclusion is continuous and proper. -/
theorem lateRipsComponent_openEmbedding [∀ j, Fintype (V j)]
    (o : ∀ j, V j) (j : ℕ) (r : ℝ) (hj : r < j) :
    letI := separatedMetric o
    IsOpenEmbedding (mapPoint (r := r) (separatedComponent (V := V) j)
      (fun x y => ((separatedComponent_isometry o j).dist_eq x y).le)) := by
  let := separatedMetric o
  exact
    { toIsEmbedding := (mapPoint_closedEmbedding _ _).isEmbedding
      isOpen_range := mapPoint_range_open _ (separatedComponent_isometry o j)
        (separatedComponent_separation o j r hj) }

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

theorem separatedRipsMap_continuous (o : ∀ j, V j) (r : ℝ) (j : ℕ) :
    letI := separatedMetric o
    Continuous (separatedRipsMap o r j) := by
  let := separatedMetric o
  exact mapPoint_continuous (separatedComponent j)
    (fun x y => ((separatedComponent_isometry o j).dist_eq x y).le)

def ripsFamilyContinuousMap (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) :
    letI := separatedMetric o
    C(Sigma Z, Point (Sigma V) r) := by
  let := separatedMetric o
  refine ⟨fun z => separatedRipsMap o r z.1 (γ z.1 z.2), ?_⟩
  exact continuous_sigma (fun j => (separatedRipsMap_continuous o r j).comp (γ j).continuous)

variable [∀ j, Fintype (V j)]

theorem ripsFamily_preimage_compact (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) :
    letI := separatedMetric o
    ∀ K, IsCompact K → IsCompact ((ripsFamilyContinuousMap o r γ) ⁻¹' K) := by
  classical
  let := separatedMetric o
  intro K hK
  obtain ⟨s, hs⟩ := compact_support_finite (fun x => separated_closedBall_finite o x r) hK
  let a : Finset ℕ := s.image Sigma.fst
  have hcover : (ripsFamilyContinuousMap o r γ) ⁻¹' K ⊆
      ⋃ j ∈ a, Set.range (@Sigma.mk ℕ Z j) := by
    rintro ⟨j, z⟩ hz
    obtain ⟨x, hx⟩ := (γ j z).exists_positive
    have hmem : (⟨j, x⟩ : Sigma V) ∈ s := hs _ hz
      (Finsupp.mem_support_iff.mpr (by
        change (separatedRipsMap o r j (γ j z)).weight ⟨j, x⟩ ≠ 0
        rw [separatedRipsMap_weight]
        exact ne_of_gt hx))
    have hj : j ∈ a := Finset.mem_image.mpr ⟨⟨j, x⟩, hmem, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hj, ⟨z, rfl⟩⟩
  have hcompact : IsCompact (⋃ j ∈ a, Set.range (@Sigma.mk ℕ Z j)) :=
    a.isCompact_biUnion (fun j _ => isCompact_range continuous_sigmaMk)
  exact hcompact.of_isClosed_subset
    (hK.isClosed.preimage (ripsFamilyContinuousMap o r γ).continuous) hcover

def ripsFamilyMap (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) :
    letI := separatedMetric o
    CocompactMap (Sigma Z) (Point (Sigma V) r) := by
  let := separatedMetric o
  exact
    { toContinuousMap := ripsFamilyContinuousMap o r γ
      cocompact_tendsto' := CocompactMap.tendsto_of_forall_preimage
        (ripsFamily_preimage_compact o r γ) }

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact boundary components in the actual boundary metric

The disjoint family of finite boundary vertex sets is isometric to the
depth-zero subtype used for the spatial boundary maps.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips

@[instance_reducible] def boundaryComponentMetric (S : Finset ArithmeticGroup)
    (t : ℤ_[2]ˣ) (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  MetricSpace.induced (boundaryFiberEmbedding j) (boundaryFiberEmbedding j).injective
    (componentMetric S t j)

@[instance_reducible] def boundaryComponentsMetric (S : Finset ArithmeticGroup)
    (t : ℤ_[2]ˣ) : MetricSpace (Sigma BoundaryComponent) := by
  letI := boundaryComponentMetric S t
  exact separatedMetric boundaryRoot

def boundaryReindex : Sigma BoundaryComponent ≃ BoundaryVertex where
  toFun b := ⟨⟨b.1, b.2.val⟩, b.2.property⟩
  invFun b := ⟨b.val.1, ⟨b.val.2, b.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem boundaryReindex_dist (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (x y : Sigma BoundaryComponent) :
    @dist BoundaryVertex (boundaryMetric S t).toDist (boundaryReindex x) (boundaryReindex y) =
      @dist (Sigma BoundaryComponent) (boundaryComponentsMetric S t).toDist x y := by
  let := componentMetric S t
  let := boundaryComponentMetric S t
  rcases x with ⟨i, u⟩
  rcases y with ⟨j, v⟩
  change separatedDist fiberBoundaryBase
    ⟨i, boundaryFiberEmbedding i u⟩ ⟨j, boundaryFiberEmbedding j v⟩ =
      separatedDist boundaryRoot ⟨i, u⟩ ⟨j, v⟩
  by_cases hij : i = j
  · subst j
    simp only [separatedDist_same]
    rfl
  · rw [separatedDist_different fiberBoundaryBase hij, separatedDist_different boundaryRoot hij]
    rfl

def boundaryFamilyMap (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (r : ℝ)
    (γ : ∀ j, C(WindingCircle,
      @Point (BoundaryComponent j) (boundaryComponentMetric S t j).toPseudoMetricSpace r)) :
    CocompactMap (Sigma (fun _ : ℕ => WindingCircle))
      (@Point BoundaryVertex (boundaryMetric S t).toPseudoMetricSpace r) := by
  let := boundaryComponentMetric S t
  let : ∀ j, PseudoMetricSpace (BoundaryComponent j) :=
    fun j => (boundaryComponentMetric S t j).toPseudoMetricSpace
  let := boundaryComponentsMetric S t
  let := boundaryMetric S t
  let : PseudoMetricSpace BoundaryVertex := (boundaryMetric S t).toPseudoMetricSpace
  exact (embeddingMap boundaryReindex.toEmbedding
    (fun x y => (boundaryReindex_dist S t x y).le) r).comp
      (ripsFamilyMap boundaryRoot r γ)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsFamilyRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact coordinates of the pushed-forward family

Restriction to a late Rips component recovers precisely the corresponding
member of the source family, irrespective of links among other components.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips Analytic

variable {V : ℕ → Type} [∀ j, MetricSpace (V j)] [∀ j, Fintype (V j)]
  {Z : ℕ → Type} [∀ j, TopologicalSpace (Z j)] [∀ j, CompactSpace (Z j)]

theorem separatedRipsEmbedding_open (o : ∀ j, V j) (r : ℝ) (j : ℕ) (hj : r < j) :
    letI := separatedMetric o
    IsOpenEmbedding (separatedRipsEmbedding o r j) := lateRipsComponent_openEmbedding o j r hj

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HexagonSides
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The six oriented sides of the lattice hexagon

These explicit vertex sequences support the boundary-walk construction.
They run counterclockwise from `(j,0)`; only the final side crosses the
half-open positive ray used by the integral charge.
-/

namespace CoarseAssembly

def hexagonPoint (s : Fin 6) (j k : ℕ) : LatticeVertex :=
  match s.val with
  | 0 => ((j : ℤ) - k, k)
  | 1 => (-(k : ℤ), j)
  | 2 => (-(j : ℤ), (j : ℤ) - k)
  | 3 => (-(j : ℤ) + k, -(k : ℤ))
  | 4 => (k, -(j : ℤ))
  | _ => (j, -(j : ℤ) + k)

theorem hexagonPoint_radius (s : Fin 6) (j k : ℕ) (hk : k ≤ j) :
    latticeRadius (hexagonPoint s j k) = j := by
  have hk' : (k : ℤ) ≤ j := by exact_mod_cast hk
  have hj : (0 : ℤ) ≤ j := by positivity
  have hn : (0 : ℤ) ≤ k := by positivity
  fin_cases s <;> simp only [hexagonPoint, latticeRadius]
  all_goals
    apply le_antisymm
    · simp only [max_le_iff, abs_le]
      omega
    · try simp only [show -(j : ℤ) + k + -(k : ℤ) = -(j : ℤ) by ring]
      try simp only [show (j : ℤ) - k + k = (j : ℤ) by ring]
      try simp only [abs_of_nonneg hj, abs_neg]
      omega

def hexagonVertex (s : Fin 6) (j k : ℕ) (hk : k ≤ j) : BoundaryComponent j :=
  ⟨⟨hexagonPoint s j k, (hexagonPoint_radius s j k hk).le⟩,
    (discDepth_eq_zero_iff _ _).mpr (hexagonPoint_radius s j k hk)⟩

theorem hexagonPoint_adj (s : Fin 6) (j k : ℕ) :
    triangularGraph.Adj (hexagonPoint s j k) (hexagonPoint s j (k + 1)) := by
  fin_cases s <;> simp only [hexagonPoint, triangularGraph, Nat.cast_add, Nat.cast_one,
    abs_le, ne_eq, Prod.mk.injEq] <;> omega

theorem hexagonVertex_adj (s : Fin 6) (j k : ℕ) (hk : k + 1 ≤ j) :
    (boundaryGraph j).Adj (hexagonVertex s j k (by omega)) (hexagonVertex s j (k + 1) hk) :=
  hexagonPoint_adj s j k

def hexagonSideWalk (s : Fin 6) (j : ℕ) : (k : ℕ) → (hk : k ≤ j) →
    (boundaryGraph j).Walk (hexagonVertex s j 0 (Nat.zero_le j)) (hexagonVertex s j k hk)
  | 0, _ => .nil
  | k + 1, hk => (hexagonSideWalk s j k (by omega)).append
      (hexagonVertex_adj s j k hk).toWalk

def boundaryCharge {j : ℕ} (x y : BoundaryComponent j) : ℤ :=
  latticeCharge x.val.val y.val.val

def hexagonCorner (s : Fin 6) (j : ℕ) : BoundaryComponent j :=
  hexagonVertex s j 0 (Nat.zero_le j)

theorem hexagonSide_end (s : Fin 6) (j : ℕ) :
    hexagonVertex s j j le_rfl = hexagonCorner (s + 1) j := by
  fin_cases s <;> apply Subtype.ext <;> apply Subtype.ext <;>
    simp [hexagonVertex, hexagonCorner, hexagonPoint]

def hexagonSide (s : Fin 6) (j : ℕ) :
    (boundaryGraph j).Walk (hexagonCorner s j) (hexagonCorner (s + 1) j) :=
  (hexagonSideWalk s j j le_rfl).copy rfl (hexagonSide_end s j)

theorem hexagonCorner_zero (j : ℕ) : hexagonCorner 0 j = boundaryRoot j := by
  apply Subtype.ext
  apply Subtype.ext
  simp [hexagonCorner, hexagonVertex, hexagonPoint, boundaryRoot, discBoundaryBase]

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyFilling
attribute [-simp] _root_.OAI.CoarseAssembly.Rips.sqrtCoordinate_selfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire family of base loops vanishes through its actual filling

Both arrows through the disjoint union of compact polygons are constructed
proper maps. The vanishing follows only from the specified published compact
homotopy and countable-additivity inputs.
-/

noncomputable section

namespace CoarseAssembly

open Rips Analytic

variable (o : ∀ j, Disc j) (p : ∀ j, (discGraph j).Walk (o j) (o j))

def baseBoundaryLoops (j : ℕ) : C(WindingCircle, Point (Disc j) 1) :=
  loopCircle (walkPath (by norm_num) discEdgeBound (p j))

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsRealClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real-radius classes at integer coarsening stages -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]

def classAt (n : ℕ) (r : ℝ) (h : r = (n : ℝ))
    (a : LocallyFiniteK1 (Point X r)) : KX1 X := by
  refine (coarsening X).of n ?_
  change LocallyFiniteK1 (Point X (n : ℝ))
  exact h ▸ a

end CoarseAssembly.Rips

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

local instance boundaryLoopMetric1 (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance boundaryLoopMetric2 (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
local instance boundaryLoopMetric3 : MetricSpace (Sigma BoundaryComponent) :=
  boundaryComponentsMetric elementaryMoves chosenHolonomyUnit
local instance boundaryLoopMetric4_r824cac_1 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
local instance boundaryLoopMetric5 : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric7

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric8

def boundaryComponentToBase (j : ℕ) : BoundaryComponent j ↪ Disc j :=
  ⟨Subtype.val, Subtype.val_injective⟩

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

theorem componentEmbedding_nonexpanding (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i) (he : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (hroot : ∀ i, e i (o i) = p i) :
    letI := separatedMetric o
    letI := separatedMetric p
    ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y := by
  let := separatedMetric o
  let := separatedMetric p
  rintro ⟨i, x⟩ ⟨j, y⟩
  change separatedDist p ⟨i, e i x⟩ ⟨j, e j y⟩ ≤ separatedDist o ⟨i, x⟩ ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    simpa only [separatedDist_same] using he i x y
  · rw [separatedDist_different p hij, separatedDist_different o hij]
    have hx := he i x (o i)
    have hy := he j (o j) y
    rw [hroot i] at hx
    rw [hroot j] at hy
    linarith

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ComponentRipsPreimage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact component preimages for the geometric inclusions -/

noncomputable section

namespace CoarseAssembly.Rips

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]

theorem componentRips_preimage (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i) (r : ℝ)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (i : ℕ) :
    letI := separatedMetric o
    letI := separatedMetric p
    ∀ x : Point (Sigma Q) r,
      mapPoint (componentEmbedding e) he x ∈ Set.range (separatedRipsEmbedding p r i) ↔
        x ∈ Set.range (separatedRipsEmbedding o r i) := by
  let := separatedMetric o
  let := separatedMetric p
  intro x
  change mapPoint (componentEmbedding e) he x ∈ Set.range (mapPoint (separatedComponent i)
      (fun a b => ((separatedComponent_isometry p i).dist_eq a b).le)) ↔
    x ∈ Set.range (mapPoint (separatedComponent i)
      (fun a b => ((separatedComponent_isometry o i).dist_eq a b).le))
  rw [mapPoint_range (separatedComponent i) (separatedComponent_isometry p i),
    mapPoint_range (separatedComponent i) (separatedComponent_isometry o i)]
  constructor
  · intro hx y hy
    have hmem : componentEmbedding e y ∈ (mapPoint (componentEmbedding e) he x).weight.support := by
      apply Finsupp.mem_support_iff.mpr
      rw [mapPoint_weight_self]
      exact Finsupp.mem_support_iff.mp hy
    obtain ⟨z, hz⟩ := hx hmem
    have hi : i = y.1 := congrArg Sigma.fst hz
    rcases y with ⟨j, y⟩
    dsimp only at hi
    subst j
    exact ⟨y, rfl⟩
  · intro hx y hy
    change y ∈ (x.weight.embDomain (componentEmbedding e)).support at hy
    rw [Finsupp.support_embDomain, Finset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨a, ha⟩ := hx hz
    rw [← ha]
    exact ⟨e i a, rfl⟩

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteCompactRoe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact self-adjoint operators on a finite component lie in its Roe algebra -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype X] [PseudoMetricSpace X] [CompleteSpace H] in
theorem compact_entries_of_compact {T : Operator X H} (hT : IsCompactOperator T) :
    CompactEntries T := fun x y => (hT.comp_clm (insert y)).clm_comp (coordinate x)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeUnitary
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of
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

variable [hS : IsClosed (S : Set A)]

theorem relativeClass_one (hu : ((1 : unitary A) : A) - 1 ∈ S) :
    relativeClass S 1 hu = 0 := by
  have hr : relativePart S 1 hu = 0 := by
    apply Subtype.ext
    simp [relativePart]
  have hm : relativeMatrix S 1 hu = 1 := by
    apply Units.ext
    change Matrix.scalar (Fin 1)
      (1 + (relativePart S 1 hu : Unitization ℂ S)) = 1
    rw [hr]
    simp
  apply Subtype.ext
  change TopologicalK1.matrixClass (Unitization ℂ S) (relativeMatrix S 1 hu) = 0
  rw [hm, TopologicalK1.matrixClass_one]

theorem relativeClass_eq_zero {u : unitary A} (hu : (u : A) - 1 ∈ S) (h : u = 1) :
    relativeClass S u hu = 0 := by
  subst u
  exact relativeClass_one S hu

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitBoundaryRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Roe representative of the counterexample's boundary cycle

This constructs the index representative from the explicit circle Fredholm
operator and the paper's hexagonal loops. Identification with the descended
canonical coarse assembly map remains a separate theorem.
-/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

variable {X : Type} [PseudoMetricSpace X] [Fintype X]

local instance explicitRepComponentDecidableEq (j : ℕ) : DecidableEq (BoundaryComponent j) :=
  Classical.decEq _

local instance explicitRepComponentMetric_r824cac_1 (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance explicitRepComponentPseudoMetric_r824cac_1 (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
local instance explicitRepUnionMetric : MetricSpace (Sigma BoundaryComponent) :=
  boundaryComponentsMetric elementaryMoves chosenHolonomyUnit

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeHomotopy
attribute [-instance] _root_.OAI.CoarseAssembly.Congruence.quotientZeroSubsingleton
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

theorem continuous_relativeMatrix (u : P → unitary A)
    (hu : ∀ p, (u p : A) - 1 ∈ S) (hcont : Continuous (fun p => (u p : A))) :
    Continuous (fun p => relativeMatrix S (u p) (hu p)) := by
  have hv := continuous_relativeUnitary S u hu hcont
  have hw : Continuous (fun p => Unitary.toUnits (relativeUnitary S (u p) (hu p))) := by
    apply Units.continuous_iff.mpr
    exact ⟨hv, hv.star⟩
  apply Continuous.comp _ hw
  apply Continuous.units_map
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hij : i = j := Subsingleton.elim _ _
  change Continuous (fun x : Unitization ℂ S => if i = j then x else 0)
  simp only [hij, ite_true, if_true]
  convert! (continuous_id : Continuous (fun x : Unitization ℂ S => x))

theorem relativeClass_homotopy (u : Interval → unitary A)
    (hu : ∀ t, (u t : A) - 1 ∈ S) (hcont : Continuous (fun t => (u t : A))) :
    relativeClass S (u start) (hu start) = relativeClass S (u finish) (hu finish) := by
  apply Subtype.ext
  exact TopologicalK1.matrixClass_homotopy (fun t => relativeMatrix S (u t) (hu t))
    (continuous_relativeMatrix S u hu hcont)

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsBoundaryDegeneracy
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

theorem isometricExtension_sq_eq_one {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E) (hF : F * F = 1) :
    isometricExtension V F * isometricExtension V F = 1 := by
  apply sub_eq_zero.mp
  rw [isometricExtension_square_defect, hF, sub_self]
  change operatorConjugationHom V 0 = 0
  exact map_zero _

end CoarseAssembly

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

theorem isometricExtension_comp (V : F →ₗᵢ[ℂ] G) (W : E →ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    isometricExtension V (isometricExtension W T) = isometricExtension (V.comp W) T := by
  change 1 + operatorConjugation V (1 + operatorConjugation W (T - 1) - 1) =
    1 + operatorConjugation (V.comp W) (T - 1)
  rw [add_sub_cancel_left, operatorConjugation_comp]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_EmbeddingTransition
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply
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

theorem embeddingTransition_partial (V W : E →ₗᵢ[ℂ] H) :
    embeddingTransition V W * star (embeddingTransition V W) * embeddingTransition V W =
      embeddingTransition V W := by
  ext x
  simp [embeddingTransition, ContinuousLinearMap.star_eq_adjoint]

theorem embeddingTransition_initial (V W : E →ₗᵢ[ℂ] H) :
    star (embeddingTransition V W) * embeddingTransition V W = operatorConjugation V 1 := by
  ext x
  simp [embeddingTransition, operatorConjugation, ContinuousLinearMap.star_eq_adjoint]

theorem embeddingTransition_support_left (V W : E →ₗᵢ[ℂ] H) (a : E →L[ℂ] E) :
    (star (embeddingTransition V W) * embeddingTransition V W) * operatorConjugation V a =
      operatorConjugation V a := by
  rw [embeddingTransition_initial, ← operatorConjugation_mul, one_mul]

theorem embeddingTransition_support_right (V W : E →ₗᵢ[ℂ] H) (a : E →L[ℂ] E) :
    operatorConjugation V a * (star (embeddingTransition V W) * embeddingTransition V W) =
      operatorConjugation V a := by
  rw [embeddingTransition_initial, ← operatorConjugation_mul, mul_one]

theorem embeddingTransition_conjugation (V W : E →ₗᵢ[ℂ] H) (a : E →L[ℂ] E) :
    embeddingTransition V W * operatorConjugation V a * star (embeddingTransition V W) =
      operatorConjugation W a := by
  ext x
  simp [embeddingTransition, operatorConjugation, ContinuousLinearMap.star_eq_adjoint]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_K1TwoByTwo
attribute [-simp] _root_.OAI.CoarseAssembly.OperatorKTheory.scalarMap_matrixClass _root_.OAI.CoarseAssembly.OperatorKTheory.unitizationMap_matrixClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-by-two stabilization used for spatial K₁ representatives -/

noncomputable section

namespace CoarseAssembly.TopologicalK1

variable {R : Type*} [Ring R] [TopologicalSpace R]

theorem matrixClass_inv {n : ℕ} (g : InvertibleMatrix R n) :
    matrixClass R g⁻¹ = -matrixClass R g := by
  have h := matrixClass_mul g g⁻¹
  rw [mul_inv_cancel, matrixClass_one] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h.symm)

theorem matrixClass_conjugate {n : ℕ} (g h : InvertibleMatrix R n) :
    matrixClass R (g * h * g⁻¹) = matrixClass R h := by
  rw [matrixClass_mul, matrixClass_mul, matrixClass_inv]
  abel

def scalarUnitMatrix (g : Rˣ) : InvertibleMatrix R 1 :=
  Units.map (Matrix.scalar (Fin 1)).toMonoidHom g

def diagonalTwoUnits (g h : Rˣ) : InvertibleMatrix R 2 :=
  Units.map (Matrix.diagonalRingHom (Fin 2) R).toMonoidHom
    { val := fun i => if i = 0 then (g : R) else (h : R)
      inv := fun i => if i = 0 then (g⁻¹ : Rˣ) else (h⁻¹ : Rˣ)
      val_inv := by ext i; by_cases hi : i = 0 <;> simp [hi]
      inv_val := by ext i; by_cases hi : i = 0 <;> simp [hi] }

omit [TopologicalSpace R] in
theorem diagonalTwo_stabilizes (g : Rˣ) :
    IsStabilization R (scalarUnitMatrix g) (diagonalTwoUnits g 1) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    (first | (simp [IsStabilization, diagonalTwoUnits, scalarUnitMatrix, Matrix.diagonal, Matrix.scalar, Matrix.fromBlocks, Matrix.submatrix, finSumFinEquiv]; all_goals first | (norm_num [IsStabilization, diagonalTwoUnits, scalarUnitMatrix, Matrix.diagonal, Matrix.scalar, Matrix.fromBlocks, Matrix.submatrix, finSumFinEquiv]; done) | rfl | decide) | (norm_num [IsStabilization, diagonalTwoUnits, scalarUnitMatrix, Matrix.diagonal, Matrix.scalar, Matrix.fromBlocks, Matrix.submatrix, finSumFinEquiv]; done) | norm_num [IsStabilization, diagonalTwoUnits, scalarUnitMatrix, Matrix.diagonal, Matrix.scalar, Matrix.fromBlocks, Matrix.submatrix, finSumFinEquiv])

theorem diagonalTwo_matrixClass_one (g : Rˣ) :
    matrixClass R (diagonalTwoUnits g 1) = matrixClass R (scalarUnitMatrix g) :=
  (matrixClass_stabilize _ _ (diagonalTwo_stabilizes g)).symm

def flipTwoUnits : InvertibleMatrix R 2 where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [TopologicalSpace R] in
theorem diagonalTwo_flip (g h : Rˣ) :
    flipTwoUnits * diagonalTwoUnits g h * (flipTwoUnits : InvertibleMatrix R 2)⁻¹ =
      diagonalTwoUnits h g := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [flipTwoUnits, diagonalTwoUnits, Matrix.mul_apply, Matrix.diagonal,
      Matrix.vecHead, Matrix.vecTail]

theorem diagonalTwo_matrixClass_swap (g h : Rˣ) :
    matrixClass R (diagonalTwoUnits g h) = matrixClass R (diagonalTwoUnits h g) := by
  exact (matrixClass_conjugate (flipTwoUnits : InvertibleMatrix R 2)
    (diagonalTwoUnits g h)).symm.trans (congrArg (matrixClass R) (diagonalTwo_flip g h))

omit [TopologicalSpace R] in
theorem diagonalTwo_mul (g h : Rˣ) :
    diagonalTwoUnits g h = diagonalTwoUnits g 1 * diagonalTwoUnits 1 h := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalTwoUnits, Matrix.mul_apply, Matrix.diagonal]

/-- The exact stabilization identity for two relative unitaries. -/
theorem diagonalTwo_matrixClass (g h : Rˣ) :
    matrixClass R (diagonalTwoUnits g h) =
      matrixClass R (scalarUnitMatrix g) + matrixClass R (scalarUnitMatrix h) := by
  rw [diagonalTwo_mul, matrixClass_mul, diagonalTwo_matrixClass_one,
    diagonalTwo_matrixClass_swap 1 h, diagonalTwo_matrixClass_one]

end CoarseAssembly.TopologicalK1

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

def relativeTwoMatrix (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    TopologicalK1.InvertibleMatrix (Unitization ℂ S) 2 :=
  Unitary.toUnits (relativeTwoUnitary S u hu)

theorem relativeTwoMatrix_scalar (u : unitary (Matrix (Fin 2) (Fin 2) R)) (hu) :
    TopologicalK1.mapGL (Unitization.fstHom ℂ S).toRingHom 2 (relativeTwoMatrix S u hu) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [TopologicalK1.mapGL, relativeTwoMatrix, relativeTwoUnitary, matrixTwoStarHom]
  · simp [TopologicalK1.mapGL, relativeTwoMatrix, relativeTwoUnitary, matrixTwoStarHom,
      hij]

def relativeTwoClass (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) : K1 S :=
  ⟨TopologicalK1.matrixClass (Unitization ℂ S) (relativeTwoMatrix S u hu), by
    rw [AddMonoidHom.mem_ker, scalarMap_matrixClass, relativeTwoMatrix_scalar,
      TopologicalK1.matrixClass_one]⟩

variable {P : Type*} [TopologicalSpace P]

theorem continuous_relativeTwoMatrix (u : P → unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ p i j, ((u p : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S)
    (hc : Continuous (fun p => (u p : Matrix (Fin 2) (Fin 2) R))) :
    Continuous (fun p => relativeTwoMatrix S (u p) (hu p)) := by
  apply Units.continuous_iff.mpr
  have hv := continuous_relativeTwoUnitary S u hu hc
  exact ⟨hv, hv.star⟩

theorem relativeTwoClass_homotopy (u : Interval → unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ t i j, ((u t : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S)
    (hc : Continuous (fun t => (u t : Matrix (Fin 2) (Fin 2) R))) :
    relativeTwoClass S (u start) (hu start) = relativeTwoClass S (u finish) (hu finish) := by
  apply Subtype.ext
  exact TopologicalK1.matrixClass_homotopy (fun t => relativeTwoMatrix S (u t) (hu t))
    (continuous_relativeTwoMatrix S u hu hc)

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeTwoDiagonal
attribute [-simp] _root_.OAI.CoarseAssembly.OperatorKTheory.mapTwoUnitary_diagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal relative matrices and addition in Roe K₁ -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {R : Type*} [CStarAlgebra R]

variable (S : NonUnitalStarSubalgebra ℂ R) [hS : IsClosed (S : Set R)]

theorem relativeTwoMatrix_diagonal (u v : unitary R)
    (hu : (u : R) - 1 ∈ S) (hv : (v : R) - 1 ∈ S) :
    relativeTwoMatrix S (diagonalTwoUnitary u v) (diagonalTwoUnitary_relative S u v hu hv) =
      TopologicalK1.diagonalTwoUnits (Unitary.toUnits (relativeUnitary S u hu))
        (Unitary.toUnits (relativeUnitary S v hv)) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [relativeTwoMatrix, relativeTwoUnitary, matrixTwoStarHom, relativeTwoPart,
      diagonalTwoUnitary, TopologicalK1.diagonalTwoUnits, Matrix.diagonal,
      relativeUnitary, relativePart]
  all_goals
    change ((0 : S) : Unitization ℂ S) = 0
    simp

/-- Two diagonal relative unitaries represent the sum of their K₁ classes. -/
theorem relativeTwoClass_diagonal (u v : unitary R)
    (hu : (u : R) - 1 ∈ S) (hv : (v : R) - 1 ∈ S) :
    relativeTwoClass S (diagonalTwoUnitary u v) (diagonalTwoUnitary_relative S u v hu hv) =
      relativeClass S u hu + relativeClass S v hv := by
  apply Subtype.ext
  change TopologicalK1.matrixClass (Unitization ℂ S)
      (relativeTwoMatrix S (diagonalTwoUnitary u v) _) = _
  rw [relativeTwoMatrix_diagonal, TopologicalK1.diagonalTwo_matrixClass]
  rfl

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

variable (S : NonUnitalStarSubalgebra ℂ R)

variable [hS : IsClosed (S : Set R)]

theorem relativeTwoClass_conjugationPath (φ : A →⋆ₐ[ℂ] R) (hφc : Continuous φ)
    (hφ : ∀ a b, b ∈ S → φ a * b ∈ S ∧ b * φ a ∈ S)
    (w : Analytic.Interval → unitary (Matrix (Fin 2) (Fin 2) A))
    (hw : Continuous w) (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    relativeTwoClass S (conjugatedTwoUnitary (mapTwoUnitary φ (w Analytic.start)) u)
      (conjugatedTwoUnitary_relative S φ hφ (w Analytic.start) u hu) =
    relativeTwoClass S (conjugatedTwoUnitary (mapTwoUnitary φ (w Analytic.finish)) u)
      (conjugatedTwoUnitary_relative S φ hφ (w Analytic.finish) u hu) := by
  apply relativeTwoClass_homotopy S
    (fun t => conjugatedTwoUnitary (mapTwoUnitary φ (w t)) u)
    (fun t => conjugatedTwoUnitary_relative S φ hφ (w t) u hu)
  have hc : Continuous (fun t => (mapTwoUnitary φ (w t)).val) :=
    (matrixTwoUnitalStarHom_continuous φ hφc).comp (continuous_subtype_val.comp hw)
  exact (hc.mul continuous_const).mul hc.star

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsUnitaryLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unitary equivalence commutes with finite-Rips localization -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricExtension_equiv (U : E ≃ₗᵢ[ℂ] H) (F : E →L[ℂ] E) :
    isometricExtension U.toLinearIsometry F = operatorConjugation U.toLinearIsometry F := by
  have h1 : operatorConjugation U.toLinearIsometry (1 : E →L[ℂ] E) = 1 := by
    have hU : U.toLinearIsometry.toContinuousLinearMap.adjoint =
        U.symm.toLinearIsometry.toContinuousLinearMap := LinearIsometryEquiv.adjoint_eq_symm U
    ext x
    simp [operatorConjugation, hU]
  change 1 + operatorConjugationHom U.toLinearIsometry (F - 1) = _
  rw [map_sub]
  change 1 + (operatorConjugation U.toLinearIsometry F -
    operatorConjugation U.toLinearIsometry 1) = _
  rw [h1]
  abel

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_IsometricDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending an orthogonal decomposition by the identity -/

noncomputable section

namespace CoarseAssembly

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricExtension_decomposition
    (U : G →ₗᵢ[ℂ] H) (V : E →ₗᵢ[ℂ] G) (W : F →ₗᵢ[ℂ] G)
    (hex : V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint +
      W.toContinuousLinearMap.comp W.toContinuousLinearMap.adjoint = 1)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    isometricExtension U (operatorConjugation V A + operatorConjugation W B) =
      1 + operatorConjugation (U.comp V) (A - 1) + operatorConjugation (U.comp W) (B - 1) := by
  have hone : operatorConjugation V (1 : E →L[ℂ] E) +
      operatorConjugation W (1 : F →L[ℂ] F) = 1 := by
    ext x
    exact DFunLike.congr_fun hex x
  have hinside : (operatorConjugation V A + operatorConjugation W B) - 1 =
      operatorConjugation V (A - 1) + operatorConjugation W (B - 1) := by
    change (operatorConjugationHom V A + operatorConjugationHom W B) - 1 =
      operatorConjugationHom V (A - 1) + operatorConjugationHom W (B - 1)
    rw [map_sub, map_sub, ← hone]
    abel
  change 1 + operatorConjugationHom U ((operatorConjugation V A + operatorConjugation W B) - 1) = _
  rw [hinside, map_add]
  change 1 + (operatorConjugation U (operatorConjugation V (A - 1)) +
    operatorConjugation U (operatorConjugation W (B - 1))) = _
  rw [operatorConjugation_comp, operatorConjugation_comp, add_assoc]

omit [CompleteSpace F] in
theorem isometry_comp_orthogonal
    (U : G →ₗᵢ[ℂ] H) (V : E →ₗᵢ[ℂ] G) (W : F →ₗᵢ[ℂ] G)
    (hVW : V.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap = 0) :
    (U.comp V).toContinuousLinearMap.adjoint.comp (U.comp W).toContinuousLinearMap = 0 := by
  have hV : (U.comp V).toContinuousLinearMap = U.toContinuousLinearMap.comp V.toContinuousLinearMap := rfl
  have hW : (U.comp W).toContinuousLinearMap = U.toContinuousLinearMap.comp W.toContinuousLinearMap := rfl
  rw [hV, hW, ContinuousLinearMap.adjoint_comp]
  ext x
  change V.toContinuousLinearMap.adjoint
    (U.toContinuousLinearMap.adjoint (U (W x))) = 0
  rw [adjoint_apply_isometry]
  exact DFunLike.congr_fun hVW x

end CoarseAssembly

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

variable [hS : IsClosed (S : Set A)]

theorem relativeClass_mul (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    relativeClass S (u * v) (relative_mul_mem S u v hu hv) =
      relativeClass S u hu + relativeClass S v hv := by
  have hm : relativeMatrix S (u * v) (relative_mul_mem S u v hu hv) =
      relativeMatrix S u hu * relativeMatrix S v hv := by
    unfold relativeMatrix
    rw [relativeUnitary_mul, map_mul, map_mul]
  apply Subtype.ext
  change TopologicalK1.matrixClass (Unitization ℂ S)
    (relativeMatrix S (u * v) _) = _
  rw [hm, TopologicalK1.matrixClass_mul]
  rfl

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_K1Nearby
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete short path between nearby invertibles -/

noncomputable section

namespace CoarseAssembly.TopologicalK1

open Analytic

variable {A : Type*} [CStarAlgebra A]

def nearbyUnitPath (u v : Aˣ) (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹)
    (t : Interval) : Aˣ :=
  Units.ofNearby u ((u : A) + (t : ℝ) • ((v : A) - u)) (by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg t.property.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) t.property.2).trans_lt h)

theorem nearbyUnitPath_continuous (u v : Aˣ)
    (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹) : Continuous (nearbyUnitPath u v h) := by
  apply (Units.isOpenEmbedding_val (R := A)).isEmbedding.continuous_iff.mpr
  change Continuous (fun t : Interval => (u : A) + (t : ℝ) • ((v : A) - u))
  exact continuous_const.add (continuous_subtype_val.smul continuous_const)

@[simp] theorem nearbyUnitPath_start (u v : Aˣ)
    (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹) : nearbyUnitPath u v h start = u := by
  apply Units.ext
  change (u : A) + (0 : ℝ) • ((v : A) - u) = u
  simp

@[simp] theorem nearbyUnitPath_finish (u v : Aˣ)
    (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹) : nearbyUnitPath u v h finish = v := by
  apply Units.ext
  change (u : A) + (1 : ℝ) • ((v : A) - u) = v
  simp

theorem continuous_scalarUnitMatrix : Continuous (scalarUnitMatrix (R := A)) := by
  apply Continuous.units_map
  exact continuous_pi (fun i => continuous_pi (fun j => by
    change Continuous (fun x : A => if i = j then x else 0)
    split_ifs <;> fun_prop))

theorem matrixClass_scalar_eq_of_nearby (u v : Aˣ)
    (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹) :
    matrixClass A (scalarUnitMatrix u) = matrixClass A (scalarUnitMatrix v) := by
  have hp := matrixClass_homotopy (fun t => scalarUnitMatrix (nearbyUnitPath u v h t))
    (continuous_scalarUnitMatrix.comp (nearbyUnitPath_continuous u v h))
  simpa only [nearbyUnitPath_start, nearbyUnitPath_finish] using hp

end CoarseAssembly.TopologicalK1

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

theorem relativeClass_eq_of_nearby (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S)
    (h : ‖(v : A) - u‖ < 1) : relativeClass S u hu = relativeClass S v hv := by
  let u' := relativeUnitary S u hu
  let v' := relativeUnitary S v hv
  have hn : ‖(v' : Unitization ℂ S) - u'‖ < 1 := by
    rw [relativeUnitary_sub_norm]
    exact h
  have hi : ‖(↑(Unitary.toUnits u')⁻¹ : Unitization ℂ S)‖ = 1 := by
    change ‖star (u' : Unitization ℂ S)‖ = 1
    rw [norm_star]
    exact CStarRing.norm_coe_unitary u'
  apply Subtype.ext
  apply TopologicalK1.matrixClass_scalar_eq_of_nearby (Unitary.toUnits u') (Unitary.toUnits v')
  simpa only [hi, inv_one, Unitary.val_toUnits_apply] using hn

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteHeadBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing finitely many components from the whole-union boundary

The argument works with the actual rational boundary unitary. Involutive
components contribute the identity in that unitary, before taking K-theory.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem relativeClass_congr {B : Type*} [CStarAlgebra B]
    (S : NonUnitalStarSubalgebra ℂ B) [hS : IsClosed (S : Set B)]
    (u v : unitary B) (hu : (u : B) - 1 ∈ S) (hv : (v : B) - 1 ∈ S) (h : u = v) :
    OperatorKTheory.relativeClass S u hu = OperatorKTheory.relativeClass S v hv := by
  subst v
  rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteIndexFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three constructed analytic index families used by the counterexample -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance constructedDiscEq (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
attribute [local instance] OAI.CoarseAssembly.constructedFiberComponentEq

local instance constructedBoundaryComponentEq_r824cac_1 (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
local instance constructedBoundaryComponentMetric (i : ℕ) : MetricSpace (BoundaryComponent i) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit i
local instance constructedBoundaryMetric : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.constructedFiberComponentMetric

attribute [local instance] OAI.CoarseAssembly.constructedTotalMetric

def separatedBaseEq : DecidableEq BaseUnion :=
  @instDecidableEqSigma ℕ Disc instDecidableEqNat constructedDiscEq

end CoarseAssembly

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

namespace DiscreteRoe

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

local instance roeAddX_r824cac_1 : AddCommMonoid (algebra (X := X) (H := H)) := inferInstance
local instance roeAddY_r824cac_1 : AddCommMonoid (algebra (X := Y) (H := H)) := inferInstance
local instance roeAddZ_r824cac_1 : AddCommMonoid (algebra (X := Z) (H := H)) := inferInstance
theorem inclusionHom_comp (e : X ↪ Y) (f : Y ↪ Z)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (hf : ∀ x y, dist (f x) (f y) ≤ dist x y) :
    NonUnitalStarAlgHom.comp (R := ℂ)
      (A := algebra (X := X) (H := H)) (B := algebra (X := Y) (H := H))
      (C := algebra (X := Z) (H := H))
      (inclusionHom (X := Y) (Y := Z) (H := H) f hf)
      (inclusionHom (X := X) (Y := Y) (H := H) e he) =
      inclusionHom (X := X) (Y := Z) (H := H) (e.trans f) (fun x y => (hf (e x) (e y)).trans (he x y)) := by
  apply DFunLike.ext
  intro T
  apply Subtype.ext
  change operatorConjugation (inclusionIsometry f) (operatorConjugation (inclusionIsometry e) T.val) =
    operatorConjugation (inclusionIsometry (e.trans f)) T.val
  rw [operatorConjugation_comp, inclusionIsometry_comp]

end DiscreteRoe

namespace Rips

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem embeddingMap_comp (e : X ↪ Y) (f : Y ↪ Z)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (hf : ∀ x y, dist (f x) (f y) ≤ dist x y) (r : ℝ) :
    (embeddingMap f hf r).comp (embeddingMap e he r) =
      embeddingMap (e.trans f) (fun x y => (hf (e x) (e y)).trans (he x y)) r := by
  apply CocompactMap.ext
  intro x
  exact mapPoint_comp e f he hf x

end Rips

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

local instance concreteDiagramBoundaryEq (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
local instance concreteDiagramFiberEq (i : ℕ) : DecidableEq (FiberVertex i) := Classical.decEq _
local instance concreteDiagramBoundaryComponentMetric (i : ℕ) : MetricSpace (BoundaryComponent i) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit i
local instance concreteDiagramBoundaryMetric : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
local instance concreteDiagramFiberComponentMetric (i : ℕ) : MetricSpace (FiberVertex i) :=
  componentMetric elementaryMoves chosenHolonomyUnit i

local instance concreteDiscEq_r824cac_1 (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
attribute [local instance] OAI.CoarseAssembly.concreteDiagramTotalMetric
local instance diagramBoundaryUnionMetric_r824cac_1 : MetricSpace (Sigma BoundaryComponent) := separatedMetric boundaryRoot
local instance diagramFiberUnionMetric_r824cac_1 : MetricSpace (Sigma FiberVertex) := separatedMetric fiberBoundaryBase
local instance diagramBoundaryRoeAdd_r824cac_1 : AddCommMonoid (algebra (X := Sigma BoundaryComponent) (H := AmpleSpace)) := inferInstance
local instance diagramFiberRoeAdd_r824cac_1 : AddCommMonoid (algebra (X := Sigma FiberVertex) (H := AmpleSpace)) := inferInstance
theorem boundaryFiberComponent_nonexpanding (i : ℕ) (x y : BoundaryComponent i) :
    dist (boundaryFiberEmbedding i x) (boundaryFiberEmbedding i y) ≤ dist x y := le_rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteIndexSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Rips-map squares for the constructed index families -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance indexSquareBoundaryEq_r824cac_1 (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
local instance indexSquareBoundaryComponentMetric (i : ℕ) : MetricSpace (BoundaryComponent i) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit i
local instance indexSquareFiberEq_r824cac_1 (i : ℕ) : DecidableEq (FiberVertex i) := Classical.decEq _
local instance indexSquareFiberComponentMetric (i : ℕ) : MetricSpace (FiberVertex i) :=
  componentMetric elementaryMoves chosenHolonomyUnit i

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RelativeNaturality
attribute [-instance] _root_.OAI.CoarseAssembly.Congruence.quotientZeroSubsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the relative-unitary K₁ representative -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (S : NonUnitalStarSubalgebra ℂ A) (T : NonUnitalStarSubalgebra ℂ B)
  [hS : IsClosed (S : Set A)] [hT : IsClosed (T : Set B)]

theorem map_relativeClass (φ : S →⋆ₙₐ[ℂ] T)
    (u : unitary A) (v : unitary B) (hu : (u : A) - 1 ∈ S) (hv : (v : B) - 1 ∈ T)
    (h : φ (relativePart S u hu) = relativePart T v hv) :
    map φ (relativeClass S u hu) = relativeClass T v hv := by
  apply Subtype.ext
  change unitizationMap φ (TopologicalK1.matrixClass (Unitization ℂ S)
    (relativeMatrix S u hu)) =
      TopologicalK1.matrixClass (Unitization ℂ T) (relativeMatrix T v hv)
  rw [unitizationMap_matrixClass]
  congr 1
  apply Units.ext
  apply Matrix.ext
  intro i j
  change Unitization.starMap φ
      (Matrix.scalar (Fin 1) (1 + (relativePart S u hu : Unitization ℂ S)) i j) =
    Matrix.scalar (Fin 1) (1 + (relativePart T v hv : Unitization ℂ T)) i j
  have hij : i = j := Subsingleton.elim _ _
  simp only [Matrix.scalar_apply, hij, Matrix.diagonal_apply_eq]
  rw [map_add, map_one, Unitization.starMap_inr, h]

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConstructedBoundaryAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the published assembly interface

The three maps are the constructed analytic cycle index maps. Their two naturality squares follow from spatial inclusion, with
explicit reindexing of the manuscript's vertex sets.
-/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance assembledDiscEq (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
local instance assemblyBoundaryEq (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
local instance assemblyFiberEq (i : ℕ) : DecidableEq (FiberVertex i) := Classical.decEq _
local instance assemblyBoundaryComponentMetric (i : ℕ) : MetricSpace (BoundaryComponent i) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit i
local instance assemblyFiberComponentMetric (i : ℕ) : MetricSpace (FiberVertex i) :=
  componentMetric elementaryMoves chosenHolonomyUnit i

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
def label1728 : Mat3 := [1, -1, 1, 1, 1, 0, 1, 0, 1]
end NuclearUltrapower.SOS
end

end OAI
end


