-- Prove2me | Definitions.Def_OAIQ229C001
-- name    : OAIQ229C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T02:25:56.538092+00:00
-- url     : https://prove2.me/theorems/c3d2f150-5b1d-4ea2-840f-7a0a1bd62d90
-- title:
--   Definitions bundle OAIQ229C001 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 198 declarations of OpenAI's Lean: 49 definitions, 6 instances and 143 theorems. The definitions and types are `OAI.CoarseAssembly.Analytic.circleCoordinate`, `OAI.CoarseAssembly.Analytic.compactFunctionForget`, `OAI.CoarseAssembly.Analytic.compactOperatorAlgebra`, `OAI.CoarseAssembly.Analytic.compactUnitary`, `OAI.CoarseAssembly.Analytic.identityUnitization`, `OAI.CoarseAssembly.Analytic.inverseSqrtCorrection`, `OAI.CoarseAssembly.Analytic.involutionNegativeProjection`, `OAI.CoarseAssembly.Analytic.involutiveNormalization`, `OAI.CoarseAssembly.Analytic.kernelClosedSubmodule`, `OAI.CoarseAssembly.Analytic.kernelProjection`, `OAI.CoarseAssembly.Analytic.negativeCoordinate`, `OAI.CoarseAssembly.Analytic.nonunitalIdentityExtension`, `OAI.CoarseAssembly.Analytic.nonunitalOrthogonalSumHom`, `OAI.CoarseAssembly.Analytic.nonunitalUnitaryExtension`, `OAI.CoarseAssembly.Analytic.normalizedReal`, `OAI.CoarseAssembly.Analytic.partialIsometryDilation`, `OAI.CoarseAssembly.Analytic.positiveProjection`, `OAI.CoarseAssembly.Analytic.projectionPhase`, `OAI.CoarseAssembly.Analytic.sigmaComponent`, `OAI.CoarseAssembly.Analytic.toeplitzCompression`, `OAI.CoarseAssembly.Analytic.unitizationEval`, `OAI.CoarseAssembly.Analytic.unitizationScalar`, `OAI.CoarseAssembly.BaseRoe`, `OAI.CoarseAssembly.BoundaryComponent`, `OAI.CoarseAssembly.BoundaryRoe`, `OAI.CoarseAssembly.BoundaryVertex`, `OAI.CoarseAssembly.CircleFamily`, `OAI.CoarseAssembly.Congruence.matrixTopBits`, `OAI.CoarseAssembly.Congruence.reduceSteps`, `OAI.CoarseAssembly.Congruence.topBit`, `OAI.CoarseAssembly.FilledDisc`, `OAI.CoarseAssembly.WindingCircle`, `OAI.CoarseAssembly.baseNeighbors`, `OAI.CoarseAssembly.boundaryAssemblyMetric3`, `OAI.CoarseAssembly.boundaryMetric`, `OAI.CoarseAssembly.boundaryToVertex`, `OAI.CoarseAssembly.compactFamilyContinuousMap`, `OAI.CoarseAssembly.compactFamilyMap`, `OAI.CoarseAssembly.compactMap`, `OAI.CoarseAssembly.discHatWeights` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BlockOperators`, `CoarseAssembly_BoundaryAssemblyMaps`, `CoarseAssembly_BoundaryEmbedding`, `CoarseAssembly_BoundaryGeometry`, `CoarseAssembly_BoundaryWalks`, `CoarseAssembly_BoundedTransformNaturality`, `CoarseAssembly_CayleyNonunitalNaturality`, `CoarseAssembly_CayleyUnitization`, `CoarseAssembly_CircleCoefficient`, `CoarseAssembly_CirclePairing`, `CoarseAssembly_CircleSequenceRepresentation`, `CoarseAssembly_ClopenRestriction`, `CoarseAssembly_CompactFamilyMap`, `CoarseAssembly_CompactFunctionalCalculus`, `CoarseAssembly_CompactIndex`, `CoarseAssembly_CompactIndexPairing`, `CoarseAssembly_ConcreteSpaces`, `CoarseAssembly_CongruenceFibers`, `CoarseAssembly_CongruenceMaps`, `CoarseAssembly_CongruenceSurjective`, `CoarseAssembly_Conjugation`, `CoarseAssembly_CountableAdditivity`, `CoarseAssembly_CycleCompactPerturbation`, `CoarseAssembly_CycleIndex`, `CoarseAssembly_EssentialToeplitz`, `CoarseAssembly_FiberConnected`, `CoarseAssembly_FiberConstants`, `CoarseAssembly_FiberDegree`, `CoarseAssembly_FiberedPersistence`, `CoarseAssembly_FilledDisc`, `CoarseAssembly_FiniteWords`, `CoarseAssembly_FredholmInvertible`, `CoarseAssembly_FredholmParametrix`, `CoarseAssembly_FredholmSquare`, `CoarseAssembly_Holonomy`, `CoarseAssembly_InvolutionUnitaryPath`, `CoarseAssembly_InvolutiveNormalization`, `CoarseAssembly_KernelProjection`, `CoarseAssembly_LatticeCharge`, `CoarseAssembly_LatticeHat`, `CoarseAssembly_LoopCircle`, `CoarseAssembly_NegativeProjection`, `CoarseAssembly_NonunitalUnitaryExtension`, `CoarseAssembly_OperatorNormalization`, `CoarseAssembly_OrthogonalExtensionBoundary`, `CoarseAssembly_OrthogonalSumBoundary`, `CoarseAssembly_PartialIsometryDilation`, `CoarseAssembly_ProjectionUnitaryPath`, `CoarseAssembly_RealNormalization`, `CoarseAssembly_Roe`, `CoarseAssembly_RoeTransfer`, `CoarseAssembly_ScalarCutDown`, `CoarseAssembly_SupportedNormalization`, `CoarseAssembly_ToeplitzCompression`, `CoarseAssembly_ToeplitzProductIndex`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C009`, `OAIQ229C010`, `OAIQ229C011`, `OAIQ229C012` and `OAIQ229C015`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Star.StarProjection
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
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
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
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
end Y
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

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

theorem blockLinear_norm_le (A : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (x : lp E 2) :
    ‖blockLinear A C hC hA x‖ ≤ C * ‖x‖ := by
  calc
    _ ≤ ‖C • lp.toNorm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro i
      change ‖A i (x i)‖ ≤ ‖C * ‖x i‖‖
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
      exact (A i).le_opNorm (x i) |>.trans
        (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
    _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, lp.norm_toNorm]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible reductions between the congruence fibers

These are the actual entrywise reductions, including level zero. In
particular, the compatibility of the chosen holonomy is a theorem, not an
extra assumption on the graph construction.
-/

namespace CoarseAssembly.Congruence

@[simp] theorem quotientMap_self (k : ℕ) (q : Quotient k) :
    quotientMap (le_refl k) q = q := by
  apply Subtype.ext
  ext i j
  simp [quotientMap, residueMap, Matrix.SpecialLinearGroup.map_apply_coe]

@[simp] theorem quotientMap_comp {l k n : ℕ} (hlk : l ≤ k) (hkn : k ≤ n)
    (q : Quotient n) :
    quotientMap hlk (quotientMap hkn q) = quotientMap (hlk.trans hkn) q := by
  have hring : (residueMap hlk).comp (residueMap hkn) =
      residueMap (hlk.trans hkn) := RingHom.ext_zmod _ _
  apply Subtype.ext
  ext i j
  exact DFunLike.congr_fun hring (q.val i j)

@[simp] theorem quotientMap_reduce {l k : ℕ} (h : l ≤ k) (w : ArithmeticGroup) :
    quotientMap h (reduce k w) = reduce l w := by
  apply Subtype.ext
  ext i j
  simp [quotientMap, reduce, Matrix.SpecialLinearGroup.map_apply_coe]

theorem map_diagonal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Rˣ) :
    Matrix.SpecialLinearGroup.map f (diagonal t) =
      diagonal (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  ext i j
  change f ((diagonal t).val i j) = (diagonal (Units.map f.toMonoidHom t)).val i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, Matrix.diagonal]

@[simp] theorem quotientMap_holonomy (t : ℤ_[2]ˣ) {l k : ℕ} (h : l ≤ k) :
    quotientMap h (holonomy t k) = holonomy t l := by
  rw [quotientMap, holonomy, map_diagonal, holonomy]
  congr 1
  apply Units.ext
  exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow l k h) (t : ℤ_[2])

instance quotientZeroSubsingleton : Subsingleton (Quotient 0) := by
  have : Subsingleton (ZMod (2 ^ 0)) := by change Subsingleton (ZMod 1); infer_instance
  exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform bound on successive congruence fibers

A residue modulo `2^(k+1)` is determined by its residue modulo `2^k`
and one binary digit. Applying this to the nine matrix entries bounds
every fiber of the special-linear reduction by `2^9`, including `k=0`.
No surjectivity or formula for the order of the group is needed.
-/

namespace CoarseAssembly.Congruence

def topBit (k : ℕ) (x : ZMod (2 ^ (k + 1))) : Fin 2 :=
  ⟨x.val / 2 ^ k, (Nat.div_lt_iff_lt_mul (by positivity)).2
    (by simpa only [pow_succ, Nat.mul_comm] using ZMod.val_lt x)⟩

def matrixTopBits (k : ℕ) (q : Quotient (k + 1)) : Fin 3 → Fin 3 → Fin 2 :=
  fun i j => topBit k (q.val i j)

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceSurjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surjectivity of the successive special-linear reductions

Lift the entries arbitrarily. The lifted determinant is odd, hence a unit;
rescaling one row by its inverse corrects the determinant without changing
the reduction. Level zero is handled by its singleton group.
-/

namespace CoarseAssembly.Congruence

@[simp] theorem residueMap_comp {l k n : ℕ} (hlk : l ≤ k) (hkn : k ≤ n)
    (a : ZMod (2 ^ n)) :
    residueMap hlk (residueMap hkn a) = residueMap (hlk.trans hkn) a := by
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((residueMap hlk).comp (residueMap hkn)) (residueMap (hlk.trans hkn))) a

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

@[simp] theorem adjoint_apply_isometry (V : E →ₗᵢ[ℂ] F) (x : E) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap] using DFunLike.congr_fun V.adjoint_comp_self x

theorem operatorConjugation_mul (V : E →ₗᵢ[ℂ] F) (T S : E →L[ℂ] E) :
    operatorConjugation V (T * S) = operatorConjugation V T * operatorConjugation V S := by
  ext x
  simp [operatorConjugation]

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized constant subspace of a finite fiber

The fiber embedding sends `h` to the constant vector `|Q|⁻¹ᐟ² h`.
It is an actual linear isometry, including for singleton boundary fibers.
-/

noncomputable section

namespace CoarseAssembly

variable (Q : Type*) [Fintype Q]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def fiberNormalization : ℝ := (Real.sqrt (Fintype.card Q))⁻¹

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Holonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The group calculation for a charged closed walk

In §3, left Cayley moves commute with the right holonomy. Recording a step
as `(s,m)` means `z ↦ s * z * g^m`; a pure Cayley step has `m=0`, and a
pure base step has `s=1`. The accumulated endpoint formula and conjugacy
obstruction are expressed using an actual finite list of steps.
-/

namespace CoarseAssembly

variable {Q : Type*} [Group Q]

/-- Product of the left moves, in the order in which they act. -/
def holonomyWord : List (Q × ℤ) → Q
  | [] => 1
  | s :: steps => holonomyWord steps * s.1

/-- Total signed crossing count. -/
def holonomyCharge : List (Q × ℤ) → ℤ
  | [] => 0
  | s :: steps => s.2 + holonomyCharge steps

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteWords
attribute [-instance] _root_.OAI.CoarseAssembly.Congruence.quotientZeroSubsingleton
attribute [-simp] _root_.OAI.CoarseAssembly.Congruence.quotientMap_comp _root_.OAI.CoarseAssembly.Congruence.quotientMap_holonomy _root_.OAI.CoarseAssembly.Congruence.quotientMap_reduce _root_.OAI.CoarseAssembly.Congruence.quotientMap_self _root_.OAI.CoarseAssembly.adjoint_apply_isometry
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

/-- Reduction of each left move, preserving its signed base charge. -/
def reduceSteps (k : ℕ) (steps : List (ArithmeticGroup × ℤ)) : List (Quotient k × ℤ) :=
  steps.map (fun s => (reduce k s.1, s.2))

@[simp] theorem holonomyCharge_reduceSteps (k : ℕ) (steps : List (ArithmeticGroup × ℤ)) :
    holonomyCharge (reduceSteps k steps) = holonomyCharge steps := by
  induction steps with
  | nil => rfl
  | cons s steps ih => simpa only [reduceSteps, List.map_cons, holonomyCharge] using congrArg (s.2 + ·) ih

@[simp] theorem holonomyWord_reduceSteps (k : ℕ) (steps : List (ArithmeticGroup × ℤ)) :
    holonomyWord (reduceSteps k steps) = reduce k (holonomyWord steps) := by
  induction steps with
  | nil => simp [reduceSteps, holonomyWord]
  | cons s steps ih =>
    simpa only [reduceSteps, List.map_cons, holonomyWord, map_mul] using
      congrArg (· * reduce k s.1) ih

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LatticeCharge
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
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

@[simp] theorem latticeCharge_self (u : LatticeVertex) : latticeCharge u u = 0 := by
  simp only [latticeCharge]
  split_ifs <;> omega

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberConnected
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

@[simp] theorem discBoundaryBase_depth (j : ℕ) :
    discDepth j (discBoundaryBase j) = 0 := by
  simp [discDepth, discBoundaryBase, latticeRadius]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberDegree
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
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

def baseNeighbors {j : ℕ} (u : Disc j) : Finset (Disc j) := by
  classical
  exact Finset.univ.filter (fun v => v = u ∨ (discGraph j).Adj u v)

@[simp] theorem mem_baseNeighbors {j : ℕ} (u v : Disc j) :
    v ∈ baseNeighbors u ↔ v = u ∨ (discGraph j).Adj u v := by
  classical
  simp [baseNeighbors]

def fiberedNeighbors (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) {j : ℕ}
    (x : FiberVertex j) : Finset (FiberVertex j) := by
  classical
  exact Finset.univ.filter (fun y => (fiberedGraph S t j).Adj x y)

@[simp] theorem mem_fiberedNeighbors (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x y : FiberVertex j) :
    y ∈ fiberedNeighbors S t x ↔ (fiberedGraph S t j).Adj x y := by
  classical
  simp [fiberedNeighbors]

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

@[simp] theorem insert_apply (x : X) (h : H) : insert x h = lp.single 2 x h := rfl

omit [DecidableEq X] in
@[simp] theorem coordinate_apply (x : X) (v : Module X H) : coordinate x v = v x := rfl

@[simp] theorem entry_apply (T : Operator X H) (x y : X) (h : H) :
    entry T x y h = T (lp.single 2 y h) x := rfl

@[simp] theorem entry_zero (x y : X) : entry (0 : Operator X H) x y = 0 := by
  ext h
  simp

@[simp] theorem entry_add (T S : Operator X H) (x y : X) :
    entry (T + S) x y = entry T x y + entry S x y := by
  ext h
  simp [entry, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]

@[simp] theorem entry_smul (c : ℂ) (T : Operator X H) (x y : X) :
    entry (c • T) x y = c • entry T x y := by
  ext h
  simp [entry]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.operatorScalarTower

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.operatorScalarComm

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

@[simp] theorem conjugationHom_apply
    (V : Module D H →ₗᵢ[ℂ] Module X H) (hV : MapsToRoe V)
    (T : algebra (X := D) (H := H)) :
    (conjugationHom V hV T : Operator X H) = operatorConjugation V T := rfl

end CoarseAssembly.DiscreteRoe

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

instance discGraphMetric (j : ℕ) : MetricSpace (Disc j) :=
  graphMetricOrDiscrete (discGraph j)

instance baseUnionMetric : MetricSpace BaseUnion := separatedMetric discBoundaryBase

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

def BoundaryVertex := {u : BaseUnion // discDepth u.1 u.2 = 0}

noncomputable instance boundaryVertexDecidableEq : DecidableEq BoundaryVertex := Classical.decEq _

def boundaryToVertex : BoundaryVertex ↪ VertexUnion where
  toFun b := ⟨b.val, 1⟩
  inj' := by
    intro b c h
    apply Subtype.ext
    exact congrArg Sigma.fst h

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

abbrev WindingCircle := AddCircle (1 : ℝ)

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

/-- Continuous maps from a compact source are cocompact. -/
def compactMap [CompactSpace X] (f : C(X, Y)) : CocompactMap X Y where
  toContinuousMap := f
  cocompact_tendsto' := by simp only [Filter.cocompact_eq_bot]; exact Filter.tendsto_bot

@[simp] theorem compactMap_apply [CompactSpace X] (f : C(X, Y)) (x : X) :
    compactMap f x = f x := rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ClopenRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting analytic K-homology to a compact open component

Extension by zero is constructed on the actual continuous-function
algebras. Its contravariant action on Fredholm modules is a left inverse
to pushforward of the component inclusion. No additivity theorem is
needed for this restriction calculation.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology
open scoped ZeroAtInfty

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space Y]

@[simp] theorem zeroExtension_apply (e : X ↪ Y) (he : IsOpenEmbedding e)
    (f : C₀(X, ℂ)) (x : X) : zeroExtension e he f (e x) = f x :=
  e.injective.extend_apply _ _ x

theorem zeroExtension_apply_outside (e : X ↪ Y) (he : IsOpenEmbedding e)
    (f : C₀(X, ℂ)) {y : Y} (hy : y ∉ Set.range e) : zeroExtension e he f y = 0 :=
  Function.extend_apply' _ _ _ hy

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CountableAdditivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable additivity in the first KK variable

The coordinate maps below are the proved extension-by-zero restrictions
on actual Fredholm-module groups. The sole published input is their
bijectivity: Blackadar, *K-Theory for Operator Algebras*, 2nd ed. (1998),
Theorem 19.7.1, for a countable disjoint union of compact metrizable spaces.
Construction of a family class and vanishing from vanishing coordinates
are consequences, not assumed inputs.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)]

def sigmaComponent (j : ℕ) : Y j ↪ Sigma Y := ⟨Sigma.mk j, sigma_mk_injective⟩

theorem sigmaComponent_open (j : ℕ) : IsOpenEmbedding (sigmaComponent Y j) :=
  IsOpenEmbedding.sigmaMk

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LatticeHat
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.CoarseAssembly.latticeCharge_self
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

def realLatticeRadius (p : ℝ × ℝ) : ℝ := max (max |p.1| |p.2|) |p.1 + p.2|

theorem realLatticeRadius_lt_iff {p : ℝ × ℝ} {a : ℝ} :
    realLatticeRadius p < a ↔ |p.1| < a ∧ |p.2| < a ∧ |p.1 + p.2| < a := by
  simp only [realLatticeRadius, max_lt_iff, and_assoc]

def hatKernel (x y : ℝ) : ℝ := max 0 (1 - realLatticeRadius (x, y))

def latticeHat (p : ℝ × ℝ) (v : LatticeVertex) : ℝ :=
  hatKernel (p.1 - v.1) (p.2 - v.2)

theorem latticeHat_nonneg (p : ℝ × ℝ) (v : LatticeVertex) : 0 ≤ latticeHat p v :=
  le_max_left _ _

theorem latticeHat_pos_iff (p : ℝ × ℝ) (v : LatticeVertex) :
    0 < latticeHat p v ↔
      |p.1 - v.1| < 1 ∧ |p.2 - v.2| < 1 ∧ |(p.1 - v.1) + (p.2 - v.2)| < 1 := by
  simp only [latticeHat, hatKernel, lt_max_iff, lt_self_iff_false, false_or,
    sub_pos, realLatticeRadius_lt_iff]

def latticeCell (p : ℝ × ℝ) : Finset LatticeVertex :=
  ({⌊p.1⌋, ⌊p.1⌋ + 1} : Finset ℤ) ×ˢ ({⌊p.2⌋, ⌊p.2⌋ + 1} : Finset ℤ)

theorem latticeHat_support_cell (p : ℝ × ℝ) (v : LatticeVertex)
    (hv : latticeHat p v ≠ 0) : v ∈ latticeCell p := by
  have hp := (latticeHat_pos_iff p v).mp (lt_of_le_of_ne (latticeHat_nonneg p v) hv.symm)
  have bound (x : ℝ) (n : ℤ) (h : |x - n| < 1) : n = ⌊x⌋ ∨ n = ⌊x⌋ + 1 := by
    have hf := Int.floor_le x
    have hc := Int.lt_floor_add_one x
    rw [abs_lt] at h
    have hlow : ⌊x⌋ < n + 1 := by exact_mod_cast (show (⌊x⌋ : ℝ) < (n : ℝ) + 1 by linarith)
    have hupp : n < ⌊x⌋ + 2 := by exact_mod_cast (show (n : ℝ) < (⌊x⌋ : ℝ) + 2 by linarith)
    omega
  simpa only [latticeCell, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    using And.intro (bound p.1 v.1 hp.1) (bound p.2 v.2 hp.2.1)

def latticeHatWeights (p : ℝ × ℝ) : LatticeVertex →₀ ℝ :=
  Finsupp.onFinset (latticeCell p) (latticeHat p) (latticeHat_support_cell p)

@[simp] theorem latticeHatWeights_apply (p : ℝ × ℝ) (v : LatticeVertex) :
    latticeHatWeights p v = latticeHat p v := rfl

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

def FilledDisc (j : ℕ) := {p : ℝ × ℝ // realLatticeRadius p ≤ j}

def discHatWeights (j : ℕ) (p : FilledDisc j) : Disc j →₀ ℝ :=
  (latticeHatWeights p.val).comapDomain Subtype.val Subtype.val_injective.injOn

@[simp] theorem discHatWeights_apply (j : ℕ) (p : FilledDisc j) (v : Disc j) :
    discHatWeights j p v = latticeHat p.val v.val := rfl

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

@[instance_reducible] def boundaryMetric (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    MetricSpace BoundaryVertex := by
  exact MetricSpace.induced boundaryToVertex boundaryToVertex.injective (vertexUnionMetric S t)

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

local instance boundaryAssemblyMetric2_r0450f2_1 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
local instance boundaryAssemblyMetric3 : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace

def BoundaryRoe : Type := algebra (X := BoundaryVertex) (H := AmpleSpace)
def BaseRoe : Type := algebra (X := BaseUnion) (H := AmpleSpace)

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

def BoundaryComponent (j : ℕ) := {u : Disc j // discDepth j u = 0}

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CycleCompactPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact changes of a Fredholm operator

The straight-line path between operators differing by a compact operator
preserves all three Fredholm defects. This is the normalization step used
when discharging the odd coefficient and circle-index inputs.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem compact_mul_right {K : End H} (hK : IsCompactOperator K) (T : End H) :
    IsCompactOperator (K * T) := hK.comp_clm T

theorem compact_mul_left {K : End H} (hK : IsCompactOperator K) (T : End H) :
    IsCompactOperator (T * K) := hK.clm_comp T

variable {A : Type} [NonUnitalCStarAlgebra A]

theorem compact_star_real_smul {K : End H} (hKs : IsCompactOperator (star K : End H)) (t : ℝ) :
    IsCompactOperator (star (t • K) : End H) := by
  rw [star_smul, star_trivial]
  exact hKs.smul t

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactFunctionalCalculus
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Functional calculus preserves compact self-adjoint operators

Compact operators whose adjoints are compact form a closed star algebra.
The nonunital functional calculus stays in that algebra. This supplies the
compactness step in the remaining normalization of the odd coefficient.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

def compactOperatorAlgebra (H : HilbertSpace) : NonUnitalStarSubalgebra ℂ (End H) where
  carrier := {T | IsCompactOperator T ∧ IsCompactOperator (star T : End H)}
  zero_mem' := by simp only [Set.mem_ofPred_eq, star_zero]; exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
  add_mem' hT hS := by
    refine ⟨hT.1.add hS.1, ?_⟩
    rw [star_add]
    exact hT.2.add hS.2
  mul_mem' hT hS := by
    refine ⟨compact_mul_right hT.1 _, ?_⟩
    rw [star_mul]
    exact compact_mul_right hS.2 _
  smul_mem' z T hT := by
    refine ⟨hT.1.smul z, ?_⟩
    rw [star_smul]
    exact hT.2.smul (star z)
  star_mem' hT := by
    exact ⟨hT.2, by simpa only [star_star] using hT.1⟩

theorem compactOperatorAlgebra_closed : IsClosed (compactOperatorAlgebra H : Set (End H)) := by
  change IsClosed ({T : End H | IsCompactOperator T} ∩
    {T : End H | IsCompactOperator (star T : End H)})
  exact isClosed_setOfPred_isCompactOperator.inter
    (isClosed_setOfPred_isCompactOperator.preimage continuous_star)

theorem compact_cfcₙ (f : ℝ → ℝ) (T : End H)
    (hT : IsCompactOperator T) (hTs : IsCompactOperator (star T : End H)) :
    IsCompactOperator (cfcₙ f T : End H) := by
  let : IsClosed (compactOperatorAlgebra H : Set (End H)) := compactOperatorAlgebra_closed
  have ht : T ∈ compactOperatorAlgebra H := ⟨hT, hTs⟩
  exact (cfcₙ_mem (𝕜' := ℂ) (s := compactOperatorAlgebra H) f ht).1

theorem compact_cfc (f : ℝ → ℝ) (T : End H)
    (hT : IsCompactOperator T) (hTs : IsCompactOperator (star T : End H))
    (hf : ContinuousOn f (quasispectrum ℝ T)) (hf0 : f 0 = 0) :
    IsCompactOperator (cfc f T : End H) := by
  rw [← cfcₙ_eq_cfc hf hf0]
  exact compact_cfcₙ f T hT hTs

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RealNormalization
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar functions for involutive Fredholm normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

def inverseSqrtCorrection (t : ℝ) : ℝ := (Real.sqrt (t + 1))⁻¹ - 1

@[simp] theorem inverseSqrtCorrection_zero : inverseSqrtCorrection 0 = 0 := by
  simp [inverseSqrtCorrection]

theorem inverseSqrtCorrection_continuousAt {t : ℝ} (ht : 0 < t + 1) :
    ContinuousAt inverseSqrtCorrection t := by
  have hs : Real.sqrt (t + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  exact ((Real.continuous_sqrt.comp (continuous_id.add continuous_const)).continuousAt.inv₀ hs).sub
    continuousAt_const

def normalizedReal (x : ℝ) : ℝ := x + x * inverseSqrtCorrection (x ^ 2 - 1)

theorem normalizedReal_eq (x : ℝ) : normalizedReal x = x * |x|⁻¹ := by
  simp only [normalizedReal, inverseSqrtCorrection, sub_add_cancel, Real.sqrt_sq_eq_abs]
  ring

theorem normalizedReal_sq {x : ℝ} (hx : x ≠ 0) : normalizedReal x ^ 2 = 1 := by
  rw [normalizedReal_eq, mul_pow, inv_pow, sq_abs]
  exact mul_inv_cancel₀ (pow_ne_zero 2 hx)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FredholmSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-dimensional kernels from the compact square defect

The kernel of `F` lies in the `-1` eigenspace of the compact operator
`F² - 1`. This supplies the finite-dimensional obstruction needed before
replacing a unital odd Fredholm operator by an invertible one.
-/

noncomputable section

namespace CoarseAssembly.Analytic

theorem finiteDimensional_ker_of_compact_square {H : HilbertSpace} (F : End H)
    (hF : IsCompactOperator (F * F - 1 : End H)) :
    FiniteDimensional ℂ F.ker := by
  let K : End H := F * F - 1
  let V : Submodule ℂ H := Module.End.eigenspace K.toLinearMap (-1)
  have hV : FiniteDimensional ℂ V :=
    ContinuousLinearMap.finite_dimensional_eigenspace hF (-1) (by norm_num)
  have hi : F.ker ≤ V := by
    intro x hx
    have hx' : F x = 0 := hx
    change x ∈ Module.End.eigenspace K.toLinearMap (-1)
    rw [Module.End.mem_eigenspace_iff]
    simp [K, hx']
  let := hV
  exact FiniteDimensional.of_injective (Submodule.inclusion hi)
    (Submodule.inclusion_injective hi)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_KernelProjection
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-rank kernel correction

For a self-adjoint operator with compact square defect, the orthogonal
projection onto its kernel is compact. Adding that projection removes the
kernel and preserves self-adjointness and the compact square defect.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

def kernelClosedSubmodule (F : End H) : ClosedSubmodule ℂ H :=
  ⟨F.ker, F.isClosed_ker⟩

def kernelProjection (F : End H) : End H := (kernelClosedSubmodule F).starProjection

theorem kernelProjection_selfAdjoint (F : End H) : IsSelfAdjoint (kernelProjection F) :=
  isSelfAdjoint_starProjection _

theorem mul_kernelProjection (F : End H) : F * kernelProjection F = 0 := by
  ext x
  exact (kernelClosedSubmodule F).starProjection_apply_mem x

theorem kernelProjection_mul (F : End H) (hF : IsSelfAdjoint F) :
    kernelProjection F * F = 0 := by
  have h := congrArg star (mul_kernelProjection F)
  simpa only [star_mul, star_zero, hF.star_eq, (kernelProjection_selfAdjoint F).star_eq] using h

theorem kernelProjection_sq (F : End H) :
    kernelProjection F * kernelProjection F = kernelProjection F :=
  (kernelClosedSubmodule F).isIdempotentElem_starProjection

theorem kernelProjection_compact (F : End H)
    (hF : IsCompactOperator (F * F - 1 : End H)) :
    IsCompactOperator (kernelProjection F) := by
  let V := kernelClosedSubmodule F
  let : FiniteDimensional ℂ V := finiteDimensional_ker_of_compact_square F hF
  have hi : IsCompactOperator (id : V → V) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).2 inferInstance
  have hp : IsCompactOperator V.orthogonalProjectionOnto := hi.comp_clm _
  exact hp.clm_comp V.subtypeL

theorem kernel_corrected_eq_zero (F : End H) (hF : IsSelfAdjoint F)
    (x : H) (hx : (F + kernelProjection F) x = 0) : x = 0 := by
  have hprod : kernelProjection F * (F + kernelProjection F) = kernelProjection F := by
    rw [mul_add, kernelProjection_mul F hF, kernelProjection_sq, zero_add]
  have hp : kernelProjection F x = 0 := by
    calc
      kernelProjection F x = (kernelProjection F * (F + kernelProjection F)) x :=
        congrArg (fun T : End H => T x) hprod.symm
      _ = kernelProjection F ((F + kernelProjection F) x) := rfl
      _ = 0 := by rw [hx, map_zero]
  have hf : F x = 0 := by
    change F x + kernelProjection F x = 0 at hx
    simpa only [hp, add_zero] using hx
  have he : kernelProjection F x = x :=
    (kernelClosedSubmodule F).starProjection_eq_self_iff.mpr hf
  exact he.symm.trans hp

theorem kernel_corrected_injective (F : End H) (hF : IsSelfAdjoint F) :
    Function.Injective (F + kernelProjection F) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply kernel_corrected_eq_zero F hF
  rw [map_sub, hxy, sub_self]

theorem kernel_corrected_selfAdjoint (F : End H) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (F + kernelProjection F) :=
  hF.add (kernelProjection_selfAdjoint F)

theorem kernel_corrected_compact_square (F : End H) (hF : IsSelfAdjoint F)
    (hc : IsCompactOperator (F * F - 1 : End H)) :
    IsCompactOperator ((F + kernelProjection F) * (F + kernelProjection F) - 1 : End H) := by
  have he : (F + kernelProjection F) * (F + kernelProjection F) - 1 =
      (F * F - 1) + kernelProjection F := by
    rw [add_mul, mul_add, mul_add, mul_kernelProjection,
      kernelProjection_mul F hF, kernelProjection_sq]
    abel
  rw [he]
  exact hc.add (kernelProjection_compact F hc)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FredholmInvertible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invertibility after the finite-rank kernel correction -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem isUnit_of_injective_compact_square (G : End H) (hinj : Function.Injective G)
    (hc : IsCompactOperator (G * G - 1 : End H)) : IsUnit G := by
  have hne : ¬ Module.End.HasEigenvalue (G * G - 1).toLinearMap (-1) := by
    intro he
    obtain ⟨x, hx, hxne⟩ := he.exists_hasEigenvector
    have hx' : G (G x) - x = -x := by
      simpa using (Module.End.mem_eigenspace_iff.mp hx)
    have hgg : G (G x) = 0 :=
      (sub_eq_iff_eq_add.mp hx').trans (neg_add_cancel x)
    have hg : G x = 0 := hinj (hgg.trans G.map_zero.symm)
    exact hxne (hinj (hg.trans G.map_zero.symm))
  have hr : (-1 : ℂ) ∈ resolventSet ℂ (G * G - 1) :=
    (hc.hasEigenvalue_or_mem_resolventSet (by norm_num)).resolve_left hne
  have hu := (spectrum.mem_resolventSet_iff.mp hr).neg
  simp only [map_neg, map_one] at hu
  have hs : IsUnit (G * G) := by
    convert hu using 1
    all_goals try with_reducible_and_instances rfl
    noncomm_ring
  rw [← pow_two] at hs
  exact (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hs

theorem kernel_corrected_isUnit (F : End H) (hF : IsSelfAdjoint F)
    (hc : IsCompactOperator (F * F - 1 : End H)) : IsUnit (F + kernelProjection F) :=
  isUnit_of_injective_compact_square _ (kernel_corrected_injective F hF)
    (kernel_corrected_compact_square F hF hc)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_InvolutiveNormalization
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Involutive representatives by compact functional calculus -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem squareDefect_cfc (F : End H) (hF : IsSelfAdjoint F) :
    cfc (fun x : ℝ => x ^ 2 - 1) F = F * F - 1 := by
  rw [cfc_sub (fun x : ℝ => x ^ 2) (fun _ => 1) F,
    cfc_pow_id F 2 hF, cfc_const_one ℝ F hF, pow_two]

theorem inverseSqrtCorrection_continuousOn (F : End H) (hF : IsSelfAdjoint F)
    (hu : IsUnit F) :
    ContinuousOn inverseSqrtCorrection (quasispectrum ℝ (F * F - 1)) := by
  rw [quasispectrum_eq_spectrum_union_zero, ← squareDefect_cfc F hF,
    cfc_map_spectrum (fun x : ℝ => x ^ 2 - 1) F hF]
  intro t ht
  rcases ht with ⟨x, hx, rfl⟩ | ht
  · apply (inverseSqrtCorrection_continuousAt _).continuousWithinAt
    have hx0 : x ≠ 0 := fun h => spectrum.zero_notMem ℝ hu (h ▸ hx)
    simpa using sq_pos_of_ne_zero hx0
  · have ht0 : t = 0 := ht
    subst t
    exact (inverseSqrtCorrection_continuousAt (by norm_num)).continuousWithinAt

theorem inverseSqrtCorrection_continuousOn_image (F : End H) (hu : IsUnit F) :
    ContinuousOn inverseSqrtCorrection ((fun x : ℝ => x ^ 2 - 1) '' spectrum ℝ F) := by
  rintro t ⟨x, hx, rfl⟩
  apply (inverseSqrtCorrection_continuousAt _).continuousWithinAt
  have hx0 : x ≠ 0 := fun h => spectrum.zero_notMem ℝ hu (h ▸ hx)
  simpa using sq_pos_of_ne_zero hx0

theorem normalizedReal_continuousOn (F : End H) (hu : IsUnit F) :
    ContinuousOn normalizedReal (spectrum ℝ F) := by
  have hc := (inverseSqrtCorrection_continuousOn_image F hu).comp
    ((continuous_id.pow 2).sub continuous_const).continuousOn (Set.mapsTo_image _ _)
  exact continuousOn_id.add (continuousOn_id.mul hc)

def involutiveNormalization (F : End H) : End H := cfc normalizedReal F

theorem involutiveNormalization_eq (F : End H) (hF : IsSelfAdjoint F) (hu : IsUnit F) :
    involutiveNormalization F = F + F * cfc inverseSqrtCorrection (F * F - 1) := by
  have hg := inverseSqrtCorrection_continuousOn_image F hu
  have hc : ContinuousOn (fun x : ℝ => inverseSqrtCorrection (x ^ 2 - 1))
      (spectrum ℝ F) := by
    exact hg.comp (by fun_prop) (Set.mapsTo_image _ _)
  unfold involutiveNormalization normalizedReal
  rw [cfc_add F (fun x : ℝ => x) (fun x => x * inverseSqrtCorrection (x ^ 2 - 1))
    continuousOn_id (continuousOn_id.mul hc),
    cfc_mul (fun x : ℝ => x) (fun x => inverseSqrtCorrection (x ^ 2 - 1)) F
      continuousOn_id hc,
    cfc_id' ℝ F hF,
    cfc_comp' inverseSqrtCorrection (fun x : ℝ => x ^ 2 - 1) F hg,
    squareDefect_cfc F hF]

theorem involutiveNormalization_sq (F : End H) (hF : IsSelfAdjoint F) (hu : IsUnit F) :
    involutiveNormalization F * involutiveNormalization F = 1 := by
  rw [← pow_two, involutiveNormalization, ← cfc_pow normalizedReal 2 F
    (normalizedReal_continuousOn F hu) hF]
  calc
    cfc (fun x => normalizedReal x ^ 2) F = cfc (fun _ : ℝ => 1) F := by
      apply cfc_congr
      intro x hx
      exact normalizedReal_sq (fun h => spectrum.zero_notMem ℝ hu (h ▸ hx))
    _ = 1 := cfc_const_one ℝ F hF

theorem involutiveNormalization_selfAdjoint (F : End H) :
    IsSelfAdjoint (involutiveNormalization F) := IsSelfAdjoint.cfc

theorem involutiveCorrection_compact (F : End H) (hF : IsSelfAdjoint F) (hu : IsUnit F)
    (hc : IsCompactOperator (F * F - 1 : End H)) :
    IsCompactOperator (F * cfc inverseSqrtCorrection (F * F - 1) : End H) ∧
    IsCompactOperator (star (F * cfc inverseSqrtCorrection (F * F - 1)) : End H) := by
  have hs : star (F * F - 1) = F * F - 1 := by rw [star_sub, star_mul, hF.star_eq, star_one]
  have hcs : IsCompactOperator (star (F * F - 1) : End H) := by rw [hs]; exact hc
  have hq := compact_cfc inverseSqrtCorrection (F * F - 1) hc hcs
    (inverseSqrtCorrection_continuousOn F hF hu) inverseSqrtCorrection_zero
  refine ⟨compact_mul_left hq F, ?_⟩
  rw [star_mul, (IsSelfAdjoint.cfc (f := inverseSqrtCorrection) (a := F * F - 1)).star_eq]
  exact compact_mul_right hq (star F)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ScalarCutDown
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting a scalar Fredholm operator down to its represented subspace -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem symmetricCutDown_sub_mul (P F : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) :
    (symmetricCutDown P F - F) * P = -(F * P - P * F) * P +
      (1 / 2 : ℝ) • (P * ((star F - F) * P)) := by
  simp only [symmetricCutDown, sub_mul, add_mul, smul_mul_assoc,
    star_mul, hP.star_eq, mul_sub, mul_assoc, hPP, one_mul, neg_mul]
  module

theorem mul_symmetricCutDown_sub (P F : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) :
    P * (symmetricCutDown P F - F) = P * (F * P - P * F) +
      (1 / 2 : ℝ) • (P * ((star F - F) * P)) := by
  simp only [symmetricCutDown, mul_sub, mul_add, mul_smul_comm,
    star_mul, hP.star_eq, sub_mul, ← mul_assoc, hPP, mul_one]
  module

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedTransformNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the path-compatible rational normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem boundedTransform_congr {F G : A} (h : F = G)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    boundedTransform F hF = boundedTransform G hG := by
  subst G
  rfl

variable {H K : HilbertSpace}

theorem map_symmetricCutDown (φ : End H →⋆ₐ[ℂ] End K) (P F : End H) :
    φ (symmetricCutDown P F) = symmetricCutDown (φ P) (φ F) := by
  unfold symmetricCutDown
  have hs (T : End H) : φ ((1 / 2 : ℝ) • T) = (1 / 2 : ℝ) • φ T :=
    φ.toAlgHom.map_smul_of_tower _ _
  rw [map_add, hs]
  simp only [map_add, map_mul, map_star, map_sub, map_one]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyUnitization
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational boundary under a nonunital spatial homomorphism

The lift `1 + (F - 1)` in a unitization makes the complementary summand
explicit. This is the algebraic input to naturality under isometric spatial
inclusions, which extend an operator by the identity off its image.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def identityUnitization (F : A) : Unitization ℂ A := 1 + ((F - 1 : A) : Unitization ℂ A)

theorem identityUnitization_selfAdjoint (F : A) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (identityUnitization F) :=
  (IsSelfAdjoint.one (Unitization ℂ A)).add
    ((hF.sub (IsSelfAdjoint.one A)).map (Unitization.inrNonUnitalStarAlgHom ℂ A))

def unitizationScalar : Unitization ℂ A →⋆ₐ[ℂ] ℂ where
  toAlgHom := Unitization.fstHom ℂ A
  map_star' := Unitization.fst_star

def unitizationEval : Unitization ℂ A →⋆ₐ[ℂ] A :=
  Unitization.starLift (NonUnitalStarAlgHom.id ℂ A)

@[simp] theorem unitizationEval_apply (a : Unitization ℂ A) :
    unitizationEval a = algebraMap ℂ A a.fst + a.snd := rfl

@[simp] theorem unitizationScalar_identity (F : A) :
    unitizationScalar (identityUnitization F) = 1 := by
  change (identityUnitization F).fst = 1
  simp only [identityUnitization, Unitization.fst_add, Unitization.fst_one,
    Unitization.fst_inr, add_zero]

@[simp] theorem unitizationEval_identity (F : A) :
    unitizationEval (identityUnitization F) = F := by
  simp only [unitizationEval_apply, identityUnitization, Unitization.fst_add,
    Unitization.fst_one, Unitization.fst_inr, Unitization.snd_add, Unitization.snd_one,
    Unitization.snd_inr, add_zero, zero_add, map_one]
  abel

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyNonunitalNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality for identity-extended nonunital homomorphisms -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def nonunitalIdentityExtension (φ : A →⋆ₙₐ[ℂ] B) (F : A) : B := 1 + φ (F - 1)

theorem nonunitalIdentityExtension_selfAdjoint (φ : A →⋆ₙₐ[ℂ] B)
    (F : A) (hF : IsSelfAdjoint F) : IsSelfAdjoint (nonunitalIdentityExtension φ F) :=
  (IsSelfAdjoint.one B).add ((hF.sub (IsSelfAdjoint.one A)).map φ)

theorem starLift_inr (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    Unitization.starLift φ (a : Unitization ℂ A) = φ a := by
  change algebraMap ℂ B 0 + φ a = φ a
  rw [map_zero, zero_add]

theorem starLift_identityUnitization (φ : A →⋆ₙₐ[ℂ] B) (F : A) :
    Unitization.starLift φ (identityUnitization F) = nonunitalIdentityExtension φ F := by
  change Unitization.starLift φ (1 + ((F - 1 : A) : Unitization ℂ A)) = 1 + φ (F - 1)
  rw [map_add, map_one, starLift_inr]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberedPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Persistence in the actual congruence-fiber graph family

The arithmetic small-loop theorem, finite-component circle index and exact
family restriction are combined here. Boundary walks remain explicit
geometric arguments; they are not labeled as published inputs. The only
published inputs in the resulting detector are the stated circle pairing
and countable first-variable additivity.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

abbrev CircleFamily := fun _ : ℕ => WindingCircle

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactFamilyMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proper maps preserving compact components

The properness argument for the family of boundary loops uses compactness
of each source component and preservation of the discrete component index.
-/

noncomputable section

namespace CoarseAssembly

open Topology

variable {X Y : ℕ → Type} [∀ j, TopologicalSpace (X j)]
  [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (X j)] [∀ j, T2Space (Y j)]

def compactFamilyContinuousMap (γ : ∀ j, C(X j, Y j)) : C(Sigma X, Sigma Y) where
  toFun z := ⟨z.1, γ z.1 z.2⟩
  continuous_toFun := continuous_sigma (fun j => continuous_sigmaMk.comp (γ j).continuous)

theorem compactFamily_preimage_compact (γ : ∀ j, C(X j, Y j))
    (K : Set (Sigma Y)) (hK : IsCompact K) :
    IsCompact ((compactFamilyContinuousMap γ) ⁻¹' K) := by
  obtain ⟨s, t, hs, _ht, heq⟩ := hK.sigma_exists_finite_sigma_eq
  have hcover : (compactFamilyContinuousMap γ) ⁻¹' K ⊆
      s.sigma (fun j => (Set.univ : Set (X j))) := by
    rintro ⟨j, z⟩ hz
    change Sigma.mk j (γ j z) ∈ K at hz
    rw [← heq] at hz
    exact ⟨hz.1, Set.mem_univ _⟩
  exact (Set.isCompact_sigma hs (fun _ _ => isCompact_univ)).of_isClosed_subset
    (hK.isClosed.preimage (compactFamilyContinuousMap γ).continuous) hcover

def compactFamilyMap (γ : ∀ j, C(X j, Y j)) : CocompactMap (Sigma X) (Sigma Y) where
  toContinuousMap := compactFamilyContinuousMap γ
  cocompact_tendsto' := CocompactMap.tendsto_of_forall_preimage
    (compactFamily_preimage_compact γ)

@[simp] theorem compactFamilyMap_apply (γ : ∀ j, C(X j, Y j)) (j : ℕ) (x : X j) :
    compactFamilyMap γ ⟨j, x⟩ = ⟨j, γ j x⟩ := rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SupportedNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization preserving the represented scalar subspace -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem commute_of_complement (F P : End H) (hF : IsSelfAdjoint F) (hP : IsSelfAdjoint P)
    (hQ : F * (1 - P) = 1 - P) : Commute F P := by
  have hQ' : (1 - P) * F = 1 - P := by
    have h := congrArg star hQ
    simpa only [star_mul, star_sub, star_one, hF.star_eq, hP.star_eq] using h
  have h1 : F - F * P = 1 - P := by simpa only [mul_sub, mul_one] using hQ
  have h2 : F - P * F = 1 - P := by simpa only [sub_mul, one_mul] using hQ'
  have h := congrArg (fun T : End H => F - T) (h1.trans h2.symm)
  exact (by simpa only [sub_sub_cancel] using h : F * P = P * F)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FredholmParametrix
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact parametrices and finite-dimensional defects

These are the finite-dimensional analytic ingredients for the scalar-unitary
index pairing. No index-pairing conclusion is assumed here.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem compact_idempotent_finiteRange (P : End H) (hp : P * P = P)
    (hc : IsCompactOperator P) : LinearMap.HasFiniteRange P.toLinearMap := by
  let V : Submodule ℂ H := Module.End.eigenspace P.toLinearMap 1
  have hv : FiniteDimensional ℂ V :=
    ContinuousLinearMap.finite_dimensional_eigenspace hc 1 one_ne_zero
  have hi : P.range ≤ V := by
    rintro y ⟨x, rfl⟩
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact congrArg (fun T : End H => T x) hp
  let := hv
  apply (Submodule.fg_iff_finiteDimensional _).mpr
  exact FiniteDimensional.of_injective (Submodule.inclusion hi) (Submodule.inclusion_injective hi)

theorem fredholm_of_finite_parametrix (S T : End H)
    (hl : LinearMap.HasFiniteRange (S * T - 1 : End H).toLinearMap)
    (hr : LinearMap.HasFiniteRange (T * S - 1 : End H).toLinearMap) : T.IsFredholm := by
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := S)
  constructor
  · rw [LinearMap.IsLeftQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    exact hl
  · rw [LinearMap.IsRightQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    exact hr

theorem isFredholm_of_compact_essential_unitary (T : End H)
    (hl : IsCompactOperator (star T * T - 1 : End H))
    (hr : IsCompactOperator (T * star T - 1 : End H)) : T.IsFredholm := by
  let G : End H := star T * T
  have hG : IsSelfAdjoint G := IsSelfAdjoint.star_mul_self T
  have hcG : IsCompactOperator (G * G - 1 : End H) := by
    have he : G * G - 1 = G * (G - 1) + (G - 1) := by noncomm_ring
    rw [he]
    exact (compact_mul_left hl G).add hl
  let P := kernelProjection G
  have hP := kernelProjection_compact G hcG
  have hPP : P * P = P := kernelProjection_sq G
  have hTP : T * P = 0 := by
    ext x
    have hx : G (P x) = 0 := congrArg (fun A : End H => A x) (mul_kernelProjection G)
    have he : G.ker = T.ker := ContinuousLinearMap.ker_adjoint_comp_self T
    have hx' : P x ∈ G.ker := hx
    exact (show P x ∈ T.ker from he ▸ hx')
  have hu : IsUnit (G + P) := kernel_corrected_isUnit G hG hcG
  let V : End H := ↑(hu.unit⁻¹)
  have hVA : V * (G + P) = 1 := by
    rw [← hu.unit_spec]
    exact Units.inv_mul hu.unit
  have hVP : V * P = P := by
    have hAP : (G + P) * P = P := by
      rw [add_mul, mul_kernelProjection G, hPP, zero_add]
    calc
      V * P = V * ((G + P) * P) := by rw [hAP]
      _ = (V * (G + P)) * P := (mul_assoc _ _ _).symm
      _ = P := by rw [hVA, one_mul]
  let S : End H := V * star T
  have hST : S * T = 1 - P := by
    calc
      S * T = V * (G + P) - V * P := by dsimp only [S, G]; noncomm_ring
      _ = 1 - P := by rw [hVA, hVP]
  have hVm : IsCompactOperator (V - 1 : End H) := by
    have he : V - 1 = -(V * ((G - 1) + P)) := by
      calc
        V - 1 = V - V * (G + P) := by rw [hVA]
        _ = -(V * ((G - 1) + P)) := by noncomm_ring
    rw [he]
    exact (compact_mul_left (hl.add hP) V).neg
  have hTS : IsCompactOperator (T * S - 1 : End H) := by
    have he : T * S - 1 = (T * star T - 1) + (T * (V - 1)) * star T := by
      dsimp only [S]
      noncomm_ring
    rw [he]
    exact hr.add (compact_mul_right (compact_mul_left hVm T) (star T))
  have hTSsq : (T * S) * (T * S) = T * S := by
    calc
      (T * S) * (T * S) = T * (S * T) * S := by noncomm_ring
      _ = T * S := by rw [hST, mul_sub, mul_one, hTP, sub_zero]
  have hQsq : (1 - T * S) * (1 - T * S) = 1 - T * S := by
    calc
      _ = 1 - T * S - T * S + (T * S) * (T * S) := by noncomm_ring
      _ = 1 - T * S := by rw [hTSsq]; abel
  have hQ : IsCompactOperator (1 - T * S : End H) := by
    rw [show (1 : End H) - T * S = -(T * S - 1) by abel]
    exact hTS.neg
  have hlfin : LinearMap.HasFiniteRange (S * T - 1 : End H).toLinearMap := by
    rw [hST, show (1 : End H) - P - 1 = -P by abel]
    exact (compact_idempotent_finiteRange P hPP hP).neg
  have hrfin : LinearMap.HasFiniteRange (T * S - 1 : End H).toLinearMap := by
    rw [show T * S - (1 : End H) = -(1 - T * S) by abel]
    exact (compact_idempotent_finiteRange _ hQsq hQ).neg
  exact fredholm_of_finite_parametrix S T hlfin hrfin

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ToeplitzCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fredholmness of scalar-unitary Toeplitz compressions -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

def toeplitzCompression (P U : End H) : End H := P * U * P + (1 - P)

theorem toeplitzCompression_star (P U : End H) (hP : IsSelfAdjoint P) :
    star (toeplitzCompression P U) = toeplitzCompression P (star U) := by
  simp only [toeplitzCompression, star_add, star_mul, star_sub, star_one, hP.star_eq, mul_assoc]

theorem toeplitzCompression_mul (P U V : End H) (hP : P * P = P) :
    toeplitzCompression P U * toeplitzCompression P V = P * U * P * V * P + (1 - P) := by
  have hright (A : End H) : A * P * P = A * P := by rw [mul_assoc, hP]
  simp only [toeplitzCompression, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
    ← mul_assoc, hright, hP]
  abel

theorem toeplitzCompression_left_defect (P U : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (hU : star U * U = 1) :
    star (toeplitzCompression P U) * toeplitzCompression P U - 1 =
      P * star U * (P * U - U * P) * P := by
  rw [toeplitzCompression_star P U hP, toeplitzCompression_mul P (star U) U hPP]
  have he : P * star U * U * P * P = P := by
    rw [mul_assoc P (star U) U, hU, mul_one, hPP, hPP]
  simp only [mul_sub, sub_mul, ← mul_assoc, he]
  abel

theorem toeplitzCompression_compact_defects (P U : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hcomm : IsCompactOperator (P * U - U * P : End H)) :
    IsCompactOperator (star (toeplitzCompression P U) * toeplitzCompression P U - 1 : End H) ∧
      IsCompactOperator (toeplitzCompression P U * star (toeplitzCompression P U) - 1 : End H) := by
  have hcommStar : IsCompactOperator (P * star U - star U * P : End H) := by
    have he : P * star U - star U * P = -(star U * (P * U - U * P) * star U) := by
      symm
      calc
        _ = -(star U * P * (U * star U) - (star U * U) * P * star U) := by noncomm_ring
        _ = _ := by rw [hUr, hUl]; noncomm_ring
    rw [he]
    exact (compact_mul_right (compact_mul_left hcomm (star U)) (star U)).neg
  constructor
  · rw [toeplitzCompression_left_defect P U hP hPP hUl]
    exact compact_mul_right (compact_mul_left hcomm (P * star U)) P
  · have he := toeplitzCompression_left_defect P (star U) hP hPP (by simpa only [star_star] using hUr)
    rw [star_star, ← toeplitzCompression_star P U hP, star_star] at he
    rw [he]
    exact compact_mul_right (compact_mul_left hcommStar (P * U)) P

theorem toeplitzCompression_fredholm (P U : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hcomm : IsCompactOperator (P * U - U * P : End H)) :
    (toeplitzCompression P U).IsFredholm := by
  obtain ⟨hl, hr⟩ := toeplitzCompression_compact_defects P U hP hPP hUl hUr hcomm
  exact isFredholm_of_compact_essential_unitary _ hl hr

theorem toeplitzCompression_unitary (P U : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hcomm : Commute P U) :
    star (toeplitzCompression P U) * toeplitzCompression P U = 1 ∧
      toeplitzCompression P U * star (toeplitzCompression P U) = 1 := by
  have hc : P * U - U * P = 0 := sub_eq_zero.mpr hcomm.eq
  have hcs : P * star U - star U * P = 0 := by
    apply sub_eq_zero.mpr
    simpa only [star_mul, hP.star_eq] using (congrArg star hcomm.eq).symm
  constructor
  · apply sub_eq_zero.mp
    rw [toeplitzCompression_left_defect P U hP hPP hUl, hc, mul_zero, zero_mul]
  · apply sub_eq_zero.mp
    have he := toeplitzCompression_left_defect P (star U) hP hPP
      (by simpa only [star_star] using hUr)
    rw [star_star, ← toeplitzCompression_star P U hP, star_star, hcs, mul_zero, zero_mul] at he
    exact he

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CycleIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Congruence.quotientZeroSubsingleton _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar-unitary index of normalized odd cycles

This constructs the Fredholm operator and its integer index. Descent to the
cycle quotient and the explicit circle-generator calculation are separate
steps; neither is assumed by these declarations.
-/

noncomputable section

theorem LinearMap.index_of_bijective {R M N : Type*} [Ring R] [Nontrivial R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] {f : M →ₗ[R] N} (hf : Function.Bijective f) :
    f.index = 0 := by
  rw [_root_.LinearMap.index_of_injective hf.1, _root_.LinearMap.range_eq_top.2 hf.2]
  simp only [neg_eq_zero, Nat.cast_eq_zero]
  exact Module.finrank_zero_of_subsingleton

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

def positiveProjection (F : End H) : End H := (1 / 2 : ℝ) • (F + 1)

theorem positiveProjection_selfAdjoint (F : End H) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (positiveProjection F) := by
  change star ((1 / 2 : ℝ) • (F + 1)) = _
  rw [star_smul, star_trivial, star_add, hF.star_eq, star_one]
  rfl

theorem positiveProjection_sq (F : End H) (hF : F * F = 1) :
    positiveProjection F * positiveProjection F = positiveProjection F := by
  have he : (F + 1) * (F + 1) = (2 : ℝ) • (F + 1) := by
    rw [add_mul, mul_add, mul_add, hF, one_mul, mul_one, one_mul]
    module
  unfold positiveProjection
  rw [smul_mul_assoc, mul_smul_comm, he]
  module

theorem positiveProjection_commutator (F U : End H) :
    positiveProjection F * U - U * positiveProjection F =
      (1 / 2 : ℝ) • (F * U - U * F) := by
  simp only [positiveProjection, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
    one_mul, mul_one]
  module

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact perturbation invariance of the Fredholm index

The compactness of both the perturbation and its adjoint keeps the straight
line path unitary modulo compact operators. Local constancy of the Fredholm
index then gives invariance, without a spectral choice of normalization.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem essentialUnitary_compactPerturb (T K : End H)
    (hl : IsCompactOperator (star T * T - 1 : End H))
    (hr : IsCompactOperator (T * star T - 1 : End H))
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End H)) :
    IsCompactOperator (star (T + K) * (T + K) - 1 : End H) ∧
      IsCompactOperator ((T + K) * star (T + K) - 1 : End H) := by
  constructor
  · have he : star (T + K) * (T + K) - 1 =
        (star T * T - 1) + star T * K + star K * T + star K * K := by
      rw [star_add]
      noncomm_ring
    rw [he]
    exact ((hl.add (compact_mul_left hK _)).add (compact_mul_right hKs _)).add
      (compact_mul_left hK _)
  · have he : (T + K) * star (T + K) - 1 =
        (T * star T - 1) + T * star K + K * star T + K * star K := by
      rw [star_add]
      noncomm_ring
    rw [he]
    exact ((hr.add (compact_mul_left hKs _)).add (compact_mul_right hK _)).add
      (compact_mul_left hKs _)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_OperatorNormalization
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A self-adjoint Fredholm operator is a compact perturbation of an involution -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem exists_compact_involution (F : End H) (hF : IsSelfAdjoint F)
    (hc : IsCompactOperator (F * F - 1 : End H)) :
    ∃ N : End H, IsSelfAdjoint N ∧ N * N = 1 ∧
      IsCompactOperator (N - F : End H) ∧ IsCompactOperator (star (N - F) : End H) := by
  let G : End H := F + kernelProjection F
  have hgs : IsSelfAdjoint G := kernel_corrected_selfAdjoint F hF
  have hgi : IsUnit G := kernel_corrected_isUnit F hF hc
  have hgc : IsCompactOperator (G * G - 1 : End H) := kernel_corrected_compact_square F hF hc
  let N := involutiveNormalization G
  have hNs : IsSelfAdjoint N := involutiveNormalization_selfAdjoint G
  have hNsq : N * N = 1 := involutiveNormalization_sq G hgs hgi
  have hcor := (involutiveCorrection_compact G hgs hgi hgc).1
  have hNF : IsCompactOperator (N - F : End H) := by
    have he : N - F = kernelProjection F + G * cfc inverseSqrtCorrection (G * G - 1) := by
      dsimp only [N]
      rw [involutiveNormalization_eq G hgs hgi]
      dsimp only [G]
      abel
    rw [he]
    exact (kernelProjection_compact F hc).add hcor
  refine ⟨N, hNs, hNsq, hNF, ?_⟩
  rw [star_sub, hNs.star_eq, hF.star_eq]
  exact hNF

theorem compact_commutator_of_compact_change (F N U : End H)
    (hFN : IsCompactOperator (N - F : End H))
    (hFU : IsCompactOperator (F * U - U * F : End H)) :
    IsCompactOperator (N * U - U * N : End H) := by
  have he : N * U - U * N = (F * U - U * F) + (N - F) * U - U * (N - F) := by
    noncomm_ring
  rw [he]
  exact (hFU.add (compact_mul_right hFN U)).sub (compact_mul_left hFN U)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_EssentialToeplitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Toeplitz Fredholmness before choosing an involution

A self-adjoint operator with compact square defect suffices. This lets the
index be defined using the explicit, continuous cut-down operator.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem positiveProjection_sub (F G : End H) :
    positiveProjection F - positiveProjection G = (1 / 2 : ℝ) • (F - G) := by
  unfold positiveProjection
  module

theorem compact_toeplitz_sub (P Q U : End H) (hPQ : IsCompactOperator (P - Q : End H)) :
    IsCompactOperator (toeplitzCompression P U - toeplitzCompression Q U : End H) := by
  have he : toeplitzCompression P U - toeplitzCompression Q U =
      (P - Q) * U * P + Q * U * (P - Q) - (P - Q) := by
    unfold toeplitzCompression
    noncomm_ring
  rw [he]
  exact ((compact_mul_right (compact_mul_right hPQ U) P).add
    (compact_mul_left hPQ (Q * U))).sub hPQ

theorem compact_star_toeplitz_sub (P Q U : End H) (hP : IsSelfAdjoint P)
    (hQ : IsSelfAdjoint Q) (hPQ : IsCompactOperator (P - Q : End H)) :
    IsCompactOperator (star (toeplitzCompression P U - toeplitzCompression Q U) : End H) := by
  rw [star_sub, toeplitzCompression_star P U hP, toeplitzCompression_star Q U hQ]
  exact compact_toeplitz_sub P Q (star U) hPQ

theorem essentialToeplitz_compact_defects (F U : End H) (hF : IsSelfAdjoint F)
    (hc : IsCompactOperator (F * F - 1 : End H))
    (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hcomm : IsCompactOperator (F * U - U * F : End H)) :
    IsCompactOperator (star (toeplitzCompression (positiveProjection F) U) *
      toeplitzCompression (positiveProjection F) U - 1 : End H) ∧
    IsCompactOperator (toeplitzCompression (positiveProjection F) U *
      star (toeplitzCompression (positiveProjection F) U) - 1 : End H) := by
  obtain ⟨N, hNs, hNsq, hNF, _⟩ := exists_compact_involution F hF hc
  have hNU := compact_commutator_of_compact_change F N U hNF hcomm
  have hQU : IsCompactOperator (positiveProjection N * U - U * positiveProjection N : End H) := by
    rw [positiveProjection_commutator]
    exact hNU.smul (1 / 2 : ℝ)
  obtain ⟨hl, hr⟩ := toeplitzCompression_compact_defects (positiveProjection N) U
    (positiveProjection_selfAdjoint N hNs) (positiveProjection_sq N hNsq) hUl hUr hQU
  have hPQ : IsCompactOperator (positiveProjection F - positiveProjection N : End H) := by
    rw [positiveProjection_sub, show F - N = -(N - F) by abel]
    exact hNF.neg.smul (1 / 2 : ℝ)
  have hd := compact_toeplitz_sub (positiveProjection F) (positiveProjection N) U hPQ
  have hds := compact_star_toeplitz_sub (positiveProjection F) (positiveProjection N) U
    (positiveProjection_selfAdjoint F hF) (positiveProjection_selfAdjoint N hNs) hPQ
  have h := essentialUnitary_compactPerturb (toeplitzCompression (positiveProjection N) U)
    (toeplitzCompression (positiveProjection F) U - toeplitzCompression (positiveProjection N) U)
    hl hr hd hds
  have he : toeplitzCompression (positiveProjection N) U +
      (toeplitzCompression (positiveProjection F) U - toeplitzCompression (positiveProjection N) U) =
      toeplitzCompression (positiveProjection F) U := by abel
  rwa [he] at h

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ToeplitzProductIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicativity of Toeplitz compression modulo compact operators -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem compact_commutator_mul (P U V : End H)
    (hU : IsCompactOperator (P * U - U * P : End H))
    (hV : IsCompactOperator (P * V - V * P : End H)) :
    IsCompactOperator (P * (U * V) - (U * V) * P : End H) := by
  have he : P * (U * V) - (U * V) * P = (P * U - U * P) * V + U * (P * V - V * P) := by
    noncomm_ring
  rw [he]
  exact (compact_mul_right hU V).add (compact_mul_left hV U)

theorem compact_commutator_star_unitary (P U : End H)
    (hul : star U * U = 1) (hur : U * star U = 1)
    (hU : IsCompactOperator (P * U - U * P : End H)) :
    IsCompactOperator (P * star U - star U * P : End H) := by
  have he : P * star U - star U * P = -(star U * (P * U - U * P) * star U) := by
    calc
      _ = -(star U * P * (U * star U) - (star U * U) * P * star U) := by rw [hul, hur]; noncomm_ring
      _ = _ := by noncomm_ring
  rw [he]
  exact (compact_mul_right (compact_mul_left hU (star U)) (star U)).neg

theorem toeplitzCompression_product_difference (P U V : End H) (hPP : P * P = P) :
    toeplitzCompression P U * toeplitzCompression P V - toeplitzCompression P (U * V) =
      P * U * (P * V - V * P) * P := by
  rw [toeplitzCompression_mul P U V hPP]
  have hlast : P * U * V * P * P = P * U * V * P := by rw [mul_assoc (P * U * V), hPP]
  simp only [toeplitzCompression, mul_sub, sub_mul, ← mul_assoc, hlast]
  abel

theorem toeplitzCompression_product_compact (P U V : End H) (hPP : P * P = P)
    (hV : IsCompactOperator (P * V - V * P : End H)) :
    IsCompactOperator (toeplitzCompression P U * toeplitzCompression P V -
      toeplitzCompression P (U * V) : End H) := by
  rw [toeplitzCompression_product_difference P U V hPP]
  exact compact_mul_right (compact_mul_left hV (P * U)) P

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactIndexPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar-unitary pairing for compact spaces -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y]

/-- A circle-valued map as a unitary in the compact continuous-function algebra. -/
def compactUnitary (f : C(X, Circle)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), continuous_subtype_val.comp f.continuous⟩

omit [CompactSpace X] in
theorem compactUnitary_star_mul (f : C(X, Circle)) : star (compactUnitary f) * compactUnitary f = 1 := by
  ext x
  change star (f x : ℂ) * (f x : ℂ) = 1
  simp only [Complex.star_def, Complex.conj_mul', Circle.norm_coe, one_pow, Complex.ofReal_one]

omit [CompactSpace X] in
theorem compactUnitary_mul_star (f : C(X, Circle)) : compactUnitary f * star (compactUnitary f) = 1 := by
  rw [mul_comm]
  exact compactUnitary_star_mul f

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_NegativeProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The negative-frequency projection for the circle cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

def negativeCoordinate (n : ℤ) : ℂ →L[ℂ] ℂ := if n < 0 then 1 else 0

theorem negativeCoordinate_norm (n : ℤ) : ‖negativeCoordinate n‖ ≤ 1 := by
  unfold negativeCoordinate
  split_ifs
  · exact ContinuousLinearMap.norm_id_le
  · simp

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CircleSequenceRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous circle functions represented by the bilateral shift -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped CStarAlgebra

def circleCoordinate : C(Circle, ℂ) := ⟨fun z => (z : ℂ), continuous_subtype_val⟩

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CircleCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional circle class of coordinate index one -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

def compactFunctionForget : C₀(X, ℂ) →⋆ₙₐ[ℂ] C(X, ℂ) where
  toFun f := f.toContinuousMap
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ProjectionUnitaryPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit unitary path for changing a projection's sign -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

def projectionPhase (P : A) (hP : IsStarProjection P) (z : unitary ℂ) : unitary A := by
  let Q := 1 - P
  have hQQ : Q * Q = Q := hP.one_sub.isIdempotentElem
  have hPP : P * P = P := hP.isIdempotentElem
  have hPQ : P * Q = 0 := hP.mul_one_sub_self
  have hQP : Q * P = 0 := hP.one_sub_mul_self
  have hz : star (z : ℂ) * (z : ℂ) = 1 := Unitary.coe_star_mul_self z
  have hz' : (z : ℂ) * star (z : ℂ) = 1 := Unitary.coe_mul_star_self z
  refine ⟨Q + (z : ℂ) • P, ?_, ?_⟩
  · change star (Q + (z : ℂ) • P) * (Q + (z : ℂ) • P) = 1
    rw [star_add, star_smul, hP.isSelfAdjoint.star_eq,
      hP.one_sub.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hQQ, mul_smul_comm, hQP, smul_zero, smul_mul_assoc, hPQ, smul_zero,
      smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
    rw [hz, one_smul, add_zero, zero_add]
    dsimp only [Q]
    abel
  · change (Q + (z : ℂ) • P) * star (Q + (z : ℂ) • P) = 1
    rw [star_add, star_smul, hP.isSelfAdjoint.star_eq,
      hP.one_sub.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hQQ, mul_smul_comm, hQP, smul_zero, smul_mul_assoc, hPQ, smul_zero,
      smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
    rw [hz', one_smul, add_zero, zero_add]
    dsimp only [Q]
    abel

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_InvolutionUnitaryPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit path from the identity to a self-adjoint involution -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

def involutionNegativeProjection (U : A) : A := (1 / 2 : ℂ) • (1 - U)

theorem involutionNegativeProjection_isStarProjection (U : A)
    (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    IsStarProjection (involutionNegativeProjection U) := by
  have hs : (1 - U) * (1 - U) = (2 : ℂ) • (1 - U) := by
    calc
      _ = 1 - U - U + U * U := by noncomm_ring
      _ = _ := by rw [hUU]; module
  constructor
  · change ((1 / 2 : ℂ) • (1 - U)) * ((1 / 2 : ℂ) • (1 - U)) =
      (1 / 2 : ℂ) • (1 - U)
    rw [smul_mul_assoc, mul_smul_comm, hs, smul_smul, smul_smul]
    norm_num
  · change star ((1 / 2 : ℂ) • (1 - U)) = (1 / 2 : ℂ) • (1 - U)
    simp only [star_smul, star_sub, star_one, hU.star_eq]
    norm_num

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_NonunitalUnitaryExtension
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identity extension of an arbitrary unitary under a nonunital map -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def nonunitalUnitaryExtension (φ : A →⋆ₙₐ[ℂ] B) (u : unitary A) : unitary B := by
  have hl : star (u : A) * (u : A) = 1 := Unitary.coe_star_mul_self u
  have hr : (u : A) * star (u : A) = 1 := by
    have h := Unitary.coe_mul_star_self u
    change (u : A) * star (u : A) = 1 at h
    exact h
  have hl' : ((u : A) - 1) + star ((u : A) - 1) +
      star ((u : A) - 1) * ((u : A) - 1) = 0 := by
    rw [star_sub, star_one]
    noncomm_ring [hl]
  have hr' : star ((u : A) - 1) + ((u : A) - 1) +
      ((u : A) - 1) * star ((u : A) - 1) = 0 := by
    rw [star_sub, star_one]
    noncomm_ring [hr]
  refine ⟨1 + φ ((u : A) - 1), ?_, ?_⟩
  · change star (1 + φ ((u : A) - 1)) * (1 + φ ((u : A) - 1)) = 1
    calc
      _ = 1 + φ (((u : A) - 1) + star ((u : A) - 1) +
        star ((u : A) - 1) * ((u : A) - 1)) := by
          rw [map_add, map_add, map_mul, map_star, star_add, star_one]
          noncomm_ring
      _ = 1 := by rw [hl', map_zero, add_zero]
  · change (1 + φ ((u : A) - 1)) * star (1 + φ ((u : A) - 1)) = 1
    calc
      _ = 1 + φ (star ((u : A) - 1) + ((u : A) - 1) +
        ((u : A) - 1) * star ((u : A) - 1)) := by
          rw [map_add, map_add, map_mul, map_star, star_add, star_one]
          noncomm_ring
      _ = 1 := by rw [hr', map_zero, add_zero]

@[simp] theorem nonunitalUnitaryExtension_val (φ : A →⋆ₙₐ[ℂ] B) (u : unitary A) :
    (nonunitalUnitaryExtension φ u : B) = 1 + φ ((u : A) - 1) := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_OrthogonalSumBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The boundary of an orthogonal sum is the product of its two boundaries -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]

variable (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R)
  (horth : ∀ a b, φ a * ψ b = 0) (hone : φ 1 + ψ 1 = 1)

include horth in
theorem orthogonal_maps_reverse (a : A) (b : B) : ψ b * φ a = 0 := by
  have h := congrArg star (horth (star a) (star b))
  simpa only [star_mul, ← map_star, star_star, star_zero] using h

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_OrthogonalExtensionBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity for orthogonal corners with an unused complementary summand -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]

def nonunitalOrthogonalSumHom (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R)
    (horth : ∀ a b, φ a * ψ b = 0) : A × B →⋆ₙₐ[ℂ] R where
  toFun p := φ p.1 + ψ p.2
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, add_mul, mul_add,
      horth, orthogonal_maps_reverse φ ψ horth, add_zero, zero_add]
  map_smul' z p := by
    change φ (z • p.1) + ψ (z • p.2) = z • (φ p.1 + ψ p.2)
    rw [map_smul, map_smul, smul_add]
  map_star' p := by simp only [Prod.fst_star, Prod.snd_star, map_star, star_add]

theorem nonunitalUnitaryExtension_orthogonal (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R)
    (horth : ∀ a b, φ a * ψ b = 0) (u : unitary A) (v : unitary B) :
    ((nonunitalUnitaryExtension φ u * nonunitalUnitaryExtension ψ v : unitary R) : R) =
      1 + φ ((u : A) - 1) + ψ ((v : B) - 1) := by
  change (1 + φ ((u : A) - 1)) * (1 + ψ ((v : B) - 1)) = _
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, horth, add_zero]
  noncomm_ring

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartialIsometryDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Swapping two isometric images by a partial-isometry dilation -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

def partialIsometryDilation (T : A) : Matrix (Fin 2) (Fin 2) A :=
  !![1 - star T * T, star T; T, 1 - T * star T]

theorem partialIsometryDilation_selfAdjoint (T : A) :
    IsSelfAdjoint (partialIsometryDilation T) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [partialIsometryDilation, Matrix.star_apply]

theorem partialIsometry_star_relation (T : A) (hT : T * star T * T = T) :
    star T * T * star T = star T := by
  have h := congrArg star hT
  simpa only [star_mul, star_star, mul_assoc] using h

theorem partialIsometry_complement_relations (T : A) (hT : T * star T * T = T) :
    (1 - star T * T) * (1 - star T * T) = 1 - star T * T ∧
    (1 - T * star T) * (1 - T * star T) = 1 - T * star T ∧
    (1 - star T * T) * star T = 0 ∧ star T * (1 - T * star T) = 0 ∧
    T * (1 - star T * T) = 0 ∧ (1 - T * star T) * T = 0 := by
  have hs := partialIsometry_star_relation T hT
  have hP : (star T * T) * (star T * T) = star T * T := by
    calc
      _ = (star T * T * star T) * T := by noncomm_ring
      _ = _ := by rw [hs]
  have hQ : (T * star T) * (T * star T) = T * star T := by
    calc
      _ = (T * star T * T) * star T := by noncomm_ring
      _ = _ := by rw [hT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [hP]
  · noncomm_ring [hQ]
  · rw [sub_mul, one_mul, hs, sub_self]
  · rw [mul_sub, mul_one, ← mul_assoc, hs, sub_self]
  · rw [mul_sub, mul_one, ← mul_assoc, hT, sub_self]
  · rw [sub_mul, one_mul, hT, sub_self]

theorem partialIsometryDilation_sq (T : A) (hT : T * star T * T = T) :
    partialIsometryDilation T * partialIsometryDilation T = 1 := by
  obtain ⟨hE, hF, hEs, hsF, hTE, hFT⟩ := partialIsometry_complement_relations T hT
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · change (1 - star T * T) * (1 - star T * T) + star T * T = 1
    rw [hE]
    abel
  · change (1 - star T * T) * star T + star T * (1 - T * star T) = 0
    rw [hEs, hsF, add_zero]
  · change T * (1 - star T * T) + (1 - T * star T) * T = 0
    rw [hTE, hFT, add_zero]
  · change T * star T + (1 - T * star T) * (1 - T * star T) = 1
    rw [hF]
    abel

end CoarseAssembly.Analytic

end

end OAI
end


