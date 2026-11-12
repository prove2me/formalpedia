-- Prove2me | Definitions.Def_OAIQ229C017
-- name    : OAIQ229C017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T10:26:30.440211+00:00
-- url     : https://prove2.me/theorems/94535acc-1d12-411d-bde4-09804efc54f7
-- title:
--   Definitions bundle OAIQ229C017 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 5 definitions and 32 theorems. The definitions and types are `OAI.CoarseAssembly.Analytic.sigmaCycleRepresentation`, `OAI.CoarseAssembly.DiscreteRoe.coefficientFamilyBoundary`, `OAI.CoarseAssembly.DiscreteRoe.coefficientFamilyMultiplier`, `OAI.CoarseAssembly.DiscreteRoe.familyCoefficientIsometry`, `OAI.CoarseAssembly.Rips.includedCycle`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BlockIsometryRelations`, `CoarseAssembly_CoefficientDecomposition`, `CoarseAssembly_CoefficientFamilyMultiplier`, `CoarseAssembly_CoefficientIsometry`, `CoarseAssembly_DiagonalFamilyDefect`, `CoarseAssembly_DiagonalSpatialFamily`, `CoarseAssembly_FamilyCoefficientEmbedding`, `CoarseAssembly_FamilyDecomposition`, `CoarseAssembly_FamilyEmbeddingIndependence`, `CoarseAssembly_LocalizationNormContinuity`, `CoarseAssembly_RipsInclusionNaturality`, `CoarseAssembly_RipsUnitaryLocalization`, `CoarseAssembly_SeparatedFamilyBoundary`, `CoarseAssembly_SigmaCycleRepresentation`, `CoarseAssembly_SummandComplement`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C009`, `OAIQ229C010` and `OAIQ229C011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C024`, `OAIQ229C025` and `OAIQ229C026`; the statement `OAI_NuclearUltrapower_SOS_interpret_coe_ca`; the proof of `OAI_NuclearUltrapower_SOS_interpret_coe_ca`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
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
import Mathlib.Analysis.InnerProductSpace.Spectrum
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
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C009
import Definitions.Def_OAIQ229C010
import Definitions.Def_OAIQ229C011

section
-- module Solutions.Q229_CA.CoarseAssembly_CoefficientIsometry
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalFamily_apply _root_.OAI.CoarseAssembly.DiscreteRoe.entry_diagonalFamily_same _root_.OAI.CoarseAssembly.DiscreteRoe.mem_multiplierRoeIdeal _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric changes of the coefficient Hilbert space

Changing coefficients by a pointwise isometry preserves propagation.
Extending by the identity on its orthogonal complement preserves compact
square defects, as required to place localized cycles on an ample module.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [DecidableEq X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [DecidableEq X] in
@[simp] theorem coefficientIsometry_adjoint_apply (V : E →ₗᵢ[ℂ] H)
    (v : Module X H) (x : X) :
    (coefficientIsometry (X := X) V).toContinuousLinearMap.adjoint v x =
      V.toContinuousLinearMap.adjoint (v x) := by
  rw [coefficientIsometry, blockIsometry_toCLM, blockOperator_adjoint]
  rfl

theorem coefficientIsometry_adjoint_single (V : E →ₗᵢ[ℂ] H) (x : X) (h : H) :
    (coefficientIsometry (X := X) V).toContinuousLinearMap.adjoint (lp.single 2 x h) =
      lp.single 2 x (V.toContinuousLinearMap.adjoint h) := by
  apply lp.ext
  funext y
  simp only [coefficientIsometry_adjoint_apply, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp

theorem coefficientConjugation_entry (V : E →ₗᵢ[ℂ] H) (T : Operator X E) (x y : X) :
    entry (operatorConjugation (coefficientIsometry V) T) x y =
      V.toContinuousLinearMap.comp ((entry T x y).comp V.toContinuousLinearMap.adjoint) := by
  ext h
  simp only [entry_apply, operatorConjugation, ContinuousLinearMap.comp_apply,
    coefficientIsometry_adjoint_single, LinearIsometry.coe_toContinuousLinearMap,
    coefficientIsometry_apply]

variable [PseudoMetricSpace X]

theorem coefficientConjugation_propagation (V : E →ₗᵢ[ℂ] H) {T : Operator X E}
    {r : ℝ} (hp : PropagationLE r T) :
    PropagationLE r (operatorConjugation (coefficientIsometry V) T) := by
  intro x y hxy
  rw [coefficientConjugation_entry, hp x y hxy]
  simp

omit [DecidableEq X] [PseudoMetricSpace X] in
theorem coefficientExtension_selfAdjoint (V : E →ₗᵢ[ℂ] H) (T : Operator X E)
    (hs : IsSelfAdjoint T) : IsSelfAdjoint (coefficientExtension V T) :=
  isometricExtension_selfAdjoint _ _ hs

omit [DecidableEq X] [PseudoMetricSpace X] in
theorem coefficientExtension_norm_le (V : E →ₗᵢ[ℂ] H) (T : Operator X E) :
    ‖coefficientExtension V T‖ ≤ ‖T‖ + 2 := isometricExtension_norm_le _ _

omit [DecidableEq X] [PseudoMetricSpace X] in
theorem coefficientExtension_square_compact (V : E →ₗᵢ[ℂ] H) (T : Operator X E)
    (hsq : IsCompactOperator (T * T - (1 : Operator X E))) :
    IsCompactOperator (coefficientExtension V T * coefficientExtension V T -
      (1 : Operator X H)) := isometricExtension_square_compact _ _ hsq

theorem coefficientExtension_propagation (V : E →ₗᵢ[ℂ] H) {T : Operator X E}
    {r : ℝ} (hr : 0 ≤ r) (hp : PropagationLE r T) :
    PropagationLE r (coefficientExtension V T) := by
  have he : coefficientExtension V T = 1 +
      operatorConjugation (coefficientIsometry V) T -
        operatorConjugation (coefficientIsometry V) 1 := by
    change 1 + operatorConjugation (coefficientIsometry V) (T - 1) = _
    simp only [operatorConjugation, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp]
    abel
  have h1 := propagationLE_one (X := X) (H := H)
  have h2 := coefficientConjugation_propagation V hp
  have h3 := coefficientConjugation_propagation (X := X) V (propagationLE_one (X := X) (H := E))
  have hn : PropagationLE 0 (-operatorConjugation (coefficientIsometry (X := X) V) 1) := by
    convert h3.smul (-1 : ℂ) using 1
    all_goals try with_reducible_and_instances rfl
    ext v
    simp
  rw [he, sub_eq_add_neg]
  simpa only [max_eq_right hr, max_eq_left hr] using (h1.add h2).add hn

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalSpatialFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform diagonal families on the actual separated vertex union -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, DecidableEq (V i)] [CompleteSpace H] in
theorem rowVector_diagonalFamily (A : ∀ i, Operator (V i) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (v : Module (Sigma V) H) (i : ℕ) :
    rowVector (diagonalFamily A C hC hA v) i = A i (rowVector v i) := by
  apply lp.ext
  rfl

omit [∀ i, DecidableEq (V i)] in
theorem diagonalFamily_selfAdjoint (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (hself : ∀ i, IsSelfAdjoint (A i)) :
    IsSelfAdjoint (diagonalFamily A C hC hA) := by
  have hb : IsSelfAdjoint (blockOperator A C hC hA) := by
    change (blockOperator A C hC hA).adjoint = _
    rw [blockOperator_adjoint]
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext i
    change (A i).adjoint (v i) = A i (v i)
    have hi : (A i).adjoint = A i := (hself i).star_eq
    exact DFunLike.congr_fun hi (v i)
  rw [diagonalFamily, flattenOperator_eq_conjugation]
  exact hb.map (operatorConjugationHom (flattenEquiv (Q := V) (H := H)).toLinearIsometry)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalFamilyDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square defects of uniformly bounded component operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, DecidableEq (V i)] in
theorem squareDefect_norm_le (A : Operator (V 0) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ‖A‖ ≤ C) : ‖A * A - 1‖ ≤ C * C + 1 := by
  calc
    ‖A * A - 1‖ ≤ ‖A * A‖ + ‖(1 : Operator (V 0) H)‖ := norm_sub_le _ _
    _ ≤ (‖A‖ * ‖A‖) + 1 := add_le_add (norm_mul_le _ _) ContinuousLinearMap.norm_id_le
    _ ≤ C * C + 1 := by gcongr

omit [∀ i, DecidableEq (V i)] in
theorem diagonalFamily_square_defect (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) :
    diagonalFamily A C hC hA * diagonalFamily A C hC hA - 1 =
      diagonalFamily (fun i => A i * A i - 1) (C * C + 1) (by positivity)
        (fun i => squareDefect_norm_le (V := fun _ => V i) (A i) C hC (hA i)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext z
  rcases z with ⟨i, x⟩
  simp only [sub_apply, mul_apply_eq_comp, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply,
    diagonalFamily_apply, rowVector_diagonalFamily]
  rfl

theorem diagonalFamily_square_compactEntries (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) :
    CompactEntries (diagonalFamily A C hC hA * diagonalFamily A C hC hA - 1) := by
  rw [diagonalFamily_square_defect]
  rintro ⟨i, x⟩ ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    rw [entry_diagonalFamily_same]
    exact compact_entries_of_compact (hsq i) x y
  · rw [entry_diagonalFamily_ne _ _ _ _ hij]
    exact isCompactOperator_zero

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedFamilyBoundary
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_adjoint_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply _root_.OAI.CoarseAssembly.separatedRipsMap_weight
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

variable (o : ∀ i, V i) (A : ∀ i, Operator (V i) H)
  (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
  (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))

include o r hr hp in
theorem diagonalFamily_square_mem_roe (hself : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) :
    letI := separatedMetric o
    (diagonalFamily A C hC hA) ^ 2 - 1 ∈ algebra (X := Sigma V) (H := H) := by
  let := separatedMetric o
  have hT := diagonalFamily_propagation o A C hC hA r hp
  have hdef : PropagationLE (r + r) (diagonalFamily A C hC hA ^ 2 - 1) := by
    have hm := hT.mul (separatedMetric_closedBall_finite o) hT
    have hn := (propagationLE_one (X := Sigma V) (H := H)).smul (-1 : ℂ)
    have hh := hm.add hn
    have he : (-1 : ℂ) • (1 : Operator (Sigma V) H) = -(1 : Operator (Sigma V) H) := by
      ext v
      simp
    rw [he] at hh
    simpa only [pow_two, sub_eq_add_neg,
      max_eq_left (add_nonneg hr hr)] using hh
  have hc : CompactEntries (diagonalFamily A C hC hA ^ 2 - 1) := by
    simpa only [pow_two] using diagonalFamily_square_compactEntries A C hC hA hsq
  have hs : IsSelfAdjoint (diagonalFamily A C hC hA ^ 2 - 1) := by
    have hs' := (diagonalFamily_selfAdjoint A C hC hA hself).pow 2
    have hi : IsSelfAdjoint (1 : Operator (Sigma V) H) := IsSelfAdjoint.one _
    exact @IsSelfAdjoint.sub (Operator (Sigma V) H) inferInstance inferInstance _ _ hs' hi
  exact generator_mem ⟨⟨r + r, add_nonneg hr hr, hdef⟩, hc, by rwa [hs.star_eq]⟩

include o r hr hp in
theorem separatedFamilyMultiplier_selfAdjoint (hself : ∀ i, IsSelfAdjoint (A i)) :
    letI := separatedMetric o
    IsSelfAdjoint (separatedFamilyMultiplier o A C hC hA r hr hp) := by
  let := separatedMetric o
  apply Subtype.ext
  exact (diagonalFamily_selfAdjoint A C hC hA hself).star_eq

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyCoefficientEmbedding
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single source Hilbert sum for all choices of ample coefficients -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, DecidableEq (Q i)]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def familyCoefficientIsometry (V : ∀ i, E i →ₗᵢ[ℂ] H) :
    lp (fun i => Module (Q i) (E i)) 2 →ₗᵢ[ℂ] Module (Sigma Q) H :=
  (flattenEquiv (Q := Q) (H := H)).toLinearIsometry.comp
    (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i)))

omit [∀ i, DecidableEq (Q i)] [∀ i, CompleteSpace (E i)] [CompleteSpace H] in
@[simp] theorem familyCoefficientIsometry_apply (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (v : lp (fun i => Module (Q i) (E i)) 2) (i : ℕ) (x : Q i) :
    familyCoefficientIsometry V v ⟨i, x⟩ = V i (v i x) := rfl

omit [∀ i, DecidableEq (Q i)] in
theorem familyCoefficientIsometry_adjoint_apply (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (v : Module (Sigma Q) H) (i : ℕ) (x : Q i) :
    (familyCoefficientIsometry V).toContinuousLinearMap.adjoint v i x =
      (V i).toContinuousLinearMap.adjoint (v ⟨i, x⟩) := by
  have he : (familyCoefficientIsometry (Q := Q) V).toContinuousLinearMap =
      (flattenEquiv (Q := Q) (H := H)).toLinearIsometry.toContinuousLinearMap.comp
        (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i))).toContinuousLinearMap := rfl
  have hflat :
      (flattenEquiv (Q := Q) (H := H)).toLinearIsometry.toContinuousLinearMap.adjoint =
        (flattenEquiv (Q := Q) (H := H)).symm.toLinearIsometry.toContinuousLinearMap := by
    exact LinearIsometryEquiv.adjoint_eq_symm (flattenEquiv (Q := Q) (H := H))
  have hadj : (familyCoefficientIsometry (Q := Q) V).toContinuousLinearMap.adjoint =
      (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i))).toContinuousLinearMap.adjoint.comp
        (flattenEquiv (Q := Q) (H := H)).symm.toLinearIsometry.toContinuousLinearMap := by
    rw [he, ContinuousLinearMap.adjoint_comp, hflat]
  have hx := congrArg (fun T : Module (Sigma Q) H →L[ℂ] lp (fun i => Module (Q i) (E i)) 2 =>
    T v i x) hadj
  change _ = _ at hx
  rw [hx]
  change (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i))).toContinuousLinearMap.adjoint
    (unflattenVector v) i x = _
  rw [blockIsometry_toCLM, blockOperator_adjoint]
  exact coefficientIsometry_adjoint_apply (V i) (rowVector v i) x

omit [∀ i, DecidableEq (Q i)] in
theorem familyCoefficient_extension (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (A : ∀ i, Operator (Q i) (E i)) (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (D : ℝ) (hD : 0 ≤ D) (hB : ∀ i, ‖coefficientExtension (V i) (A i)‖ ≤ D) :
    isometricExtension (familyCoefficientIsometry V) (blockOperator A C hC hA) =
      diagonalFamily (fun i => coefficientExtension (V i) (A i)) D hD hB := by
  ext v p
  rcases p with ⟨i, x⟩
  have hr : (familyCoefficientIsometry V).toContinuousLinearMap.adjoint v i =
      (coefficientIsometry (X := Q i) (V i)).toContinuousLinearMap.adjoint (rowVector v i) := by
    apply lp.ext
    funext y
    rw [familyCoefficientIsometry_adjoint_apply, coefficientIsometry_adjoint_apply]
    rfl
  change v ⟨i, x⟩ + familyCoefficientIsometry V
    ((blockOperator A C hC hA - 1)
      ((familyCoefficientIsometry V).toContinuousLinearMap.adjoint v)) ⟨i, x⟩ =
    coefficientExtension (V i) (A i) (rowVector v i) x
  rw [familyCoefficientIsometry_apply]
  simp only [sub_apply, blockOperator_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply]
  rw [hr]
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem blockOperator_selfAdjoint (A : ∀ i, Operator (Q i) (E i))
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (hs : ∀ i, IsSelfAdjoint (A i)) :
    IsSelfAdjoint (blockOperator A C hC hA) := by
  change (blockOperator A C hC hA).adjoint = _
  rw [blockOperator_adjoint]
  ext v i x
  change (A i).adjoint (v i) x = A i (v i) x
  rw [show (A i).adjoint = A i from (hs i).star_eq]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyEmbeddingIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ample coefficient choices do not affect a whole-family Roe boundary -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Boundary of a family after specified coefficient embeddings. -/
def coefficientFamilyBoundary (o : ∀ i, Q i) (A : ∀ i, Operator (Q i) (E i))
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))
    (hs : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i))))
    (V : ∀ i, E i →ₗᵢ[ℂ] H) :
    letI := separatedMetric o
    OperatorKTheory.K1 (algebra (X := Sigma Q) (H := H)) := by
  let := separatedMetric o
  exact separatedFamilyBoundary (H := H) o (fun i => coefficientExtension (V i) (A i))
    (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))
    r hr (fun i => coefficientExtension_propagation (V i) hr (hp i))
    (fun i => coefficientExtension_selfAdjoint (V i) (A i) (hs i))
    (fun i => coefficientExtension_square_compact (V i) (A i) (hsq i))

end CoarseAssembly.DiscreteRoe

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

namespace DiscreteRoe

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [CompleteSpace E] [CompleteSpace H] [Fintype X] [DecidableEq X] in
theorem coefficientIsometry_comp {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (V : H →ₗᵢ[ℂ] G) (W : E →ₗᵢ[ℂ] H) :
    (coefficientIsometry (X := X) V).comp (coefficientIsometry W) =
      coefficientIsometry (V.comp W) := by
  ext v x
  rfl

end DiscreteRoe

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CoefficientDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal decompositions lifted to the spatial vertex modules -/

noncomputable section

namespace CoarseAssembly

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DiscreteRoe

variable {X : Type*} [DecidableEq X]

omit [DecidableEq X] in
theorem coefficientIsometry_exhaustive (V : E →ₗᵢ[ℂ] H) (W : F →ₗᵢ[ℂ] H)
    (hex : V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint +
      W.toContinuousLinearMap.comp W.toContinuousLinearMap.adjoint = 1) :
    (coefficientIsometry (X := X) V).toContinuousLinearMap.comp
        (coefficientIsometry V).toContinuousLinearMap.adjoint +
      (coefficientIsometry W).toContinuousLinearMap.comp
        (coefficientIsometry W).toContinuousLinearMap.adjoint = 1 := by
  ext v x
  change coefficientIsometry V ((coefficientIsometry V).toContinuousLinearMap.adjoint v) x +
    coefficientIsometry W ((coefficientIsometry W).toContinuousLinearMap.adjoint v) x = v x
  rw [coefficientIsometry_apply, coefficientIsometry_apply,
    coefficientIsometry_adjoint_apply, coefficientIsometry_adjoint_apply]
  exact DFunLike.congr_fun hex (v x)

end DiscreteRoe

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockIsometryRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing decompositions and intertwiners on bounded Hilbert sums -/

noncomputable section

namespace CoarseAssembly

variable {I : Type*} {E F G : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

theorem blockIsometry_adjoint_coordinate (V : ∀ i, E i →ₗᵢ[ℂ] G i) (v : lp G 2) (i : I) :
    (blockIsometry V).toContinuousLinearMap.adjoint v i =
      (V i).toContinuousLinearMap.adjoint (v i) := by
  rw [blockIsometry_toCLM, blockOperator_adjoint]
  rfl

theorem blockIsometry_exhaustive (V : ∀ i, E i →ₗᵢ[ℂ] G i) (W : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hex : ∀ i, (V i).toContinuousLinearMap.comp (V i).toContinuousLinearMap.adjoint +
      (W i).toContinuousLinearMap.comp (W i).toContinuousLinearMap.adjoint = 1) :
    (blockIsometry V).toContinuousLinearMap.comp (blockIsometry V).toContinuousLinearMap.adjoint +
      (blockIsometry W).toContinuousLinearMap.comp (blockIsometry W).toContinuousLinearMap.adjoint = 1 := by
  ext v i
  change blockIsometry V ((blockIsometry V).toContinuousLinearMap.adjoint v) i +
    blockIsometry W ((blockIsometry W).toContinuousLinearMap.adjoint v) i = v i
  rw [blockIsometry_apply, blockIsometry_apply,
    blockIsometry_adjoint_coordinate, blockIsometry_adjoint_coordinate]
  exact DFunLike.congr_fun (hex i) (v i)

theorem blockOperator_decomposition
    (V : ∀ i, E i →ₗᵢ[ℂ] G i) (W : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hex : ∀ i, (V i).toContinuousLinearMap.comp (V i).toContinuousLinearMap.adjoint +
      (W i).toContinuousLinearMap.comp (W i).toContinuousLinearMap.adjoint = 1)
    (A : ∀ i, E i →L[ℂ] E i) (B : ∀ i, F i →L[ℂ] F i) (T : ∀ i, G i →L[ℂ] G i)
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D) (hT : ∀ i, ‖T i‖ ≤ K)
    (hV : ∀ i, (T i).comp (V i).toContinuousLinearMap = (V i).toContinuousLinearMap.comp (A i))
    (hW : ∀ i, (T i).comp (W i).toContinuousLinearMap = (W i).toContinuousLinearMap.comp (B i)) :
    blockOperator T K hK hT =
      operatorConjugation (blockIsometry V) (blockOperator A C hC hA) +
        operatorConjugation (blockIsometry W) (blockOperator B D hD hB) :=
  orthogonal_isometries_decompose _ _ (blockIsometry_exhaustive V W hex) _ _ _
    (blockOperator_intertwines V A T C K hC hK hA hT hV)
    (blockOperator_intertwines W B T D K hD hK hB hT hW)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CoefficientFamilyMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual multiplier underlying a coefficient-family boundary -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (o : ∀ i, Q i) (A : ∀ i, Operator (Q i) (E i))
  (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
  (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))
  (V : ∀ i, E i →ₗᵢ[ℂ] H)

def coefficientFamilyMultiplier :
    letI := separatedMetric o
    multiplierAlgebra (X := Sigma Q) (H := H) := by
  let := separatedMetric o
  exact separatedFamilyMultiplier o (fun i => coefficientExtension (V i) (A i))
    (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))
    r hr (fun i => coefficientExtension_propagation (V i) hr (hp i))

theorem coefficientFamilyMultiplier_value :
    letI := separatedMetric o
    (coefficientFamilyMultiplier o A C hC hA r hr hp V).val =
      isometricExtension (familyCoefficientIsometry V) (blockOperator A C hC hA) := by
  let := separatedMetric o
  exact (familyCoefficient_extension V A C hC hA (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))).symm

theorem coefficientFamilyMultiplier_selfAdjoint (hs : ∀ i, IsSelfAdjoint (A i)) :
    letI := separatedMetric o
    IsSelfAdjoint (coefficientFamilyMultiplier o A C hC hA r hr hp V) := by
  let := separatedMetric o
  exact separatedFamilyMultiplier_selfAdjoint o (fun i => coefficientExtension (V i) (A i))
    (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))
    r hr (fun i => coefficientExtension_propagation (V i) hr (hp i))
    (fun i => coefficientExtension_selfAdjoint (V i) (A i) (hs i))

theorem coefficientFamilyMultiplier_defect (hs : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i)))) :
    letI := separatedMetric o
    (coefficientFamilyMultiplier o A C hC hA r hr hp V).val ^ 2 - 1 ∈
      algebra (X := Sigma Q) (H := H) := by
  let := separatedMetric o
  exact diagonalFamily_square_mem_roe o (fun i => coefficientExtension (V i) (A i))
    (C + 2) (by linarith)
    (fun i => (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i]))
    r hr (fun i => coefficientExtension_propagation (V i) hr (hp i))
    (fun i => coefficientExtension_selfAdjoint (V i) (A i) (hs i))
    (fun i => coefficientExtension_square_compact (V i) (A i) (hsq i))

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal decomposition of a whole coefficient family -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E F G : ℕ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
  [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (G i)] [CompleteSpace H] in
theorem familyCoefficientIsometry_comp (U : ∀ i, G i →ₗᵢ[ℂ] H) (V : ∀ i, E i →ₗᵢ[ℂ] G i) :
    (familyCoefficientIsometry (Q := Q) U).comp
      (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i))) =
        familyCoefficientIsometry (fun i => (U i).comp (V i)) := by
  ext v p
  rcases p with ⟨i, x⟩
  rfl

theorem coefficientFamilyMultiplier_decomposition_value
    (o : ∀ i, Q i) (A : ∀ i, Operator (Q i) (E i)) (B : ∀ i, Operator (Q i) (F i))
    (T : ∀ i, Operator (Q i) (G i))
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D) (hT : ∀ i, ‖T i‖ ≤ K)
    (r : ℝ) (hr : 0 ≤ r) (hpT : ∀ i, PropagationLE r (T i))
    (L : ∀ i, E i →ₗᵢ[ℂ] G i) (R : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hex : ∀ i, (L i).toContinuousLinearMap.comp (L i).toContinuousLinearMap.adjoint +
      (R i).toContinuousLinearMap.comp (R i).toContinuousLinearMap.adjoint = 1)
    (hL : ∀ i, (T i).comp (coefficientIsometry (L i)).toContinuousLinearMap =
      (coefficientIsometry (L i)).toContinuousLinearMap.comp (A i))
    (hR : ∀ i, (T i).comp (coefficientIsometry (R i)).toContinuousLinearMap =
      (coefficientIsometry (R i)).toContinuousLinearMap.comp (B i))
    (U : ∀ i, G i →ₗᵢ[ℂ] H) :
    letI := separatedMetric o
    (coefficientFamilyMultiplier o T K hK hT r hr hpT U).val =
      1 + operatorConjugation (familyCoefficientIsometry (fun i => (U i).comp (L i)))
        (blockOperator A C hC hA - 1) +
      operatorConjugation (familyCoefficientIsometry (fun i => (U i).comp (R i)))
        (blockOperator B D hD hB - 1) := by
  let := separatedMetric o
  let VL : lp (fun i => Module (Q i) (E i)) 2 →ₗᵢ[ℂ] lp (fun i => Module (Q i) (G i)) 2 :=
    blockIsometry (fun i => coefficientIsometry (X := Q i) (L i))
  let VR : lp (fun i => Module (Q i) (F i)) 2 →ₗᵢ[ℂ] lp (fun i => Module (Q i) (G i)) 2 :=
    blockIsometry (fun i => coefficientIsometry (X := Q i) (R i))
  have hext : VL.toContinuousLinearMap.comp VL.toContinuousLinearMap.adjoint +
      VR.toContinuousLinearMap.comp VR.toContinuousLinearMap.adjoint = 1 :=
    blockIsometry_exhaustive _ _ (fun i => coefficientIsometry_exhaustive (L i) (R i) (hex i))
  have hb : blockOperator T K hK hT = operatorConjugation VL (blockOperator A C hC hA) +
      operatorConjugation VR (blockOperator B D hD hB) :=
    blockOperator_decomposition
      (fun i => coefficientIsometry (X := Q i) (L i))
      (fun i => coefficientIsometry (X := Q i) (R i))
      (fun i => coefficientIsometry_exhaustive (L i) (R i) (hex i))
      A B T C D K hC hD hK hA hB hT hL hR
  have hVL : (familyCoefficientIsometry U).comp VL =
      familyCoefficientIsometry (Q := Q) (fun i => (U i).comp (L i)) :=
    familyCoefficientIsometry_comp U L
  have hVR : (familyCoefficientIsometry U).comp VR =
      familyCoefficientIsometry (Q := Q) (fun i => (U i).comp (R i)) :=
    familyCoefficientIsometry_comp U R
  rw [coefficientFamilyMultiplier_value, hb]
  have h := isometricExtension_decomposition (familyCoefficientIsometry (Q := Q) U) VL VR hext
    (blockOperator A C hC hA) (blockOperator B D hD hB)
  simpa only [hVL, hVR] using h

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LocalizationNormContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Localization is contractive in the Fredholm operator -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype X] [DecidableEq X] in
theorem coefficientExtension_sub_norm_le (V : E →ₗᵢ[ℂ] H) (F G : Operator X E) :
    ‖coefficientExtension V F - coefficientExtension V G‖ ≤ ‖F - G‖ := by
  change ‖isometricExtension (coefficientIsometry V) F - isometricExtension (coefficientIsometry V) G‖ ≤ _
  rw [isometricExtension_sub]
  exact operatorConjugation_norm_le _ _

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsInclusionNaturality
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

def includedCycle (c : OddCycle C(Point X r, ℂ)) : OddCycle C(Point Y r, ℂ) :=
  c.precomp (inclusionFunctionHom r e he).toNonUnitalStarAlgHom

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaCycleRepresentation
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Block representations of a countable compact family -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty CStarAlgebra

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
variable (c : ∀ j, OddCycle C(Y j, ℂ))

def sigmaCycleRepresentation : C₀(Sigma Y, ℂ) →⋆ₙₐ[ℂ]
    End (countableHilbertSpace (cycleHilbertFamily Y c)) where
  toFun := sigmaRepresentationOperator Y c
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j 0) (x j) = 0
    rw [map_zero, map_zero]
    rfl
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j (f + g)) (x j) = _
    rw [map_add, map_add]
    rfl
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j (f * g)) (x j) = _
    rw [map_mul, map_mul]
    rfl
  map_smul' z f := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j (z • f)) (x j) = _
    rw [map_smul, map_smul]
    rfl
  map_star' f := by
    change sigmaRepresentationOperator Y c (star f) = (sigmaRepresentationOperator Y c f).adjoint
    rw [sigmaRepresentationOperator, sigmaRepresentationOperator, CoarseAssembly.blockOperator_adjoint]
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j (star f)) (x j) = _
    rw [map_star, map_star]
    rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SummandComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The orthogonal complement of one countable Hilbert summand -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : ℕ → HilbertSpace) (j : ℕ)

theorem summand_complement_orthogonal :
    (summandIsometry H j).toContinuousLinearMap.adjoint.comp
      (complementIsometry H j).toContinuousLinearMap = 0 := by
  rw [summandIsometry_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  exact x.property

theorem summand_complement_exhaustive :
    (summandIsometry H j).toContinuousLinearMap.comp
        (summandIsometry H j).toContinuousLinearMap.adjoint +
      (complementIsometry H j).toContinuousLinearMap.comp
        (complementIsometry H j).toContinuousLinearMap.adjoint = 1 := by
  rw [summandIsometry_adjoint, complementIsometry_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  change summandIsometry H j (x j) +
    (complementProjection H j x : countableHilbertSpace H) = x
  rw [complementProjection_coe]
  abel

end CoarseAssembly.Analytic

end

end OAI
end


