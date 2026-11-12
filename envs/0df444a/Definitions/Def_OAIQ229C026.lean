-- Prove2me | Definitions.Def_OAIQ229C026
-- name    : OAIQ229C026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:34:57.71955+00:00
-- url     : https://prove2.me/theorems/15eb42e9-1611-4b6e-bab7-351156335669
-- title:
--   Definitions bundle OAIQ229C026 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_AmpleRipsFamily`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/AmpleRipsFamily.lean), [`CoarseAssembly_DiagonalBoundaryCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/DiagonalBoundaryCoordinates.lean), [`CoarseAssembly_FiniteHeadBoundary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FiniteHeadBoundary.lean), [`CoarseAssembly_RipsInclusionNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsInclusionNaturality.lean), [`CoarseAssembly_RipsLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsLocalization.lean), [`CoarseAssembly_SpatialBoundaryNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SpatialBoundaryNaturality.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C016`, `OAIQ229C017`, `OAIQ229C018` and `OAIQ229C019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C028`, `OAIQ229C029` and `OAIQ229C030`; the statement `OAI_CoarseAssembly_provedKazhdanInput_ca`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
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
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C016
import Definitions.Def_OAIQ229C017
import Definitions.Def_OAIQ229C018
import Definitions.Def_OAIQ229C019

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

theorem ripsCompression_eq_localized (c : OddCycle C(Point X r, ℂ)) :
    partitionCompression (representedSqrt r c) c.operator =
      localizedOperator c (sqrtCoordinate r) := by
  rw [partitionCompression_eq_sum]
  simp only [representedSqrt_adjoint]
  apply Finset.sum_congr rfl
  intro x _
  change (c.representation (sqrtCoordinate r x)).comp
    (c.operator.comp (c.representation (sqrtCoordinate r x))) =
      (c.representation (sqrtCoordinate r x) * c.operator) *
        c.representation (sqrtCoordinate r x)
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

theorem ripsCompression_square_compact (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsCompactOperator (partitionCompression (representedSqrt r c) c.operator *
      partitionCompression (representedSqrt r c) c.operator - (1 : End c.space)) := by
  have hp : ∑ x, c.representation (sqrtCoordinate r x) *
      c.representation (sqrtCoordinate r x) = 1 := by
    simp only [← map_mul, ← map_sum, sqrtCoordinate_square_sum, hπ]
  let d := localizedCycle c (sqrtCoordinate r) hF (sqrtCoordinate_selfAdjoint r) hp
  have hd := d.square_compact 1
  change IsCompactOperator (((c.operator + (localizedOperator c (sqrtCoordinate r) - c.operator)) *
    (c.operator + (localizedOperator c (sqrtCoordinate r) - c.operator)) - (1 : End c.space)) *
      c.representation 1) at hd
  have he : c.operator + (localizedOperator c (sqrtCoordinate r) - c.operator) =
      localizedOperator c (sqrtCoordinate r) := by abel
  rw [he, hπ, mul_one] at hd
  rw [ripsCompression_eq_localized]
  exact hd

theorem ripsSpatialOperator_square_compact (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsCompactOperator (ripsSpatialOperator r c hπ * ripsSpatialOperator r c hπ -
      (1 : Operator X c.space)) :=
  isometricExtension_square_compact _ _ (ripsCompression_square_compact r c hπ hF)

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AmpleRipsFamily
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial representatives for finite-Rips families on the fixed ample module

The source Hilbert spaces may vary with the component. Each is embedded
isometrically into ℓ²(ℕ, ℂ), and the operator is extended by the identity.
The compact square defects give one whole-union boundary class.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem ampleRipsOperator_square_compact (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsCompactOperator (ampleRipsOperator r c hπ * ampleRipsOperator r c hπ -
      (1 : Operator X (lp (fun _ : ℕ => ℂ) 2))) :=
  coefficientExtension_square_compact _ _ (ripsSpatialOperator_square_compact r c hπ hF)

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalBoundaryCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates of the whole-union rational boundary unitary -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PseudoMetricSpace (Sigma V)]

theorem row_multiplierBoundaryUnitary
    (F : multiplierAlgebra (X := Sigma V) (H := H)) (hF : IsSelfAdjoint F)
    (A : ∀ i, Operator (V i) H) (hself : ∀ i, IsSelfAdjoint (A i))
    (hrow : ∀ v i, rowVector ((F : Operator (Sigma V) H) v) i = A i (rowVector v i))
    (v : Module (Sigma V) H) (i : ℕ) :
    rowVector ((multiplierBoundaryUnitary F hF : Operator (Sigma V) H) v) i =
      (rationalBoundaryUnitary (A i) (hself i) : Operator (V i) H) (rowVector v i) := by
  let φ := (multiplierAlgebra (X := Sigma V) (H := H)).subtype
  have hm := map_rationalBoundaryUnitary φ F hF
  change rowVector (φ (rationalBoundaryUnitary F hF) v) i = _
  rw [hm]
  exact rationalBoundaryUnitary_intertwines (rowRestriction i) (F : Operator (Sigma V) H)
    (A i) (hF.map φ) (hself i) (fun w => hrow w i) v

end CoarseAssembly.DiscreteRoe

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

theorem separatedFamilyBoundary_eq_of_rational (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (V i) H)))
    (hAB : ∀ i, rationalBoundaryUnitary (A i) (hAs i) = rationalBoundaryUnitary (B i) (hBs i)) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq =
      separatedFamilyBoundary o B D hD hB s hs hq hBs hBsq := by
  let := separatedMetric o
  let F := separatedFamilyMultiplier o A C hC hA r hr hp
  let G := separatedFamilyMultiplier o B D hD hB s hs hq
  have hFs : IsSelfAdjoint F := separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hp hAs
  have hGs : IsSelfAdjoint G := separatedFamilyMultiplier_selfAdjoint o B D hD hB s hs hq hBs
  have hu : multiplierBoundaryUnitary F hFs = multiplierBoundaryUnitary G hGs := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext z
    rcases z with ⟨i, x⟩
    have h1 := congrArg (fun w : Module (V i) H => w x)
      (row_multiplierBoundaryUnitary F hFs A hAs
        (fun w j => rowVector_diagonalFamily A C hC hA w j) v i)
    have h2 := congrArg (fun w : Module (V i) H => w x)
      (row_multiplierBoundaryUnitary G hGs B hBs
        (fun w j => rowVector_diagonalFamily B D hD hB w j) v i)
    exact h1.trans ((congrArg (fun u : unitary (Operator (V i) H) =>
      (u : Operator (V i) H) (rowVector v i) x) (hAB i)).trans h2.symm)
  exact relativeClass_congr (hS := algebra_isClosed) _ _ _ _ _ hu

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsInclusionNaturality
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
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

omit [DecidableEq X] [DecidableEq Y] in
theorem includedCycle_unital (c : OddCycle C(Point X r, ℂ)) (hπ : c.representation 1 = 1) :
    (includedCycle r e he c).representation 1 = 1 := by
  change c.representation (inclusionFunctionHom r e he 1) = 1
  rw [map_one, hπ]

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SpatialBoundaryNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The boundary representative respects spatial Roe maps

The target Fredholm operator is extended by the identity on the complement
of the spatial isometry. The conclusion is the actual K₁ map equality.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X Y H : Type*} [DecidableEq X] [DecidableEq Y]
  [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance spatialBoundaryScalarTower_r4b83d6_1 {Z : Type*} : IsScalarTower ℂ (Operator Z H) (Operator Z H) where
  smul_assoc c T S := by ext v; simp
local instance spatialBoundaryScalarComm_r4b83d6_1 {Z : Type*} : SMulCommClass ℂ (Operator Z H) (Operator Z H) where
  smul_comm c T S := by ext v; simp
theorem multiplierBoundaryUnitary_spatial
    (V : Module X H →ₗᵢ[ℂ] Module Y H)
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (G : multiplierAlgebra (X := Y) (H := H)) (hG : IsSelfAdjoint G)
    (hGF : G.val = isometricExtension V F.val) :
    (multiplierBoundaryUnitary G hG : Operator Y H) - 1 =
      operatorConjugation V ((multiplierBoundaryUnitary F hF : Operator X H) - 1) := by
  let φ : multiplierAlgebra (X := X) (H := H) →⋆ₙₐ[ℂ] Operator Y H :=
    (operatorConjugationHom V).comp
      (multiplierAlgebra (X := X) (H := H)).subtype.toNonUnitalStarAlgHom
  have he : Analytic.nonunitalIdentityExtension φ F = G.val := hGF.symm
  have h := Analytic.nonunital_rationalBoundaryUnitary φ F hF
  have hg := Analytic.map_rationalBoundaryUnitary
    (multiplierAlgebra (X := Y) (H := H)).subtype G hG
  have hg' : (multiplierBoundaryUnitary G hG : Operator Y H) =
      (Analytic.rationalBoundaryUnitary (Analytic.nonunitalIdentityExtension φ F)
        (Analytic.nonunitalIdentityExtension_selfAdjoint φ F hF) : Operator Y H) := by
    convert! hg using 2
    all_goals try with_reducible_and_instances rfl
    congr 1
  have hu : 1 + φ ((Analytic.rationalBoundaryUnitary F hF : multiplierAlgebra
      (X := X) (H := H)) - 1) = (multiplierBoundaryUnitary G hG : Operator Y H) :=
    h.trans hg'.symm
  have hu' := congrArg (fun T : Operator Y H => T - 1) hu.symm
  have hφ : φ ((Analytic.rationalBoundaryUnitary F hF :
      multiplierAlgebra (X := X) (H := H)) - 1) =
      operatorConjugation V ((multiplierBoundaryUnitary F hF : Operator X H) - 1) := rfl
  simpa only [add_sub_cancel_left, hφ] using hu'

end CoarseAssembly.DiscreteRoe

end

end OAI
end


