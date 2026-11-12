-- Prove2me | Definitions.Def_OAIQ229C032
-- name    : OAIQ229C032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:43:17.117967+00:00
-- url     : https://prove2.me/theorems/0307f5af-fac0-4298-b209-6d73e42613c2
-- title:
--   Definitions bundle OAIQ229C032 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 13 definitions and 7 theorems. The definitions and types are `OAI.NuclearUltrapower.Elementary.IntegralGroup`, `OAI.NuclearUltrapower.Elementary.integralAction`, `OAI.NuclearUltrapower.Elementary.integralTheta`, `OAI.NuclearUltrapower.Elementary.integralTranslation`, `OAI.NuclearUltrapower.Elementary.residue`, `OAI.NuclearUltrapower.Elementary.residueMatrix`, `OAI.NuclearUltrapower.SOS.E`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.unitaryRep`, `OAI.NuclearUltrapower.SOS.eInterpret`, `OAI.NuclearUltrapower.SOS.elementary`, `OAI.NuclearUltrapower.SOS.genSet`, `OAI.NuclearUltrapower.SOS.generator0`, `OAI.NuclearUltrapower.SOS.generator1`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_DirectSumIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/DirectSumIntertwining.lean), [`CoarseAssembly_SeparatedFamilyInclusion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SeparatedFamilyInclusion.lean), `NuclearUltrapower_IntegerMatrices`, `NuclearUltrapower_Kazhdan`, `NuclearUltrapower_SOSGap`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C028`, `OAIQ229C029` and `OAIQ229C031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C035` and `OAIQ229C036`; the statements `OAI_CoarseAssembly_elementaryKernel_projection`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_energy`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_nonneg`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_sum_gen_star`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_value_inv` and `OAI_NuclearUltrapower_SOS_ElementarySpectral_value_mul`; the proofs of `OAI_CoarseAssembly_elementaryKernel_projection`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_energy`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_nonneg`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_sum_gen_star`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_value_inv` and `OAI_NuclearUltrapower_SOS_ElementarySpectral_value_mul`.
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
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C028
import Definitions.Def_OAIQ229C029
import Definitions.Def_OAIQ229C031

section
-- module Solutions.Q229_CA.CoarseAssembly_DirectSumIntertwining
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct-sum inclusions intertwine the actual localized operators -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d e : OddCycle C(Point X r, ℂ)}

theorem ripsSpatialOperator_directSum_left (h : c.IsDirectSum d e)
    (hc : c.representation 1 = 1) (he : e.representation 1 = 1) :
    (ripsSpatialOperator r e he).comp (coefficientIsometry h.left).toContinuousLinearMap =
      (coefficientIsometry h.left).toContinuousLinearMap.comp (ripsSpatialOperator r c hc) := by
  apply localizedSpatialOperator_intertwines h.left
    (representedSqrt r c) (representedSqrt r e)
    (representedSqrt_adjoint r c) (representedSqrt_adjoint r e)
    (representedSqrt_partition r c hc) (representedSqrt_partition r e he)
  · intro x v
    change e.representation (sqrtCoordinate r x) (h.left v) = _
    rw [h.representation_eq]
    exact h.block_apply_left _ _ v
  · intro v
    rw [h.operator_eq]
    exact h.block_apply_left _ _ v

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedFamilyInclusion
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-union boundary naturality for component-preserving inclusions -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_inclusion (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (A : ∀ i, Operator (Q i) H) (B : ∀ i, Operator (P i) H)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (P i) H)))
    (hAB : ∀ i, B i = isometricExtension (inclusionIsometry (e i)) (A i)) :
    letI := separatedMetric o
    letI := separatedMetric p
    OperatorKTheory.map (inclusionHom (X := Sigma Q) (Y := Sigma P) (H := H) (componentEmbedding e) he)
      (separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq) =
        separatedFamilyBoundary p B D hD hB s hs hq hBs hBsq := by
  let := separatedMetric o
  let := separatedMetric p
  let F := separatedFamilyMultiplier o A C hC hA r hr hp
  let G := separatedFamilyMultiplier p B D hD hB s hs hq
  have hFs := separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hp hAs
  have hGs := separatedFamilyMultiplier_selfAdjoint p B D hD hB s hs hq hBs
  have hGF : G.val = isometricExtension (inclusionIsometry (componentEmbedding e)) F.val := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext z
    rcases z with ⟨i, x⟩
    have hh := congrArg (fun w : Module (P i) H => w x)
      (row_isometricExtension e (diagonalFamily A C hC hA) A
        (fun w j => rowVector_diagonalFamily A C hC hA w j) v i)
    change B i (rowVector v i) x = _
    rw [hAB i]
    exact hh.symm
  exact multiplierBoundaryClass_spatial (inclusionIsometry (componentEmbedding e))
    (inclusion_mapsToRoe (componentEmbedding e) he) F hFs
    (diagonalFamily_square_mem_roe o A C hC hA r hr hp hAs hAsq) G hGs
    (diagonalFamily_square_mem_roe p B D hD hB s hs hq hBs hBsq) hGF

end CoarseAssembly.DiscreteRoe

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

def genSet : Finset SL := (generators.map interpret).toFinset

def generator0 : Mat3 := [1, -1, 0, 0, 1, 0, 0, 0, 1]
def generator1 : Mat3 := [1, 1, 0, 0, 1, 0, 0, 0, 1]

end NuclearUltrapower.SOS
end
end

section

noncomputable section
namespace NuclearUltrapower.SOS

/-- The subgroup generated by the elementary integer matrices. -/
def elementary : Subgroup SL := Subgroup.closure (genSet : Set SL)
abbrev E := elementary

def eInterpret (m : Mat3) : E := by
  classical
  exact if h : interpret m ∈ elementary then ⟨interpret m, h⟩ else 1

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitaryRep (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : E →* unitary (H →L[ℂ] H) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp ρ

@[simp] theorem unitaryRep_coe (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (g : E) :
    (unitaryRep ρ g : H →L[ℂ] H) = (ρ g : H →L[ℂ] H) := rfl

end Hilbert
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

def integralAction : SOS.E →* MulAut (Multiplicative IntegralVector3) where
  toFun M := AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' M).toAddEquiv
  map_one' := by ext v i; simp
  map_mul' M N := by ext v i; simp [map_mul]

abbrev IntegralGroup := SemidirectProduct (Multiplicative IntegralVector3) SOS.E integralAction

def integralTranslation (v : IntegralVector3) : IntegralGroup :=
  SemidirectProduct.inl (Multiplicative.ofAdd v)

def integralTheta : Monoid.End IntegralGroup where
  toFun g := ⟨Multiplicative.ofAdd ((2 : ℤ) • g.left.toAdd), g.right⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd ((2 : ℤ) • (g.left.toAdd +
        Matrix.SpecialLinearGroup.toLin' g.right h.left.toAdd)) =
        Multiplicative.ofAdd ((2 : ℤ) • g.left.toAdd +
        Matrix.SpecialLinearGroup.toLin' g.right ((2 : ℤ) • h.left.toAdd))
      simp only [smul_add, map_smul]
    · rfl

@[simp] theorem integralTheta_left (g : IntegralGroup) :
    (integralTheta g).left.toAdd = (2 : ℤ) • g.left.toAdd := rfl

@[simp] theorem integralTheta_right (g : IntegralGroup) :
    (integralTheta g).right = g.right := rfl

@[simp] theorem integralTheta_translation (v : IntegralVector3) :
    integralTheta (integralTranslation v) = integralTranslation ((2 : ℤ) • v) := rfl

@[simp] theorem integralTheta_pow_translation (n : ℕ) (v : IntegralVector3) :
    (integralTheta ^ n) (integralTranslation v) = integralTranslation ((2 : ℤ) ^ n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Monoid.End.coe_mul, Function.comp_apply, ih, integralTheta_translation]
      congr 1
      simp only [pow_succ', mul_smul]

def residue (g : IntegralGroup) : Residue3 := fun i => (g.left.toAdd i : ZMod 2)

def residueMatrix (M : SOS.E) : Residue3 ≃ₗ[ZMod 2] Residue3 :=
  Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)) M)

end NuclearUltrapower.Elementary
end
end

end OAI
end


