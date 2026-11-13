-- Prove2me | Definitions.Def_Q260K001
-- name    : Q260K001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:34:52.458102+00:00
-- url     : https://prove2.me/theorems/2f235e6a-cd41-486c-ac1d-c5577af740c9
-- title:
--   Definitions bundle Q260K001 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 139 declarations of OpenAI's Lean: 68 definitions, 15 instances and 56 theorems. The definitions and types are `OAI.Generator.Tracial.TraceFreePreHilbert`, `OAI.Generator.Tracial.approxTraceCStar`, `OAI.Generator.Tracial.approxTraceLE`, `OAI.Generator.Tracial.ballContinuousFunctionals`, `OAI.Generator.Tracial.clippingCStar`, `OAI.Generator.Tracial.conjugateFunctional`, `OAI.Generator.Tracial.cornerStateCStar`, `OAI.Generator.Tracial.cornerStateLE`, `OAI.Generator.Tracial.cornerStateOrder`, `OAI.Generator.Tracial.cornerValueCStar`, `OAI.Generator.Tracial.cornerValueLE`, `OAI.Generator.Tracial.cornerValueOrder`, `OAI.Generator.Tracial.cyclicCoefficient`, `OAI.Generator.Tracial.cyclicPredual`, `OAI.Generator.Tracial.cyclicPredualEvaluation`, `OAI.Generator.Tracial.dominationCStar`, `OAI.Generator.Tracial.dominationLE`, `OAI.Generator.Tracial.dominationOrder`, `OAI.Generator.Tracial.dyadicFalseIndex`, `OAI.Generator.Tracial.hermitianFunctional`, `OAI.Generator.Tracial.localizedCStar`, `OAI.Generator.Tracial.localizedLE`, `OAI.Generator.Tracial.localizedOrder`, `OAI.Generator.Tracial.polarizationCStar`, `OAI.Generator.Tracial.positiveSupportLE`, `OAI.Generator.Tracial.positiveSupportPreorder`, `OAI.Generator.Tracial.quadraticStateCStar`, `OAI.Generator.Tracial.quadraticStateLE`, `OAI.Generator.Tracial.spectralAdditivityCStar`, `OAI.Generator.Tracial.spectralCut`, `OAI.Generator.Tracial.spectralFaithfulCStar`, `OAI.Generator.Tracial.spectralFaithfulLE`, `OAI.Generator.Tracial.spectralFaithfulOrder`, `OAI.Generator.Tracial.spectralFaithfulPreorder`, `OAI.Generator.Tracial.spectralSquareCStar`, `OAI.Generator.Tracial.spectralSquareOrder`, `OAI.Generator.Tracial.spectralValueCStar`, `OAI.Generator.Tracial.spectralValueLE`, `OAI.Generator.Tracial.spectralValueOrder`, `OAI.Generator.Tracial.spectralValuePreorder` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_SignedMatrixUnitaries`, `FactorGeneration_CyclicPredual`, `FactorGeneration_Dimension`, `FactorGeneration_DyadicComparison`, `FactorGeneration_FiniteComparison`, `FactorGeneration_FunctionalLimits`, `FactorGeneration_HilbertLimits`, `FactorGeneration_LocalizedStates`, `FactorGeneration_NormalDimension`, `FactorGeneration_NormalTrace`, `FactorGeneration_OperatorLimits`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_SpectralStates`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Supports`, `FactorGeneration_TraceHilbert`, `KadisonKastler_BaireSelectionHulls`, `KadisonKastler_TwoRatioParameters`.
--
--   **Imports.** It imports the bundles `OAIQ075A019` and `OAIQ075A021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K010`, `Q260K012`, `Q260K014` and `Q260K053`; the statement `OAI.KadisonKastler.vector_state_eq_trace_of_relative_central`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_OAIQ075A019
import Definitions.Def_OAIQ075A021

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_SignedMatrixUnitaries
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite group of signed permutation unitaries in a matrix system. -/

noncomputable section

open scoped BigOperators

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

def signScalar (b : Bool) : ℂ := if b then -1 else 1

@[simp] lemma signScalar_star (a : Bool) : star (signScalar a) = signScalar a := by
  cases a <;> simp [signScalar]

end MatrixSystem
end HochschildMatrixSystems

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OperatorLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

def weakOperatorBall (M : VonNeumannAlgebra H) (C : ℝ) : Set (H →WOT[ℂ] H) :=
  {T | T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ C}

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem card_dyadicIndex (n : ℕ) : Fintype.card (DyadicIndex n) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => change Fintype.card (DyadicIndex n × Bool) = _; simp [ih,pow_succ]

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : S →ₗ[ℂ] H where
  toFun a := a.val ξ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectorOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (vectorOrbitMap S ξ).range.topologicalClosure

instance vectorOrbitClosure_complete (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    CompleteSpace (vectorOrbitClosure S ξ) :=
  inferInstanceAs (CompleteSpace (vectorOrbitMap S ξ).range.topologicalClosure)

theorem mem_vectorOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ vectorOrbitClosure S ξ :=
  Submodule.le_topologicalClosure _ ⟨1,rfl⟩

theorem vectorOrbitClosure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    (a : S) {y : H} (hy : y ∈ vectorOrbitClosure S ξ) : a.val y ∈ vectorOrbitClosure S ξ := by
  have h : (vectorOrbitMap S ξ).range.topologicalClosure ≤
      (vectorOrbitClosure S ξ).comap a.val.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨a*b,rfl⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage a.val.continuous
  exact h hy

end

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/
namespace Tracial

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

abbrev traceCyclicSpace := vectorOrbitClosure M.toStarSubalgebra τ.vector

def traceCyclicVector : traceCyclicSpace τ := ⟨τ.vector,mem_vectorOrbitClosure _ _⟩

def traceCyclicOperator (a : M.toStarSubalgebra) :
    traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ :=
  a.val.restrict (fun _ hy => vectorOrbitClosure_invariant _ _ a hy)

@[simp] theorem traceCyclicOperator_apply (a : M.toStarSubalgebra) (y : traceCyclicSpace τ) :
    (traceCyclicOperator τ a y).val=a.val y.val := rfl

theorem traceCyclicOperator_star (a : M.toStarSubalgebra) :
    traceCyclicOperator τ (star a)=star (traceCyclicOperator τ a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y.val (star a.val x.val)=inner ℂ y (star (traceCyclicOperator τ a) x)
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rfl

def traceCyclicHom : M.toStarSubalgebra →⋆ₐ[ℂ]
    (traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ) where
  toFun := traceCyclicOperator τ
  map_one' := by ext y; rfl
  map_mul' _ _ := by ext y; rfl
  map_zero' := by ext y; rfl
  map_add' _ _ := by ext y; rfl
  commutes' _ := by ext y; rfl
  map_star' := traceCyclicOperator_star τ

theorem traceCyclicHom_injective : Function.Injective (traceCyclicHom τ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply τ.separating
  have h := congrArg (fun T : traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ =>
    (T (traceCyclicVector τ)).val) hab
  exact sub_eq_zero.mpr h

theorem traceCyclicHom_norm (a : M.toStarSubalgebra) : ‖traceCyclicHom τ a‖=‖a‖ := by
  let : CStarAlgebra M.toStarSubalgebra := {}
  let : CStarAlgebra (traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ) := {}
  exact NonUnitalStarAlgHom.norm_map (traceCyclicHom τ) (traceCyclicHom_injective τ) a

end

/-! The faithful cyclic restriction sends actual algebra balls to compact
weak-operator balls. On each bounded ball it is a closed topological embedding. -/
open scoped Topology
open UltrapowerBridge

end Tracial

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_CyclicPredual
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A concrete candidate predual: the norm-closed complex span of vector
functionals from the faithful cyclic trace representation, with completeness,
separability, and an isometric evaluation map. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- Name the existing operator-norm structure to keep the norm topology
explicit through the nested dual and submodule constructions. -/
instance algebraDualNormed (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (StrongDual ℂ M.toStarSubalgebra) := inferInstance

def traceCyclicLinearIsometry : M.toStarSubalgebra →ₗᵢ[ℂ]
    (traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ) :=
  { (traceCyclicHom τ).toLinearMap with norm_map' := traceCyclicHom_norm τ }

def cyclicCoefficient (ξ η : traceCyclicSpace τ) : StrongDual ℂ M.toStarSubalgebra :=
  (innerSL ℂ ξ).comp ((ContinuousLinearMap.apply ℂ (traceCyclicSpace τ) η).comp
    (traceCyclicLinearIsometry τ).toContinuousLinearMap)

@[simp] theorem cyclicCoefficient_apply (ξ η : traceCyclicSpace τ) (a : M.toStarSubalgebra) :
    cyclicCoefficient τ ξ η a=inner ℂ ξ (traceCyclicHom τ a η) := rfl

abbrev cyclicPredual : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) :=
  (Submodule.span ℂ (Set.range (fun p : traceCyclicSpace τ × traceCyclicSpace τ =>
    cyclicCoefficient τ p.1 p.2))).topologicalClosure

instance cyclicPredual_normed : NormedAddCommGroup (cyclicPredual τ) := inferInstance

instance cyclicPredual_normedSpace : NormedSpace ℂ (cyclicPredual τ) := inferInstance

instance cyclicPredual_complete : CompleteSpace (cyclicPredual τ) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (Set.range
    (fun p : traceCyclicSpace τ × traceCyclicSpace τ => cyclicCoefficient τ p.1 p.2))).topologicalClosure)

def cyclicPredualEvaluation (a : M.toStarSubalgebra) : StrongDual ℂ (cyclicPredual τ) :=
  (ContinuousLinearMap.apply ℂ ℂ a).domRestrict (cyclicPredual τ)

@[simp] theorem cyclicPredualEvaluation_apply (a : M.toStarSubalgebra) (f : cyclicPredual τ) :
    cyclicPredualEvaluation τ a f=f.val a := rfl

end

/-! Every functional in the constructed norm-closed vector-functional space is
weak-operator continuous on each bounded ball of the original algebra. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def ballContinuousFunctionals (M : VonNeumannAlgebra H) (C : ℝ) :
    Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) where
  carrier := {f | Continuous (fun T : weakOperatorBall M C => f ⟨T.val.toCLM,T.property.1⟩)}
  zero_mem' := by exact continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := hf.const_smul c

theorem ballContinuousFunctionals_isClosed (M : VonNeumannAlgebra H) (C : ℝ) :
    IsClosed (ballContinuousFunctionals M C : Set (StrongDual ℂ M.toStarSubalgebra)) := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  have hbound : Tendsto (fun n => ‖g-f n‖*(|C|+1)) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := g)).sub hfg).norm.mul_const (|C|+1))
  have hu : TendstoUniformly
      (fun n (T : weakOperatorBall M C) => f n ⟨T.val.toCLM,T.property.1⟩)
      (fun T : weakOperatorBall M C => g ⟨T.val.toCLM,T.property.1⟩) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hbound ε hε] with n hn
    intro T
    have hT : ‖T.val.toCLM‖ ≤ |C|+1 :=
      T.property.2.trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
    rw [dist_eq_norm]
    change ‖(g-f n) ⟨T.val.toCLM,T.property.1⟩‖ < ε
    have h := ((g-f n).le_opNorm ⟨T.val.toCLM,T.property.1⟩).trans
      (mul_le_mul_of_nonneg_left hT (norm_nonneg _))
    have hnn : 0 ≤ ‖g-f n‖*(|C|+1) := mul_nonneg (norm_nonneg _) (by positivity)
    exact h.trans_lt (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hnn] using hn)
  exact hu.continuous (Eventually.of_forall hf).frequently

end

/-! Recover every functional on the constructed predual from an actual algebra
element, using compact bounded balls and weak-dual Hahn--Banach separation. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

instance predualWeakScalarTower : IsScalarTower ℝ ℂ (WeakDual ℂ (cyclicPredual τ)) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ (cyclicPredual τ)))

instance predualWeakLocallyConvex : LocallyConvexSpace ℝ (WeakDual ℂ (cyclicPredual τ)) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ (cyclicPredual τ))))

end

/-! Evaluation surjectivity for any subspace of bounded-unit-ball WOT-continuous
functionals. Compactness and Hahn--Banach supply actual algebra elements. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (F : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra))

instance functionalSubspaceNormed : NormedAddCommGroup F := inferInstance

instance functionalSubspaceNormedSpace : NormedSpace ℂ F := inferInstance

instance functionalSubspaceWeakScalarTower : IsScalarTower ℝ ℂ (WeakDual ℂ F) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ F))

instance functionalSubspaceWeakLocallyConvex : LocallyConvexSpace ℝ (WeakDual ℂ F) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ F)))

end

/-! Exact characterization of the cyclic predual by WOT continuity on the
unit ball. No continuity of an arbitrary given-predual evaluation is assumed
or asserted here. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Supports
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.PopaCorner.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.positiveSupportCStar
attribute [local instance] OAI.Generator.Tracial.positiveSupportOrder
local instance positiveSupportPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance positiveSupportLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

attribute [local instance] OAI.Generator.Tracial.positiveSupportStarOrder
def spectralCut (x : M.toStarSubalgebra) (t : ℝ) : AlgebraProjection M :=
  positiveSupport (x-(t : ℂ) • (1 : M.toStarSubalgebra))

end

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance unitaryPolarCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance unitaryPolarOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance unitaryPolarStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

/-- A proper diffuse subprojection splits a nonzero corner into orthogonal pieces. -/
theorem traceFree_exists_orthogonal_split
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection M) (hp : p.val≠0) :
    ∃ q r : AlgebraProjection M, q ≤ p ∧ r ≤ p ∧ q.val≠0 ∧ r.val≠0 ∧
      q.val*r.val=0 ∧ q.val+r.val=p.val := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := hdiff p.val p.property hp
  let r : AlgebraProjection M := ⟨p.val-q,hq.sub_of_mul_eq_right p.property hpq⟩
  refine ⟨⟨q,hq⟩,r,hpq,?_,hq0,sub_ne_zero.mpr hqp.symm,?_,?_⟩
  · change p.val*(p.val-q)=p.val-q
    rw [mul_sub,p.property.isIdempotentElem.eq,hpq]
  · change q*(p.val-q)=0
    rw [mul_sub,hqp',hq.isIdempotentElem.eq,sub_self]
  · change q+(p.val-q)=p.val
    abel

end Tracial

end

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Follow the false child at every level of the actual coherent dyadic system. -/
def dyadicFalseIndex : (n : ℕ) → DyadicIndex n
  | 0 => ()
  | n+1 => (dyadicFalseIndex n,false)

end Tracial

end

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem exists_disjoint_card (s t : Finset ι) (h : s.card+t.card ≤ Fintype.card ι) :
    ∃ u : Finset ι, Disjoint s u ∧ u.card=t.card := by
  classical
  have hc : t.card ≤ (Finset.univ \ s).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s),Finset.card_univ]
    omega
  obtain ⟨u,hu,huc⟩ := Finset.exists_subset_card_eq hc
  refine ⟨u,Finset.disjoint_left.mpr ?_,huc⟩
  intro i hi hui
  exact (Finset.mem_sdiff.mp (hu hui)).2 hi

end EquivalentPartition
end

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem eq_of_all_dyadic_errors (a b : ℝ) (h : ∀ n : ℕ, |a-b| ≤ 2/2^n) : a=b := by
  by_contra hab
  have hp : 0 < |a-b|/2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hab)) (by norm_num)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hh := h n
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring] at hh
  linarith

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem le_of_all_dyadic_errors (a b : ℝ) (h : ∀ n : ℕ, a ≤ b+1/2^n) : a ≤ b := by
  by_contra hab
  have hp : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hh := h n
  linarith

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_FunctionalLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A functional bounded by a Hilbert-valued linear map factors through one
inner product. The proof uses the actual range, Hahn--Banach, and Riesz. -/
namespace Tracial

section
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem exists_inner_factor_of_bound (F : E →ₗ[ℂ] V) (φ : E →ₗ[ℂ] ℂ)
    (C : ℝ) (hb : ∀ x : E, ‖φ x‖ ≤ C*‖F x‖) :
    ∃ η : V, ∀ x : E, φ x=inner ℂ η (F x) := by
  classical
  have hfiber {x y : E} (h : F x=F y) : φ x=φ y := by
    have hb' := hb (x-y)
    rw [map_sub,map_sub,h,sub_self,norm_zero,mul_zero] at hb'
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb' (norm_nonneg _)))
  have hex (z : LinearMap.range F) : ∃ x : E, F x=z.val := z.property
  choose a ha using hex
  let L : LinearMap.range F →ₗ[ℂ] ℂ :=
    { toFun := fun z => φ (a z)
      map_add' := by
        intro z w
        calc φ (a (z+w)) = φ (a z+a w) := hfiber (by rw [ha,map_add,ha,ha]; rfl)
          _ = φ (a z)+φ (a w) := map_add φ _ _
      map_smul' := by
        intro c z
        calc φ (a (c • z)) = φ (c • a z) := hfiber (by rw [ha,map_smul,ha]; rfl)
          _ = c • φ (a z) := map_smul φ _ _ }
  have hL (x : E) : L ⟨F x,LinearMap.mem_range_self F x⟩=φ x := hfiber (ha _)
  let l : LinearMap.range F →L[ℂ] ℂ := L.mkContinuous C (fun z => by
    have h := hb (a z)
    rw [ha] at h
    exact h)
  obtain ⟨g,hg,_⟩ := exists_extension_norm_eq (LinearMap.range F) l
  refine ⟨(InnerProductSpace.toDual ℂ V).symm g,?_⟩
  intro x
  rw [InnerProductSpace.toDual_symm_apply]
  exact ((hg ⟨F x,LinearMap.mem_range_self F x⟩).trans (hL x)).symm

end

/-! Pointwise ultrafilter limits of uniformly bounded complex functionals.
Compactness is used only for scalar closed balls, with no separability premise. -/
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_bounded_functional_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (f : ι → E →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    ∃ φ : E →L[ℂ] ℂ, ‖φ‖ ≤ C ∧
      ∀ x : E, Tendsto (fun i => f i x) (ω : Filter ι) (𝓝 (φ x)) := by
  have hex (x : E) : ∃ z : ℂ, ‖z‖ ≤ C*‖x‖ ∧
      Tendsto (fun i => f i x) (ω : Filter ι) (𝓝 z) := by
    obtain ⟨z,hz,ht⟩ := (isCompact_closedBall (0 : ℂ) (C*‖x‖)).ultrafilter_le_nhds
      (ω.map (fun i => f i x)) (by
        apply le_principal_iff.mpr
        change ∀ᶠ i in (ω : Filter ι), f i x ∈ Metric.closedBall 0 (C*‖x‖)
        exact Eventually.of_forall (fun i => by
          simpa only [Metric.mem_closedBall,dist_zero_right] using
            (f i).le_of_opNorm_le (hf i) x))
    exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz,ht⟩
  choose v hv ht using hex
  have hadd (x y : E) : v (x+y)=v x+v y := by
    apply tendsto_nhds_unique (ht (x+y))
    simpa only [map_add] using (ht x).add (ht y)
  have hsmul (c : ℂ) (x : E) : v (c • x)=c • v x := by
    apply tendsto_nhds_unique (ht (c • x))
    simpa only [map_smul,smul_eq_mul] using (ht x).const_mul c
  let φ : E →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨φ,φ.opNorm_le_bound hC hv,ht⟩

end Tracial

/-! A separable normed space has a countable family of bounded linear
functionals separating its points. All functionals are constructed by
Hahn--Banach at a countable dense family of vectors. -/

/-! Hermitian symmetrization and complex polarization for bounded functionals.
No tracial functional or finite factor is supplied to these algebraic lemmas. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarizationCStar : CStarAlgebra M.toStarSubalgebra := {}

def conjugateFunctional (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    M.toStarSubalgebra →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => star (φ (star x))
      map_add' := by intros; simp only [star_add,map_add]
      map_smul' := by intros; simp only [star_smul,map_smul,star_star,RingHom.id_apply] }
    ‖φ‖ (fun x => by
      change ‖star (φ (star x))‖ ≤ ‖φ‖*‖x‖
      simpa only [norm_star] using φ.le_opNorm (star x))

theorem conjugateFunctional_apply (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : conjugateFunctional φ x=star (φ (star x)) := rfl

theorem conjugateFunctional_norm_le (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    ‖conjugateFunctional φ‖ ≤ ‖φ‖ := by
  apply (conjugateFunctional φ).opNorm_le_bound (norm_nonneg φ)
  intro x
  simpa only [conjugateFunctional_apply,norm_star] using φ.le_opNorm (star x)

def hermitianFunctional (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    M.toStarSubalgebra →L[ℂ] ℂ := (1/2 : ℂ) • (φ+conjugateFunctional φ)

theorem hermitianFunctional_apply (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : hermitianFunctional φ x=(φ x+star (φ (star x)))/2 := by
  simp only [hermitianFunctional,smul_apply,add_apply,
    conjugateFunctional_apply,smul_eq_mul]
  ring

theorem hermitianFunctional_norm_le (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    ‖hermitianFunctional φ‖ ≤ ‖φ‖ := by
  change ‖(1/2 : ℂ) • (φ+conjugateFunctional φ)‖ ≤ _
  rw [norm_smul]
  have h := norm_add_le φ (conjugateFunctional φ)
  have h' := conjugateFunctional_norm_le φ
  norm_num
  linarith

theorem hermitianFunctional_star (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : hermitianFunctional φ (star x)=star (hermitianFunctional φ x) := by
  simp only [hermitianFunctional_apply,star_star,star_div₀,star_add,star_ofNat]
  rw [add_comm]

theorem hermitianFunctional_selfAdjoint (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    hermitianFunctional φ x=((φ x).re : ℂ) := by
  rw [hermitianFunctional_apply,hx.star_eq]
  exact (Complex.re_eq_add_conj _).symm

theorem hermitianFunctional_one (φ : M.toStarSubalgebra →L[ℂ] ℂ) (hφ : φ 1=1) :
    hermitianFunctional φ 1=1 := by
  rw [hermitianFunctional_selfAdjoint φ 1 (IsSelfAdjoint.one _),hφ]
  rfl

/-- Equality of complex quadratic values polarizes to the full trace identity. -/
theorem functional_trace_of_quadratic (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hφ : ∀ x : M.toStarSubalgebra, φ (star x*x)=φ (x*star x))
    (x y : M.toStarSubalgebra) : φ (x*y)=φ (y*x) := by
  have hp := hφ (x+star y)
  have hi := hφ (x+Complex.I • star y)
  simp only [star_add,star_star,add_mul,mul_add,map_add] at hp
  simp only [star_add,star_smul,star_star,add_mul,mul_add,smul_mul_assoc,
    mul_smul_comm,map_add,map_smul,smul_eq_mul] at hi
  rw [hφ x,← hφ y] at hp hi
  simp only [show star Complex.I = -Complex.I from Complex.conj_I] at hi
  linear_combination (norm := ring_nf) -(1/2 : ℂ)*hp - (Complex.I/2)*hi
  simp only [Complex.I_sq]
  ring

theorem hermitianFunctional_trace (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hφ : ∀ x : M.toStarSubalgebra, (φ (star x*x)).re=(φ (x*star x)).re)
    (x y : M.toStarSubalgebra) : hermitianFunctional φ (x*y)=hermitianFunctional φ (y*x) := by
  apply functional_trace_of_quadratic
  intro z
  rw [hermitianFunctional_selfAdjoint φ _ (IsSelfAdjoint.star_mul_self z),
    hermitianFunctional_selfAdjoint φ _ (IsSelfAdjoint.mul_star_self z),hφ z]

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- Every countable family in a directed preorder has an increasing majorant
above a specified index. This is not countable cofinality of the preorder. -/
theorem exists_monotone_dominating_from
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] (f : ℕ → I) (i : I) :
    ∃ a : ℕ → I, Monotone a ∧ (∀ n, f n ≤ a n) ∧ (∀ n, i ≤ a n) := by
  classical
  let upper (x y : I) := (exists_ge_ge x y).choose
  have hl (x y : I) : x ≤ upper x y := (exists_ge_ge x y).choose_spec.1
  have hr (x y : I) : y ≤ upper x y := (exists_ge_ge x y).choose_spec.2
  let a : ℕ → I := Nat.rec (upper i (f 0)) (fun n j => upper j (f (n+1)))
  have ha : Monotone a := monotone_nat_of_le_succ (fun n => hl (a n) (f (n+1)))
  refine ⟨a,ha,?_,fun n => (hl i (f 0)).trans (ha (Nat.zero_le n))⟩
  intro n
  cases n with
  | zero => exact hr i (f 0)
  | succ n => exact hr (a n) (f (n+1))

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralValueCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralValueOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralValuePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralValueLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralValueStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem child_endpoints (hI : I.lo ≤ I.hi) (b : Bool) :
    I.lo ≤ (I.child hx b).lo ∧ (I.child hx b).lo ≤ (I.child hx b).hi ∧
      (I.child hx b).hi ≤ I.hi := by
  cases b <;> dsimp [child,low,high,midpoint]
  · exact ⟨le_rfl,by linarith,by linarith⟩
  · exact ⟨by linarith,by linarith,le_rfl⟩

theorem level_endpoints (hI : I.lo ≤ I.hi) : ∀ n i,
    I.lo ≤ (I.level hx n i).lo ∧ (I.level hx n i).lo ≤ (I.level hx n i).hi ∧
      (I.level hx n i).hi ≤ I.hi
  | 0,_ => ⟨le_rfl,hI,le_rfl⟩
  | n+1,i => by
    have h := level_endpoints hI n i.1
    have hchild := (I.level hx n i.1).child_endpoints hx h.2.1 i.2
    exact ⟨h.1.trans hchild.1,hchild.2.1,hchild.2.2.trans h.2.2⟩

end SpectralInterval

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralFaithfulCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralFaithfulOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralFaithfulPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralFaithfulLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralFaithfulStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem positive_spectral_cut_ne_zero
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) (ht : 0 ≤ t) (htx : t < ‖x‖) :
    (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t).val ≠ 0 := by
  intro hz
  have h := cornerSpectralCut_upper ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint t
  dsimp only at h
  rw [hz,sub_zero,one_mul,mul_one] at h
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_nonpos.mp h) hx
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg ht] at hn
  have hone := (IsStarProjection.one M.toStarSubalgebra).norm_le
  have hb : ‖x‖ ≤ t := hn.trans (by nlinarith)
  exact (not_lt_of_ge hb) htx

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralSquareCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralSquareOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralSquareStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerValueCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerValueOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerValuePreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerValueLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerValueStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

/-- The actual bounded complex-linear vector functional on the original algebra. -/
def vectorFunctional (ξ : H) : M.toStarSubalgebra →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => inner ℂ ξ (x.val ξ)
      map_add' := fun x y => inner_add_right _ _ _
      map_smul' := fun c x => inner_smul_right _ _ _ }
    (‖ξ‖^2) (fun x => by
      calc ‖inner ℂ ξ (x.val ξ)‖ ≤ ‖ξ‖*‖x.val ξ‖ := norm_inner_le_norm _ _
           _ ≤ ‖ξ‖*(‖x.val‖*‖ξ‖) := mul_le_mul_of_nonneg_left (x.val.le_opNorm ξ) (norm_nonneg _)
           _ = ‖ξ‖^2*‖x‖ := by change ‖ξ‖*(‖x‖*‖ξ‖)=_; ring)

theorem vectorFunctional_apply (ξ : H) (x : M.toStarSubalgebra) :
    vectorFunctional ξ x=inner ℂ ξ (x.val ξ) := rfl

theorem vectorFunctional_norm_le (ξ : H) : ‖vectorFunctional (M := M) ξ‖ ≤ ‖ξ‖^2 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance localizedCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance localizedOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance localizedPreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance localizedLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance localizedStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerStateOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerStatePreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerStateStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem exists_unit_vector_of_unit_ne_zero (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ ξ : H, ‖ξ‖=1 := by
  classical
  have hne : ∃ ξ : H, ξ≠0 := by
    by_contra h
    push Not at h
    apply hunit
    apply Subtype.ext
    ext ξ
    exact h ξ
  obtain ⟨ξ,hξ⟩ := hne
  refine ⟨(‖ξ‖⁻¹ : ℂ) • ξ,?_⟩
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg ξ),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]

theorem vectorFunctional_star_mul_self (ξ : H) (x : M.toStarSubalgebra) :
    vectorFunctional ξ (star x*x)=(‖x.val ξ‖^2 : ℂ) := by
  change inner ℂ ξ (star x.val (x.val ξ))=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem vectorFunctional_positive (ξ : H) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ (vectorFunctional ξ x).re := by
  let b := CFC.sqrt x
  have hb : star b=b := (CFC.sqrt_nonneg x).isSelfAdjoint.star_eq
  have he : star b*b=x := by rw [hb]; exact CFC.sqrt_mul_sqrt_self x hx
  rw [← he,vectorFunctional_star_mul_self]
  norm_cast
  positivity

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance approxTraceCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance approxTraceOrder_r85ce55_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approxTracePreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance approxTraceLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance quadraticStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance quadraticStateOrder_r85ce55_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance quadraticStatePreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance quadraticStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance tracialStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance tracialStateOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracialStatePreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance tracialStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance tracialStateStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance stateDimensionCStar_r85ce55_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance stateDimensionOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance stateDimensionPreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance stateDimensionLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance stateDimensionStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralAdditivityCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracePreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance traceStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance dominationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance dominationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance dominationPreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance dominationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance dominationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceNormalCStar_r85ce55_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance traceNormalOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceNormalPreorder_r85ce55_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceNormalLE_r85ce55_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance traceNormalStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance clippingCStar : CStarAlgebra M.toStarSubalgebra := {}

local instance clippingOrder_r85ce55_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance clippingStarOrder_r85ce55_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
def traceSymmetrize (a : M.toStarSubalgebra) : M.toStarSubalgebra :=
  (2 : ℂ)⁻¹ • (a+star a)

theorem traceSymmetrize_selfAdjoint (a : M.toStarSubalgebra) : IsSelfAdjoint (traceSymmetrize a) := by
  change star ((2 : ℂ)⁻¹ • (a+star a)) = (2 : ℂ)⁻¹ • (a+star a)
  simp [add_comm]

theorem traceSymmetrize_eq_self (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) :
    traceSymmetrize a = a := by
  simp only [traceSymmetrize,ha.star_eq,← two_smul ℂ a,smul_smul]
  norm_num

theorem traceSymmetrize_sub (a b : M.toStarSubalgebra) :
    traceSymmetrize (a-b) = traceSymmetrize a-traceSymmetrize b := by
  simp only [traceSymmetrize,star_sub,smul_add,smul_sub]
  abel

theorem traceSymmetrize_norm₂_le (τ : TracialRepresentation M) (a : M.toStarSubalgebra) :
    τ.norm₂ (traceSymmetrize a) ≤ τ.norm₂ a := by
  rw [traceSymmetrize,τ.norm₂_smul,norm_inv]
  norm_num only [Complex.norm_ofNat]
  have h := τ.norm₂_add_le a (star a)
  rw [τ.norm₂_star] at h
  linarith

def traceClip (a : M.toStarSubalgebra) (C : ℝ) : M.toStarSubalgebra :=
  -upperTruncate (-upperTruncate a C) C

theorem traceClip_selfAdjoint (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    IsSelfAdjoint (traceClip a C) :=
  (upperTruncate_selfAdjoint _ (upperTruncate_selfAdjoint a ha C).neg C).neg

theorem traceClip_cfc (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    traceClip a C = cfc (fun t : ℝ => -min (-min t C) C) a := by
  rw [traceClip,upperTruncate_cfc _ (upperTruncate_selfAdjoint a ha C).neg C,
    upperTruncate_cfc a ha C,← cfc_neg (fun t : ℝ => min t C) a,
    ← cfc_comp (fun t : ℝ => min t C) (fun t : ℝ => -min t C) a]
  simp only [Function.comp_def]
  rw [cfc_neg (fun t : ℝ => min (-min t C) C) a]

theorem traceClip_norm_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C : ℝ) (hC : 0 ≤ C) : ‖traceClip a C‖ ≤ C := by
  rw [traceClip_cfc a ha C]
  apply norm_cfc_le hC
  intro t _
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · exact neg_le_neg (min_le_right _ _)
  · have h : -C ≤ min (-min t C) C :=
      le_min (neg_le_neg (min_le_right _ _)) (by linarith)
    linarith

theorem traceClip_distance (τ : TracialRepresentation M) (a x : M.toStarSubalgebra)
    (ha : IsSelfAdjoint a) (hx : IsSelfAdjoint x) :
    τ.norm₂ (traceClip a ‖x‖-x) ≤ τ.norm₂ (a-x) := by
  have h₁ := upperTruncate_distance τ a x ha hx
  have h₂ := upperTruncate_distance τ (-upperTruncate a ‖x‖) (-x)
    (upperTruncate_selfAdjoint a ha ‖x‖).neg hx.neg
  rw [norm_neg] at h₂
  have hn (b : M.toStarSubalgebra) : τ.norm₂ (-b) = τ.norm₂ b := norm_neg _
  have he : traceClip a ‖x‖-x = -(upperTruncate (-upperTruncate a ‖x‖) ‖x‖-(-x)) := by
    dsimp [traceClip]; abel
  have he' : -upperTruncate a ‖x‖-(-x) = -(upperTruncate a ‖x‖-x) := by abel
  rw [he',hn] at h₂
  rw [he,hn]
  have hnonneg : 0 ≤ τ.norm₂ (a-x) := norm_nonneg _
  nlinarith [sq_nonneg (τ.norm₂ ((a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)),
    sq_nonneg (τ.norm₂ ((-upperTruncate a ‖x‖-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺))]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Algebraic type copy indexed by the original factor hypotheses. -/
def TraceFreePreHilbert
(_hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
(_hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
(_hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
(_hunit : (1 : M.toStarSubalgebra) ≠ 0)
    : Type _ := M.toStarSubalgebra

local instance traceHilbertCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit

instance traceFreePreHilbertRing : Ring E := inferInstanceAs (Ring M.toStarSubalgebra)
instance traceFreePreHilbertAlgebra : Algebra ℂ E :=
  inferInstanceAs (Algebra ℂ M.toStarSubalgebra)
instance traceFreePreHilbertStarRing : StarRing E :=
  inferInstanceAs (StarRing M.toStarSubalgebra)
instance traceFreePreHilbertStarModule : StarModule ℂ E :=
  inferInstanceAs (StarModule ℂ M.toStarSubalgebra)

/-- Algebraic identification only: it does not identify the two norms. -/
def traceFreeCopy : M.toStarSubalgebra ≃⋆ₐ[ℂ] E :=
  _root_.StarAlgEquiv.refl ℂ M.toStarSubalgebra

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BaireSelectionHulls
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable hulls of finite-prefix images

For a continuous Baire-space parametrization, measurable hulls permit
successive prefix choices outside one null set. This is the measure-specific
selection construction needed for the published unitary selector.
-/

namespace KadisonKastler

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

def bairePrefixCylinder (s : List ℕ) : Set (ℕ → ℕ) :=
  {a | PiNat.res a s.length = s}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioParameters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two fixed product-state parameters

The manuscript uses `exp (-1)` and `exp (-sqrt 2)`. Their logarithms
generate an incommensurable pair of modular frequencies. No parameter
depends on an algebra, representation, or requested perturbation bound.
-/

namespace KadisonKastler

noncomputable section

def fixedProductMu : ℝ := Real.exp (-Real.sqrt 2)

end

end KadisonKastler

end OAI
end


