-- Prove2me | Definitions.Def_Q260K000
-- name    : Q260K000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:34:38.525627+00:00
-- url     : https://prove2.me/theorems/746125fe-2d88-4571-a890-c99a6e2c1bf1
-- title:
--   Definitions bundle Q260K000 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 168 declarations of OpenAI's Lean: 39 definitions, 3 inductive types or structures, 24 instances and 102 theorems. The definitions and types are `OAI.CuntzPureness.ClosedStarIdeal`, `OAI.CuntzPureness.ClosedStarIdeal.Quotient`, `OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebra`, `OAI.CuntzPureness.ClosedStarIdeal.idealSubmodule`, `OAI.CuntzPureness.ClosedStarIdeal.instLESubtypeMemNonUnitalStarSubalgebraComplexIdealStarAlgebra`, `OAI.CuntzPureness.ClosedStarIdeal.quotientLinearEquiv`, `OAI.CuntzPureness.ClosedStarIdeal.quotientMap`, `OAI.CuntzPureness.ClosedStarIdeal.quotientNormEquiv`, `OAI.CuntzPureness.ClosedStarIdeal.quotientStarHom`, `OAI.CurrentMain.ProjectionPartition`, `OAI.CurrentMain.selfAdjointEmbedding`, `OAI.CurrentMain.selfAdjointFunctionalComplex`, `OAI.CurrentMain.stateRealContinuous`, `OAI.CurrentMain.stateRealLinear`, `OAI.Generator.MatrixUnitSystem.adaptedBasis`, `OAI.Generator.MatrixUnitSystem.adaptedVector`, `OAI.Generator.MatrixUnitSystem.coefficientEval`, `OAI.Generator.MatrixUnitSystem.coefficientHom`, `OAI.Generator.MatrixUnitSystem.initialColumn`, `OAI.Generator.MatrixUnitSystem.initialCoordinate`, `OAI.Generator.MatrixUnitSystem.initialHilbertSpace`, `OAI.Generator.MatrixUnitSystem.isometricCommutantEquiv`, `OAI.Generator.Tracial.AlgebraProjection.Equivalent`, `OAI.Generator.Tracial.AlgebraProjection.Subequivalent`, `OAI.Generator.Tracial.AlgebraProjection.finsetSum`, `OAI.Generator.Tracial.AlgebraProjection.remainder`, `OAI.Generator.Tracial.AlgebraProjection.unitaryConjugate`, `OAI.Generator.Tracial.AlgebraProjection.vectorValue`, `OAI.Generator.Tracial.CornerPartition.single`, `OAI.Generator.Tracial.EquivalentPartition`, `OAI.Generator.Tracial.EquivalentPartition.ofHalving`, `OAI.Generator.Tracial.EquivalentPartition.refine`, `OAI.Generator.Tracial.EquivalentPartition.singleton`, `OAI.Generator.Tracial.EquivalentPartition.subset`, `OAI.Generator.Tracial.PartialIsometry.compose`, `OAI.Generator.Tracial.PartialIsometry.onProjection`, `OAI.Generator.Tracial.centralSupport`, `OAI.Generator.Tracial.dyadicWeight`, `OAI.Generator.Tracial.orthogonalSum`, `OAI.Generator.Tracial.projectionOrbitClosure` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Dimension`, `FactorGeneration_DyadicComparison`, `FactorGeneration_FiniteComparison`, `FactorGeneration_LocalizedStates`, `FactorGeneration_MatrixUnits`, `FactorGeneration_NormalDimension`, `FactorGeneration_PartialIsometries`, `FactorGeneration_Pinching`, `FactorGeneration_SpectralStates`, `KadisonKastler_BilateralRandomWalk`, `KadisonKastler_FiniteMatrixUnitBasis`, `KadisonKastler_RelativeMatrixFactorEquiv`, `Pureness_Completion_ClosedStarIdealQuotientCStar`, `Pureness_Completion_ClosedStarIdealQuotientNorm`, `TracialSplitting_ChallengeDefinitions`, `TracialSplitting_Model`, `TracialSplitting_ScalarCompression`, `TracialSplitting_StateExtension`.
--
--   **Imports.** It imports the bundle `OAIQ075A026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K010`, `Q260K011`, `Q260K013`, `Q260K015` and `Q260K053`; the proofs of `OAI.KadisonKastler.tomiyama_corner_supported` and `OAI.KadisonSimilarity.concreteDihedralSpectralArcInput`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_OAIQ075A026

section
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
/-- d13f23b's `IsSelfAdjoint.norm_le_max_of_le_of_le`: a selfadjoint element squeezed between `a` and `b`
has norm at most `max ‖a‖ ‖b‖` (Kadison similarity, oaiq-075). -/
theorem _root_.IsSelfAdjoint.norm_le_max_of_le_of_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b x : A} (hlo : a ≤ x) (hhi : x ≤ b) (hx : IsSelfAdjoint x) :
    ‖x‖ ≤ max ‖a‖ ‖b‖ := by
  by_cases! nontriv : Nontrivial A
  swap
  · have : x = 0 := Subsingleton.elim _ _
    simp [this]
  have hb : IsSelfAdjoint b := by
    have h1 : IsSelfAdjoint (b - x) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hhi)
    simpa using h1.add hx
  have ha : IsSelfAdjoint a := by
    have h1 : IsSelfAdjoint (x - a) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hlo)
    simpa using hx.sub h1
  have hbx : x ≤ algebraMap ℝ A ‖b‖ := hhi.trans hb.le_algebraMap_norm_self
  have hax : -(algebraMap ℝ A ‖a‖) ≤ x := ha.neg_algebraMap_norm_le_self.trans hlo
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hx with h | h
  · exact ((le_algebraMap_iff_spectrum_le hx).mp hbx _ h).trans (le_max_right _ _)
  · have hax' : algebraMap ℝ A (-‖a‖) ≤ x := by simpa using hax
    have := (algebraMap_le_cfc_iff (R := ℝ) id (-‖a‖) x).mp (by rwa [cfc_id ℝ x hx]) _ h
    simp only [id] at this
    exact (by linarith : ‖x‖ ≤ ‖a‖).trans (le_max_left _ _)
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_PartialIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual partial isometries, allowing distinct initial and final projections,
with the extension order and its exact trace distance. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

theorem support_mono {v w : PartialIsometry M} (h : v ≤ w) : v.support ≤ w.support :=
  support_le_of_extends h

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Orthogonal patching with distinct source and target supports. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem patch_target (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    (patch v w hp hq).target.val=v.target.val+w.target.val := by
  have hwt : w.adjoint.target=w.support := Subtype.ext (by
    change star w.val*star (star w.val)=w.support.val
    rw [star_star,w.initial])
  have hvt : v.adjoint.target=v.support := Subtype.ext (by
    change star v.val*star (star v.val)=v.support.val
    rw [star_star,v.initial])
  have h₁ : v.val*star w.val=0 := v.mul_eq_zero w.adjoint (by rw [hwt]; exact hp)
  have h₂ : w.val*star v.val=0 := w.mul_eq_zero v.adjoint (by
    rw [hvt]; exact orthogonal_reverse _ _ hp)
  change (v.val+w.val)*star (v.val+w.val)=v.val*star v.val+w.val*star w.val
  simp only [star_add,add_mul,mul_add,h₁,h₂,add_zero,zero_add]

end PartialIsometry

end

/-! A maximal actual partial isometry between subprojections of prescribed
projections. Chain upper bounds are constructed L2 limits, not assumed. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def projectionOrbitVectors (p : AlgebraProjection M) : Set H :=
  {y | ∃ a : M.toStarSubalgebra, ∃ x : H, y=a.val (p.val.val x)}

def projectionOrbitClosure (p : AlgebraProjection M) : Submodule ℂ H :=
  (Submodule.span ℂ (projectionOrbitVectors p)).topologicalClosure

instance projectionOrbitClosure_complete (p : AlgebraProjection M) :
    CompleteSpace (projectionOrbitClosure p) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (projectionOrbitVectors p)).topologicalClosure)

theorem projectionOrbitClosure_invariant_of_vectors (p : AlgebraProjection M)
    (T : H →L[ℂ] H)
    (hT : ∀ y ∈ projectionOrbitVectors p, T y ∈ projectionOrbitVectors p) :
    ∀ y ∈ projectionOrbitClosure p, T y ∈ projectionOrbitClosure p := by
  have h : projectionOrbitClosure p ≤ (projectionOrbitClosure p).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro y hy
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (hT y hy))
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact fun y hy => h hy

theorem projectionOrbitClosure_invariant (p : AlgebraProjection M) (a : M.toStarSubalgebra) :
    ∀ y ∈ projectionOrbitClosure p, a.val y ∈ projectionOrbitClosure p := by
  apply projectionOrbitClosure_invariant_of_vectors
  rintro y ⟨b,x,rfl⟩
  exact ⟨a*b,x,rfl⟩

theorem projectionOrbitClosure_commutant_invariant (p : AlgebraProjection M)
    (T : H →L[ℂ] H) (hT : T ∈ M.commutant) :
    ∀ y ∈ projectionOrbitClosure p, T y ∈ projectionOrbitClosure p := by
  apply projectionOrbitClosure_invariant_of_vectors
  rintro y ⟨a,x,rfl⟩
  refine ⟨a,T x,?_⟩
  have ha := VonNeumannAlgebra.mem_commutant_iff.mp hT a.val a.property
  have hp := VonNeumannAlgebra.mem_commutant_iff.mp hT p.val.val p.val.property
  have hea := congrArg (fun R : H →L[ℂ] H => R (p.val.val x)) ha
  have hep := congrArg (fun R : H →L[ℂ] H => R x) hp
  change a.val (T (p.val.val x))=T (a.val (p.val.val x)) at hea
  change p.val.val (T x)=T (p.val.val x) at hep
  exact hea.symm.trans (congrArg a.val hep.symm)

theorem projectionOrbitProjection_mem (p : AlgebraProjection M) :
    (projectionOrbitClosure p).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro T hT
  rw [Submodule.range_starProjection]
  exact projectionOrbitClosure_commutant_invariant p T hT

def centralSupport (p : AlgebraProjection M) : AlgebraProjection M :=
  ⟨⟨(projectionOrbitClosure p).starProjection, projectionOrbitProjection_mem p⟩, by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := projectionOrbitClosure p)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := projectionOrbitClosure p)).isSelfAdjoint.star_eq⟩

theorem centralSupport_commutes (p : AlgebraProjection M) (a : M.toStarSubalgebra) :
    a*(centralSupport p).val=(centralSupport p).val*a := by
  apply Subtype.ext
  exact (Generator.starProjection_commutes_of_invariant (projectionOrbitClosure p) a.val
    (projectionOrbitClosure_invariant p a)
    (projectionOrbitClosure_invariant p (star a))).symm

theorem le_centralSupport (p : AlgebraProjection M) : p ≤ centralSupport p := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨1,x,rfl⟩

theorem mul_centralSupport_eq_zero_of_no_links (p q : AlgebraProjection M)
    (hlink : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0) :
    q.val*(centralSupport p).val=0 := by
  have hK : projectionOrbitClosure p ≤ q.val.val.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro y ⟨a,x,rfl⟩
      exact congrArg (fun R : M.toStarSubalgebra => R.val x) (hlink a)
    · exact q.val.val.isClosed_ker
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact hK ((projectionOrbitClosure p).starProjection_apply_mem x)

/-- Scalar center forces every nonzero projection to have full central support. -/
theorem centralSupport_eq_one_of_factor
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p : AlgebraProjection M) (hp : p.val≠0) : (centralSupport p).val=1 := by
  obtain ⟨z,hz⟩ := hfactor (centralSupport p).val (centralSupport_commutes p)
  have he := le_centralSupport p
  change (centralSupport p).val*p.val=p.val at he
  rw [hz,smul_mul_assoc,one_mul] at he
  have hz1 : z=1 := (smul_left_injective ℂ hp) (he.trans (one_smul ℂ p.val).symm)
  rw [hz,hz1,one_smul]

theorem traceFree_projection_eq_zero_or_eq_zero_of_no_links
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) (hlink : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0) :
    p.val=0 ∨ q.val=0 := by
  by_cases hp : p.val=0
  · exact Or.inl hp
  · right
    have h := mul_centralSupport_eq_zero_of_no_links p q hlink
    rwa [centralSupport_eq_one_of_factor hfactor p hp,mul_one] at h

end

/-! Trace-free upper bounds of arbitrary directed nets of partial isometries.
A weak operator ultralimit suffices: extension identities with each fixed net
member force the limit to satisfy b b* b = b. No trace or countability is used. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Left multiplication by a fixed operator preserves matrix-coefficient limits. -/
theorem wot_limit_mul_left {ι : Type*} {l : Filter ι}
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) :
    ∀ x y : H, Tendsto (fun i => inner ℂ y ((c*a i).val x)) l
      (𝓝 (inner ℂ y ((c*b).val x))) := by
  intro x y
  change Tendsto (fun i => inner ℂ y (c.val ((a i).val x))) l
    (𝓝 (inner ℂ y (c.val (b.val x))))
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    using ht x (star c.val y)

/-- Right multiplication by a fixed operator preserves matrix-coefficient limits. -/
theorem wot_limit_mul_right {ι : Type*} {l : Filter ι}
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) :
    ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i*c).val x)) l
      (𝓝 (inner ℂ y ((b*c).val x))) := fun x y => ht (c.val x) y

/-- Matrix coefficients determine an element of the concrete algebra. -/
theorem wot_limit_unique {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x))))
    (hc : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (c.val x)))) : b=c := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact ext_inner_left ℂ (fun y => tendsto_nhds_unique (hb x y) (hc x y))

namespace PartialIsometry

/-- Every monotone directed net has a partial-isometry upper bound, retaining
any prescribed bounds on its initial and final projections. -/
theorem traceFree_monotone_upper_bound
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a)
    (p q : AlgebraProjection M) (hp : ∀ i, (a i).support ≤ p)
    (hq : ∀ i, (a i).target ≤ q) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧ v.support ≤ p ∧ v.target ≤ q := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  refine ⟨v, hbp, ?_, ?_⟩
  · apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · apply (v.target_le_iff_mul q).mpr
    apply wot_limit_unique (fun i => q.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul q).mp (hq i)] using hb

end PartialIsometry
end

/-! Trace-free chain upper bounds and maximal partial isometries, with prescribed
initial and final projection bounds. The index set may be uncountable. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem traceFree_chain_upper_bound (c : Set (PartialIsometry M))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p q : AlgebraProjection M) (hp : ∀ v ∈ c, v.support ≤ p)
    (hq : ∀ v ∈ c, v.target ≤ q) :
    ∃ v : PartialIsometry M, (∀ w ∈ c, w ≤ v) ∧ v.support ≤ p ∧ v.target ≤ q := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v, h, le_rfl⟩
    · exact ⟨u, le_rfl, h⟩⟩
  obtain ⟨v, hv, hvp, hvq⟩ := traceFree_monotone_upper_bound
    (fun w : c => w.val) (fun _ _ h => h) p q
    (fun w => hp w.val w.property) (fun w => hq w.val w.property)
  exact ⟨v, fun w hw => hv ⟨w,hw⟩, hvp, hvq⟩

theorem traceFree_exists_maximal_between (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ q → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) := {v | v.support ≤ p ∧ v.target ≤ q}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨v, hcv, hvp, hvq⟩ := traceFree_chain_upper_bound c hchain hne p q
        (fun w hw => (hc hw).1) (fun w hw => (hc hw).2)
      exact ⟨v, ⟨hvp, hvq⟩, hcv⟩
    · refine ⟨zero, ⟨?_, ?_⟩, ?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul q).mpr
        exact mul_zero _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2,fun w hp hq h => hv.2 ⟨hp,hq⟩ h⟩

end PartialIsometry
end

/-! Projection comparison from scalar center, without a supplied trace.
The maximal partial isometry, central support and polar linking are constructed. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfactor in
theorem traceFree_exists_nonzero_partialIsometry_between_projections
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val≠0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val≠0 := by
  have hex : ∃ a : M.toStarSubalgebra, q.val*a*p.val≠0 := by
    by_contra hn
    have hz : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0 := by
      simpa only [not_exists,not_not] using hn
    exact (traceFree_projection_eq_zero_or_eq_zero_of_no_links hfactor p q hz).elim hp hq
  obtain ⟨a,ha⟩ := hex
  apply exists_partialIsometry_of_link p q (q.val*a*p.val)
  · rw [mul_assoc,p.property.isIdempotentElem.eq]
  · rw [← mul_assoc,← mul_assoc,q.property.isIdempotentElem.eq]
  · exact ha

include hfactor in
theorem traceFree_exists_partialIsometry_comparison (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      (v.support=p ∨ v.target=q) := by
  obtain ⟨v,hvp,hvq,hmax⟩ := PartialIsometry.traceFree_exists_maximal_between p q
  let r : AlgebraProjection M :=
    ⟨p.val-v.support.val,v.support.property.sub_of_mul_eq_right p.property hvp⟩
  let s : AlgebraProjection M :=
    ⟨q.val-v.target.val,v.target.property.sub_of_mul_eq_right q.property hvq⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-v.support.val)=p.val-v.support.val
    rw [mul_sub,p.property.isIdempotentElem.eq,hvp]
  have hsq : s ≤ q := by
    change q.val*(q.val-v.target.val)=q.val-v.target.val
    rw [mul_sub,q.property.isIdempotentElem.eq,hvq]
  have hzero : r.val=0 ∨ s.val=0 := by
    by_contra hn
    have hr : r.val≠0 := fun h => hn (Or.inl h)
    have hs : s.val≠0 := fun h => hn (Or.inr h)
    obtain ⟨w,hwr,hws,hw0⟩ :=
      traceFree_exists_nonzero_partialIsometry_between_projections hfactor r s hr hs
    have hpw : v.support.val*w.support.val=0 := by
      calc _ = v.support.val*(r.val*w.support.val) := by rw [hwr]
           _ = (v.support.val*r.val)*w.support.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.support.val*(p.val-v.support.val))*w.support.val=0
             rw [mul_sub,projection_mul_of_le hvp,v.support.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    have hqw : v.target.val*w.target.val=0 := by
      calc _ = v.target.val*(s.val*w.target.val) := by rw [hws]
           _ = (v.target.val*s.val)*w.target.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.target.val*(q.val-v.target.val))*w.target.val=0
             rw [mul_sub,projection_mul_of_le hvq,v.target.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    let u := PartialIsometry.patch v w hpw hqw
    have hup : u.support ≤ p := by
      change p.val*(v.support.val+w.support.val)=v.support.val+w.support.val
      rw [mul_add,hvp,show p.val*w.support.val=w.support.val from hwr.trans hrp]
    have huq : u.target ≤ q := by
      apply (u.target_le_iff_mul q).mpr
      change q.val*(v.val+w.val)=v.val+w.val
      rw [mul_add,(v.target_le_iff_mul q).mp hvq,
        (w.target_le_iff_mul q).mp (hws.trans hsq)]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq hvu) hvu)
  refine ⟨v,hvp,hvq,?_⟩
  rcases hzero with hr | hs
  · exact Or.inl (Subtype.ext (sub_eq_zero.mp hr).symm)
  · exact Or.inr (Subtype.ext (sub_eq_zero.mp hs).symm)

end Tracial

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- The identity partial isometry on a projection. -/
def onProjection (p : AlgebraProjection M) : PartialIsometry M :=
  ⟨p, p.val, by rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]⟩

theorem onProjection_target (p : AlgebraProjection M) : (onProjection p).target=p := by
  apply Subtype.ext
  change p.val*star p.val=p.val
  rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]

/-- A finite algebra has no partial isometry from a projection onto a proper
subprojection of itself. Finiteness is used on v + (1 - p). -/
theorem target_eq_support_of_finite
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (v : PartialIsometry M) (hv : v.target ≤ v.support) : v.target=v.support := by
  let r : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let w := onProjection r
  have hp : v.support.val*w.support.val=0 := by
    change v.support.val*(1-v.support.val)=0
    rw [mul_sub,mul_one,v.support.property.isIdempotentElem.eq,sub_self]
  have hq : v.target.val*w.target.val=0 := by
    rw [show w.target=r from onProjection_target r]
    change v.target.val*(1-v.support.val)=0
    rw [mul_sub,mul_one,projection_mul_of_le hv,sub_self]
  let u := patch v w hp hq
  have hu : star u.val*u.val=1 := by
    rw [u.initial]
    change v.support.val+(1-v.support.val)=1
    abel
  have huf := hfinite u.val hu
  change u.target.val=1 at huf
  rw [patch_target,show w.target=r from onProjection_target r] at huf
  apply Subtype.ext
  change v.target.val+(1-v.support.val)=1 at huf
  have he : v.target.val+(1-v.support.val)=v.support.val+(1-v.support.val) := by
    rw [huf]
    abel
  exact add_right_cancel he

/-- Finiteness also excludes a proper enlargement equivalent to a projection. -/
theorem target_eq_support_of_finite_of_le
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (v : PartialIsometry M) (hv : v.support ≤ v.target) : v.target=v.support := by
  have he : v.adjoint.target=v.support := by
    apply Subtype.ext
    change star v.val*star (star v.val)=v.support.val
    rw [star_star,v.initial]
  have h := target_eq_support_of_finite hfinite v.adjoint (by
    change v.adjoint.target ≤ v.target
    rw [he]
    exact hv)
  change v.adjoint.target=v.target at h
  rw [he] at h
  exact h.symm

end PartialIsometry
end Tracial

end

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/
namespace Tracial
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Orthogonality passes to subprojections in both variables. -/
theorem projection_orthogonal_of_le {p q r s : AlgebraProjection M}
    (h : p.val*q.val=0) (hr : r ≤ p) (hs : s ≤ q) : r.val*s.val=0 := by
  calc _ = (r.val*p.val)*(q.val*s.val) := by rw [projection_mul_of_le hr,hs]
       _ = r.val*(p.val*q.val)*s.val := by simp only [mul_assoc]
       _ = 0 := by rw [h,mul_zero,zero_mul]

namespace PartialIsometry

theorem target_mono {v w : PartialIsometry M} (h : v ≤ w) : v.target ≤ w.target := by
  apply (v.target_le_iff_mul w.target).mpr
  calc _ = w.target.val*(w.val*v.support.val) := by rw [h]
       _ = v.val := by rw [← mul_assoc,w.target_mul,h]

/-- A directed increasing family of square-zero partial isometries has an
upper bound with orthogonal initial/final projections inside p. -/
theorem traceFree_orthogonal_monotone_upper_bound
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : ∀ i, (a i).support ≤ p)
    (hq : ∀ i, (a i).target ≤ p)
    (ho : ∀ i, (a i).support.val*(a i).target.val=0) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧ v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  have hcross (i j : ι) : (a i).val*(a j).val=0 := by
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    exact (a i).mul_eq_zero (a j)
      (projection_orthogonal_of_le (ho k) (support_mono (ha hik)) (target_mono (ha hjk)))
  have hbi (i : ι) : b*(a i).val=0 := by
    apply wot_limit_unique (fun j => (a j).val*(a i).val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [hcross] using (fun x y : H =>
      (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y ((0 : M.toStarSubalgebra).val x))
        (ω : Filter ι) (𝓝 (inner ℂ y ((0 : M.toStarSubalgebra).val x)))))
  have hbb : b*b=0 := by
    apply wot_limit_unique (fun i => b*(a i).val) _ _ (wot_limit_mul_left _ _ _ hb)
    simpa only [hbi] using (fun x y : H =>
      (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y ((0 : M.toStarSubalgebra).val x))
        (ω : Filter ι) (𝓝 (inner ℂ y ((0 : M.toStarSubalgebra).val x)))))
  refine ⟨v, hbp, ?_, ?_, ?_⟩
  · apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · apply (v.target_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => p.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul p).mp (hq i)] using hb
  · change (star b*b)*(b*star b)=0
    calc _ = star b*(b*b)*star b := by simp only [mul_assoc]
         _ = 0 := by rw [hbb,mul_zero,zero_mul]

/-! Simultaneous least initial and final support bounds for arbitrary directed
partial-isometry nets. The actual ultralimit is chosen once for all bounds. -/

/-- The initial and final projections of this upper bound are the respective
least upper bounds of the net's initial and final projections. -/
theorem traceFree_monotone_least_supports
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧
      (∀ p : AlgebraProjection M, (∀ i, (a i).support ≤ p) → v.support ≤ p) ∧
      (∀ q : AlgebraProjection M, (∀ i, (a i).target ≤ q) → v.target ≤ q) := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  refine ⟨v, hbp, ?_, ?_⟩
  · intro p hp
    apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · intro q hq
    apply (v.target_le_iff_mul q).mpr
    apply wot_limit_unique (fun i => q.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul q).mp (hq i)] using hb

end PartialIsometry
end Tracial

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

variable [StarModule ℂ A]

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

theorem product_algebra_eq_sup : (E.product F hc).algebra = E.algebra ⊔ F.algebra := by
  apply le_antisymm
  · apply ((E.product F hc).algebra_le_iff _).mpr
    intro a b
    exact (E.algebra ⊔ F.algebra).mul_mem ((show E.algebra ≤ E.algebra ⊔ F.algebra from le_sup_left) (E.entry_mem a.1 b.1))
      ((show F.algebra ≤ E.algebra ⊔ F.algebra from le_sup_right) (F.entry_mem a.2 b.2))
  · exact sup_le (E.algebra_le_product_left F hc) (E.algebra_le_product_right F hc)

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

open scoped BigOperators
variable {ι κ A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B]
variable (E : MatrixUnitSystem ι A)

theorem map_entry (f : A →⋆ₐ[ℂ] B) (i j : ι) : (E.map f).entry i j=f (E.entry i j) := rfl

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def coefficientEval (a : Matrix ι ι E.commutant) : A :=
  ∑ i,∑ j,E.commutant.subtype (a i j)*E.entry i j

theorem coefficientEval_mul (a b : Matrix ι ι E.commutant) :
    E.coefficientEval (a*b)=E.coefficientEval a*E.coefficientEval b := by
  simp only [coefficientEval,Matrix.mul_apply,map_sum,map_mul,
    Finset.sum_mul,Finset.mul_sum]
  have he (i j k l : ι) :
      ((a i j).val*E.entry i j)*((b k l).val*E.entry k l)=
        (a i j).val*(b k l).val*(E.entry i j*E.entry k l) := by
    rw [mul_assoc,← mul_assoc (E.entry i j),((b k l).property i j).eq]
    simp only [mul_assoc]
  change (∑ i,∑ j,∑ k,(a i k).val*(b k j).val*E.entry i j) =
    ∑ k,∑ l,∑ i,∑ j,((a i j).val*E.entry i j)*((b k l).val*E.entry k l)
  simp only [he,E.mul_entry,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem coefficientEval_star (a : Matrix ι ι E.commutant) :
    E.coefficientEval (star a)=star (E.coefficientEval a) := by
  simp only [coefficientEval,star_sum,star_mul,E.star_entry,Matrix.star_apply,
    map_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact ((star (a i j)).property j i).eq.symm

theorem coefficientEval_one : E.coefficientEval 1=1 := by
  simpa [coefficientEval,Matrix.one_apply,apply_ite,ite_mul] using E.total

def coefficientHom : Matrix ι ι E.commutant →⋆ₐ[ℂ] A where
  toFun := E.coefficientEval
  map_one' := E.coefficientEval_one
  map_mul' := E.coefficientEval_mul
  map_zero' := by simp [coefficientEval]
  map_add' a b := by simp [coefficientEval,add_mul,Finset.sum_add_distrib]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    change E.coefficientEval (c • 1)=algebraMap ℂ A c
    simp only [coefficientEval,Matrix.smul_apply,map_smul,smul_mul_assoc,
      ← Finset.smul_sum]
    change c • E.coefficientEval 1=algebraMap ℂ A c
    rw [E.coefficientEval_one,Algebra.algebraMap_eq_smul_one]
  map_star' := E.coefficientEval_star

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

/-- The sum of two orthogonal projections, in the original algebra. -/
def orthogonalSum (p q : AlgebraProjection M) (h : p.val*q.val=0) : AlgebraProjection M :=
  ⟨p.val+q.val,p.property.add q.property h⟩

theorem le_orthogonalSum_left (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    p ≤ orthogonalSum p q h := by
  change (p.val+q.val)*p.val=p.val
  rw [add_mul,p.property.isIdempotentElem.eq,PartialIsometry.orthogonal_reverse _ _ h,add_zero]

theorem le_orthogonalSum_right (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    q ≤ orthogonalSum p q h := by
  change (p.val+q.val)*q.val=q.val
  rw [add_mul,h,q.property.isIdempotentElem.eq,zero_add]

theorem orthogonalSum_le {p q r : AlgebraProjection M} (h : p.val*q.val=0)
    (hp : p ≤ r) (hq : q ≤ r) : orthogonalSum p q h ≤ r := by
  change r.val*(p.val+q.val)=p.val+q.val
  rw [mul_add,hp,hq]

end Tracial

end

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- Composition with range contained in the initial projection. -/
def compose (v w : PartialIsometry M) (h : w.target ≤ v.support) : PartialIsometry M where
  support := w.support
  val := v.val*w.val
  initial := by
    calc star (v.val*w.val)*(v.val*w.val) = star w.val*(star v.val*v.val)*w.val := by
           simp only [star_mul,mul_assoc]
         _ = star w.val*w.val := by
           rw [v.initial,mul_assoc,(w.target_le_iff_mul v.support).mp h]
         _ = w.support.val := w.initial

theorem compose_target (v w : PartialIsometry M) (h : w.target ≤ v.support) :
    (compose v w h).target.val=v.val*w.target.val*star v.val := by
  change (v.val*w.val)*star (v.val*w.val)=v.val*(w.val*star w.val)*star v.val
  simp only [star_mul,mul_assoc]

theorem compose_target_le (v w : PartialIsometry M) (h : w.target ≤ v.support) :
    (compose v w h).target ≤ v.target := by
  apply ((compose v w h).target_le_iff_mul v.target).mpr
  change v.target.val*(v.val*w.val)=v.val*w.val
  rw [← mul_assoc,v.target_mul]

end PartialIsometry

/-- A partition of p with actual partial isometries from a common projection.
The cross identities encode orthogonality. This structure is constructed below. -/
structure EquivalentPartition (p : AlgebraProjection M) (ι : Type*) [Fintype ι] where
  base : AlgebraProjection M
  leg : ι → PartialIsometry M
  initial : ∀ i, (leg i).support=base
  cross : ∀ i j, i≠j → star (leg i).val*(leg j).val=0
  total : ∑ i, (leg i).target.val=p.val
  bound : ∀ i, (leg i).target ≤ p

namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem orthogonal (E : EquivalentPartition p ι) (i j : ι) (hij : i≠j) :
    (E.leg i).target.val*(E.leg j).target.val=0 := by
  change ((E.leg i).val*star (E.leg i).val)*((E.leg j).val*star (E.leg j).val)=0
  calc _ = (E.leg i).val*(star (E.leg i).val*(E.leg j).val)*star (E.leg j).val := by
           simp only [mul_assoc]
       _ = 0 := by rw [E.cross i j hij,mul_zero,zero_mul]

/-- Refinement is performed on the common initial corner and transported. -/
def refine (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ) :
    EquivalentPartition p (ι × κ) where
  base := F.base
  leg a := (E.leg a.1).compose (F.leg a.2) (by rw [E.initial]; exact F.bound a.2)
  initial a := F.initial a.2
  cross a b hab := by
    change star ((E.leg a.1).val*(F.leg a.2).val)*
      ((E.leg b.1).val*(F.leg b.2).val)=0
    rw [star_mul]
    have hr : (star (F.leg a.2).val*star (E.leg a.1).val)*
        ((E.leg b.1).val*(F.leg b.2).val)=
        star (F.leg a.2).val*(star (E.leg a.1).val*(E.leg b.1).val)*(F.leg b.2).val := by
      simp only [mul_assoc]
    rw [hr]
    by_cases h : a.1=b.1
    · rw [h,(E.leg b.1).initial,E.initial,mul_assoc,
        ((F.leg b.2).target_le_iff_mul E.base).mp (F.bound b.2)]
      exact F.cross a.2 b.2 (fun hh => hab (Prod.ext h hh))
    · rw [E.cross a.1 b.1 h,mul_zero,zero_mul]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [PartialIsometry.compose_target,← Finset.sum_mul,← Finset.mul_sum,F.total]
    have h (i : ι) : (E.leg i).val*E.base.val=(E.leg i).val := by
      rw [← E.initial i,(E.leg i).mul_support]
    simp only [h]
    exact E.total
  bound a := ((E.leg a.1).compose_target_le (F.leg a.2) _).trans (E.bound a.1)

/-- Depth zero consists of the original projection itself. -/
def singleton (p : AlgebraProjection M) : EquivalentPartition p Unit where
  base := p
  leg _ := PartialIsometry.onProjection p
  initial _ := rfl
  cross i j hij := (hij (Subsingleton.elim _ _)).elim
  total := by simp only [PartialIsometry.onProjection_target,Fintype.sum_unique]
  bound _ := by rw [PartialIsometry.onProjection_target]

/-- Two equivalent orthogonal halves, as a family with a common initial corner. -/
def ofHalving (v : PartialIsometry M) (ho : v.support.val*v.target.val=0)
    (hp : v.support.val+v.target.val=p.val) : EquivalentPartition p Bool where
  base := v.support
  leg b := if b then v else PartialIsometry.onProjection v.support
  initial b := by cases b <;> rfl
  cross b c hbc := by
    have h : v.support.val*v.val=0 := by
      calc _ = v.support.val*(v.target.val*v.val) := by rw [v.target_mul]
           _ = 0 := by rw [← mul_assoc,ho,zero_mul]
    cases b <;> cases c
    · exact (hbc rfl).elim
    · simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,PartialIsometry.onProjection,
        v.support.property.isSelfAdjoint.star_eq] using h
    · simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,PartialIsometry.onProjection,
        star_mul,star_zero,v.support.property.isSelfAdjoint.star_eq] using congrArg star h
    · exact (hbc rfl).elim
  total := by
    simp only [Fintype.sum_bool,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,
      PartialIsometry.onProjection_target]
    exact (add_comm _ _).trans hp
  bound b := by
    have he : orthogonalSum v.support v.target ho=p := Subtype.ext hp
    cases b
    · simpa only [Bool.false_eq_true,ite_false, if_false,PartialIsometry.onProjection_target,he]
        using le_orthogonalSum_left v.support v.target ho
    · simpa only [ite_true, if_true,he] using le_orthogonalSum_right v.support v.target ho

end EquivalentPartition
end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem adjoint_target (v : PartialIsometry M) : v.adjoint.target=v.support := by
  apply Subtype.ext
  change star v.val*star (star v.val)=v.support.val
  rw [star_star,v.initial]

theorem compose_target_of_eq (v w : PartialIsometry M) (h : w.target=v.support) :
    (v.compose w (le_of_eq h)).target=v.target := by
  apply Subtype.ext
  rw [compose_target,h,v.mul_support]
  rfl

end PartialIsometry
namespace AlgebraProjection

def Subequivalent (p q : AlgebraProjection M) : Prop :=
  ∃ v : PartialIsometry M, v.support=p ∧ v.target ≤ q

def Equivalent (p q : AlgebraProjection M) : Prop :=
  ∃ v : PartialIsometry M, v.support=p ∧ v.target=q

theorem subequivalent_refl (p : AlgebraProjection M) : p.Subequivalent p :=
  ⟨PartialIsometry.onProjection p,rfl,le_of_eq (PartialIsometry.onProjection_target p)⟩

theorem subequivalent_of_le {p q : AlgebraProjection M} (h : p ≤ q) :
    p.Subequivalent q :=
  ⟨PartialIsometry.onProjection p,rfl,(le_of_eq (PartialIsometry.onProjection_target p)).trans h⟩

theorem subequivalent_trans {p q r : AlgebraProjection M}
    (h : p.Subequivalent q) (k : q.Subequivalent r) : p.Subequivalent r := by
  obtain ⟨v,hv,hvq⟩ := h
  obtain ⟨w,hw,hwr⟩ := k
  have hc : v.target ≤ w.support := by rw [hw]; exact hvq
  exact ⟨w.compose v hc,hv,(w.compose_target_le v hc).trans hwr⟩

theorem equivalent_refl (p : AlgebraProjection M) : p.Equivalent p :=
  ⟨PartialIsometry.onProjection p,rfl,PartialIsometry.onProjection_target p⟩

theorem equivalent_symm {p q : AlgebraProjection M} (h : p.Equivalent q) : q.Equivalent p := by
  obtain ⟨v,hv,hvq⟩ := h
  exact ⟨v.adjoint,hvq,v.adjoint_target.trans hv⟩

theorem equivalent_trans {p q r : AlgebraProjection M}
    (h : p.Equivalent q) (k : q.Equivalent r) : p.Equivalent r := by
  obtain ⟨v,hv,hvq⟩ := h
  obtain ⟨w,hw,hwr⟩ := k
  have hc : v.target=w.support := hvq.trans hw.symm
  exact ⟨w.compose v (le_of_eq hc),hv,(w.compose_target_of_eq v hc).trans hwr⟩

theorem Equivalent.subequivalent {p q : AlgebraProjection M} (h : p.Equivalent q) :
    p.Subequivalent q := by
  obtain ⟨v,hv,hvq⟩ := h
  exact ⟨v,hv,le_of_eq hvq⟩

/-- Scalar-center comparison gives totality of actual subequivalence. -/
theorem subequivalent_total
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) : p.Subequivalent q ∨ q.Subequivalent p := by
  obtain ⟨v,hp,hq,h⟩ := traceFree_exists_partialIsometry_comparison hfactor p q
  rcases h with h | h
  · exact Or.inl ⟨v,h,hq⟩
  · exact Or.inr ⟨v.adjoint,h,by rw [v.adjoint_target]; exact hp⟩

end AlgebraProjection

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
namespace AlgebraProjection

variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Mutual subequivalence is equivalence in a finite algebra. -/
theorem equivalent_of_mutual_subequivalent {p q : AlgebraProjection M}
    (hpq : p.Subequivalent q) (hqp : q.Subequivalent p) : p.Equivalent q := by
  obtain ⟨v,hv,hvq⟩ := hpq
  obtain ⟨w,hw,hwp⟩ := hqp
  have hc : v.target ≤ w.support := by rw [hw]; exact hvq
  let u := w.compose v hc
  have hu : u.target ≤ u.support := by
    change u.target ≤ v.support
    rw [hv]
    exact (w.compose_target_le v hc).trans hwp
  have he : u.target=p := (u.target_eq_support_of_finite hfinite hu).trans hv
  have hw' : w.target=p := le_antisymm hwp (by
    rw [← he]; exact w.compose_target_le v hc)
  exact ⟨w.adjoint,hw',w.adjoint_target.trans hw⟩

include hfinite in
/-- Equivalent comparable projections in a finite algebra coincide. -/
theorem eq_of_equivalent_of_le {p q : AlgebraProjection M}
    (he : p.Equivalent q) (hle : p ≤ q) : p=q := by
  obtain ⟨v,hv,ht⟩ := he
  exact ht.symm.trans ((v.target_eq_support_of_finite_of_le hfinite (by
    rw [hv,ht]; exact hle)).trans hv) |>.symm

include hfinite in
/-- Any embedding onto a subprojection of an equivalent projection is onto. -/
theorem target_eq_of_equivalent (v : PartialIsometry M) (q : AlgebraProjection M)
    (he : v.support.Equivalent q) (hle : v.target ≤ q) : v.target=q := by
  have hv : v.target.Equivalent v.support := ⟨v.adjoint,rfl,v.adjoint_target⟩
  exact eq_of_equivalent_of_le hfinite (equivalent_trans hv he) hle

theorem subequivalent_orthogonalSum {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0)
    (h₁ : p.Subequivalent q) (h₂ : r.Subequivalent s) :
    (orthogonalSum p r hp).Subequivalent (orthogonalSum q s hq) := by
  obtain ⟨v,hv,hvq⟩ := h₁
  obtain ⟨w,hw,hws⟩ := h₂
  have hi : v.support.val*w.support.val=0 := by rw [hv,hw]; exact hp
  have ht := projection_orthogonal_of_le hq hvq hws
  refine ⟨v.patch w hi ht,Subtype.ext (by
    change v.support.val+w.support.val=_
    rw [hv,hw]
    rfl),?_⟩
  have he : (v.patch w hi ht).target=orthogonalSum v.target w.target ht :=
    Subtype.ext (v.patch_target w hi ht)
  rw [he]
  exact orthogonalSum_le ht (hvq.trans (le_orthogonalSum_left _ _ hq))
    (hws.trans (le_orthogonalSum_right _ _ hq))

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfinite hfactor in
/-- Cancel equivalent orthogonal pieces from a subequivalence. -/
theorem subequivalent_cancel {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0) (he : p.Equivalent q)
    (h : (orthogonalSum p r hp).Subequivalent (orthogonalSum q s hq)) :
    r.Subequivalent s := by
  rcases subequivalent_total hfactor r s with hgood | hrev
  · exact hgood
  · obtain ⟨v,hv,ht⟩ := equivalent_symm he
    obtain ⟨w,hw,hwr⟩ := hrev
    have hi : v.support.val*w.support.val=0 := by rw [hv,hw]; exact hq
    have ho : v.target.val*w.target.val=0 := by
      rw [ht]; exact projection_orthogonal_of_le hp le_rfl hwr
    let u := v.patch w hi ho
    have hus : u.support=orthogonalSum q s hq := Subtype.ext (by
      change v.support.val+w.support.val=_; rw [hv,hw]; rfl)
    have hut : u.target ≤ orthogonalSum p r hp := by
      have hu : u.target=orthogonalSum v.target w.target ho :=
        Subtype.ext (v.patch_target w hi ho)
      rw [hu]
      exact orthogonalSum_le ho (by rw [ht]; exact le_orthogonalSum_left _ _ hp)
        (hwr.trans (le_orthogonalSum_right _ _ hp))
    have heq : u.support.Equivalent (orthogonalSum p r hp) := by
      rw [hus]
      exact equivalent_of_mutual_subequivalent hfinite ⟨u,hus,hut⟩ h
    have hu := congrArg Subtype.val (target_eq_of_equivalent hfinite u _ heq hut)
    rw [PartialIsometry.patch_target,ht] at hu
    change p.val+w.target.val=p.val+r.val at hu
    have hw' : w.target=r := Subtype.ext (add_left_cancel hu)
    exact (equivalent_symm (show s.Equivalent r from ⟨w,hw,hw'⟩)).subequivalent

include hfinite hfactor in
theorem equivalent_cancel {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0) (he : p.Equivalent q)
    (h : (orthogonalSum p r hp).Equivalent (orthogonalSum q s hq)) :
    r.Equivalent s :=
  equivalent_of_mutual_subequivalent hfinite
    (subequivalent_cancel hfinite hfactor hp hq he h.subequivalent)
    (subequivalent_cancel hfinite hfactor hq hp (equivalent_symm he)
      (equivalent_symm h).subequivalent)

/-- The relative complement is the actual difference of the operators. -/
def remainder (p q : AlgebraProjection M) (h : p ≤ q) : AlgebraProjection M :=
  ⟨q.val-p.val,p.property.sub_of_mul_eq_right q.property h⟩

theorem remainder_orthogonal (p q : AlgebraProjection M) (h : p ≤ q) :
    p.val*(remainder p q h).val=0 := by
  change p.val*(q.val-p.val)=0
  rw [mul_sub,projection_mul_of_le h,p.property.isIdempotentElem.eq,sub_self]

theorem orthogonalSum_remainder (p q : AlgebraProjection M) (h : p ≤ q) :
    orthogonalSum p (remainder p q h) (remainder_orthogonal p q h)=q :=
  Subtype.ext (by change p.val+(q.val-p.val)=q.val; abel)

theorem remainder_le (p q : AlgebraProjection M) (h : p ≤ q) : remainder p q h ≤ q := by
  change q.val*(q.val-p.val)=q.val-p.val
  rw [mul_sub,q.property.isIdempotentElem.eq,h]

include hfinite hfactor in
/-- Comparison respects subtraction of equivalent pieces. -/
theorem remainder_subequivalent {p q P Q : AlgebraProjection M}
    (hp : p ≤ P) (hq : q ≤ Q) (he : p.Equivalent q) (h : P.Subequivalent Q) :
    (remainder p P hp).Subequivalent (remainder q Q hq) := by
  apply subequivalent_cancel hfinite hfactor
    (remainder_orthogonal p P hp) (remainder_orthogonal q Q hq) he
  simpa only [orthogonalSum_remainder] using h

include hfinite hfactor in
theorem remainder_equivalent {p q P Q : AlgebraProjection M}
    (hp : p ≤ P) (hq : q ≤ Q) (he : p.Equivalent q) (h : P.Equivalent Q) :
    (remainder p P hp).Equivalent (remainder q Q hq) := by
  apply equivalent_cancel hfinite hfactor
    (remainder_orthogonal p P hp) (remainder_orthogonal q Q hq) he
  simpa only [orthogonalSum_remainder] using h

end AlgebraProjection
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem exists_finsetSum {ι : Type*} (a : ι → PartialIsometry M) (s : Finset ι)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).support.val*(a j).support.val=0)
    (hq : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).target.val*(a j).target.val=0) :
    ∃ v : PartialIsometry M, v.val=∑ i ∈ s, (a i).val ∧
      v.support.val=∑ i ∈ s, (a i).support.val ∧
      v.target.val=∑ i ∈ s, (a i).target.val := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨zero,by simp [zero],by simp [zero],by simp [zero,target]⟩
  | @insert i s hi ih =>
    obtain ⟨v,hv,hs,ht⟩ := ih
      (fun j hj k hk => hp j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj k hk => hq j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
    have ho₁ : (a i).support.val*v.support.val=0 := by
      rw [hs,Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => hp i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h.symm ▸ hj)))
    have ho₂ : (a i).target.val*v.target.val=0 := by
      rw [ht,Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => hq i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h.symm ▸ hj)))
    refine ⟨(a i).patch v ho₁ ho₂,?_,?_,?_⟩
    · change (a i).val+v.val=_
      rw [hv,Finset.sum_insert hi]
    · change (a i).support.val+v.support.val=_
      rw [hs,Finset.sum_insert hi]
    · rw [patch_target,ht,Finset.sum_insert hi]

end PartialIsometry
namespace AlgebraProjection

theorem isStarProjection_sum {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) :
    IsStarProjection (∑ i ∈ s, (a i).val) := by
  obtain ⟨v,_,hs,_⟩ := PartialIsometry.exists_finsetSum
    (fun i => PartialIsometry.onProjection (a i)) s ho
    (by simpa only [PartialIsometry.onProjection_target] using ho)
  change v.support.val=(∑ i ∈ s, (a i).val) at hs
  exact hs ▸ v.support.property

def finsetSum {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) : AlgebraProjection M :=
  ⟨∑ i ∈ s, (a i).val,isStarProjection_sum a s ho⟩

theorem finsetSum_le_iff {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) (p : AlgebraProjection M) :
    finsetSum a s ho ≤ p ↔ ∀ i ∈ s, a i ≤ p := by
  classical
  constructor
  · intro h i hi
    apply le_trans ?_ h
    change (∑ j ∈ s, (a j).val)*(a i).val=(a i).val
    rw [Finset.sum_mul]
    exact (Finset.sum_eq_single_of_mem i hi
      (fun j hj hji => ho j hj i hi hji)).trans (a i).property.isIdempotentElem.eq
  · intro h
    change p.val*(∑ i ∈ s, (a i).val)=∑ i ∈ s, (a i).val
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl h

end AlgebraProjection
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

def subset (E : EquivalentPartition p ι) (s : Finset ι) : AlgebraProjection M :=
  AlgebraProjection.finsetSum (fun i => (E.leg i).target) s
    (fun i _ j _ => E.orthogonal i j)

theorem subset_val (E : EquivalentPartition p ι) (s : Finset ι) :
    (E.subset s).val=∑ i ∈ s, (E.leg i).target.val := rfl

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

def dyadicWeight (n : ℕ) (s : Finset (DyadicIndex n)) : ℝ := (s.card : ℝ)/2^n

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace AlgebraProjection

/-- Actual least upper bounds for arbitrary nonempty directed projection nets. -/
theorem exists_isLUB_monotone
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range q) p := by
  obtain ⟨v,hv,hs,_⟩ := PartialIsometry.traceFree_monotone_least_supports
    (fun i => PartialIsometry.onProjection (q i)) (fun _ _ h => hq h)
  refine ⟨v.support,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact PartialIsometry.support_mono (hv i)
  · intro p hp
    exact hs p (fun i => hp ⟨i,rfl⟩)

end AlgebraProjection
namespace PartialIsometry

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hfinite in
/-- Extend a given embedding to a larger source while keeping its target in r. -/
theorem exists_extension_of_subequivalent (v : PartialIsometry M)
    (p r : AlgebraProjection M) (hp : v.support ≤ p) (hr : v.target ≤ r)
    (hpr : p.Subequivalent r) :
    ∃ w : PartialIsometry M, v ≤ w ∧ w.support=p ∧ w.target ≤ r := by
  obtain ⟨u,hu,ht⟩ := AlgebraProjection.remainder_subequivalent hfinite hfactor hp hr
    (show v.support.Equivalent v.target from ⟨v,rfl,rfl⟩) hpr
  have hi : v.support.val*u.support.val=0 := by
    rw [hu]
    exact AlgebraProjection.remainder_orthogonal _ _ hp
  have ho : v.target.val*u.target.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal _ _ hr) le_rfl ht
  refine ⟨v.patch u hi ho,v.le_patch u hi ho,?_,?_⟩
  · apply Subtype.ext
    change v.support.val+u.support.val=p.val
    rw [hu]
    change v.support.val+(p.val-v.support.val)=p.val
    abel
  · have he : (v.patch u hi ho).target=orthogonalSum v.target u.target ho :=
      Subtype.ext (v.patch_target u hi ho)
    rw [he]
    exact orthogonalSum_le ho hr (ht.trans (AlgebraProjection.remainder_le _ _ hr))

include hfactor hfinite in
/-- A sequence of comparable sources admits compatible actual embeddings. -/
theorem exists_monotone_embeddings (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (r : AlgebraProjection M) (hr : ∀ n, (q n).Subequivalent r) :
    ∃ a : ℕ → PartialIsometry M, Monotone a ∧
      (∀ n, (a n).support=q n) ∧ (∀ n, (a n).target ≤ r) := by
  classical
  obtain ⟨v,hv,ht⟩ := hr 0
  let step (n : ℕ) (w : {w : PartialIsometry M // w.support=q n ∧ w.target ≤ r}) :=
    exists_extension_of_subequivalent hfactor hfinite w.val (q (n+1)) r
      (by rw [w.property.1]; exact hq (Nat.le_succ n)) w.property.2 (hr (n+1))
  let a : (n : ℕ) → {w : PartialIsometry M // w.support=q n ∧ w.target ≤ r} :=
    Nat.rec ⟨v,hv,ht⟩ (fun n w => ⟨(step n w).choose,(step n w).choose_spec.2⟩)
  refine ⟨fun n => (a n).val,?_,fun n => (a n).property.1,fun n => (a n).property.2⟩
  apply monotone_nat_of_le_succ
  intro n
  exact (step n (a n)).choose_spec.1

end PartialIsometry
namespace AlgebraProjection

/-- Sequential increasing-union comparison, with a constructed compatible
partial-isometry limit. No dimension-continuity premise occurs. -/
theorem isLUB_subequivalent_of_sequence
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p)
    (r : AlgebraProjection M) (hr : ∀ n, (q n).Subequivalent r) :
    p.Subequivalent r := by
  obtain ⟨a,ha,hs,ht⟩ := PartialIsometry.exists_monotone_embeddings hfactor hfinite q hq r hr
  obtain ⟨v,hv,hvs,hvt⟩ := PartialIsometry.traceFree_monotone_least_supports a ha
  refine ⟨v,le_antisymm (hvs p (fun n => by rw [hs]; exact hp.1 ⟨n,rfl⟩)) ?_,hvt r ht⟩
  apply hp.2
  rintro _ ⟨n,rfl⟩
  rw [← hs n]
  exact PartialIsometry.support_mono (hv n)

end AlgebraProjection
end

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace AlgebraProjection

/-- The original Hilbert-space vector functional on actual projections. -/
def vectorValue (ξ : H) (p : AlgebraProjection M) : ℝ :=
  (inner ℂ ξ (p.val.val ξ)).re

theorem vectorValue_eq_norm_sq (ξ : H) (p : AlgebraProjection M) :
    vectorValue ξ p = ‖p.val.val ξ‖^2 := by
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  have hi : p.val.val (p.val.val ξ)=p.val.val ξ :=
    congrArg (fun a : M.toStarSubalgebra => a.val ξ) p.property.isIdempotentElem.eq
  have he : inner ℂ (p.val.val ξ) (p.val.val ξ)=inner ℂ ξ (p.val.val ξ) := by
    rw [← ContinuousLinearMap.adjoint_inner_right p.val.val]
    rw [← ContinuousLinearMap.star_eq_adjoint,hs,hi]
  rw [vectorValue,← he,inner_self_eq_norm_sq_to_K]
  norm_cast

theorem vectorValue_nonneg (ξ : H) (p : AlgebraProjection M) : 0 ≤ vectorValue ξ p := by
  rw [vectorValue_eq_norm_sq]
  positivity

theorem vectorValue_remainder (ξ : H) (p q : AlgebraProjection M) (h : p ≤ q) :
    vectorValue ξ (remainder p q h)=vectorValue ξ q-vectorValue ξ p := by
  change (inner ℂ ξ (q.val.val ξ-p.val.val ξ)).re=_
  rw [inner_sub_right,Complex.sub_re]
  rfl

theorem vectorValue_mono (ξ : H) : Monotone (vectorValue (M := M) ξ) := by
  intro p q hpq
  have h := vectorValue_nonneg ξ (remainder p q hpq)
  rw [vectorValue_remainder] at h
  linarith

/-- Retains the matrix-coefficient limit of the concrete projection supremum.
The ultrafilter is the fixed extension of atTop, not a countable subsequence. -/
theorem exists_isLUB_monotone_vector_limit
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range a) p ∧
      ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x))
        ((Ultrafilter.of atTop : Ultrafilter ι) : Filter ι) (𝓝 (inner ℂ y (p.val.val x))) := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => ((a i).val : H →L[ℂ] H)) 1 (by norm_num)
    (fun i => (a i).property.norm_le)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb (x y : H) : Tendsto (fun i => inner ℂ y (((a i).val : H →L[ℂ] H) x))
    (ω : Filter ι) (𝓝 (inner ℂ y ((b : H →L[ℂ] H) x))) := ht x y
  have hadj (i : ι) (x y : H) :
      inner ℂ x (((a i).val : H →L[ℂ] H) y) =
      inner ℂ (((a i).val : H →L[ℂ] H) x) y := by
    have hs : star (((a i).val : H →L[ℂ] H)) = ((a i).val : H →L[ℂ] H) :=
      congrArg Subtype.val (a i).property.isSelfAdjoint.star_eq
    calc inner ℂ x (((a i).val : H →L[ℂ] H) y) =
          inner ℂ x (star (((a i).val : H →L[ℂ] H)) y) := by rw [hs]
         _ = inner ℂ (((a i).val : H →L[ℂ] H) x) y := by
           rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hself : star b = b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hh := (hb y x).star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ x (((a i).val : H →L[ℂ] H) y)))
      (ω : Filter ι) (𝓝 ((starRingEnd ℂ) (inner ℂ x ((b : H →L[ℂ] H) y)))) at hh
    simp only [inner_conj_symm] at hh
    have eq := tendsto_nhds_unique (hb x y) (hh.congr (fun i => (hadj i y x).symm))
    change inner ℂ y (star (b : H →L[ℂ] H) x) = inner ℂ y ((b : H →L[ℂ] H) x)
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact eq.symm
  have hba (i : ι) : b * (a i).val = (a i).val := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (hb (((a i).val : H →L[ℂ] H) x) y)
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (ha hj)).symm
  have hab (i : ι) : (a i).val * b = (a i).val := by
    have h := congrArg star (hba i)
    simpa only [star_mul, hself, (a i).property.isSelfAdjoint.star_eq] using h
  have hid : b * b = b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (hb ((b : H →L[ℂ] H) x) y)
    exact (hb x y).congr (fun i =>
      (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (hab i)).symm)
  refine ⟨⟨b,⟨hid,hself⟩⟩,⟨?_,?_⟩,hb⟩
  · rintro _ ⟨i,rfl⟩
    exact hba i
  · intro p hp
    change p.val*b=b
    apply wot_limit_unique (fun i => p.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    have hpa (i : ι) : p.val*(a i).val=(a i).val := hp ⟨i,rfl⟩
    simpa only [hpa] using hb

/-- The vector functional preserves any directed projection supremum. -/
theorem vectorValue_isLUB_monotone
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range a) p) (ξ : H) :
    IsLUB (Set.range (fun i => vectorValue ξ (a i))) (vectorValue ξ p) := by
  obtain ⟨q,hq,ht⟩ := exists_isLUB_monotone_vector_limit a ha
  have he : q=p := le_antisymm (hq.2 hp.1) (hp.2 hq.1)
  subst q
  refine ⟨?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact vectorValue_mono ξ (hp.1 ⟨i,rfl⟩)
  · intro r hr
    exact le_of_tendsto ((Complex.continuous_re.tendsto _).comp (ht ξ ξ))
      (Eventually.of_forall (fun i => hr ⟨i,rfl⟩))

theorem vectorValue_tendsto_monotone
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range a) p) (ξ : H) :
    Tendsto (fun i => vectorValue ξ (a i)) atTop (𝓝 (vectorValue ξ p)) :=
  tendsto_atTop_isLUB ((vectorValue_mono ξ).comp ha)
    (vectorValue_isLUB_monotone a ha p hp ξ)

end AlgebraProjection
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

/-- The partition with its corner as its only piece. -/
def single (p : AlgebraProjection M) : CornerPartition p where
  size := 1
  piece _ := p
  orthogonal i j hij := (hij (Subsingleton.elim _ _)).elim
  total := by simp

@[simp] theorem single_pinch (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    (single p).pinch x = p.val*x*p.val := by
  change (∑ _ : Fin 1, p.val*x*p.val) = _
  simp

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
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

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def AlgebraProjection.unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u p.val,
    p.property.map (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u)⟩

theorem AlgebraProjection.equivalent_unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) : p.Equivalent (p.unitaryConjugate u) := by
  let v : PartialIsometry M :=
    { support := p
      val := (u : M.toStarSubalgebra)*p.val
      initial := by
        simp only [star_mul,p.property.isSelfAdjoint.star_eq]
        rw [mul_assoc,← mul_assoc (star (u : M.toStarSubalgebra)),
          Unitary.star_mul_self_of_mem u.property,one_mul,p.property.isIdempotentElem.eq] }
  refine ⟨v,rfl,?_⟩
  apply Subtype.ext
  change ((u : M.toStarSubalgebra)*p.val)*star ((u : M.toStarSubalgebra)*p.val)=
    (u : M.toStarSubalgebra)*p.val*star (u : M.toStarSubalgebra)
  simp only [star_mul,p.property.isSelfAdjoint.star_eq,mul_assoc]
  rw [← mul_assoc p.val,p.property.isIdempotentElem.eq]

end

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instRing
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
section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace AlgebraProjection

/-- A continuous orthogonally additive real charge nonnegative on G admits a
nonzero corner all of whose subprojections have nonnegative charge. -/
theorem exists_nonnegative_corner
    (μ : AlgebraProjection M → ℝ)
    (hadd : ∀ p q (ho : p.val*q.val=0), μ (orthogonalSum p q ho)=μ p+μ q)
    (hcont : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (a : I → AlgebraProjection M), Monotone a →
      ∀ p, IsLUB (Set.range a) p → Tendsto (fun i => μ (a i)) atTop (𝓝 (μ p)))
    (G : AlgebraProjection M) (hG : G.val≠0) (hμG : 0 ≤ μ G) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F → 0 ≤ μ p := by
  classical
  by_cases hall : ∀ p : AlgebraProjection M, p ≤ G → 0 ≤ μ p
  · exact ⟨G,le_rfl,hG,hall⟩
  push Not at hall
  obtain ⟨r,hrG,hr⟩ := hall
  let S : Set (AlgebraProjection M) := {p | p ≤ G ∧ μ p ≤ μ r}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · let : Nonempty c := hne.to_subtype
      let : IsDirected c (· ≤ ·) := ⟨by
        intro a b
        rcases hchain.total a.property b.property with h | h
        · exact ⟨b,h,le_rfl⟩
        · exact ⟨a,le_rfl,h⟩⟩
      obtain ⟨p,hp⟩ := exists_isLUB_monotone (fun q : c => q.val) (fun _ _ h => h)
      refine ⟨p,⟨?_,?_⟩,fun q hq => hp.1 ⟨⟨q,hq⟩,rfl⟩⟩
      · exact hp.2 (by rintro _ ⟨q,rfl⟩; exact (hc q.property).1)
      · exact le_of_tendsto (hcont c (fun q : c => q.val) (fun _ _ h => h) p hp)
          (Eventually.of_forall (fun q => (hc q.property).2))
    · exact ⟨r,⟨hrG,le_rfl⟩,fun q hq => (hne ⟨q,hq⟩).elim⟩)
  have hvG : v ≤ G := hv.1.1
  have hvneg : μ v < 0 := hv.1.2.trans_lt hr
  let F := remainder v G hvG
  have hF : F.val≠0 := by
    intro hz
    have he : G=v := Subtype.ext (sub_eq_zero.mp hz)
    rw [he] at hμG
    exact (not_lt_of_ge hμG) hvneg
  refine ⟨F,remainder_le v G hvG,hF,?_⟩
  intro p hp
  by_contra hnot
  have hpneg : μ p<0 := lt_of_not_ge hnot
  have ho : v.val*p.val=0 := projection_orthogonal_of_le
    (remainder_orthogonal v G hvG) le_rfl hp
  let q := orthogonalSum v p ho
  have hqG : q ≤ G := orthogonalSum_le ho hvG (hp.trans (remainder_le v G hvG))
  have he : μ q=μ v+μ p := hadd v p ho
  have hqμ : μ q ≤ μ r := by linarith [hv.1.2]
  have hqv : q ≤ v := hv.2 ⟨hqG,hqμ⟩ (le_orthogonalSum_left _ _ ho)
  have hqeq : q=v := le_antisymm hqv (le_orthogonalSum_left _ _ ho)
  rw [hqeq] at he
  linarith

end AlgebraProjection

end

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralRandomWalk
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independent forward and reflected backward random walks -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

abbrev BilateralWalkPath := ℤ → G

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteMatrixUnitBasis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A Hilbert basis adapted to a full matrix system

A basis of one diagonal corner is transported by the matrix columns. This
gives an explicit tensor-shaped basis on which every matrix unit has its
standard action, the bridge needed for compatible finite matrix groups.
-/

open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace Generator.MatrixUnitSystem

variable (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (o : ι)

def initialHilbertSpace : Submodule ℂ H := (E.entry o o).range

instance initialHilbertSpace_complete : CompleteSpace (E.initialHilbertSpace o) := by
  have hp : IsIdempotentElem (E.entry o o) := by
    change E.entry o o * E.entry o o = E.entry o o
    simp only [E.mul_entry, ite_true, if_true]
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp).completeSpace_coe

theorem initialHilbertSpace_fixed (x : E.initialHilbertSpace o) : E.entry o o x = x := by
  obtain ⟨y, hy⟩ := x.property
  change E.entry o o y = (x : H) at hy
  rw [← hy]
  change (E.entry o o * E.entry o o) y = E.entry o o y
  simp only [E.mul_entry, ite_true, if_true]

def initialCoordinate (i : ι) (x : H) : E.initialHilbertSpace o :=
  ⟨E.entry o i x, ⟨E.entry o i x, by
    change (E.entry o o * E.entry o i) x = E.entry o i x
    simp only [E.mul_entry, ite_true, if_true]⟩⟩

def initialColumn (i : ι) : E.initialHilbertSpace o →ₗ[ℂ] H :=
  (E.entry i o).toLinearMap.comp (E.initialHilbertSpace o).subtype

@[simp]
theorem initialColumn_apply (i : ι) (x : E.initialHilbertSpace o) :
    E.initialColumn o i x = E.entry i o x := rfl

theorem inner_initialColumns (i j : ι) (x y : E.initialHilbertSpace o) :
    inner ℂ (E.initialColumn o i x) (E.initialColumn o j y) =
      if i = j then inner ℂ x y else 0 := by
  change inner ℂ (E.entry i o x) (E.entry j o y) = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (x : H) ((star (E.entry i o) * E.entry j o) (y : H)) = _
  rw [E.star_entry, E.mul_entry]
  split_ifs
  · rw [E.initialHilbertSpace_fixed o y]
    rfl
  · simp

theorem sum_initialColumn_coordinate (x : H) :
    ∑ i, E.initialColumn o i (E.initialCoordinate o i x) = x := by
  have he (i : ι) : E.initialColumn o i (E.initialCoordinate o i x) = E.entry i i x := by
    change (E.entry i o * E.entry o i) x = E.entry i i x
    simp only [E.mul_entry, ite_true, if_true]
  simp_rw [he]
  rw [← sum_apply, E.total]
  rfl

variable (b : OrthonormalBasis κ ℂ (E.initialHilbertSpace o))

def adaptedVector (p : ι × κ) : H := E.initialColumn o p.1 (b p.2)

theorem adaptedVector_orthonormal : Orthonormal ℂ (E.adaptedVector o b) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, k⟩ ⟨j, l⟩
  change inner ℂ (E.initialColumn o i (b k)) (E.initialColumn o j (b l)) = _
  rw [E.inner_initialColumns, b.inner_eq_ite]
  by_cases hi : i = j <;> by_cases hk : k = l <;> simp [hi, hk]

omit [DecidableEq κ] in
theorem adaptedVector_span : ⊤ ≤ Submodule.span ℂ (Set.range (E.adaptedVector o b)) := by
  let S := Submodule.span ℂ (Set.range (E.adaptedVector o b))
  have hc (i : ι) (y : E.initialHilbertSpace o) : E.initialColumn o i y ∈ S := by
    rw [← b.sum_repr y, map_sum]
    apply S.sum_mem
    intro k _
    rw [map_smul]
    exact S.smul_mem _ (Submodule.subset_span ⟨(i, k), rfl⟩)
  intro x _
  rw [← E.sum_initialColumn_coordinate o x]
  exact S.sum_mem (fun i _ => hc i _)

/-- The explicit basis obtained by transporting the initial-corner basis. -/
def adaptedBasis : OrthonormalBasis (ι × κ) ℂ H :=
  OrthonormalBasis.mk (E.adaptedVector_orthonormal o b) (E.adaptedVector_span o b)

@[simp]
theorem adaptedBasis_apply (p : ι × κ) : E.adaptedBasis o b p = E.entry p.1 o (b p.2) := by
  change OrthonormalBasis.mk _ _ p = _
  rw [OrthonormalBasis.coe_mk]
  rfl

/-- On the adapted basis the original matrix units act on the first index. -/
theorem entry_adaptedBasis (i j k : ι) (r : κ) :
    E.entry i j (E.adaptedBasis o b (k, r)) =
      if j = k then E.adaptedBasis o b (i, r) else 0 := by
  simp only [E.adaptedBasis_apply]
  change (E.entry i j * E.entry k o) (b r) = _
  rw [E.mul_entry]
  split_ifs <;> rfl

end Generator.MatrixUnitSystem

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Pureness_Completion_ClosedStarIdealQuotientNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.PopaCorner.algebra_closed _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter
open scoped Topology NNReal ENNReal

structure ClosedStarIdeal (D : Type*) [CStarAlgebra D] where
  ideal : TwoSidedIdeal D
  star_mem : ∀ {u : D}, u ∈ ideal → star u ∈ ideal
  isClosed : IsClosed (ideal : Set D)

namespace ClosedStarIdeal
variable {D : Type*} [CStarAlgebra D] (J : ClosedStarIdeal D)

abbrev Quotient := J.ideal.ringCon.Quotient

def quotientMap : D →ₐ[ℂ] J.Quotient := J.ideal.ringCon.mkₐ ℂ

lemma quotientMap_surjective : Function.Surjective J.quotientMap :=
  J.ideal.ringCon.mkₐ_surjective (α := ℂ)

lemma rel_star (u v : D) (h : J.ideal.ringCon u v) :
    J.ideal.ringCon (star u) (star v) := by
  rw [TwoSidedIdeal.rel_iff] at h ⊢
  simpa only [star_sub] using J.star_mem h

instance quotientStar : Star (J.Quotient) where
  star := Quotient.map' star (J.rel_star)

lemma quotientMap_star (u : D) :
    J.quotientMap (star u) = star (J.quotientMap u) := rfl

instance quotientStarRing : StarRing (J.Quotient) where
  star_involutive x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← J.quotientMap_star,← J.quotientMap_star,star_star]
  star_mul x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_mul,← J.quotientMap_star,star_mul,map_mul,
      J.quotientMap_star,J.quotientMap_star]
  star_add x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_add,← J.quotientMap_star,star_add,map_add,
      J.quotientMap_star,J.quotientMap_star]

instance quotientStarModule : StarModule ℂ (J.Quotient) where
  star_smul c x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← _root_.map_smul,← J.quotientMap_star,star_smul,_root_.map_smul,J.quotientMap_star]

def quotientStarHom : D →⋆ₐ[ℂ] J.Quotient :=
  { J.quotientMap with map_star' := J.quotientMap_star }

abbrev idealSubmodule : Submodule ℂ (D) :=
  (J.quotientMap).toLinearMap.ker

lemma idealSubmodule_coe :
    (J.idealSubmodule : Set (D)) =
      (J.ideal : Set (D)) := by
  ext u
  change J.quotientMap u = 0 ↔ u ∈ J.ideal
  change (J.ideal).ringCon.mk' u = (J.ideal).ringCon.mk' 0 ↔ _
  exact Quotient.eq

instance idealSubmodule_closed : IsClosed (J.idealSubmodule : Set (D)) := by
  rw [J.idealSubmodule_coe]
  exact J.isClosed

def quotientLinearEquiv :
    (D ⧸ J.idealSubmodule) ≃ₗ[ℂ] J.Quotient :=
  (J.quotientMap).toLinearMap.quotKerEquivOfSurjective (J.quotientMap_surjective)

lemma quotientLinearEquiv_mk (u : D) :
    J.quotientLinearEquiv (Submodule.Quotient.mk u) = J.quotientMap u := rfl

instance quotientNormedAddCommGroup : NormedAddCommGroup (J.Quotient) :=
  NormedAddCommGroup.induced _ _ (J.quotientLinearEquiv).symm
    (J.quotientLinearEquiv).symm.injective

instance quotientNormedSpace : NormedSpace ℂ (J.Quotient) :=
  NormedSpace.induced ℂ _ _ (J.quotientLinearEquiv).symm

def quotientNormEquiv : J.Quotient ≃ₗᵢ[ℂ]
    (D ⧸ J.idealSubmodule) where
  __ := (J.quotientLinearEquiv).symm
  norm_map' _ := rfl

lemma quotientMap_norm_le (u : D) :
    ‖J.quotientMap u‖ ≤ ‖u‖ := by
  change ‖(J.quotientLinearEquiv).symm (J.quotientMap u)‖ ≤ ‖u‖
  rw [← J.quotientLinearEquiv_mk, LinearEquiv.symm_apply_apply]
  exact Submodule.Quotient.norm_mk_le _ u

lemma quotient_norm_lt_rep (x : J.Quotient) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : D, J.quotientMap u = x ∧ ‖u‖ < ‖x‖+ε := by
  obtain ⟨u,hu,hun⟩ := Submodule.Quotient.norm_mk_lt ((J.quotientLinearEquiv).symm x) hε
  refine ⟨u,?_,hun⟩
  apply (J.quotientLinearEquiv).symm.injective
  rw [← J.quotientLinearEquiv_mk,LinearEquiv.symm_apply_apply,hu]

instance quotientCompleteSpace : CompleteSpace (J.Quotient) :=
  (J.quotientNormEquiv).toIsometryEquiv.completeSpace_iff.mpr inferInstance

lemma quotient_norm_mul_le (x y : J.Quotient) : ‖x*y‖ ≤ ‖x‖*‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
    Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖,‖y‖)) ε hε
  simp only [Set.mem_prod,Metric.mem_ball,and_imp,Prod.forall,Prod.exists] at hc
  obtain ⟨δ,η,⟨hδ,hη⟩,h⟩ := hc
  obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep x hδ
  obtain ⟨v,rfl,hv⟩ := J.quotient_norm_lt_rep y hη
  simp only [Real.dist_eq,abs_sub_lt_iff] at h
  specialize h ‖u‖ ‖v‖ ⟨by linarith,by linarith [J.quotientMap_norm_le u]⟩
    ⟨by linarith,by linarith [J.quotientMap_norm_le v]⟩
  calc
    _ = ‖J.quotientMap (u*v)‖ := by rw [map_mul]
    _ ≤ ‖u*v‖ := J.quotientMap_norm_le _
    _ ≤ ‖u‖*‖v‖ := norm_mul_le _ _
    _ ≤ _ := by linarith [h.2]

instance quotientNormedRing : NormedRing (J.Quotient) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := J.quotient_norm_mul_le

instance quotientNormedAlgebra : NormedAlgebra ℂ (J.Quotient) where
  norm_smul_le := norm_smul_le

lemma quotient_norm_star (x : J.Quotient) : ‖star x‖ = ‖x‖ := by
  have hle (y : J.Quotient) : ‖star y‖ ≤ ‖y‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep y hε
    rw [← J.quotientMap_star]
    exact (J.quotientMap_norm_le (star u)).trans (by simpa only [norm_star] using hu.le)
  exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

instance quotientNormedStarGroup : NormedStarGroup (J.Quotient) where
  norm_star_le x := (J.quotient_norm_star x).le

end ClosedStarIdeal
end CuntzPureness

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Pureness_Completion_ClosedStarIdealQuotientCStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace CuntzPureness.ClosedStarIdeal
open Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (J : ClosedStarIdeal D)

def idealStarAlgebra : NonUnitalStarSubalgebra ℂ (D) where
  carrier := J.ideal
  zero_mem' := (J.ideal).zero_mem
  add_mem' := (J.ideal).add_mem
  mul_mem' {u v} _ hv := (J.ideal).mul_mem_left u v hv
  smul_mem' c u hu := by
    change c • u ∈ J.ideal
    rw [Algebra.smul_def]
    exact (J.ideal).mul_mem_left (algebraMap ℂ _ c) u hu
  star_mem' := J.star_mem

instance idealStarAlgebraCompleteSpace : CompleteSpace (J.idealStarAlgebra) :=
  (J.isClosed).completeSpace_coe
instance idealStarAlgebraCStar : NonUnitalCStarAlgebra (J.idealStarAlgebra) where
  norm_mul_self_le u := CStarRing.norm_mul_self_le u.1

instance idealPartialOrder : PartialOrder (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrder _
instance idealStarOrderedRing : StarOrderedRing (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrderedRing _

local instance instLESubtypeMemNonUnitalStarSubalgebraComplexIdealStarAlgebra : LE (J.idealStarAlgebra) := (J.idealPartialOrder).toLE

local instance instPreorderSubtypeMemNonUnitalStarSubalgebraComplexIdealStarAlgebra_rd020b9_1 : Preorder (J.idealStarAlgebra) := (J.idealPartialOrder).toPreorder
lemma idealInclusion_nonneg {e : J.idealStarAlgebra} (he : 0 ≤ e) :
    0 ≤ (e : D) :=
  by
    have hs : star (CFC.sqrt e)*CFC.sqrt e = e := by
      rw [(CFC.sqrt_nonneg e).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self e he]
    have hs' := congrArg Subtype.val hs
    rw [← hs']
    exact star_mul_self_nonneg _

lemma norm_one_sub {e : D} (he : 0 ≤ e) (hn : ‖e‖ ≤ 1) :
    ‖1-e‖ ≤ 1 := by
  have he1 : e ≤ 1 := by
    simpa using (CStarAlgebra.norm_le_iff_le_algebraMap e (by norm_num : (0:ℝ) ≤ 1) he).mp hn
  rw [CStarAlgebra.norm_le_iff_le_algebraMap (1-e) (by norm_num : (0:ℝ) ≤ 1) (sub_nonneg.mpr he1)]
  simpa using sub_le_self (1 : D) he

lemma exists_ideal_contraction {w : D} (hw : w ∈ J.ideal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, e ∈ J.ideal ∧ IsSelfAdjoint e ∧
      ‖1-e‖ ≤ 1 ∧ ‖w*(1-e)‖ < ε := by
  let W : J.idealStarAlgebra := ⟨w,hw⟩
  let l := CStarAlgebra.approximateUnit (J.idealStarAlgebra)
  have hl := CStarAlgebra.increasingApproximateUnit (J.idealStarAlgebra)
  have ht := hl.tendsto_mul_left W
  have heps := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨e,hp,hn,hm⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and heps)).exists
  refine ⟨e.1,e.2,?_,norm_one_sub (J.idealInclusion_nonneg hp) hn,?_⟩
  · exact congrArg Subtype.val hp.isSelfAdjoint
  · change dist (W*e) W < ε at hm
    rw [dist_eq_norm] at hm
    change ‖w*e.1-w‖ < ε at hm
    simpa only [mul_sub,mul_one,← neg_sub (w*e.1) w,norm_neg] using hm

lemma quotient_norm_square_le (x : J.Quotient) :
    ‖x‖*‖x‖ ≤ ‖star x*x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
  obtain ⟨v,hv,hvn⟩ := J.quotient_norm_lt_rep
    (star (J.quotientMap u)*J.quotientMap u) (half_pos hε)
  let w := star u*u-v
  have hw : w ∈ J.ideal := by
    change (J.ideal).ringCon w 0
    apply Quotient.exact
    change J.quotientMap w = J.quotientMap 0
    simp only [w,map_sub,map_mul,J.quotientMap_star,hv,sub_self]
    exact (_root_.map_zero (J.quotientMap)).symm
  obtain ⟨e,he,hestar,hen,hwe⟩ := J.exists_ideal_contraction hw (half_pos hε)
  have heq : J.quotientMap e = 0 := Quotient.sound he
  have hmap : J.quotientMap (u*(1-e)) = J.quotientMap u := by
    simp [map_mul,map_sub,heq]
  have hun := J.quotientMap_norm_le (u*(1-e))
  rw [hmap] at hun
  have hidentity : star (u*(1-e))*(u*(1-e)) =
      (1-e)*v*(1-e)+(1-e)*(w*(1-e)) := by
    simp only [star_mul,star_sub,star_one,hestar.star_eq,w]
    noncomm_ring
  have hterm1 : ‖(1-e)*v*(1-e)‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖1-e‖*‖v‖*‖1-e‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖v‖*1 := by gcongr
      _ = ‖v‖ := by ring
  have hterm2 : ‖(1-e)*(w*(1-e))‖ < ε/2 := by
    calc
      _ ≤ ‖1-e‖*‖w*(1-e)‖ := norm_mul_le _ _
      _ ≤ 1*‖w*(1-e)‖ := by gcongr
      _ < ε/2 := by simpa using hwe
  calc
    _ ≤ ‖u*(1-e)‖*‖u*(1-e)‖ := mul_self_le_mul_self (norm_nonneg _) hun
    _ = ‖star (u*(1-e))*(u*(1-e))‖ := (CStarRing.norm_star_mul_self (x := u*(1-e))).symm
    _ ≤ ‖(1-e)*v*(1-e)‖+‖(1-e)*(w*(1-e))‖ := by rw [hidentity]; exact norm_add_le _ _
    _ ≤ ‖star (J.quotientMap u)*J.quotientMap u‖+ε := by linarith

instance quotientCStarAlgebra : CStarAlgebra (J.Quotient) where
  norm_mul_self_le := J.quotient_norm_square_le
end CuntzPureness.ClosedStarIdeal

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeMatrixFactorEquiv
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A finite matrix commutant in a type III factor

An isometry onto one diagonal matrix corner identifies the ambient algebra
with the matrix commutant. This also transports the type III predicate.
-/

noncomputable section

namespace Generator.MatrixUnitSystem

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (E : Generator.MatrixUnitSystem ι A) (o : ι) (v : A)
  (hv : star v * v = 1) (hp : v * star v = E.entry o o)

include hv hp

omit [StarModule ℂ A] in
theorem corner_isometry_left : E.entry o o * v = v := by
  rw [← hp,mul_assoc,hv,mul_one]

omit [StarModule ℂ A] in
theorem corner_isometry_right : star v * E.entry o o = star v := by
  rw [← hp,← mul_assoc,hv,one_mul]

def isometricCommutantEquiv : A ≃⋆ₐ[ℂ] E.commutant where
  toFun x := ⟨E.amplify o (v*x*star v),E.amplify_mem o _⟩
  invFun y := star v*y.val*v
  left_inv x := by
    change star v * E.amplify o (v*x*star v) * v = x
    calc
      _ = star v * (E.entry o o * E.amplify o (v*x*star v) * E.entry o o) * v := by
        symm
        calc
          _ = ((star v * E.entry o o) * E.amplify o (v*x*star v)) *
              (E.entry o o * v) := by simp only [mul_assoc]
          _ = _ := by rw [E.corner_isometry_right o v hv hp,E.corner_isometry_left o v hv hp]
      _ = star v * (E.entry o o * (v*x*star v) * E.entry o o) * v := by
        rw [E.amplify_corner]
      _ = x := by
        calc
          _ = (star v * E.entry o o) * (v*x*star v) * (E.entry o o * v) := by
            simp only [mul_assoc]
          _ = star v * (v*x*star v) * v := by
            rw [E.corner_isometry_right o v hv hp,E.corner_isometry_left o v hv hp]
          _ = (star v*v)*x*(star v*v) := by simp only [mul_assoc]
          _ = x := by rw [hv,one_mul,mul_one]
  right_inv y := by
    apply Subtype.ext
    change E.amplify o (v*(star v*y.val*v)*star v) = y.val
    have he : v*(star v*y.val*v)*star v = E.entry o o*y.val := by
      calc
        _ = E.entry o o*y.val*E.entry o o := by simp only [← hp,mul_assoc]
        _ = E.entry o o*(E.entry o o*y.val) := by
          rw [mul_assoc,← (y.property o o).eq]
        _ = E.entry o o*y.val := by
          rw [← mul_assoc,E.mul_entry,ite_eq_left rfl]
    rw [he,E.amplify_compression o y.val y.property]
  map_mul' x y := by
    apply Subtype.ext
    change E.amplify o (v*(x*y)*star v) =
      E.amplify o (v*x*star v)*E.amplify o (v*y*star v)
    rw [E.amplify_mul]
    congr 1
    symm
    calc
      _ = (v*x*star v)*((E.entry o o*v)*y*star v) := by simp only [mul_assoc]
      _ = v*x*(star v*v)*y*star v := by
        rw [E.corner_isometry_left o v hv hp]
        simp only [mul_assoc]
      _ = _ := by rw [hv,mul_one]; simp only [mul_assoc]
  map_add' x y := by
    apply Subtype.ext
    change E.amplify o (v*(x+y)*star v) =
      E.amplify o (v*x*star v) + E.amplify o (v*y*star v)
    simp only [amplify,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' c x := by
    apply Subtype.ext
    change E.amplify o (v*(c • x)*star v) = c • E.amplify o (v*x*star v)
    simp only [amplify,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]
  map_star' x := by
    apply Subtype.ext
    change E.amplify o (v*star x*star v) = star (E.amplify o (v*x*star v))
    rw [E.amplify_star]
    simp only [star_mul,star_star,mul_assoc]

end Generator.MatrixUnitSystem

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_ChallengeDefinitions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
The final claim constructs the tracial quotients and states the original gamma assertion.
`Analysis.TracialSplitting.Challenge.main_iff_original` verifies statement preservation.
-/

universe uA uD uE uI uR uX u v

universe uNuclear

namespace ComparatorModel

section

namespace CurrentMain

open Filter

open scoped Topology NNReal ENNReal

instance boundedFamilyProductCStar {X : Type} {D : Type} [CStarAlgebra D] [Nontrivial D] :
    CStarAlgebra (lp (fun _ : X => D) ∞) where

end CurrentMain

namespace CurrentMain

section

open Filter

open scoped Topology NNReal ENNReal ComplexOrder

section UltraTrace

variable {D : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (U : Ultrafilter X)

instance boundedFamilyProductOrder : PartialOrder (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrder _

instance boundedFamilyProductStarOrdered : StarOrderedRing (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrderedRing _

end UltraTrace

end

open Filter

open scoped Topology NNReal ENNReal ComplexOrder

end CurrentMain

end

end ComparatorModel

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_Model
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD uE uI uR uX

section

namespace CurrentMain

open Filter

open scoped Topology NNReal ENNReal

instance boundedFamilyProductCStar {X : Type uX} {D : Type uD} [CStarAlgebra D] [Nontrivial D] :
    CStarAlgebra (lp (fun _ : X => D) ∞) where

end CurrentMain

namespace CurrentMain

section

open Filter

open scoped Topology NNReal ENNReal ComplexOrder

section UltraTrace

variable {D : Type uD} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (U : Ultrafilter X)

instance boundedFamilyProductOrder : PartialOrder (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrder _

instance boundedFamilyProductStarOrdered : StarOrderedRing (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrderedRing _

end UltraTrace

end

open Filter

open scoped Topology NNReal ENNReal ComplexOrder

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_ScalarCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open scoped ComplexOrder

section ScalarCompression

variable {D : Type uD} [CStarAlgebra D]

structure ProjectionPartition (r : D) where
  Index : Type
  [indexFintype : Fintype Index]
  piece : Index → D
  isProjection : ∀ i, IsStarProjection (piece i)
  nonzero : ∀ i, piece i ≠ 0
  orthogonal : Pairwise (fun i j => piece i * piece j = 0)
  sum_eq : ∑ i, piece i = r

attribute [instance] ProjectionPartition.indexFintype

end ScalarCompression

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_StateExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uB uE

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace CurrentMain

open scoped ComplexOrder ComplexStarModule

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

def selfAdjointFunctionalComplex (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (ℜ a) : ℂ) + Complex.I * (f (ℑ a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add] <;> ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
def selfAdjointEmbedding (ι : A →⋆ₐ[ℂ] B) (hi : Function.Injective ι) :
    selfAdjoint A →ₗᵢ[ℝ] selfAdjoint B where
  toFun a := ⟨ι a,by change star (ι a) = ι a; rw [← map_star,a.property.star_eq]⟩
  map_add' a b := Subtype.ext (map_add ι (a : A) (b : A))
  map_smul' c a := Subtype.ext (by
    change ι (c • (a : A)) = c • ι a
    rw [← Complex.coe_smul, map_smul, Complex.coe_smul])
  norm_map' a := (NonUnitalStarAlgHom.isometry ι hi).norm_map_of_map_zero (map_zero ι) (a : A)

omit [PartialOrder B] [StarOrderedRing B] in
lemma state_realPart_bound (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) (a : selfAdjoint A) :
    |(f a).re| ≤ ‖a‖ := by
  have hu (b : selfAdjoint A) : (f b).re ≤ ‖b‖ := by
    have h := f.apply_le_of_isSelfAdjoint b b.property
    have he : f (algebraMap ℝ A ‖(b : A)‖) = (‖b‖ : ℂ) := by
      rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, hf]
      simp
    rw [he] at h
    exact h.1
  refine abs_le.mpr ⟨?_,hu a⟩
  have h := hu (-a)
  change (f (-(a : A))).re ≤ ‖-a‖ at h
  simp only [map_neg,Complex.neg_re,norm_neg] at h
  linarith

omit [PartialOrder B] [StarOrderedRing B] in
def stateRealLinear (f : A →ₚ[ℂ] ℂ) : selfAdjoint A →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp
    (((f : A →ₗ[ℂ] ℂ).restrictScalars ℝ).comp (selfAdjoint.submodule ℝ A).subtype)

omit [PartialOrder B] [StarOrderedRing B] in
def stateRealContinuous (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : selfAdjoint A →L[ℝ] ℝ :=
  (stateRealLinear f).mkContinuous 1 (fun a => by
    change |(f a).re| ≤ 1 * ‖a‖
    simpa only [one_mul] using state_realPart_bound f hf a)

end CurrentMain

open scoped ComplexOrder InnerProductSpace

end

end OAI
end


