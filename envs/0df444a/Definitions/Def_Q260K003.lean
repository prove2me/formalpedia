-- Prove2me | Definitions.Def_Q260K003
-- name    : Q260K003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:34:08.942021+00:00
-- url     : https://prove2.me/theorems/e8e8d4ee-afdd-45da-8808-bb7f3c08d9c9
-- title:
--   Definitions bundle Q260K003 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 87 declarations of OpenAI's Lean: 27 definitions, 3 inductive types or structures, 4 instances and 53 theorems. The definitions and types are `OAI.KadisonKastler.CStarSimple`, `OAI.KadisonKastler.IsMeasurableOperatorField`, `OAI.KadisonKastler.NonsingularAction`, `OAI.KadisonKastler.NonsingularAction.diagonal`, `OAI.KadisonKastler.NonsingularAction.prod`, `OAI.KadisonKastler.RationalComplexCore`, `OAI.KadisonKastler.RationalComplexCore.extendComplex`, `OAI.KadisonKastler.RationalComplexCore.extendRational`, `OAI.KadisonKastler.RationalComplexCore.mulI`, `OAI.KadisonKastler.RawOperatorField`, `OAI.KadisonKastler.UniformMeasurableOperators`, `OAI.KadisonKastler.WeakOperatorRepresentative`, `OAI.KadisonKastler.WeakOperatorRepresentative.eval`, `OAI.KadisonKastler.WeakOperatorRepresentative.mk`, `OAI.KadisonKastler.WeakOperatorRepresentative.pullback`, `OAI.KadisonKastler.boundaryConstant`, `OAI.KadisonKastler.complexifyRational`, `OAI.KadisonKastler.coreKernelRationalNormedSpace`, `OAI.KadisonKastler.fixedProductLambda`, `OAI.KadisonKastler.matrixSequencesTargetOrder`, `OAI.KadisonKastler.measurableOperatorSubalgebra`, `OAI.KadisonKastler.operatorFieldAERel`, `OAI.KadisonKastler.operatorRepresentativeConst`, `OAI.KadisonKastler.rationalFNormedSpace`, `OAI.KadisonKastler.rawOperatorEval`, `OAI.KadisonKastler.rawOperatorVectorEval`, `OAI.KadisonKastler.weakOperatorRepresentativeOrder`, `OAI.NuclearTrace.rightGNS`, `OAI.NuclearTrace.rightGNSMap`, `OAI.NuclearTrace.rightPreGNS`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_BoundaryBoundedTransport`, `KadisonKastler_BoundaryErgodicReduction`, `KadisonKastler_CoreKernelOperator`, `KadisonKastler_FaithfulTracePullback`, `KadisonKastler_MatrixSequences`, `KadisonKastler_NonsingularBoundary`, `KadisonKastler_PublishedSimpleDerivation`, `KadisonKastler_RationalComplexCore`, `KadisonKastler_RationalCoreExtension`, `KadisonKastler_ScalarMeanCoefficients`, `KadisonKastler_TwoRatioParameters`, `KadisonKastler_UltrafilterDiagonal`, `KadisonKastler_WeakFieldPullback`, `KadisonKastler_WeakOperatorFields`, `TracialSplitting_GNSRepresentations`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `Q260K009`, `Q260K010`, `Q260K011`, `Q260K012`, `Q260K013`, `Q260K014` and `Q260K015`; the statements `OAI_KadisonKastler_FullMatrixCorner_exists_localized_embedding`, `OAI.KadisonKastler.WeakOperatorRepresentative.eval_posPart`, `OAI.KadisonKastler.WeakOperatorRepresentative.ext_eval`, `OAI.KadisonKastler.WeakOperatorRepresentative.selfAdjoint_mem_closed_projection_span`, `OAI_KadisonKastler_antiStar_derivation_inner_of_simple`, `OAI.KadisonKastler.exists_group_representation_of_mean`, `OAI_KadisonKastler_exists_localized_unitary_matrixUnits_embedding`, `OAI.KadisonKastler.exists_product_state_of_commuting_simple`, `OAI.KadisonKastler.exists_simple_spatial_derivation`, `OAI.KadisonKastler.exists_unitary_boundary_intertwiner` and `OAI_KadisonKastler_exists_unitary_embedding_of_invariant_group_in_algebra`; the proof of `OAI.KadisonKastler.exists_simple_spatial_derivation`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
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
import Mathlib.Data.Nat.Find
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded transport fields and the correction step

For an action on a C-star algebra, the transport fields are actual bounded
unitary families.  An equivariant bimodule mean therefore gives the quadratic
step in the complete metric space of unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance boundaryBoundedComplete_rf8f9ca_1 : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe
local instance boundaryBoundedCStar_rf8f9ca_1 : CStarAlgebra (G →ᵇ B) where
local instance boundaryBoundedOrder_rf8f9ca_1 : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryBoundedStarOrder_rf8f9ca_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
/-- Fields independent of the averaged group coordinate. -/
def boundaryConstant : B →⋆ₐ[ℂ] (G →ᵇ B) where
  toFun := BoundedContinuousFunction.const G
  map_one' := by ext t; rfl
  map_mul' _ _ := by ext t; rfl
  map_zero' := by ext t; rfl
  map_add' _ _ := by ext t; rfl
  commutes' _ := by ext t; rfl
  map_star' _ := by ext t; rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NonsingularBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonsingular boundary actions and simultaneous representatives

The action preserves null sets, not necessarily the measure. Countability
allows all the identities used in the boundary argument to hold on one
invariant conull set. The final definition isolates the exact unitary
coefficient property in Björklund, arXiv:1406.0763, Theorem 2.1 and
Remark 2.2, expressed as a property of the unitary coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {G D : Type*} [Group G] [MeasurableSpace D]

/-- A measurable group action preserving the measure class. -/
structure NonsingularAction (G D : Type*) [Group G] [MeasurableSpace D]
    (μ : Measure D) where
  toPerm : G →* Equiv.Perm D
  quasi : ∀ g, Measure.QuasiMeasurePreserving (toPerm g) μ μ

namespace NonsingularAction

variable {μ : Measure D} (α : NonsingularAction G D μ)

@[simp]
theorem one_apply (x : D) : α.toPerm 1 x = x := by
  rw [map_one]
  rfl

@[simp]
theorem mul_apply (g h : G) (x : D) :
    α.toPerm (g * h) x = α.toPerm g (α.toPerm h x) := by
  rw [map_mul]
  rfl

/-- The separate action on the product is again nonsingular. -/
def prod [SFinite μ] : NonsingularAction (G × G) (D × D) (μ.prod μ) where
  toPerm :=
    { toFun := fun g => Equiv.prodCongr (α.toPerm g.1) (α.toPerm g.2)
      map_one' := by ext x <;> simp
      map_mul' g h := by ext x <;> simp }
  quasi g := MeasureTheory.QuasiMeasurePreserving.prodMap (α.quasi g.1) (α.quasi g.2)

@[simp]
theorem prod_apply [SFinite μ] (g : G × G) (x : D × D) :
    α.prod.toPerm g x = (α.toPerm g.1 x.1, α.toPerm g.2 x.2) := rfl

/-- Restricting the separate action to the diagonal. -/
def diagonal [SFinite μ] : NonsingularAction G (D × D) (μ.prod μ) where
  toPerm :=
    { toFun := fun g => α.prod.toPerm (g, g)
      map_one' := by ext x <;> simp
      map_mul' g h := by ext x <;> simp }
  quasi g := α.prod.quasi (g, g)

@[simp]
theorem diagonal_apply [SFinite μ] (g : G) (x : D × D) :
    α.diagonal.toPerm g x = (α.toPerm g x.1, α.toPerm g x.2) := rfl

end NonsingularAction

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryErgodicReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the boundary variables by double ergodicity

The diagonal comparison gives the vector field `L* a Ω`.  Its covariance
is derived from the product intertwiner and the tracial right action.
Double ergodicity is used only for this actual bounded measurable field.
-/

namespace KadisonKastler

universe uG uD uH

open MeasureTheory Filter

noncomputable section

section Measurability

variable {P H : Type*} [MeasurableSpace P] [NormedAddCommGroup H]
  [NormedSpace ℂ H] {μ : Measure P}

/-- Strongly measurable evaluations of an operator field can be applied
to a varying strongly measurable vector. No operator-norm measurability
of the field is required. -/
theorem aestronglyMeasurable_field_apply (T : P → H →L[ℂ] H)
    (hT : ∀ ξ, AEStronglyMeasurable (fun p => T p ξ) μ)
    (v : P → H) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun p => T p (v p)) μ := by
  have haux (w : P → H) (hw : StronglyMeasurable w) :
      AEStronglyMeasurable (fun p => T p (w p)) μ := by
    induction w, hw using StronglyMeasurable.induction with
    | @ind ξ s hs =>
      convert (hT ξ).indicator hs using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      by_cases hp : p ∈ s <;> simp [hp]
    | add hf hg hfg hdisj ihf ihg =>
      convert ihf.add ihg using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      simp only [Pi.add_apply, map_add]
    | lim hf hg ih hlim =>
      exact aestronglyMeasurable_of_tendsto_ae atTop ih
        (Eventually.of_forall fun p => (T p).continuous.tendsto _ |>.comp (hlim p))
  exact (haux (hv.mk v) hv.stronglyMeasurable_mk).congr
    (hv.ae_eq_mk.symm.mono fun p hp => congrArg (T p) hp)

end Measurability

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RationalComplexCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A countable rational core stable under multiplication by i

All coefficient identities can be made simultaneous on this countable
core before bounded maps are extended to the whole Hilbert space.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The canonical rational scalar action inherited from the complex action. -/
instance (priority := 100) rationalCoreModule : Module ℚ H :=
  Module.compHom H (algebraMap ℚ ℂ)

/-- A dense rational subspace on which all complex-linearity tests remain
countable, since multiplication by `i` preserves the subspace. -/
structure RationalComplexCore where
  space : Submodule ℚ H
  countable : Countable space
  dense : Dense (space : Set H)
  mul_I : ∀ x ∈ space, Complex.I • x ∈ space

/-- Every separable complex normed space admits such a core. -/
theorem exists_rationalComplexCore [SeparableSpace H] : Nonempty (RationalComplexCore H) := by
  obtain ⟨v, hv⟩ := exists_dense_seq (α := H)
  let w : Bool × ℕ → H := fun j => if j.1 then Complex.I • v j.2 else v j.2
  let S : Submodule ℚ H := Submodule.span ℚ (Set.range w)
  have hvm (n : ℕ) : v n ∈ S := Submodule.subset_span ⟨(false, n), rfl⟩
  have him (n : ℕ) : Complex.I • v n ∈ S := Submodule.subset_span ⟨(true, n), rfl⟩
  have hI : ∀ x ∈ S, Complex.I • x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨b, n⟩, rfl⟩ := hy
      cases b
      · exact him n
      · have he : Complex.I • (Complex.I • v n) = -(v n) := by
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        change Complex.I • (Complex.I • v n) ∈ S
        rw [he]
        exact S.neg_mem (hvm n)
    | zero => simp only [smul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => simpa only [smul_add] using S.add_mem hx hy
    | smul r x _ hx => simpa only [smul_comm Complex.I r x] using S.smul_mem r hx
  refine ⟨⟨S, inferInstance, ?_, hI⟩⟩
  exact hv.mono (by rintro _ ⟨n, rfl⟩; exact hvm n)

namespace RationalComplexCore

variable {H} (C : RationalComplexCore H)

/-- Multiplication by i as an endomorphism of the countable core. -/
def mulI : C.space →ₗ[ℚ] C.space where
  toFun x := ⟨Complex.I • (x : H), C.mul_I x x.property⟩
  map_add' x y := Subtype.ext (smul_add Complex.I (x : H) (y : H))
  map_smul' r x := Subtype.ext (smul_comm Complex.I r (x : H))

@[simp]
theorem coe_mulI (x : C.space) : (C.mulI x : H) = Complex.I • (x : H) := rfl

end RationalComplexCore

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RationalCoreExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded complex-linear extension from the rational core -/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance rationalHNormedSpace_rf8f9ca_1 : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H
local instance rationalFNormedSpace : NormedSpace ℚ F := NormedSpace.restrictScalars ℚ ℂ F

/-- A continuous rational-linear map commuting with multiplication by i
is complex-linear. Real-linearity follows from continuity. -/
def complexifyRational (f : H →L[ℚ] F)
    (hI : ∀ x, f (Complex.I • x) = Complex.I • f x) : H →L[ℂ] F where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    have hdec (y : H) : c • y = c.re • y + c.im • (Complex.I • y) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    have hdecF (y : F) : c • y = c.re • y + c.im • (Complex.I • y) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    rw [hdec, f.map_add, map_real_smul f f.continuous, map_real_smul f f.continuous, hI,
      ← hdecF]
    rfl
  cont := f.continuous

@[simp]
theorem complexifyRational_apply (f : H →L[ℚ] F) (hI) (x : H) :
    complexifyRational f hI x = f x := rfl

namespace RationalComplexCore

variable [CompleteSpace F]
variable (C : RationalComplexCore H)

local instance rationalHNormedSpace_rf8f9ca_2 : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H
/-- Extend a bounded rational-linear map on the dense core. -/
def extendRational (f : C.space →ₗ[ℚ] F) : H →L[ℚ] F :=
  f.extendOfNorm C.space.subtype

/-- The extension agrees with every core value. -/
theorem extendRational_coe (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖) (x : C.space) :
    C.extendRational f (x : H) = f x :=
  LinearMap.extendOfNorm_eq C.dense.denseRange_val ⟨B, hb⟩ x

/-- The norm bound is unchanged by the dense extension. -/
theorem norm_extendRational_le (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖) (x : H) :
    ‖C.extendRational f x‖ ≤ B * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le C.dense.denseRange_val B hb x

/-- Commutation with i persists from the core to its norm completion. -/
theorem extendRational_mul_I (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖)
    (hI : ∀ x, f (C.mulI x) = Complex.I • f x) (x : H) :
    C.extendRational f (Complex.I • x) = Complex.I • C.extendRational f x := by
  have he : (fun x => C.extendRational f (Complex.I • x)) =
      fun x => Complex.I • C.extendRational f x := by
    have hd : DenseRange ((↑) : C.space → H) := C.dense.denseRange_val
    apply hd.equalizer
    · exact (C.extendRational f).continuous.comp (continuous_const.smul continuous_id)
    · exact continuous_const.smul (C.extendRational f).continuous
    · funext y
      change C.extendRational f ((C.mulI y : C.space) : H) =
        Complex.I • C.extendRational f (y : H)
      rw [C.extendRational_coe f hb, C.extendRational_coe f hb, hI]
  exact congrFun he x

/-- The final complex-linear extension, with no change of bound. -/
def extendComplex (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖)
    (hI : ∀ x, f (C.mulI x) = Complex.I • f x) : H →L[ℂ] F :=
  complexifyRational (C.extendRational f) (C.extendRational_mul_I f hb hI)

@[simp]
theorem extendComplex_coe (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖)
    (hI : ∀ x, f (C.mulI x) = Complex.I • f x) (x : C.space) :
    C.extendComplex f hb hI (x : H) = f x := C.extendRational_coe f hb x

theorem norm_extendComplex_le (f : C.space →ₗ[ℚ] F) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B * ‖(x : H)‖)
    (hI : ∀ x, f (C.mulI x) = Complex.I • f x) (x : H) :
    ‖C.extendComplex f hb hI x‖ ≤ B * ‖x‖ := C.norm_extendRational_le f hb x

end RationalComplexCore

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarMeanCoefficients
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix coefficients of the scalar boundary mean

A uniformly bounded family of weakly measurable operators gives a
sesquilinear family of scalar L-infinity classes. Applying the scalar
conditional expectation preserves its algebraic identities and bounds.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*}
  [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact uniformly bounded measurable family needed for coefficient
averaging. The bound is retained as data to control the output operator. -/
structure UniformMeasurableOperators (G D H : Type*) [MeasurableSpace D]
    (μ : Measure D) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  eval : G → D → H →L[ℂ] H
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ g x, ‖eval g x‖ ≤ bound
  measurable : ∀ g ξ, AEStronglyMeasurable (fun x => eval g x ξ) μ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreKernelOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reconstruction of a bounded operator from a coherent core kernel

Riesz representation first reconstructs the image of every vector in the
countable rational core. The complex-linear extension preserves the bound.
-/

namespace KadisonKastler

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance coreKernelRationalNormedSpace : NormedSpace ℚ H :=
  NormedSpace.restrictScalars ℚ ℂ H

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulTracePullback
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pulling a faithful trace back through an injective star map -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem starAlgHom_codRestrict_surjective (f : A →⋆ₐ[ℂ] B)
    (S : StarSubalgebra ℂ B) (hf : ∀ a, f a ∈ S)
    (hs : ∀ b : B, b ∈ S → ∃ a, f a = b) :
    Function.Surjective (f.codRestrict S hf) := by
  intro b
  obtain ⟨a, ha⟩ := hs b.val b.property
  exact ⟨a, Subtype.ext ha⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixSequences
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrices and bounded sequences

Entrywise evaluation identifies bounded sequences of finite matrices
with finite matrices of bounded sequences. Applying a tracial quotient
to the entries gives the normalized matrix trace formula.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {B C ι : Type*} [CStarAlgebra B] [CStarAlgebra C] [Fintype ι] [DecidableEq ι]

local instance matrixSequencesOrder_rf8f9ca_1 : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixSequencesStarOrder_rf8f9ca_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
local instance matrixSequencesTargetOrder : PartialOrder C := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedSimpleDerivation
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sakai's inner-derivation theorem, in its needed unital form

S. Sakai, *Derivations of simple C*-algebras II*, Bulletin de la Société
Mathématique de France 99 (1971), 259--263, §2, unnumbered theorem on p.260,
together with the unital specialization explained in §1 on p.259.
DOI: 10.24033/bsmf.1719. The only input is innerness of bounded derivations
of a simple unital C-star algebra. Self-adjointness of an implementer is
derived below, not included in that input.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- Simplicity in the C-star sense: there are no proper nonzero closed
two-sided ideals. Nontriviality is supplied separately where used. -/
def CStarSimple (A : Type*) [CStarAlgebra A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioParameters
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
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

def fixedProductLambda : ℝ := Real.exp (-1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UltrafilterDiagonal
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A diagonal index for countably many ultrafilter-large sets -/

namespace KadisonKastler

open Filter

noncomputable section

/-- The index grows along the free ultrafilter, while its corresponding
constraint holds at the chosen coordinate. -/
theorem exists_ultrafilter_diagonal_index (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (A : ℕ → Set ℕ) (hA : ∀ n, A n ∈ ω) :
    ∃ k : ℕ → ℕ, Tendsto k (ω : Filter ℕ) atTop ∧ ∀ᶠ j in (ω : Filter ℕ), j ∈ A (k j) := by
  classical
  let k : ℕ → ℕ := fun j => Nat.findGreatest (fun n => j ∈ A n) j
  refine ⟨k, ?_, ?_⟩
  · apply tendsto_atTop.mpr
    intro n
    filter_upwards [hA n, hω (eventually_ge_atTop n)] with j hj hjn
    exact Nat.le_findGreatest hjn hj
  · filter_upwards [hA 0] with j hj
    exact Nat.findGreatest_spec (P := fun n => j ∈ A n) (Nat.zero_le j) hj

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakOperatorFields
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Essentially bounded weak operator fields

The representatives are bounded operator-valued functions with measurable
evaluations of the function and its adjoint. Their closed C-star algebra
is quotiented by the closed star ideal of almost-everywhere zero fields.
The resulting norm is bounded by every essential operator-norm bound.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The discrete topology is used only to package arbitrary bounded
families; all measurable assertions use the original measure space. -/
abbrev RawOperatorField (D H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :=
  WithDiscreteTopology D →ᵇ (H →L[ℂ] H)

instance rawOperatorFieldCStar : CStarAlgebra (RawOperatorField D H) where

def rawOperatorEval (F : RawOperatorField D H) (x : D) : H →L[ℂ] H :=
  F (WithTopology.toTopology ⊥ x)

@[simp]
theorem rawOperatorEval_zero (x : D) : rawOperatorEval (0 : RawOperatorField D H) x = 0 := rfl

@[simp]
theorem rawOperatorEval_one (x : D) : rawOperatorEval (1 : RawOperatorField D H) x = 1 := rfl

@[simp]
theorem rawOperatorEval_add (F G : RawOperatorField D H) (x : D) :
    rawOperatorEval (F + G) x = rawOperatorEval F x + rawOperatorEval G x := rfl

@[simp]
theorem rawOperatorEval_mul (F G : RawOperatorField D H) (x : D) :
    rawOperatorEval (F * G) x = rawOperatorEval F x * rawOperatorEval G x := rfl

@[simp]
theorem rawOperatorEval_smul (c : ℂ) (F : RawOperatorField D H) (x : D) :
    rawOperatorEval (c • F) x = c • rawOperatorEval F x := rfl

@[simp]
theorem rawOperatorEval_star (F : RawOperatorField D H) (x : D) :
    rawOperatorEval (star F) x = star (rawOperatorEval F x) := rfl

theorem rawOperatorEval_continuous (x : D) :
    Continuous (fun F : RawOperatorField D H => rawOperatorEval F x) :=
  (BoundedContinuousFunction.evalCLM ℂ (WithTopology.toTopology ⊥ x)).continuous

def rawOperatorVectorEval (x : D) (ξ : H) : RawOperatorField D H →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).comp
    (BoundedContinuousFunction.evalCLM ℂ (WithTopology.toTopology ⊥ x))

@[simp]
theorem rawOperatorVectorEval_apply (x : D) (ξ : H) (F : RawOperatorField D H) :
    rawOperatorVectorEval x ξ F = rawOperatorEval F x ξ := rfl

variable [MeasurableSpace D] (μ : Measure D)

def IsMeasurableOperatorField (F : RawOperatorField D H) : Prop :=
  ∀ ξ : H,
    AEStronglyMeasurable (fun x => rawOperatorEval F x ξ) μ ∧
    AEStronglyMeasurable (fun x => star (rawOperatorEval F x) ξ) μ

/-- Measurable operator fields form a star subalgebra. -/
def measurableOperatorSubalgebra : StarSubalgebra ℂ (RawOperatorField D H) where
  carrier := IsMeasurableOperatorField μ
  zero_mem' := by
    intro ξ
    constructor <;> simpa using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : D => (0 : H)) μ)
  one_mem' := by
    intro ξ
    constructor <;> simpa using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : D => ξ) μ)
  add_mem' {F G} hF hG := by
    intro ξ
    constructor
    · convert (hF ξ).1.add (hG ξ).1 using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      simp only [rawOperatorEval_add, add_apply, Pi.add_apply]
    · convert (hF ξ).2.add (hG ξ).2 using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      simp only [rawOperatorEval_add, star_add, add_apply, Pi.add_apply]
  mul_mem' {F G} hF hG := by
    intro ξ
    constructor
    · exact aestronglyMeasurable_field_apply (rawOperatorEval F) (fun η => (hF η).1)
        (fun x => rawOperatorEval G x ξ) (hG ξ).1
    · simpa only [rawOperatorEval_mul, star_mul, mul_apply_eq_comp] using
        aestronglyMeasurable_field_apply (fun x => star (rawOperatorEval G x))
          (fun η => (hG η).2) (fun x => star (rawOperatorEval F x) ξ) (hF ξ).2
  algebraMap_mem' c := by
    intro ξ
    constructor
    · change AEStronglyMeasurable (fun _ : D => (algebraMap ℂ (H →L[ℂ] H) c) ξ) μ
      exact aestronglyMeasurable_const
    · change AEStronglyMeasurable (fun _ : D => star (algebraMap ℂ (H →L[ℂ] H) c) ξ) μ
      exact aestronglyMeasurable_const
  star_mem' {F} hF := by
    intro ξ
    simpa only [rawOperatorEval_star, star_star] using And.intro (hF ξ).2 (hF ξ).1

/-- The measurability condition is preserved by operator-norm limits. -/
instance measurableOperatorSubalgebra_closed :
    IsClosed (measurableOperatorSubalgebra (H := H) μ : Set (RawOperatorField D H)) := by
  apply IsSeqClosed.isClosed
  intro F G hF hG ξ
  constructor
  · exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n ξ).1)
      (Eventually.of_forall fun x =>
        ((rawOperatorVectorEval x ξ).continuous.tendsto G).comp hG)
  · exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n ξ).2)
      (Eventually.of_forall fun x =>
        ((rawOperatorVectorEval x ξ).continuous.tendsto (star G)).comp
          ((continuous_star.tendsto G).comp hG))

abbrev WeakOperatorRepresentative : Type _ := measurableOperatorSubalgebra (H := H) μ

instance weakOperatorRepresentativeCStar :
    CStarAlgebra (WeakOperatorRepresentative (H := H) μ) := inferInstance

namespace WeakOperatorRepresentative

variable {μ}

def eval (F : WeakOperatorRepresentative (H := H) μ) (x : D) : H →L[ℂ] H :=
  rawOperatorEval F.val x

@[simp]
theorem eval_zero (x : D) : eval (0 : WeakOperatorRepresentative (H := H) μ) x = 0 := rfl

@[simp]
theorem eval_one (x : D) : eval (1 : WeakOperatorRepresentative (H := H) μ) x = 1 := rfl

@[simp]
theorem eval_add (F G : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (F + G) x = eval F x + eval G x := rfl

@[simp]
theorem eval_mul (F G : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (F * G) x = eval F x * eval G x := rfl

@[simp]
theorem eval_sub (F G : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (F - G) x = eval F x - eval G x := rfl

@[simp]
theorem eval_neg (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (-F) x = -eval F x := rfl

@[simp]
theorem eval_smul (c : ℂ) (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (c • F) x = c • eval F x := rfl

@[simp]
theorem eval_star (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (star F) x = star (eval F x) := rfl

theorem eval_aestronglyMeasurable (F : WeakOperatorRepresentative (H := H) μ) (ξ : H) :
    AEStronglyMeasurable (fun x => eval F x ξ) μ := (F.property ξ).1

theorem star_eval_aestronglyMeasurable (F : WeakOperatorRepresentative (H := H) μ) (ξ : H) :
    AEStronglyMeasurable (fun x => star (eval F x) ξ) μ := (F.property ξ).2

theorem eval_norm_le (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    ‖eval F x‖ ≤ ‖F‖ := F.val.norm_coe_le_norm _

theorem eval_continuous (x : D) :
    Continuous (fun F : WeakOperatorRepresentative (H := H) μ => eval F x) :=
  (rawOperatorEval_continuous x).comp continuous_subtype_val

/-- Bundle any uniformly bounded measurable operator field. -/
def mk (f : D → H →L[ℂ] H) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hf : ∀ ξ, AEStronglyMeasurable (fun x => f x ξ) μ)
    (hfstar : ∀ ξ, AEStronglyMeasurable (fun x => star (f x) ξ) μ) :
    WeakOperatorRepresentative (H := H) μ :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x : WithDiscreteTopology D => f x.ofTopology) C (fun x => hC x.ofTopology),
    fun ξ => ⟨hf ξ, hfstar ξ⟩⟩

@[simp]
theorem eval_mk (f : D → H →L[ℂ] H) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hf : ∀ ξ, AEStronglyMeasurable (fun x => f x ξ) μ)
    (hfstar : ∀ ξ, AEStronglyMeasurable (fun x => star (f x) ξ) μ) (x : D) :
    eval (mk f C hC hf hfstar) x = f x := rfl

theorem norm_mk_le (f : D → H →L[ℂ] H) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C)
    (hf : ∀ ξ, AEStronglyMeasurable (fun x => f x ξ) μ)
    (hfstar : ∀ ξ, AEStronglyMeasurable (fun x => star (f x) ξ) μ) :
    ‖mk f C hC hf hfstar‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC0).mpr (fun x => hC x.ofTopology)

end WeakOperatorRepresentative

/-- Constant operators as measurable fields. -/
def operatorRepresentativeConst : (H →L[ℂ] H) →⋆ₐ[ℂ] WeakOperatorRepresentative (H := H) μ where
  toFun T := ⟨BoundedContinuousFunction.const _ T, by
    intro ξ
    constructor
    · change AEStronglyMeasurable (fun _ : D => T ξ) μ
      exact aestronglyMeasurable_const
    · change AEStronglyMeasurable (fun _ : D => star T ξ) μ
      exact aestronglyMeasurable_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem operatorRepresentativeConst_eval (T : H →L[ℂ] H) (x : D) :
    WeakOperatorRepresentative.eval (operatorRepresentativeConst μ T) x = T := rfl

/-- Equality almost everywhere is an algebra congruence. -/
def operatorFieldAERel : RingCon (WeakOperatorRepresentative (H := H) μ) where
  r F G := WeakOperatorRepresentative.eval F =ᵐ[μ] WeakOperatorRepresentative.eval G
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl, fun h => h.symm, fun h k => h.trans k⟩
  add' h k := h.add k
  mul' h k := h.mul k

local instance weakOperatorRepresentativeOrder :
    PartialOrder (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrder _
local instance weakOperatorRepresentativeStarOrder :
    StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonsingular pullback of weak operator fields

Composition preserves the measurable representatives and their uniform
bound. Nonsingularity makes the construction independent of representatives.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

theorem eq_of_eval {F G : WeakOperatorRepresentative (H := H) μ}
    (h : ∀ x, eval F x = eval G x) : F = G := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact h x.ofTopology

/-- Pullback of bounded measurable representatives by a nonsingular map. -/
def pullback (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ) :
    WeakOperatorRepresentative (H := H) μ →⋆ₐ[ℂ]
      WeakOperatorRepresentative (H := H) μ where
  toFun F := mk (fun x => eval F (T x)) ‖F‖ (fun x => eval_norm_le F (T x))
    (fun ξ => (eval_aestronglyMeasurable F ξ).comp_quasiMeasurePreserving hT)
    (fun ξ => (star_eval_aestronglyMeasurable F ξ).comp_quasiMeasurePreserving hT)
  map_one' := by apply eq_of_eval; intro x; rfl
  map_mul' F G := by apply eq_of_eval; intro x; rfl
  map_zero' := by apply eq_of_eval; intro x; rfl
  map_add' F G := by apply eq_of_eval; intro x; rfl
  commutes' c := by apply eq_of_eval; intro x; rfl
  map_star' F := by apply eq_of_eval; intro x; rfl

@[simp]
theorem eval_pullback (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    eval (pullback T hT F) x = eval F (T x) := rfl

theorem pullback_congr_ae (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    {F G : WeakOperatorRepresentative (H := H) μ} (hFG : eval F =ᵐ[μ] eval G) :
    eval (pullback T hT F) =ᵐ[μ] eval (pullback T hT G) :=
  hT.ae hFG

@[simp]
theorem pullback_constant (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (A : H →L[ℂ] H) :
    pullback T hT (operatorRepresentativeConst μ A) = operatorRepresentativeConst μ A := by
  apply eq_of_eval
  intro x
  rfl

@[simp]
theorem pullback_id (F : WeakOperatorRepresentative (H := H) μ) :
    pullback id (Measure.QuasiMeasurePreserving.id μ) F = F := by
  apply eq_of_eval
  intro x
  rfl

theorem pullback_comp (T S : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) :
    pullback S hS (pullback T hT F) = pullback (T ∘ S) (hT.comp hS) F := by
  apply eq_of_eval
  intro x
  rfl

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_GNSRepresentations
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uE uH uN


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace NuclearTrace

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a*b) = f (b*a))

include ht in
lemma norm_preGNS_star (a : A) : ‖f.toPreGNS (star a)‖ = ‖f.toPreGNS a‖ := by
  rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
  rw [ht]

include ht in
lemma right_preGNS_norm (a : A) (x : f.PreGNS) :
    ‖f.toPreGNS (f.ofPreGNS x*a)‖ ≤ ‖a‖*‖x‖ := by
  rw [← norm_preGNS_star f ht]
  simp only [star_mul]
  have h := (f.leftMulMapPreGNS (star a)).le_opNorm
    (f.toPreGNS (star (f.ofPreGNS x)))
  have hb : ‖f.leftMulMapPreGNS (star a)‖ ≤ ‖star a‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  apply h.trans
  rw [norm_star] at hb
  rw [norm_preGNS_star f ht, PositiveLinearMap.toPreGNS_ofPreGNS]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

def rightPreGNS (a : A) : f.PreGNS →L[ℂ] f.PreGNS :=
  (f.toPreGNS.toLinearMap.comp ((LinearMap.mulRight ℂ a).comp f.ofPreGNS.toLinearMap)).mkContinuous
    ‖a‖ (right_preGNS_norm f ht a)

@[simp] lemma rightPreGNS_apply (a : A) (x : f.PreGNS) :
    rightPreGNS f ht a x = f.toPreGNS (f.ofPreGNS x*a) := rfl

def rightGNSMap (a : A) : f.GNS →L[ℂ] f.GNS := (rightPreGNS f ht a).completion

@[simp] lemma rightGNSMap_coe (a : A) (x : f.PreGNS) :
    rightGNSMap f ht a (x : f.GNS) = (rightPreGNS f ht a x : f.GNS) :=
  ContinuousLinearMap.completion_apply_coe (rightPreGNS f ht a) x

lemma rightGNSMap_mul (a b : A) :
    rightGNSMap f ht (a*b) = rightGNSMap f ht b * rightGNSMap f ht a := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using induction_on with
  | hp => exact isClosed_eq (map_continuous _) (map_continuous _)
  | ih x => simp [rightPreGNS_apply,mul_assoc]

lemma rightGNSMap_star (a : A) : rightGNSMap f ht (star a) = star (rightGNSMap f ht a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    simp only [rightGNSMap_coe,UniformSpace.Completion.inner_coe,
      PositiveLinearMap.preGNS_inner_def,rightPreGNS_apply,
      PositiveLinearMap.ofPreGNS_toPreGNS,star_mul,star_star]
    simpa only [mul_assoc] using ht a (star (f.ofPreGNS x) * f.ofPreGNS y)

def rightGNS : Aᵐᵒᵖ →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  toFun a := rightGNSMap f ht a.unop
  map_one' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (map_continuous _) continuous_id
    | ih x => simp
  map_mul' a b := rightGNSMap_mul f ht b.unop a.unop
  map_zero' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (map_continuous _) continuous_const
    | ih x => simp [UniformSpace.Completion.coe_zero]
  map_add' a b := by
    ext x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [mul_add,map_add,UniformSpace.Completion.coe_add]
  commutes' c := by
    ext x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      simp [Algebra.algebraMap_eq_smul_one,UniformSpace.Completion.coe_smul]
  map_star' a := rightGNSMap_star f ht a.unop

@[simp] lemma rightGNS_coe (a : Aᵐᵒᵖ) (x : f.PreGNS) :
    rightGNS f ht a (x : f.GNS) = (f.toPreGNS (f.ofPreGNS x*a.unop) : f.GNS) :=
  rightGNSMap_coe f ht a.unop x

lemma left_right_commute (a : A) (b : Aᵐᵒᵖ) :
    Commute (f.gnsStarAlgHom a) (rightGNS f ht b) := by
  change f.gnsStarAlgHom a * rightGNS f ht b = rightGNS f ht b * f.gnsStarAlgHom a
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (map_continuous _) (map_continuous _)
  | ih x =>
    simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS,mul_assoc]

end NuclearTrace

end

end

end

end OAI
end


