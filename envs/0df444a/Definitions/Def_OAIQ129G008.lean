-- Prove2me | Definitions.Def_OAIQ129G008
-- name    : OAIQ129G008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:30:13.315997+00:00
-- url     : https://prove2.me/theorems/45e973fb-f265-4ffd-8ada-3dd40723e478
-- title:
--   Definitions bundle OAIQ129G008 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 84 declarations of OpenAI's Lean: 19 definitions, 1 inductive type or structure, 4 instances and 60 theorems. The definitions and types are `OAI.Generator.FiniteMatrixStage.commutant`, `OAI.Generator.Tracial.Q`, `OAI.Generator.Tracial.TraceOrthogonal`, `OAI.Generator.Tracial.TraceUnitary`, `OAI.Generator.Tracial.TraceUnitary.algebra`, `OAI.Generator.Tracial.TraceUnitary.vector`, `OAI.Generator.Tracial.baseVector`, `OAI.Generator.Tracial.boundedPartialSupport`, `OAI.Generator.Tracial.cyclicCoefficient`, `OAI.Generator.Tracial.cyclicPredual`, `OAI.Generator.Tracial.cyclicPredualEvaluation`, `OAI.Generator.Tracial.instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.quotientInclusion`, `OAI.Generator.Tracial.selfAdjointTraceBall`, `OAI.Generator.Tracial.traceCyclicHom`, `OAI.Generator.Tracial.traceCyclicLinearIsometry`, `OAI.Generator.Tracial.traceCyclicOperator`, `OAI.Generator.Tracial.traceCyclicSpace`, `OAI.Generator.Tracial.traceCyclicVector`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_CornerTrace`, `FactorGeneration_CyclicPredual`, `FactorGeneration_Dimension`, `FactorGeneration_Expectations`, `FactorGeneration_GroupTrace`, `FactorGeneration_HaarPatches`, `FactorGeneration_HilbertLimits`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixSequence`, `FactorGeneration_NormalDimension`, `FactorGeneration_NormalTrace`, `FactorGeneration_Pinching`, `FactorGeneration_QuotientHilbert`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralDimension`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Subfactors`, `FactorGeneration_TraceTopology`, `FactorGeneration_TracialInclusion`, `FactorGeneration_Ultrapower`, `FactorGeneration_UnitaryMetric`.
--
--   **Imports.** It imports the bundles `OAIQ129G003`, `OAIQ129G004` and `OAIQ129G005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G010`, `OAIQ129G011` and `OAIQ129G012`; the statements `OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1_q129`, `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget_q129`, `OAI.Generator.Tracial.exists_finite_partial_independence_q129`, `OAI.Generator.Tracial.represented_four_selfAdjoint_generators_q129`, `OAI.Generator.Tracial.represented_relative_generation_q129` and `OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129`; the proofs of `OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits_q129`, `OAI.Generator.Tracial.predual_small_of_small_trace_sandwich_q129` and `OAI.Generator.Tracial.representedCorner_factor_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ129G003
import Definitions.Def_OAIQ129G004
import Definitions.Def_OAIQ129G005

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Algebra _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Semiring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_smul (c : ℂ) (T : Algebra (M := M)) : τ.norm₂ (c • T) = ‖c‖*τ.norm₂ T :=
  norm_smul _ _

theorem norm₂_eq_zero_iff (T : Algebra (M := M)) : τ.norm₂ T = 0 ↔ T = 0 := by
  constructor
  · intro h
    exact τ.separating T (norm_eq_zero.mp h)
  · rintro rfl
    exact τ.norm₂_zero

end TracialRepresentation

end

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

instance (priority := high) q129Mul : Mul (TracialQuotient τ l) := inferInstance
instance (priority := high) q129Add : Add (TracialQuotient τ l) := inferInstance
instance (priority := high) q129SMul : SMul ℂ (TracialQuotient τ l) := inferInstance

end

open Filter
open scoped Topology

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem bounded_trace_limit (a : ℕ → M.toStarSubalgebra) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C) (ξ : H)
    (hξ : Tendsto (fun n => (a n : H →L[ℂ] H) τ.vector) atTop (𝓝 ξ)) :
    ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧ (b : H →L[ℂ] H) τ.vector = ξ := by
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T, hT, ht⟩ := exists_weak_operator_ultralimit ω
    (fun n => (a n : H →L[ℂ] H)) C hC ha
  refine ⟨⟨T, weak_operator_limit_mem M a T ht⟩, hT, ?_⟩
  apply ext_inner_left ℂ
  intro y
  exact tendsto_nhds_unique (ht τ.vector y)
    ((continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (hξ.mono_left (Ultrafilter.of_le atTop)))

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

def baseVector : M.toStarSubalgebra →ₗ[ℂ] H where
  toFun a := (a : H →L[ℂ] H) τ.vector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator.Tracial

/-! The restricted faithful trace and the actual P^omega -> M^omega
inclusion. All constructions are on the bounded-sequence quotient. -/
noncomputable section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

def quotientInclusion (l : Filter ℕ) :
    TracialQuotient (restrictedTrace τ hPM) l →⋆ₐ[ℂ] TracialQuotient τ l where
  toFun := Quotient.map (boundedInclusion hPM) (fun _ _ h => h)
  map_one' := rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl
  map_zero' := rfl
  map_add' a b := by
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl
  commutes' _ := rfl
  map_star' a := by induction a using Quotient.inductionOn with | h a => rfl

@[simp] theorem quotientInclusion_mk (l : Filter ℕ) (a : Bounded P) :
    quotientInclusion τ hPM l (quotientMap (restrictedTrace τ hPM) l a) =
      quotientMap τ l (boundedInclusion hPM a) := rfl

@[simp] theorem quotientInclusion_trace (ω : Ultrafilter ℕ)
    (a : TracialQuotient (restrictedTrace τ hPM) (ω : Filter ℕ)) :
    quotientTrace τ ω (quotientInclusion τ hPM (ω : Filter ℕ) a) =
      quotientTrace (restrictedTrace τ hPM) ω a := by
  induction a using Quotient.inductionOn with
  | h a =>
    change traceRep τ ω (boundedInclusion hPM a) = traceRep (restrictedTrace τ hPM) ω a
    exact tendsto_nhds_unique (traceRep_tendsto τ ω (boundedInclusion hPM a))
      (traceRep_tendsto (restrictedTrace τ hPM) ω a)

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem cornerTrace_add (x y : M.toStarSubalgebra) :
    τ.trace (x+y) = τ.trace x + τ.trace y := inner_add_right _ _ _

theorem trace_sub (x y : M.toStarSubalgebra) :
    τ.trace (x-y) = τ.trace x - τ.trace y := inner_sub_right _ _ _

theorem cornerTrace_smul (c : ℂ) (x : M.toStarSubalgebra) :
    τ.trace (c • x) = c * τ.trace x := inner_smul_right _ _ _

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (τ : TracialRepresentation M)

theorem trace_nonneg_of_nonneg (a : M.toStarSubalgebra) (ha : 0 ≤ a) :
    0 ≤ (τ.trace a).re := by
  have hs := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have h := congrArg Complex.re (τ.trace_star_mul (CFC.sqrt a))
  rw [hs,CFC.sqrt_mul_sqrt_self a ha] at h
  rw [h]
  simp only [← Complex.ofReal_pow,Complex.ofReal_re]
  positivity

end

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/
namespace Tracial
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem tendsto_vector_iff_norm₂ {I : Type*} (l : Filter I)
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra) :
    Tendsto (fun i => (a i : H →L[ℂ] H) τ.vector) l (𝓝 ((b : H →L[ℂ] H) τ.vector)) ↔
    Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0) := by
  simpa only [dist_eq_norm,TracialRepresentation.norm₂_sub] using
    (tendsto_iff_dist_tendsto_zero (f := fun i => (a i : H →L[ℂ] H) τ.vector)
      (a := (b : H →L[ℂ] H) τ.vector))

theorem norm₂_limit_unique {I : Type*} {l : Filter I} [l.NeBot]
    (a : I → M.toStarSubalgebra) {b c : M.toStarSubalgebra}
    (hb : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0))
    (hc : Tendsto (fun i => τ.norm₂ (a i-c)) l (𝓝 0)) : b=c := by
  have he := tendsto_nhds_unique ((tendsto_vector_iff_norm₂ τ l a b).mpr hb)
    ((tendsto_vector_iff_norm₂ τ l a c).mpr hc)
  apply sub_eq_zero.mp
  apply τ.separating
  change (b : H →L[ℂ] H) τ.vector-(c : H →L[ℂ] H) τ.vector=0
  exact sub_eq_zero.mpr he

theorem norm₂_limit_star {I : Type*} {l : Filter I} (a : I → M.toStarSubalgebra)
    (b : M.toStarSubalgebra) (h : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    Tendsto (fun i => τ.norm₂ (star (a i)-star b)) l (𝓝 0) := by
  simpa only [← star_sub,τ.norm₂_star] using h

end Tracial

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_CyclicPredual
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

/-! Evaluation surjectivity for any subspace of bounded-unit-ball WOT-continuous
functionals. Compactness and Hahn--Banach supply actual algebra elements. -/
open Filter
open scoped Topology

/-! Exact characterization of the cyclic predual by WOT continuity on the
unit ball. No continuity of an arbitrary given-predual evaluation is assumed
or asserted here. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

theorem dyadicWeight_univ (n : ℕ) : dyadicWeight n Finset.univ=1 := by
  unfold dyadicWeight
  rw [Finset.card_univ,card_dyadicIndex,Nat.cast_pow,Nat.cast_ofNat]
  exact div_self (ne_of_gt (pow_pos (by norm_num : (0 : ℝ)<2) n))

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

theorem traceFreeDyadicSup_self (p : AlgebraProjection M) :
    traceFreeDyadicSup hfactor hdiff p p=1 := by
  apply le_antisymm (traceFreeDyadicSup_le_one hfactor hdiff p p)
  rw [← dyadicWeight_univ 0]
  apply traceFreeDyadicSup_lower_bound hfactor hdiff p p 0 Finset.univ
  rw [EquivalentPartition.subset_univ]
  exact AlgebraProjection.subequivalent_refl p

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
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_subequivalent {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDimension hfactor hdiff q ≤ traceFreeDimension hfactor hdiff r :=
  traceFreeDyadicSup_mono hfactor hdiff _ h

theorem traceFreeDimension_mono : Monotone (traceFreeDimension hfactor hdiff) :=
  fun _ _ h => traceFreeDimension_subequivalent hfactor hdiff
    (AlgebraProjection.subequivalent_of_le h)

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

theorem norm₂_sq_trace (x : M.toStarSubalgebra) :
    τ.norm₂ x ^ 2 = (τ.trace (star x*x)).re := by
  rw [τ.trace_star_mul, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem baseVector_inner_trace (x y : M.toStarSubalgebra) :
    inner ℂ (baseVector τ x) (baseVector τ y) = τ.trace (star x*y) := by
  change inner ℂ ((x : H →L[ℂ] H) τ.vector) ((y : H →L[ℂ] H) τ.vector) = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rfl

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_UnitaryMetric
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Bounded self-adjoint least-distance elements in a von Neumann subalgebra. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def selfAdjointTraceBall (τ : TracialRepresentation N) (R : ℝ) : Set H :=
  {ξ | ∃ a : N.toStarSubalgebra, IsSelfAdjoint a ∧ ‖a‖ ≤ R ∧ baseVector τ a=ξ}

theorem selfAdjointTraceBall_closed (τ : TracialRepresentation N) (R : ℝ) :
    IsClosed (selfAdjointTraceBall τ R) := by
  apply IsSeqClosed.isClosed
  intro ξ z hz hlim
  choose a ha hR he using hz
  have hlimA : Tendsto (fun n => baseVector τ (a n)) atTop (𝓝 z) := by
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    exact funext he
  obtain ⟨b,hb,hbz⟩ := bounded_trace_limit τ a R ((norm_nonneg _).trans (hR 0)) hR z
    hlimA
  have hvec : Tendsto (fun n => (a n : H →L[ℂ] H) τ.vector) atTop
      (𝓝 ((b : H →L[ℂ] H) τ.vector)) := by rw [hbz]; exact hlimA
  have h := (tendsto_vector_iff_norm₂ τ atTop a b).mp hvec
  have hs := norm₂_limit_star τ a b h
  simp only [(ha _).star_eq] at hs
  have hsb : star b=b := norm₂_limit_unique τ a hs h
  exact ⟨b,hsb,hb,hbz⟩

theorem selfAdjointTraceBall_convex (τ : TracialRepresentation N) (R : ℝ) :
    Convex ℝ (selfAdjointTraceBall τ R) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨a,ha,hRa,rfl⟩ := hx
  obtain ⟨b,hb,hRb,rfl⟩ := hy
  refine ⟨s • a+t • b,((IsSelfAdjoint.all s).smul ha).add
    ((IsSelfAdjoint.all t).smul hb),?_,rfl⟩
  calc ‖s • a+t • b‖ ≤ ‖s • a‖+‖t • b‖ := norm_add_le _ _
       _ = s*‖a‖+t*‖b‖ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg hs,Real.norm_of_nonneg ht]
       _ ≤ s*R+t*R := add_le_add (mul_le_mul_of_nonneg_left hRa hs)
          (mul_le_mul_of_nonneg_left hRb ht)
       _ = R := by rw [← add_mul,hst,one_mul]

theorem exists_selfAdjoint_ball_variational (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : N.toStarSubalgebra, IsSelfAdjoint c ∧ ‖c‖ ≤ R ∧
      (∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
        τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) ∧
      ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
        (inner ℂ (baseVector τ (x-coordinateInclusion hNM c))
          (baseVector τ (coordinateInclusion hNM (a-c)))).re ≤ 0 := by
  let τN := restrictedTrace τ hNM
  let K := selfAdjointTraceBall τN R
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨ξ,hξ,hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (show K.Nonempty from ⟨0,0,IsSelfAdjoint.zero _,by simpa using hR,rfl⟩)
    (selfAdjointTraceBall_closed τN R).isComplete (selfAdjointTraceBall_convex τN R)
    (baseVector τ x)
  obtain ⟨c,hc,hRc,rfl⟩ := hξ
  refine ⟨c,hc,hRc,?_,?_⟩
  · intro a ha hRa
    have h := ciInf_le (show BddBelow (Set.range (fun w : K => ‖baseVector τ x-w.val‖)) from
      ⟨0,by rintro _ ⟨w,rfl⟩; exact norm_nonneg _⟩)
      (⟨baseVector τN a,a,ha,hRa,rfl⟩ : K)
    rw [← hmin] at h
    exact h
  · intro a ha hRa
    have h := (norm_eq_iInf_iff_real_inner_le_zero (selfAdjointTraceBall_convex τN R)
      (show baseVector τN c ∈ K from ⟨c,hc,hRc,rfl⟩)).mp hmin
      (baseVector τN a) ⟨a,ha,hRa,rfl⟩
    exact h

end

/-! Countable determination of a relative commutant from actual L2
separability. Operator norm separability is not required. -/

/-! The unitary metric induced by a faithful trace vector, distinguishing the trace two-norm topology from the operator norm topology. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

structure TraceUnitary (τ : TracialRepresentation M) where
  toUnitary : unitary M.toStarSubalgebra

namespace TraceUnitary

def algebra (u : TraceUnitary τ) : M.toStarSubalgebra := u.toUnitary

def vector (u : TraceUnitary τ) : H := (u.algebra τ).val τ.vector

theorem vector_injective : Function.Injective (vector τ) := by
  intro u v h
  have he : u.algebra τ = v.algebra τ := by
    apply sub_eq_zero.mp
    apply τ.separating
    exact sub_eq_zero.mpr h
  cases u
  cases v
  congr 1
  exact Subtype.ext he

instance instMetricSpace : MetricSpace (TraceUnitary τ) :=
  MetricSpace.induced (vector τ) (vector_injective τ) inferInstance

@[simp] theorem dist_eq (u v : TraceUnitary τ) :
    dist u v = τ.norm₂ (u.algebra τ-v.algebra τ) := by
  change dist (vector τ u) (vector τ v) = _
  rw [dist_eq_norm]
  rfl

end TraceUnitary

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.tracePairingCStar
attribute [local instance] OAI.Generator.Tracial.tracePairingOrder
attribute [local instance] OAI.Generator.Tracial.tracePairingPreorder
attribute [local instance] OAI.Generator.Tracial.tracePairingLE
attribute [local instance] OAI.Generator.Tracial.tracePairingStarOrder
theorem trace_mul_nonneg (a b : M.toStarSubalgebra) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (τ.trace (a*b)).re := by
  let s := CFC.sqrt a
  have hs : star s=s := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have h := trace_nonneg_of_nonneg τ (star s*b*s) (star_left_conjugate_nonneg hb s)
  rw [hs,τ.trace_mul_comm (s*b) s,← mul_assoc,CFC.sqrt_mul_sqrt_self a ha] at h
  exact h

theorem trace_mul_mono (a b c : M.toStarSubalgebra) (ha : 0 ≤ a) (hbc : b ≤ c) :
    (τ.trace (a*b)).re ≤ (τ.trace (a*c)).re := by
  have h := trace_mul_nonneg τ a (c-b) ha (sub_nonneg.mpr hbc)
  rw [mul_sub,trace_sub,Complex.sub_re] at h
  linarith

theorem trace_mul_le_norm (a x : M.toStarSubalgebra) (ha : 0 ≤ a)
    (hx : IsSelfAdjoint x) :
    (τ.trace (a*x)).re ≤ ‖x‖ * (τ.trace a).re := by
  have h := trace_mul_mono τ a x (algebraMap ℝ M.toStarSubalgebra ‖x‖) ha
    hx.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,← Complex.coe_smul,
    cornerTrace_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  exact h

theorem norm₂_sub_sq (x y : M.toStarSubalgebra) :
    τ.norm₂ (x-y)^2 = τ.norm₂ x^2 + τ.norm₂ y^2 -
      2*(τ.trace (star x*y)).re := by
  have h := norm_sub_sq (𝕜 := ℂ) (baseVector τ x) (baseVector τ y)
  rw [← map_sub,baseVector_inner_trace] at h
  change τ.norm₂ (x-y)^2 = τ.norm₂ x^2 - 2*(τ.trace (star x*y)).re + τ.norm₂ y^2 at h
  linarith

end

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.truncationCStar
attribute [local instance] OAI.Generator.Tracial.truncationOrder
attribute [local instance] OAI.Generator.Tracial.truncationLE
attribute [local instance] OAI.Generator.Tracial.truncationStarOrder
theorem upperTruncate_distance (τ : TracialRepresentation M)
    (a x : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hx : IsSelfAdjoint x) :
    τ.norm₂ (upperTruncate a ‖x‖-x)^2 +
      τ.norm₂ ((a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)^2 ≤ τ.norm₂ (a-x)^2 := by
  let d := (a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺
  let z := upperTruncate a ‖x‖
  have hd : 0 ≤ d := CFC.posPart_nonneg _
  have had : a=z+d := by dsimp [z,d,upperTruncate]; abel
  have hdz : d*z=‖x‖ • d := upperTruncate_discard_mul a ha ‖x‖
  have ht := trace_mul_le_norm τ d x hd hx
  have hsq := norm₂_sub_sq τ (a-x) d
  have hid : a-x-d=z-x := by rw [had]; abel
  rw [hid,(ha.sub hx).star_eq,τ.trace_mul_comm (a-x) d] at hsq
  have htrace : (τ.trace (d*(a-x))).re =
      τ.norm₂ d^2+‖x‖*(τ.trace d).re-(τ.trace (d*x)).re := by
    rw [had,mul_sub,mul_add,trace_sub,cornerTrace_add,hdz,← Complex.coe_smul,
      cornerTrace_smul,Complex.sub_re,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [norm₂_sq_trace τ,hd.isSelfAdjoint.star_eq]
    ring
  rw [htrace] at hsq
  change τ.norm₂ (z-x)^2 + τ.norm₂ d^2 ≤ τ.norm₂ (a-x)^2
  linarith

end

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem included_selfAdjoint (hNM : N ≤ M) (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (coordinateInclusion hNM a) := by
  change star (coordinateInclusion hNM a)=coordinateInclusion hNM a
  rw [← map_star,ha.star_eq]

attribute [local instance] OAI.Generator.Tracial.interiorCStar
attribute [local instance] OAI.Generator.Tracial.interiorOrder
attribute [local instance] OAI.Generator.Tracial.interiorPreorder
attribute [local instance] OAI.Generator.Tracial.interiorLE
attribute [local instance] OAI.Generator.Tracial.interiorStarOrder
theorem included_upperTruncate (hNM : N ≤ M) (a : N.toStarSubalgebra)
    (ha : IsSelfAdjoint a) (C : ℝ) :
    coordinateInclusion hNM (upperTruncate a C)=upperTruncate (coordinateInclusion hNM a) C := by
  rw [upperTruncate_cfc a ha C,
    upperTruncate_cfc _ (included_selfAdjoint hNM a ha) C]
  exact (coordinateInclusion hNM).map_cfc (fun t : ℝ => min t C) a
    (by fun_prop) (by fun_prop) ha (included_selfAdjoint hNM a ha)

theorem selfAdjoint_ball_minimum_upper (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (R : ℝ)
    (c : N.toStarSubalgebra) (hc : IsSelfAdjoint c) (hcR : ‖c‖ ≤ R)
    (hmin : ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
      τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) :
    coordinateInclusion hNM c ≤ algebraMap ℝ M.toStarSubalgebra ‖x‖ := by
  have hz := hmin (upperTruncate c ‖x‖) (upperTruncate_selfAdjoint c hc ‖x‖)
    (upperTruncate_norm_le c hc ‖x‖ R (norm_nonneg _) hcR)
  rw [included_upperTruncate hNM c hc] at hz
  have hd := upperTruncate_distance τ (coordinateInclusion hNM c) x
    (included_selfAdjoint hNM c hc) hx
  have hrev (a b : M.toStarSubalgebra) : τ.norm₂ (a-b)=τ.norm₂ (b-a) := norm_sub_rev _ _
  rw [hrev x,hrev x] at hz
  have he : τ.norm₂ ((coordinateInclusion hNM c-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)=0 := by
    nlinarith [show 0 ≤ τ.norm₂ (coordinateInclusion hNM c-x) from norm_nonneg _,
      show 0 ≤ τ.norm₂ (upperTruncate (coordinateInclusion hNM c) ‖x‖-x) from norm_nonneg _,
      show 0 ≤ τ.norm₂ ((coordinateInclusion hNM c-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺) from norm_nonneg _]
  exact sub_nonpos.mp ((CFC.posPart_eq_zero_iff _
    ((included_selfAdjoint hNM c hc).sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all ‖x‖)))).mp
      ((τ.norm₂_eq_zero_iff _).mp he))

theorem selfAdjoint_ball_minimum_norm (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (R : ℝ)
    (c : N.toStarSubalgebra) (hc : IsSelfAdjoint c) (hcR : ‖c‖ ≤ R)
    (hmin : ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
      τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) :
    ‖c‖ ≤ ‖x‖ := by
  have hu := selfAdjoint_ball_minimum_upper τ hNM x hx R c hc hcR hmin
  have hn := selfAdjoint_ball_minimum_upper τ hNM (-x) hx.neg R (-c) hc.neg
    (by simpa using hcR) (by
      intro a ha hRa
      have h := hmin (-a) ha.neg (by simpa using hRa)
      have hneg (b : M.toStarSubalgebra) : τ.norm₂ (-b)=τ.norm₂ b := norm_neg _
      rw [map_neg,show -x- -(coordinateInclusion hNM c)=-(x-coordinateInclusion hNM c) by abel,
        show -x-coordinateInclusion hNM a=-(x-coordinateInclusion hNM (-a)) by rw [map_neg]; abel,
        hneg,hneg]
      exact h)
  rw [map_neg,norm_neg] at hn
  exact selfAdjoint_norm_le_of_bounds _ (included_selfAdjoint hNM c hc) ‖x‖ (norm_nonneg _) hu hn

end

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem traceSymmetrize_norm₂_le (τ : TracialRepresentation M) (a : M.toStarSubalgebra) :
    τ.norm₂ (traceSymmetrize a) ≤ τ.norm₂ a := by
  rw [traceSymmetrize,τ.norm₂_smul,norm_inv]
  norm_num only [Complex.norm_ofNat]
  have h := τ.norm₂_add_le a (star a)
  rw [τ.norm₂_star] at h
  linarith

attribute [local instance] OAI.Generator.Tracial.clippingCStar
local instance clippingOrder_rf4ddfe_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance clippingStarOrder_rf4ddfe_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
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
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

theorem jointPiece_total : (∑ a : Fin Q.size × Fin R.size, (Q.jointPiece R hc a).val)=p.val := by
  change (∑ a : Fin Q.size × Fin R.size, (Q.piece a.1).val*(R.piece a.2).val)=p.val
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le _)]
  exact Q.total

end CornerPartition

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

end

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def TraceOrthogonal (P : StarSubalgebra ℂ M.toStarSubalgebra) (x : M.toStarSubalgebra) : Prop :=
  ∀ a : P, τ.trace ((a : M.toStarSubalgebra)*x)=0

/-! Quantitative control of the scalar energy that survives compatible
refinement. An orthogonal residual changes none of the block traces. -/

end

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem selfAdjoint_pairing_im (τ : TracialRepresentation M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    (τ.trace (a*b)).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  have hi := inner_conj_symm (𝕜 := ℂ) (baseVector τ a) (baseVector τ b)
  rw [baseVector_inner_trace,baseVector_inner_trace,ha.star_eq,hb.star_eq] at hi
  simpa only [τ.trace_mul_comm b a] using hi

end

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x y : M.toStarSubalgebra}
theorem add (hx : TraceOrthogonal τ P x) (hy : TraceOrthogonal τ P y) :
    TraceOrthogonal τ P (x+y) := by
  intro a
  rw [mul_add,cornerTrace_add,hx a,hy a,add_zero]
theorem smul (hx : TraceOrthogonal τ P x) (z : ℂ) : TraceOrthogonal τ P (z • x) := by
  intro a
  rw [mul_smul_comm,cornerTrace_smul,hx a,mul_zero]
end TraceOrthogonal

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/
variable {ι A B : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem ι N.toStarSubalgebra) (hNM : N ≤ M)

theorem relative_inclusion :
    E.relativeVonNeumann ≤ (E.map (coordinateInclusion hNM)).relativeVonNeumann := by
  intro x hx
  have h := (E.relativeStar_mem x).mp hx
  apply ((E.map (coordinateInclusion hNM)).relativeStar_mem x).mpr
  exact ⟨hNM h.1,h.2⟩

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteMatrixStage
open Tracial
variable {N M : VonNeumannAlgebra H}

def commutant (E : FiniteMatrixStage N) (hNM : N ≤ M) : VonNeumannAlgebra H :=
  (E.units.map (coordinateInclusion hNM)).relativeVonNeumann

theorem commutant_le (E : FiniteMatrixStage N) (hNM : N ≤ M) : E.commutant hNM ≤ M :=
  (E.units.map (coordinateInclusion hNM)).relativeVonNeumann_le

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def boundedPartialSupport (v : ℕ → PartialUnitary M) : Bounded M :=
  ⟨fun j => (v j).support.val,1,zero_le_one,fun j => (v j).support.property.norm_le⟩

end

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

theorem traceFreeDimension_range_bddAbove {I : Type*} (q : I → AlgebraProjection M) :
    BddAbove (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) :=
  ⟨1,by rintro _ ⟨i,rfl⟩; exact traceFreeDimension_le_one hfactor hdiff (q i)⟩

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/
namespace Tracial

/-! Finite partitions with prescribed dimensions, and actual equivalent
partitions of arbitrary positive finite size in every corner. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_remainder
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (q p : AlgebraProjection M) (hq : q ≤ p) :
    traceFreeDimension hfactor hdiff (AlgebraProjection.remainder q p hq)=
      traceFreeDimension hfactor hdiff p-traceFreeDimension hfactor hdiff q := by
  have h := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
    ⟨1,IsStarProjection.one _⟩ q (AlgebraProjection.remainder q p hq)
    hunit (one_mul _) (one_mul _) (AlgebraProjection.remainder_orthogonal q p hq)
  rw [AlgebraProjection.orthogonalSum_remainder] at h
  change traceFreeDimension hfactor hdiff p=
    traceFreeDimension hfactor hdiff q+
      traceFreeDimension hfactor hdiff (AlgebraProjection.remainder q p hq) at h
  linarith

end Tracial

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.norm_le {x : M.toStarSubalgebra} {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff x t) : ‖t‖ ≤ ‖x‖ := by
  have h := ht (CornerPartition.single ⟨1,IsStarProjection.one _⟩) (fun _ => 0)
    (fun _ => Commute.one_left x)
  simpa only [zero_mul,zero_smul,Finset.sum_const_zero,sub_zero] using h

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.stateDimensionCStar
attribute [local instance] OAI.Generator.Tracial.stateDimensionOrder
local instance stateDimensionPreorder_rf4ddfe_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.stateDimensionLE
attribute [local instance] OAI.Generator.Tracial.stateDimensionStarOrder
theorem tracialFunctional_equivalent (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    {p q : AlgebraProjection M} (h : p.Equivalent q) : φ p.val=φ q.val := by
  obtain ⟨v,hv,ht⟩ := h
  rw [← hv,← ht,← v.initial]
  exact htrace (star v.val) v.val

theorem positiveFunctional_projection_mono (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    {p q : AlgebraProjection M} (h : p ≤ q) : (φ p.val).re ≤ (φ q.val).re := by
  have hr := hpos (AlgebraProjection.remainder p q h).val
    (algebraProjection_nonneg _)
  change 0 ≤ (φ (q.val-p.val)).re at hr
  rw [map_sub,Complex.sub_re] at hr
  linarith

theorem tracialFunctional_subequivalent (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    {p q : AlgebraProjection M} (h : p.Subequivalent q) : (φ p.val).re ≤ (φ q.val).re := by
  obtain ⟨v,hv,ht⟩ := h
  have he := tracialFunctional_equivalent φ htrace
    (show p.Equivalent v.target from ⟨v,hv,rfl⟩)
  rw [he]
  exact positiveFunctional_projection_mono φ hpos ht

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem tracialFunctional_dyadic_subset_re (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (h1 : φ 1=1) (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (n : ℕ) (s : Finset (DyadicIndex n)) :
    (φ ((traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset s).val).re=
      dyadicWeight n s := by
  let E := traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n
  have he (i : DyadicIndex n) : (φ (E.leg i).target.val).re=(φ E.base.val).re := by
    exact congrArg Complex.re (tracialFunctional_equivalent φ htrace
      (show (E.leg i).target.Equivalent E.base from
        AlgebraProjection.equivalent_symm ⟨E.leg i,E.initial i,rfl⟩))
  have ht := congrArg (fun x : M.toStarSubalgebra => (φ x).re) E.total
  simp only [map_sum,Complex.re_sum,he,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,card_dyadicIndex,Nat.cast_pow,Nat.cast_ofNat,h1,Complex.one_re] at ht
  have hb : (φ E.base.val).re=1/(2 : ℝ)^n := by
    apply (eq_div_iff (ne_of_gt (pow_pos (by norm_num : (0 : ℝ)<2) n))).mpr
    nlinarith [ht]
  change (φ (E.subset s).val).re=_
  rw [E.subset_val,map_sum,Complex.re_sum]
  simp only [he,hb,Finset.sum_const,nsmul_eq_mul]
  change (s.card : ℝ)*(1/2^n)=(s.card : ℝ)/2^n
  ring

include hfinite in
theorem tracialFunctional_projection_dimension_re (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (p : AlgebraProjection M) : (φ p.val).re=traceFreeDimension hfactor hdiff p := by
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨s,t,_,_,hs,ht,hl,hu,hgap⟩ := traceFreeDyadicSup_rounding hfactor hdiff hfinite
    ⟨1,IsStarProjection.one _⟩ p hunit (one_mul _) n
  have hφl := tracialFunctional_subequivalent φ hpos htrace hs
  have hφu := tracialFunctional_subequivalent φ hpos htrace ht
  rw [tracialFunctional_dyadic_subset_re hfactor hdiff φ h1 htrace] at hφl hφu
  change dyadicWeight n s ≤ traceFreeDimension hfactor hdiff p at hl
  change traceFreeDimension hfactor hdiff p ≤ dyadicWeight n t at hu
  have hn : 0 ≤ 1/(2 : ℝ)^n := by positivity
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
  apply abs_le.mpr
  constructor <;> linarith

include hfinite in
theorem tracialFunctional_projection_dimension (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (hstar : ∀ x : M.toStarSubalgebra, φ (star x)=star (φ x))
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (p : AlgebraProjection M) : φ p.val=(traceFreeDimension hfactor hdiff p : ℂ) := by
  apply Complex.ext
  · exact tracialFunctional_projection_dimension_re hfactor hdiff hfinite hunit φ h1 hpos htrace p
  · have h := congrArg Complex.im (hstar p.val)
    rw [p.property.isSelfAdjoint.star_eq] at h
    change (φ p.val).im= -(φ p.val).im at h
    change (φ p.val).im=0
    linarith

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralAdditivityCStar
local instance spectralAdditivityOrder_rf4ddfe_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralAdditivityPreorder_rf4ddfe_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralAdditivityLE_rf4ddfe_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralAdditivityStarOrder_rf4ddfe_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem functional_isDimensionSpectralValue (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hnorm : ‖φ‖ ≤ 1)
    (hproj : ∀ p : AlgebraProjection M, φ p.val=(traceFreeDimension hfactor hdiff p : ℂ))
    (x : M.toStarSubalgebra) : IsDimensionSpectralValue hfactor hdiff x (φ x) := by
  intro Q c _
  have he : φ (∑ i, c i • (Q.piece i).val)=
      ∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [map_sum,map_smul,smul_eq_mul,hproj]
  rw [← he,← map_sub]
  simpa only [one_mul] using φ.le_of_opNorm_le hnorm (x-∑ i, c i • (Q.piece i).val)

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.traceCyclicOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual trace Hilbert completion of the bounded-sequence tracial quotient.
The vector-trace representation is explicit data; its existence for an arbitrary
factor is not asserted here. No free-independence premise occurs. -/
open Filter
open scoped Topology ComplexConjugate
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev Q := TracialQuotient τ (ω : Filter ℕ)

@[simp] theorem trace_add (a b : Q τ ω) :
    quotientTrace τ ω (a+b) = quotientTrace τ ω a + quotientTrace τ ω b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      apply tendsto_nhds_unique (traceRep_tendsto τ ω (a+b))
      change Tendsto (fun n => τ.trace (a.val n + b.val n)) _
        (𝓝 (traceRep τ ω a + traceRep τ ω b))
      simpa only [TracialRepresentation.trace_add] using
        (traceRep_tendsto τ ω a).add (traceRep_tendsto τ ω b)

@[simp] theorem trace_smul (c : ℂ) (a : Q τ ω) :
    quotientTrace τ ω (c • a) = c * quotientTrace τ ω a := by
  induction a using Quotient.inductionOn with
  | h a =>
    apply tendsto_nhds_unique (traceRep_tendsto τ ω (c • a))
    change Tendsto (fun n => τ.trace (c • a.val n)) _ (𝓝 (c * traceRep τ ω a))
    simpa only [TracialRepresentation.trace_smul] using
      (traceRep_tendsto τ ω a).const_mul c

end

/-! Centering actual bounded representatives changes no centered quotient
class. Every such class is a nonzero scalar multiple of a coordinatewise
centered contraction representative. -/
open Filter
open scoped Topology

/-! Trace Cauchy–Schwarz and unitary invariance on the tracial quotient. -/
open Filter
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end


