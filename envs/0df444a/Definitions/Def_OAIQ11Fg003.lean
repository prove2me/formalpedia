-- Prove2me | Definitions.Def_OAIQ11Fg003
-- name    : OAIQ11Fg003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:33:23.000148+00:00
-- url     : https://prove2.me/theorems/0146079b-c288-43e8-8072-f649e61058a4
-- title:
--   Definitions bundle OAIQ11Fg003 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 18 definitions, 1 inductive type or structure, 1 instance and 38 theorems. The definitions and types are `OAI.Generator.FiniteMatrixStage.commutant`, `OAI.Generator.FiniteMatrixStage.generated`, `OAI.Generator.FiniteMatrixStage.scalarStage`, `OAI.Generator.MatrixUnitSystem.concreteAlgebra`, `OAI.Generator.MatrixUnitSystem.concreteHom`, `OAI.Generator.Tracial.TraceOrthogonal`, `OAI.Generator.Tracial.TraceUnitary`, `OAI.Generator.Tracial.TraceUnitary.algebra`, `OAI.Generator.Tracial.TraceUnitary.vector`, `OAI.Generator.Tracial.baseVector`, `OAI.Generator.Tracial.boundedInclusion`, `OAI.Generator.Tracial.quotientInclusion`, `OAI.Generator.Tracial.restrictedTrace`, `OAI.Generator.Tracial.selfAdjointTraceBall`, `OAI.Generator.Tracial.traceCyclicOperator`, `OAI.Generator.Tracial.traceCyclicSpace`, `OAI.Generator.diagonalOperator`, `OAI.Generator.operatorEntry`, `OAI.Generator.tupleSingle`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Bicommutant`, `FactorGeneration_CornerTrace`, `FactorGeneration_Expectations`, `FactorGeneration_GroupTrace`, `FactorGeneration_HilbertLimits`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixSequence`, `FactorGeneration_Pinching`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Subfactors`, `FactorGeneration_TraceTopology`, `FactorGeneration_TracialInclusion`, `FactorGeneration_Ultrapower`, `FactorGeneration_UnitaryMetric`.
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`; the bundles `OAIQ11Fg000` and `OAIQ11Fg001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg007`, `OAIQ11Fg008`, `OAIQ11Fg009` and `OAIQ11Fg010`; the statements `OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1`, `OAI.Generator.FiniteMatrixStage.generated_isII1`, `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget`, `OAI_Generator_Tracial_betweenWord_integerValue`, `OAI_Generator_Tracial_cyclicPredual_separable_of_given_membership`, `OAI_Generator_Tracial_exists_exact_residual_step`, `OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor`, `OAI.Generator.Tracial.exists_supported_corner_partial_sequence`, `OAI_Generator_Tracial_integerPowerBlock_eval`, `OAI_Generator_Tracial_integerValueWord_blocks`, `OAI_Generator_Tracial_integerWord_right_factor`, `OAI_Generator_Tracial_predualFunctional_unitBall_continuous`, `OAI.Generator.Tracial.represented_relative_generation`, `OAI_Generator_Tracial_signedLetter_integer`, `OAI.Generator.Tracial.singlyGenerated_of_tracialRepresentation` and `OAI_Generator_evaluated_prefixes`; the proofs of `OAI_Generator_Tracial_betweenWord_integerValue`, `OAI_Generator_Tracial_cyclicPredual_separable_of_given_membership`, `OAI_Generator_Tracial_integerPowerBlock_eval`, `OAI_Generator_Tracial_integerWord_right_factor`, `OAI_Generator_Tracial_signedLetter_integer`, `OAI_Generator_Tracial_traceOrbit_isSeparable_of_separablePredual` and `OAI_Generator_evaluated_prefixes`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg000
import Definitions.Def_OAIQ11Fg001

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

def diagonalOperator (T : H →L[ℂ] H) : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i)))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_apply (T : H →L[ℂ] H) (x : FiniteHilbert ι H) (i : ι) :
    diagonalOperator T x i=T (x i) := rfl

variable [DecidableEq ι]

def tupleSingle (i : ι) : H →L[ℂ] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem tupleSingle_apply (i j : ι) (x : H) :
    tupleSingle i x j=(Pi.single i x : ι → H) j := rfl

omit [CompleteSpace H] in
theorem tuple_eq_sum_single (x : FiniteHilbert ι H) :
    x=∑ i,tupleSingle i (x i) := by
  ext j
  simp [WithLp.ofLp_sum,tupleSingle_apply,Pi.single_apply]

omit [CompleteSpace H] [Fintype ι] in
theorem diagonalOperator_single (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonalOperator T (tupleSingle i x)=tupleSingle i (T x) := by
  ext j
  by_cases h : j=i <;> simp [h]

def operatorEntry (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (Q.comp (tupleSingle j))

end

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

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
-- module Solutions.OAIQ11_FG.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem quotientTrace_mk (a : Bounded M) :
    quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) a) = traceRep τ ω a := rfl

@[simp] theorem quotientTrace_one : quotientTrace τ ω 1 = 1 := by
  apply tendsto_nhds_unique (traceRep_tendsto τ ω 1)
  simp

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
-- module Solutions.OAIQ11_FG.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator.Tracial

/-! The restricted faithful trace and the actual P^omega -> M^omega
inclusion. All constructions are on the bounded-sequence quotient. -/
noncomputable section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

def restrictedTrace : TracialRepresentation P where
  vector := τ.vector
  norm_vector := τ.norm_vector
  cyclic a b := τ.cyclic (coordinateInclusion hPM a) (coordinateInclusion hPM b)
  separating a ha := by
    have h := τ.separating (coordinateInclusion hPM a) ha
    apply Subtype.ext
    exact congrArg (fun x : M.toStarSubalgebra => x.val) h

@[simp] theorem restrictedTrace_trace (a : P.toStarSubalgebra) :
    (restrictedTrace τ hPM).trace a = τ.trace (coordinateInclusion hPM a) := rfl

@[simp] theorem restrictedTrace_norm₂ (a : P.toStarSubalgebra) :
    (restrictedTrace τ hPM).norm₂ a = τ.norm₂ (coordinateInclusion hPM a) := rfl

def boundedInclusion : Bounded P →⋆ₐ[ℂ] Bounded M where
  toFun a := ⟨fun n => coordinateInclusion hPM (a.val n), a.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

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
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
variable (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
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
-- module Solutions.OAIQ11_FG.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
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
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

def traceCyclicOperator (a : M.toStarSubalgebra) :
    traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ :=
  a.val.restrict (fun _ hy => vectorOrbitClosure_invariant _ _ a hy)

@[simp] theorem traceCyclicOperator_apply (a : M.toStarSubalgebra) (y : traceCyclicSpace τ) :
    (traceCyclicOperator τ a y).val=a.val y.val := rfl

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
-- module Solutions.OAIQ11_FG.FactorGeneration_UnitaryMetric
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace MatrixUnitSystem
variable (E : Generator.MatrixUnitSystem ι M.toStarSubalgebra)

def concreteHom : Matrix ι ι ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp E.hom

def concreteAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) := E.concreteHom.range

end MatrixUnitSystem

end

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/

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
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def generated (A : ℕ → FiniteMatrixStage N) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  wstar (⋃ n,((A n).units.concreteAlgebra : Set (H →L[ℂ] H)))

theorem generated_closed (A : ℕ → FiniteMatrixStage N) : WOTClosed (generated A) := wstar_closed _

def scalarStage (N : VonNeumannAlgebra H) : FiniteMatrixStage N where
  size := 1
  positive := by norm_num
  units := {
    entry := fun _ _ => 1
    star_entry := by intros; simp
    mul_entry := by
      intro i j k l
      rw [ite_eq_left (Subsingleton.elim j k),one_mul]
    total := by simp }

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end


