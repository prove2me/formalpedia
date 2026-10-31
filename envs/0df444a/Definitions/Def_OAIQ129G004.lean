-- Prove2me | Definitions.Def_OAIQ129G004
-- name    : OAIQ129G004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:18:07.402814+00:00
-- url     : https://prove2.me/theorems/a66d8ffb-3b17-4e35-a320-f5d2b033c59f
-- title:
--   Definitions bundle OAIQ129G004 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 157 declarations of OpenAI's Lean: 69 definitions, 5 instances and 83 theorems. The definitions and types are `OAI.Generator.Tracial.AlgebraProjection.unitaryConjugate`, `OAI.Generator.Tracial.AlgebraProjection.vectorValue`, `OAI.Generator.Tracial.CornerPartition.binary`, `OAI.Generator.Tracial.CornerPartition.ofFamily`, `OAI.Generator.Tracial.EquivalentPartition.rebase`, `OAI.Generator.Tracial.PartialIsometry.orthogonalPartialSum`, `OAI.Generator.Tracial.approximationCStar`, `OAI.Generator.Tracial.approximationLE`, `OAI.Generator.Tracial.approximationOrder`, `OAI.Generator.Tracial.approximationPreorder`, `OAI.Generator.Tracial.boundedInclusion`, `OAI.Generator.Tracial.conjugateFunctional`, `OAI.Generator.Tracial.cornerCutCStar`, `OAI.Generator.Tracial.cornerCutLE`, `OAI.Generator.Tracial.cornerCutOrder`, `OAI.Generator.Tracial.cornerCutPreorder`, `OAI.Generator.Tracial.cornerSpectralShift`, `OAI.Generator.Tracial.cornerValueLE`, `OAI.Generator.Tracial.cornerValueOrder`, `OAI.Generator.Tracial.dyadicFalseIndex`, `OAI.Generator.Tracial.hermitianFunctional`, `OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.localizedCStar`, `OAI.Generator.Tracial.localizedLE`, `OAI.Generator.Tracial.localizedOrder`, `OAI.Generator.Tracial.polarizationCStar`, `OAI.Generator.Tracial.quadraticStateCStar`, `OAI.Generator.Tracial.quadraticStateLE`, `OAI.Generator.Tracial.restrictedTrace`, `OAI.Generator.Tracial.spectralAdditivityCStar`, `OAI.Generator.Tracial.spectralCommutationCStar`, `OAI.Generator.Tracial.spectralCommutationOrder`, `OAI.Generator.Tracial.spectralFaithfulCStar`, `OAI.Generator.Tracial.spectralFaithfulLE`, `OAI.Generator.Tracial.spectralFaithfulOrder`, `OAI.Generator.Tracial.spectralFaithfulPreorder`, `OAI.Generator.Tracial.spectralSquareCStar`, `OAI.Generator.Tracial.spectralSquareOrder`, `OAI.Generator.Tracial.spectralValueCStar`, `OAI.Generator.Tracial.spectralValueLE` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Coefficients`, `FactorGeneration_CornerTrace`, `FactorGeneration_Dimension`, `FactorGeneration_DyadicComparison`, `FactorGeneration_FiniteComparison`, `FactorGeneration_FunctionalLimits`, `FactorGeneration_GroupTrace`, `FactorGeneration_LocalizedStates`, `FactorGeneration_NormalDimension`, `FactorGeneration_NormalTrace`, `FactorGeneration_Pinching`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_SpectralPinching`, `FactorGeneration_SpectralStates`, `FactorGeneration_TraceHilbert`, `FactorGeneration_TracialInclusion`, `FactorGeneration_Ultrapower`.
--
--   **Imports.** It imports the bundles `OAIQ129G000` and `OAIQ129G001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G007`, `OAIQ129G008` and `OAIQ129G009`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ129G000
import Definitions.Def_OAIQ129G001

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Coefficients
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Coefficientwise absolute-value product comparison, retaining all convolution terms contributing to the same group element. -/
section
open scoped BigOperators
variable {G : Type*} [Monoid G]

omit [Monoid G] in
@[simp] theorem normCoefficients_support (f : MonoidAlgebra ℂ G) :
    (normCoefficients f).coeff.support = f.coeff.support := by
  ext g
  simp only [Finsupp.mem_support_iff, normCoefficients_apply, ne_eq, norm_eq_zero]

end

/-! The coefficientwise ordered ring of real finite group-ring sums.
The multiplication is actual collected convolution. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_GroupTrace
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
open scoped ENNReal Pointwise
abbrev Ell2 (G : Type*) := FreeGroupFactorMain.GroupHilbert G
local instance groupAlgebraDecEq_rc1cadd_1 (G : Type*) : DecidableEq G := Classical.decEq _
/-- Reindex a square-summable vector by a permutation. -/
abbrev reindexVector {G : Type*} (e : G ≃ G) (f : Ell2 G) : Ell2 G :=
  FreeGroupFactorMain.hilbertReindex e f

@[simp] theorem reindexVector_apply {G : Type*} (e : G ≃ G) (f : Ell2 G) (g : G) :
    reindexVector e f g = f (e.symm g) := rfl

/-- The bounded unitary implementation of a permutation on ell2. -/
abbrev reindex {G : Type*} (e : G ≃ G) : Ell2 G ≃ₗᵢ[ℂ] Ell2 G :=
  FreeGroupFactorMain.hilbertReindex e

/-- The left regular operator, constructed on every square-summable vector. -/
abbrev leftRegular {G : Type*} [Group G] (g : G) : Ell2 G →L[ℂ] Ell2 G :=
  FreeGroupFactorMain.leftRegular g

@[simp] theorem leftRegular_apply {G : Type*} [Group G] (g b : G) (f : Ell2 G) :
    leftRegular g f b = f (g⁻¹ * b) := rfl

@[simp] theorem leftRegular_one {G : Type*} [Group G] : leftRegular (1 : G) = 1 := by
  ext f b
  simp

@[simp] theorem leftRegular_mul {G : Type*} [Group G] (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext f b
  simp

variable (G : Type*) [Group G]

variable {G}
@[simp] theorem leftRegular_star {G : Type*} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((reindex (Equiv.mulLeft g)) : Ell2 G →L[ℂ] Ell2 G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext f b
  change f (g * b) = f ((g⁻¹)⁻¹ * b)
  simp

/-- Right translations, needed to prove that the identity vector is separating. -/
def rightRegular {G : Type*} [Group G] (g : G) : Ell2 G →L[ℂ] Ell2 G :=
  (reindex (Equiv.mulRight g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type*} [Group G] (g b : G) (f : Ell2 G) :
    rightRegular g f b = f (b * g⁻¹) := rfl

end

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

@[simp] theorem trace_one : τ.trace 1 = 1 := by
  simp [trace, inner_self_eq_norm_sq_to_K, τ.norm_vector]

theorem trace_mul_comm (S T : Algebra (M := M)) : τ.trace (S*T) = τ.trace (T*S) :=
  τ.cyclic S T

theorem trace_star_mul (T : Algebra (M := M)) :
    τ.trace (star T*T) = (τ.norm₂ T : ℂ)^2 := by
  unfold trace norm₂
  change inner ℂ τ.vector ((star (T : H →L[ℂ] H)) ((T : H →L[ℂ] H) τ.vector)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem norm₂_star (T : Algebra (M := M)) : τ.norm₂ (star T) = τ.norm₂ T := by
  have h := τ.trace_mul_comm (star T) T
  have h2 := τ.trace_star_mul (star T)
  simp only [star_star] at h2
  rw [τ.trace_star_mul, h2] at h
  have hr := congrArg Complex.re h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hr
  have hn : 0 ≤ τ.norm₂ T := norm_nonneg _
  have hs : 0 ≤ τ.norm₂ (star T) := norm_nonneg _
  nlinarith

@[simp] theorem norm₂_zero : τ.norm₂ 0 = 0 := by simp [norm₂]
@[simp] theorem norm₂_sub (S T : Algebra (M := M)) :
    τ.norm₂ (S-T) = ‖(S : H →L[ℂ] H) τ.vector - (T : H →L[ℂ] H) τ.vector‖ := rfl

theorem norm₂_add_le (S T : Algebra (M := M)) : τ.norm₂ (S+T) ≤ τ.norm₂ S+τ.norm₂ T :=
  norm_add_le _ _

theorem norm₂_mul_le (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ ‖S‖ * τ.norm₂ T :=
  (S : H →L[ℂ] H).le_opNorm ((T : H →L[ℂ] H) τ.vector)

theorem norm₂_mul_le_right (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ τ.norm₂ S * ‖T‖ := by
  rw [← τ.norm₂_star (S*T), star_mul]
  have h := τ.norm₂_mul_le (star T) (star S)
  simpa [τ.norm₂_star, mul_comm, ContinuousLinearMap.star_eq_adjoint] using h

theorem norm₂_le_norm (T : Algebra (M := M)) : τ.norm₂ T ≤ ‖T‖ := by
  have h := (T : H →L[ℂ] H).le_opNorm τ.vector
  simpa [norm₂, τ.norm_vector] using h

theorem norm_trace_le_norm₂ (T : Algebra (M := M)) : ‖τ.trace T‖ ≤ τ.norm₂ T := by
  simpa [trace, norm₂, τ.norm_vector] using norm_inner_le_norm τ.vector ((T : H →L[ℂ] H) τ.vector)

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
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (τ : TracialRepresentation M) (l : Filter ℕ)
/-- The trace-null equivalence relation, before descending algebra operations. -/
def TraceRel (a b : Bounded M) : Prop :=
  Tendsto (fun n => τ.norm₂ (a.val n-b.val n)) l (𝓝 0)

theorem traceRel_refl (a : Bounded M) : TraceRel τ l a a := by
  simp only [TraceRel, sub_self, τ.norm₂_zero]
  exact tendsto_const_nhds

theorem traceRel_symm {a b : Bounded M} (h : TraceRel τ l a b) : TraceRel τ l b a := by
  simpa only [TraceRel, τ.norm₂_sub, norm_sub_rev] using h

theorem traceRel_trans {a b c : Bounded M}
    (hab : TraceRel τ l a b) (hbc : TraceRel τ l b c) : TraceRel τ l a c := by
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hab.add hbc)
  have he : a.val n-c.val n = (a.val n-b.val n)+(b.val n-c.val n) := by abel
  rw [he]
  exact τ.norm₂_add_le _ _

theorem traceRel_add {a b c d : Bounded M}
    (hab : TraceRel τ l a b) (hcd : TraceRel τ l c d) : TraceRel τ l (a+c) (b+d) := by
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hab.add hcd)
  change τ.norm₂ ((a.val n+c.val n)-(b.val n+d.val n)) ≤ _
  have he : (a.val n+c.val n)-(b.val n+d.val n) =
      (a.val n-b.val n)+(c.val n-d.val n) := by abel
  rw [he]
  exact τ.norm₂_add_le _ _

theorem traceRel_mul {a b c d : Bounded M}
    (hab : TraceRel τ l a b) (hcd : TraceRel τ l c d) : TraceRel τ l (a*c) (b*d) := by
  obtain ⟨C,hC,hc⟩ := c.property
  obtain ⟨B,hB,hb⟩ := b.property
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using (hab.mul_const C).add (hcd.const_mul B))
  change τ.norm₂ (a.val n*c.val n-b.val n*d.val n) ≤ _
  have he : a.val n*c.val n-b.val n*d.val n =
      (a.val n-b.val n)*c.val n+b.val n*(c.val n-d.val n) := by noncomm_ring
  rw [he]
  exact (τ.norm₂_add_le _ _).trans (add_le_add
    ((τ.norm₂_mul_le_right _ _).trans (mul_le_mul_of_nonneg_left (hc n) (norm_nonneg _)))
    ((τ.norm₂_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))))

theorem traceRel_star {a b : Bounded M} (hab : TraceRel τ l a b) :
    TraceRel τ l (star a) (star b) := by
  change Tendsto (fun n => τ.norm₂ (star (a.val n)-star (b.val n))) l (𝓝 0)
  simpa only [TraceRel, ← star_sub, τ.norm₂_star] using hab

/-- Algebra congruence proved from actual trace-norm estimates. -/
def traceCongruence : RingCon (Bounded M) where
  r := TraceRel τ l
  iseqv := ⟨traceRel_refl τ l, traceRel_symm τ l, traceRel_trans τ l⟩
  add' := traceRel_add τ l
  mul' := traceRel_mul τ l

/-- Underlying ring of the tracial ultrapower when l is a free ultrafilter. -/
abbrev TracialQuotient := (traceCongruence τ l).Quotient

def quotientMap : Bounded M →+* TracialQuotient τ l := (traceCongruence τ l).mk'

end

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

instance instStarTracialQuotient : Star (TracialQuotient τ l) :=
  ⟨Quotient.map' star (fun _ _ h => traceRel_star τ l h)⟩

@[simp] theorem quotientMap_star (a : Bounded M) :
    quotientMap τ l (star a) = star (quotientMap τ l a) := rfl

@[simp] theorem quotientMap_smul (c : ℂ) (a : Bounded M) :
    quotientMap τ l (c • a) = c • quotientMap τ l a := rfl

instance (priority := high) q129Semiring : Semiring (TracialQuotient τ l) := inferInstance
instance (priority := high) q129One : One (TracialQuotient τ l) := inferInstance
instance (priority := high) q129Algebra : Algebra ℂ (TracialQuotient τ l) := inferInstance

end

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem TracialRepresentation.trace_sub (a b : M.toStarSubalgebra) :
    τ.trace (a-b) = τ.trace a-τ.trace b := inner_sub_right _ _ _

@[simp] theorem TracialRepresentation.trace_add (a b : M.toStarSubalgebra) :
    τ.trace (a+b) = τ.trace a+τ.trace b := inner_add_right _ _ _

@[simp] theorem TracialRepresentation.trace_smul (c : ℂ) (a : M.toStarSubalgebra) :
    τ.trace (c • a) = c*τ.trace a := inner_smul_right _ _ _

def traceRep (a : Bounded M) : ℂ := limUnder (ω : Filter ℕ) (fun n => τ.trace (a.val n))

theorem traceRep_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.trace (a.val n)) (ω : Filter ℕ) (𝓝 (traceRep τ ω a)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨C,_,ha⟩ := a.property
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds
    (ω.map (fun n => τ.trace (a.val n))) (by
      apply le_principal_iff.mpr
      change {n | τ.trace (a.val n) ∈ Metric.closedBall 0 C} ∈ (ω : Filter ℕ)
      exact Filter.Eventually.of_forall (fun n => by
        simpa using ((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (ha n)))
  exact ⟨z,hz⟩

theorem traceRep_eq_of_rel {a b : Bounded M} (h : TraceRel τ (ω : Filter ℕ) a b) :
    traceRep τ ω a = traceRep τ ω b := by
  have hz : Tendsto (fun n => ‖τ.trace (a.val n)-τ.trace (b.val n)‖)
      (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
    rw [← τ.trace_sub]
    exact τ.norm_trace_le_norm₂ _
  have hnorm := ((traceRep_tendsto τ ω a).sub (traceRep_tendsto τ ω b)).norm
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hnorm hz))

/-- The actual ultralimit trace on the operator-algebra quotient. -/
def quotientTrace : TracialQuotient τ (ω : Filter ℕ) → ℂ :=
  Quotient.lift (traceRep τ ω) (fun _ _ h => traceRep_eq_of_rel τ ω h)

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

instance dyadicIndexDecidableEq (n : ℕ) : DecidableEq (DyadicIndex n) := Classical.decEq _

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
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

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete
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

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : CStarAlgebra M.toStarSubalgebra := {}

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
namespace Tracial
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

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
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.unitaryPolarCStar
local instance unitaryPolarOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance unitaryPolarStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

variable (a : ℕ → PartialIsometry M)
variable (hp : ∀ i j, i ≠ j → (a i).support.val*(a j).support.val=0)
variable (hq : ∀ i j, i ≠ j → (a i).target.val*(a j).target.val=0)

include hp hq in
theorem exists_orthogonalPartialSum (n : ℕ) :
    ∃ v : PartialIsometry M, v.val=∑ i ∈ Finset.range n, (a i).val ∧
      v.support.val=∑ i ∈ Finset.range n, (a i).support.val ∧
      v.target.val=∑ i ∈ Finset.range n, (a i).target.val := by
  induction n with
  | zero => exact ⟨zero, by simp [zero], by simp [zero], by simp [zero,target]⟩
  | succ n ih =>
    obtain ⟨v,hv,hs,ht⟩ := ih
    have ho₁ : v.support.val*(a n).support.val=0 := by
      rw [hs,Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi => hp i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
    have ho₂ : v.target.val*(a n).target.val=0 := by
      rw [ht,Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi => hq i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
    refine ⟨patch v (a n) ho₁ ho₂, ?_, ?_, ?_⟩
    · change v.val+(a n).val=_
      rw [hv,Finset.sum_range_succ]
    · change v.support.val+(a n).support.val=_
      rw [hs,Finset.sum_range_succ]
    · rw [patch_target,ht,Finset.sum_range_succ]

def orthogonalPartialSum (n : ℕ) : PartialIsometry M :=
  (exists_orthogonalPartialSum a hp hq n).choose

theorem orthogonalPartialSum_val (n : ℕ) :
    (orthogonalPartialSum a hp hq n).val=∑ i ∈ Finset.range n, (a i).val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.1

theorem orthogonalPartialSum_support (n : ℕ) :
    (orthogonalPartialSum a hp hq n).support.val=∑ i ∈ Finset.range n, (a i).support.val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.2.1

theorem orthogonalPartialSum_target (n : ℕ) :
    (orthogonalPartialSum a hp hq n).target.val=∑ i ∈ Finset.range n, (a i).target.val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.2.2

theorem le_orthogonalPartialSum (i n : ℕ) (hin : i < n) :
    a i ≤ orthogonalPartialSum a hp hq n := by
  change (orthogonalPartialSum a hp hq n).val*(a i).support.val=(a i).val
  rw [orthogonalPartialSum_val,Finset.sum_mul]
  apply Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hin) _ |>.trans (a i).mul_support
  intro j _ hji
  calc (a j).val*(a i).support.val = ((a j).val*(a j).support.val)*(a i).support.val := by
         rw [(a j).mul_support]
       _ = 0 := by rw [mul_assoc,hp j i hji,mul_zero]

theorem orthogonalPartialSum_monotone : Monotone (orthogonalPartialSum a hp hq) := by
  apply monotone_nat_of_le_succ
  intro n
  let v := orthogonalPartialSum a hp hq n
  have ho₁ : v.support.val*(a n).support.val=0 := by
    rw [orthogonalPartialSum_support,Finset.sum_mul]
    exact Finset.sum_eq_zero (fun i hi => hp i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
  have ho₂ : v.target.val*(a n).target.val=0 := by
    rw [orthogonalPartialSum_target,Finset.sum_mul]
    exact Finset.sum_eq_zero (fun i hi => hq i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
  have he : orthogonalPartialSum a hp hq (n+1)=patch v (a n) ho₁ ho₂ := by
    apply ext
    change (orthogonalPartialSum a hp hq (n+1)).val=v.val+(a n).val
    rw [orthogonalPartialSum_val,show v.val=∑ i ∈ Finset.range n, (a i).val from
      orthogonalPartialSum_val a hp hq n,Finset.sum_range_succ]
  rw [he]
  exact v.le_patch (a n) ho₁ ho₂

include hp hq in
/-- An actual infinite orthogonal sum, with least upper bound characterizations
for both support projections. It may be used to construct a shift. -/
theorem traceFree_orthogonal_sum :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧
      (∀ p : AlgebraProjection M, v.support ≤ p ↔ ∀ i, (a i).support ≤ p) ∧
      (∀ q : AlgebraProjection M, v.target ≤ q ↔ ∀ i, (a i).target ≤ q) := by
  obtain ⟨v,hv,hs,ht⟩ := traceFree_monotone_least_supports
    (orthogonalPartialSum a hp hq) (orthogonalPartialSum_monotone a hp hq)
  have hav (i : ℕ) : a i ≤ v :=
    (le_orthogonalPartialSum a hp hq i (i+1) (Nat.lt_succ_self i)).trans (hv (i+1))
  refine ⟨v,hav,?_,?_⟩
  · intro p
    refine ⟨fun h i => (support_mono (hav i)).trans h, fun h => hs p ?_⟩
    intro n
    change p.val*(orthogonalPartialSum a hp hq n).support.val=_
    rw [orthogonalPartialSum_support,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)
  · intro q
    refine ⟨fun h i => (target_mono (hav i)).trans h, fun h => ht q ?_⟩
    intro n
    change q.val*(orthogonalPartialSum a hp hq n).target.val=_
    rw [orthogonalPartialSum_target,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)

end PartialIsometry
end

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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
-- module Solutions.OAIQ129_RG2.FactorGeneration_FunctionalLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Semiring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! A functional bounded by a Hilbert-valued linear map factors through one
inner product. The proof uses the actual range, Hahn--Banach, and Riesz. -/

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch
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

end AlgebraProjection
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

/-- Reindex an explicitly finite orthogonal family by Fin. -/
def ofFamily {ι : Type*} [Fintype ι] (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0)
    (ht : ∑ i, (a i).val=p.val) : CornerPartition p where
  size := Fintype.card ι
  piece i := a ((Fintype.equivFin ι).symm i)
  orthogonal i j hij := ha _ _ (fun h => hij ((Fintype.equivFin ι).symm.injective h))
  total := by simpa only using (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (a i).val)).trans ht

theorem ofFamily_pinch {ι : Type*} [Fintype ι] (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0)
    (ht : ∑ i, (a i).val=p.val) (x : M.toStarSubalgebra) :
    (ofFamily a ha ht).pinch x = ∑ i, (a i).val*x*(a i).val := by
  exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (a i).val*x*(a i).val)

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerCutCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerCutOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerCutPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerCutLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerCutStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

/-- Functional calculus positive parts retain a given right support. -/
theorem positivePart_right_support (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (p : AlgebraProjection M) (hp : x*p.val=x) : x⁺*p.val=x⁺ := by
  have he : x⁺*(1-p.val)=x⁻*(1-p.val) := by
    apply sub_eq_zero.mp
    rw [← sub_mul,CFC.posPart_sub_negPart x hx,mul_sub,mul_one,hp,sub_self]
  have hz : star (x⁺*(1-p.val))*(x⁺*(1-p.val))=0 := by
    nth_rw 2 [he]
    rw [star_mul,star_sub,star_one,p.property.isSelfAdjoint.star_eq,
      (CFC.posPart_nonneg x).isSelfAdjoint.star_eq]
    calc (1-p.val)*x⁺*(x⁻*(1-p.val)) = (1-p.val)*(x⁺*x⁻)*(1-p.val) := by
           simp only [mul_assoc]
      _ = 0 := by rw [CFC.posPart_mul_negPart,mul_zero,zero_mul]
  have h := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [mul_sub,mul_one,sub_eq_zero] at h
  exact h.symm

def cornerSpectralShift (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    M.toStarSubalgebra := p.val*x*p.val-(t : ℂ) • p.val

theorem cornerSpectralShift_selfAdjoint (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℝ) :
    IsSelfAdjoint (cornerSpectralShift p x t) := by
  change star (p.val*x*p.val-(t : ℂ) • p.val) = _
  simp only [cornerSpectralShift,star_sub,star_mul,star_smul,p.property.isSelfAdjoint.star_eq,hx.star_eq,
    Complex.star_def,Complex.conj_ofReal,mul_assoc]

theorem cornerSpectralShift_support (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    cornerSpectralShift p x t*p.val=cornerSpectralShift p x t := by
  simp only [cornerSpectralShift,sub_mul,smul_mul_assoc,mul_assoc,p.property.isIdempotentElem.eq]

namespace CornerPartition
/-- Splitting p at an explicitly given subprojection q. -/
def binary (p q : AlgebraProjection M) (hq : q ≤ p) : CornerPartition p :=
  ofFamily (fun b : Bool => if b then q else
    ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hq⟩)
    (by
      intro i j hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · change (p.val-q.val)*q.val=0
        rw [sub_mul,hq,q.property.isIdempotentElem.eq,sub_self]
      · change q.val*(p.val-q.val)=0
        rw [mul_sub,projection_mul_of_le hq,q.property.isIdempotentElem.eq,sub_self]
      · exact (hij rfl).elim)
    (by
      rw [Fintype.sum_bool]
      change q.val+(p.val-q.val)=p.val
      abel)

theorem binary_pinch (p q : AlgebraProjection M) (hq : q ≤ p) (x : M.toStarSubalgebra) :
    (binary p q hq).pinch x = q.val*x*q.val+(p.val-q.val)*x*(p.val-q.val) := by
  rw [binary,ofFamily_pinch,Fintype.sum_bool]
  rfl

end CornerPartition

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition

theorem binary_pinch_of_commutes (p q : AlgebraProjection M) (hq : q ≤ p)
    (x : M.toStarSubalgebra) (hl : p.val*x=x) (hr : x*p.val=x)
    (hc : q.val*x=x*q.val) : (binary p q hq).pinch x=x := by
  have hqq : q.val*x*q.val=q.val*x := by
    rw [hc,mul_assoc,q.property.isIdempotentElem.eq]
  rw [binary_pinch]
  simp only [sub_mul,mul_sub,hl,hr,hqq]
  rw [hc]
  simp only [mul_assoc,projection_mul_of_le hq]
  abel

end CornerPartition

end

/-! Interval bounds propagated through constructed spectral corner splits. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem compress_scalar_shift {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ) :
    q.val*(p.val*x*p.val-(t : ℂ) • p.val)*q.val =
      q.val*x*q.val-(t : ℂ) • q.val := by
  have hl : p.val*q.val=q.val := hqp
  have hr := projection_mul_of_le hqp
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  simp only [← mul_assoc,hr]
  simp only [mul_assoc,hl,q.property.isIdempotentElem.eq]

end

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/
local instance approximationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance approximationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approximationPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance approximationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance approximationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralCommutationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralCommutationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralCommutationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem kernelProjection_commutes (x y : M.toStarSubalgebra)
    (hxy : Commute x y) (hxys : Commute x (star y)) :
    Commute (kernelProjection x).val y := by
  let k := x.val.ker.starProjection
  have hk : IsIdempotentElem k.toLinearMap :=
    (isStarProjection_starProjection (U := x.val.ker)).isIdempotentElem.toLinearMap
  have h₁ := kernel_invariant_of_commutes x.val y.val (congrArg Subtype.val hxy.eq)
  have h₂ : x.val.ker ∈ Module.End.invtSubmodule y.val.adjoint.toLinearMap := by
    exact kernel_invariant_of_commutes x.val (star y).val (congrArg Subtype.val hxys.eq)
  have hc : Commute k.toLinearMap y.val.toLinearMap := by
    apply (LinearMap.IsIdempotentElem.commute_iff hk).mpr
    change k.range ∈ Module.End.invtSubmodule y.val.toLinearMap ∧
      k.ker ∈ Module.End.invtSubmodule y.val.toLinearMap
    rw [Submodule.range_starProjection,Submodule.ker_starProjection]
    exact ⟨h₁,ContinuousLinearMap.orthogonal_mem_invtSubmodule h₂⟩
  apply Subtype.ext
  ext ξ
  exact congrArg (fun t : H →ₗ[ℂ] H => t ξ) hc.eq

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

end

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

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
attribute [local instance] OAI.Generator.Tracial.cornerValueCStar
local instance cornerValueOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerValuePreorder_rc1cadd_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerValueLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerValueStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance localizedCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance localizedOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance localizedPreorder_rc1cadd_1 : Preorder M.toStarSubalgebra :=
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

attribute [local instance] OAI.Generator.Tracial.cornerStateCStar
theorem vectorFunctional_star_mul_self (ξ : H) (x : M.toStarSubalgebra) :
    vectorFunctional ξ (star x*x)=(‖x.val ξ‖^2 : ℂ) := by
  change inner ℂ ξ (star x.val (x.val ξ))=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

attribute [local instance] OAI.Generator.Tracial.cornerStateOrder
local instance cornerStatePreorder_rc1cadd_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerStateLE
attribute [local instance] OAI.Generator.Tracial.cornerStateStarOrder
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
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem compose_base_target (E : EquivalentPartition p ι) (v : PartialIsometry M)
    (hv : v.target=E.base) (i : ι) :
    ((E.leg i).compose v (by rw [hv,E.initial])).target=(E.leg i).target := by
  apply Subtype.ext
  rw [PartialIsometry.compose_target,hv,← E.initial i,(E.leg i).mul_support]
  rfl

/-- Change the common initial corner by a displayed equivalence. -/
def rebase (E : EquivalentPartition p ι) (v : PartialIsometry M) (hv : v.target=E.base) :
    EquivalentPartition p ι where
  base := v.support
  leg i := (E.leg i).compose v (by rw [hv,E.initial])
  initial _ := rfl
  cross i j hij := by
    change star ((E.leg i).val*v.val)*((E.leg j).val*v.val)=0
    calc _ = star v.val*(star (E.leg i).val*(E.leg j).val)*v.val := by
           simp only [star_mul,mul_assoc]
         _ = 0 := by rw [E.cross i j hij,mul_zero,zero_mul]
  total := by simpa only [E.compose_base_target v hv] using E.total
  bound i := by rw [E.compose_base_target v hv]; exact E.bound i

theorem base_ne_zero (E : EquivalentPartition p ι) (hp : p.val≠0) : E.base.val≠0 := by
  intro hz
  have hl (i : ι) : (E.leg i).val=0 := by
    have h := (E.leg i).mul_support
    rw [E.initial,hz,mul_zero] at h
    exact h.symm
  have ht := E.total
  have hz' (i : ι) : (E.leg i).target.val=0 := by
    change (E.leg i).val*star (E.leg i).val=0
    rw [hl,zero_mul]
  rw [show (∑ i, (E.leg i).target.val)=0 from Finset.sum_eq_zero (fun i _ => hz' i)] at ht
  exact hp ht.symm

end EquivalentPartition

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance quadraticStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance quadraticStateOrder_rc1cadd_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance quadraticStatePreorder_rc1cadd_1 : Preorder M.toStarSubalgebra :=
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
local instance tracialStatePreorder_rc1cadd_1 : Preorder M.toStarSubalgebra :=
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
local instance stateDimensionCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance stateDimensionOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance stateDimensionPreorder_rc1cadd_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance stateDimensionLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance stateDimensionStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem algebraProjection_nonneg (p : AlgebraProjection M) : 0 ≤ p.val := by
  have h : star p.val*p.val=p.val := by
    rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq]
  rw [← h]
  exact star_mul_self_nonneg _

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
attribute [local instance] OAI.Generator.Tracial.traceCStar
local instance traceOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracePreorder_rc1cadd_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance traceStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

local instance traceHilbertCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertBoundCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertBoundOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertBoundPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceHilbertBoundLE : LE M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toLE
local instance traceHilbertBoundStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertActionCStar : CStarAlgebra M.toStarSubalgebra := {}

end

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


