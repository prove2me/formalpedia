-- Prove2me | Definitions.Def_OAIQ129G015
-- name    : OAIQ129G015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:13:30.999785+00:00
-- url     : https://prove2.me/theorems/456be7ab-87a0-4871-84c0-e79d197dbc94
-- title:
--   Definitions bundle OAIQ129G015 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 47 declarations of OpenAI's Lean: 24 definitions, 1 instance and 22 theorems. The definitions and types are `OAI.Generator.FactorTraceUnitary.represented`, `OAI.Generator.FactorTraceUnitary.representedEquiv`, `OAI.Generator.FactorTraceUnitary.representedHomeomorph`, `OAI.Generator.FactorTraceUnitary.representedIsometryEquiv`, `OAI.Generator.FactorTraceUnitary.traceHomeomorph`, `OAI.Generator.Tracial.productCenteredFamily`, `OAI.Generator.Tracial.traceFreeHilbertActionCLM`, `OAI.Generator.Tracial.traceFreeHilbertBallMap`, `OAI.Generator.Tracial.traceFreeHilbertClosureTrace`, `OAI.Generator.Tracial.traceFreeHilbertCoefficient`, `OAI.Generator.Tracial.traceFreeHilbertEquiv`, `OAI.Generator.Tracial.traceFreeHilbertIntoClosure`, `OAI.Generator.Tracial.traceFreeHilbertIsometry`, `OAI.Generator.Tracial.traceFreeHilbertVectorBall`, `OAI.Generator.Tracial.traceFreeHilbertWeakBall`, `OAI.Generator.Tracial.traceFreeSubalgebraVectorBall`, `OAI.Generator.Tracial.traceFreeSubalgebraWeakBall`, `OAI.Generator.Tracial.traceHilbertImageClosureCStar`, `OAI.Generator.Tracial.traceHilbertTransportClosureCStar`, `OAI.Generator.Tracial.traceHilbertWOTOperatorCStar`, `OAI.Generator.Tracial.traceSubalgebraImageOperatorCStar`, `OAI.Generator.factorTracePreInner`, `OAI.Generator.factorTracePreNormed`, `OAI.Generator.normalizedFactorTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_ProductWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProductWords.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean), [`FactorGeneration_TraceTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTransport.lean), [`RelativeGeneration_OriginalUnitary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RelativeGeneration/OriginalUnitary.lean).
--
--   **Imports.** It imports the published bundles `Def_FactorGeneration` and `Def_RelativeGeneration`; the bundles `OAIQ129G013` and `OAIQ129G014` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ129G016`; the proof of `OAI.Generator.Tracial.nonempty_successiveCoordinateHaar_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_RelativeGeneration
import Definitions.Def_OAIQ129G013
import Definitions.Def_OAIQ129G014

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeInclusion_inner
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

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.dominationCStar
attribute [local instance] OAI.Generator.Tracial.dominationOrder
local instance dominationPreorder_r683021_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.dominationLE
attribute [local instance] OAI.Generator.Tracial.dominationStarOrder
theorem traceFreeTrace_exists_finite_vector_domination :
    ∃ (n : ℕ) (ξ : Fin n → H) (C : ℝ), 0<C ∧
      ∀ x : M.toStarSubalgebra, 0 ≤ x →
        (traceFreeTrace hfactor hdiff hfinite hunit x).re ≤
          C * ∑ i, (inner ℂ (ξ i) (x.val (ξ i))).re := by
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,a,hE,ha,hloc⟩ := exists_localized_vector_functional hfactor hdiff hfinite hunit ξ hξ 1 (by norm_num)
  obtain ⟨n,_,Q,hQE,_⟩ := exists_equivalent_partition_base_le hfactor hdiff hfinite hunit E hE
  refine ⟨n,fun i => (Q.leg i).val.val ξ,a⁻¹,inv_pos.mpr ha,?_⟩
  intro x hx
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have hi (i : Fin n) : a*(τ (Q.stateCoefficient x i i)).re ≤
      (vectorFunctional ξ (Q.stateCoefficient x i i)).re := by
    have hpos : 0 ≤ Q.stateCoefficient x i i := star_left_conjugate_nonneg hx (Q.leg i).val
    have hEx : E.val*Q.stateCoefficient x i i=Q.stateCoefficient x i i := by
      calc E.val*Q.stateCoefficient x i i =
          E.val*(Q.base.val*Q.stateCoefficient x i i) := by rw [Q.stateCoefficient_left]
        _ = Q.stateCoefficient x i i := by rw [← mul_assoc,hQE,Q.stateCoefficient_left]
    have h := (hloc (Q.stateCoefficient x i i) hpos hEx).1
    rwa [← traceFreeTrace_selfAdjoint hfactor hdiff hfinite hunit _ hpos.isSelfAdjoint] at h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
  rw [← Finset.mul_sum,← Complex.re_sum,
    traceFreeTrace_matrix_diagonal hfactor hdiff hfinite hunit] at hsum
  have hv : (∑ i, (vectorFunctional ξ (Q.stateCoefficient x i i)).re)=
      ∑ i, (inner ℂ ((Q.leg i).val.val ξ) (x.val ((Q.leg i).val.val ξ))).re := by
    rw [← Complex.re_sum,← Q.matrixVectorFunctional_apply]
    simp only [EquivalentPartition.matrixVectorFunctional,sum_apply,Complex.re_sum,
      vectorFunctional_apply]
  rw [hv] at hsum
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr ha.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] using h

end

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.traceNormalCStar
attribute [local instance] OAI.Generator.Tracial.traceNormalOrder
local instance traceNormalPreorder_r683021_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceNormalLE_r683021_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
attribute [local instance] OAI.Generator.Tracial.traceNormalStarOrder
theorem traceFreeTrace_finite_vector_representation :
    ∃ (n : ℕ) (ξ η : Fin n → H), ∀ x : M.toStarSubalgebra,
      traceFreeTrace hfactor hdiff hfinite hunit x=∑ i, inner ℂ (η i) (x.val (ξ i)) := by
  obtain ⟨n,ξ,C,hC,hbound⟩ := traceFreeTrace_exists_finite_vector_domination hfactor hdiff hfinite hunit
  let V := PiLp 2 (fun _ : Fin n => H)
  let F : M.toStarSubalgebra →ₗ[ℂ] V :=
    { toFun := fun x => WithLp.toLp 2 (fun i => x.val (ξ i))
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have hb (x : M.toStarSubalgebra) : ‖τ x‖ ≤ Real.sqrt C*‖F x‖ := by
    have hs := (traceFreeTrace_norm_sq_le hfactor hdiff hfinite hunit x).trans
      (hbound (star x*x) (star_mul_self_nonneg _))
    have hi (i : Fin n) : (inner ℂ (ξ i) ((star x*x).val (ξ i))).re=‖x.val (ξ i)‖^2 := by
      change (vectorFunctional (ξ i) (star x*x)).re=_
      rw [vectorFunctional_star_mul_self,← Complex.ofReal_pow,Complex.ofReal_re]
    simp only [hi] at hs
    have hFn : ‖F x‖^2=∑ i, ‖x.val (ξ i)‖^2 := PiLp.norm_sq_eq_of_L2 _ (F x)
    rw [← hFn] at hs
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hC.le]
    exact hs
  obtain ⟨η,hη⟩ := exists_inner_factor_of_bound F τ.toLinearMap (Real.sqrt C) hb
  refine ⟨n,ξ,fun i => η i,?_⟩
  intro x
  exact (hη x).trans (PiLp.inner_apply η (F x))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProductWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact signed-word expansion for a product of two unitaries. A unit gap
is allowed only between equal signs; opposite signs retain a centered gap. -/

/-! The actual countable centered coefficients needed to expand words in UV. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def productCenteredFamily (u : Q τ ω) (x : ℕ → Q τ ω) (n : ℕ) : Q τ ω :=
  match Encodable.decode (α := ProductFamilyIndex) n with
  | none => 0
  | some i => productFamilyValue τ ω u x i

end

/-! Expand positive-length signed powers into individual letters. Repeated
letters have unit gaps; boundaries between powers retain centered coefficients. -/

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit

local notation "L" => traceFreeLeftAction hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertActionCStar
attribute [local instance] OAI.Generator.Tracial.traceHilbertOperatorCStar
theorem traceFreeHilbertVector_norm : ‖Ω‖ = 1 := by
  have h := traceFreeCopy_norm_sq hfactor hdiff hfinite hunit 1
  rw [star_one,one_mul,(traceFreeTrace_spec hfactor hdiff hfinite hunit).2.1] at h
  change ‖ι (copy 1)‖ = 1
  rw [LinearIsometry.norm_map]
  have hn := norm_nonneg (copy 1)
  change ‖copy 1‖^2 = 1 at h
  nlinarith

theorem traceFreeHilbertAction_injective : Function.Injective π := by
  intro a b hab
  have hv := congrArg (fun T : K →L[ℂ] K => T Ω) hab
  simp only [traceFreeHilbertAction_vector] at hv
  exact (copy).injective ((ι).injective hv)

local instance traceHilbertActionOrder_r683021_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertActionStarOrder_r683021_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem traceFreeHilbertAction_norm (a : M.toStarSubalgebra) : ‖π a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map π (traceFreeHilbertAction_injective hfactor hdiff hfinite hunit) a

end

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/
section
open Filter
open scoped ComplexConjugate CStarAlgebra Pointwise Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

local instance traceHilbertClosureCStar_r683021_1 : CStarAlgebra M.toStarSubalgebra := {}
attribute [local instance] OAI.Generator.Tracial.traceHilbertClosureOperatorCStar
theorem traceFreeHilbertAction_mem_closure (a : M.toStarSubalgebra) : π a ∈ N := by
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit _).mpr
  intro T hT
  exact (hT (π a) ⟨a,rfl⟩).symm

def traceFreeHilbertIntoClosure : M.toStarSubalgebra →⋆ₐ[ℂ] (N).toStarSubalgebra :=
  (π).codRestrict (N).toStarSubalgebra (traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit)

/-- Output tracial representation on the actual bicommutant. Its fields are
proved above; no TracialRepresentation is an input to this construction. -/
def traceFreeHilbertClosureTrace : UltrapowerBridge.TracialRepresentation N where
  vector := Ω
  norm_vector := traceFreeHilbertVector_norm hfactor hdiff hfinite hunit
  cyclic := traceFreeHilbertClosure_trace_commute hfactor hdiff hfinite hunit
  separating := traceFreeHilbertClosure_separating hfactor hdiff hfinite hunit

end

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertWOTOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertWOTCStar
local instance traceHilbertWOTOrder_r683021_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertWOTStarOrder_r683021_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
def traceFreeHilbertActionCLM : M.toStarSubalgebra →L[ℂ] (K →L[ℂ] K) :=
  (π).toLinearMap.mkContinuous 1 (by
    intro a
    rw [one_mul]
    exact (traceFreeHilbertAction_norm hfactor hdiff hfinite hunit a).le)

def traceFreeHilbertCoefficient (x y : K) : StrongDual ℂ M.toStarSubalgebra :=
  (innerSL ℂ y).comp ((ContinuousLinearMap.apply ℂ K x).comp
    (traceFreeHilbertActionCLM hfactor hdiff hfinite hunit))

@[simp] theorem traceFreeHilbertCoefficient_apply (x y : K) (a : M.toStarSubalgebra) :
    traceFreeHilbertCoefficient hfactor hdiff hfinite hunit x y a = inner ℂ y (π a x) := rfl

theorem traceFreeHilbertCoefficient_continuous : Continuous
    (fun p : K × K => traceFreeHilbertCoefficient hfactor hdiff hfinite hunit p.1 p.2) :=
  ((innerSL ℂ).continuous.comp continuous_snd).clm_comp
    (((ContinuousLinearMap.apply ℂ K).continuous.comp continuous_fst).clm_comp continuous_const)

theorem traceFreeHilbertCoefficient_copy_ball_continuous (C : ℝ) (a b : M.toStarSubalgebra) :
    Continuous (fun T : weakOperatorBall M C =>
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit (ι (copy a)) (ι (copy b))
        ⟨T.val.toCLM,T.property.1⟩) := by
  obtain ⟨n,ξ,η,ht⟩ := traceFreeTrace_finite_vector_representation hfactor hdiff hfinite hunit
  have he (T : weakOperatorBall M C) :
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit (ι (copy a)) (ι (copy b))
        ⟨T.val.toCLM,T.property.1⟩ = ∑ i, inner ℂ (b.val (η i)) (T.val (a.val (ξ i))) := by
    rw [traceFreeHilbertCoefficient_apply,traceFreeHilbertAction_inclusion,traceFreeInclusion_inner,ht]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (η i) ((star b.val) (T.val (a.val (ξ i)))) = _
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp_rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (a.val (ξ i)) (b.val (η i)))

theorem traceFreeHilbertCoefficient_ball_continuous (C : ℝ) (x y : K) :
    Continuous (fun T : weakOperatorBall M C =>
      inner ℂ y (π ⟨T.val.toCLM,T.property.1⟩ x)) := by
  have hd : DenseRange (fun a : M.toStarSubalgebra => ι (copy a)) := by
    simpa only [traceFreeHilbertAction_vector] using
      traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit
  have hc := (ballContinuousFunctionals_isClosed M C).preimage
    (traceFreeHilbertCoefficient_continuous hfactor hdiff hfinite hunit)
  have hm : ∀ p : K × K,
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit p.1 p.2 ∈ ballContinuousFunctionals M C := by
    apply isClosed_property (hd.prodMap hd) hc
    intro p
    exact traceFreeHilbertCoefficient_copy_ball_continuous hfactor hdiff hfinite hunit C p.1 p.2
  exact hm (x,y)

def traceFreeHilbertBallMap (C : ℝ) (T : weakOperatorBall M C) : K →WOT[ℂ] K :=
  ContinuousLinearMapWOT.ofCLM (π ⟨T.val.toCLM,T.property.1⟩)

theorem traceFreeHilbertBallMap_continuous (C : ℝ) :
    Continuous (traceFreeHilbertBallMap hfactor hdiff hfinite hunit C) :=
  ContinuousLinearMapWOT.continuous_iff.mpr
    (traceFreeHilbertCoefficient_ball_continuous hfactor hdiff hfinite hunit C)

def traceFreeHilbertWeakBall (C : ℝ) : Set (K →WOT[ℂ] K) :=
  {T | ∃ a : M.toStarSubalgebra, ‖a‖ ≤ C ∧ ContinuousLinearMapWOT.ofCLM (π a) = T}

theorem traceFreeHilbertWeakBall_eq_range (C : ℝ) :
    traceFreeHilbertWeakBall hfactor hdiff hfinite hunit C =
      Set.range (traceFreeHilbertBallMap hfactor hdiff hfinite hunit C) := by
  ext T
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,ha⟩⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨⟨a.val.toCLM,a.property.1⟩,a.property.2,rfl⟩

theorem traceFreeHilbertWeakBall_isCompact (C : ℝ) :
    IsCompact (traceFreeHilbertWeakBall hfactor hdiff hfinite hunit C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  rw [traceFreeHilbertWeakBall_eq_range]
  exact isCompact_range (traceFreeHilbertBallMap_continuous hfactor hdiff hfinite hunit C)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
attribute [local instance] OAI.Generator.Tracial.traceHilbertImageCStar
local instance traceHilbertImageOrder_r683021_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertImageStarOrder_r683021_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceHilbertImageOperatorCStar_r683021_1 : CStarAlgebra (K →L[ℂ] K) := {}
local instance traceHilbertImageClosureCStar : CStarAlgebra (N).toStarSubalgebra := {}

def traceFreeHilbertVectorBall (C : ℝ) : Set K :=
  {x | ∃ a : M.toStarSubalgebra, ‖a‖ ≤ C ∧ π a Ω = x}

theorem traceFreeHilbertVectorBall_isClosed (C : ℝ) :
    IsClosed (traceFreeHilbertVectorBall hfactor hdiff hfinite hunit C) := by
  apply IsSeqClosed.isClosed
  intro v x hv hx
  choose a ha he using hv
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T,hT,ht⟩ := (traceFreeHilbertWeakBall_isCompact hfactor hdiff hfinite hunit C).ultrafilter_le_nhds
    (ω.map (fun n => ContinuousLinearMapWOT.ofCLM (π (a n)))) (by
      apply le_principal_iff.mpr
      change ∀ᶠ n in (ω : Filter ℕ), ContinuousLinearMapWOT.ofCLM (π (a n)) ∈
        traceFreeHilbertWeakBall hfactor hdiff hfinite hunit C
      exact Eventually.of_forall (fun n => ⟨a n,ha n,rfl⟩))
  obtain ⟨b,hb,rfl⟩ := hT
  refine ⟨b,hb,?_⟩
  apply ext_inner_left ℂ
  intro y
  have hw := (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp ht) Ω y
  change Tendsto (fun n => inner ℂ y (π (a n) Ω)) (ω : Filter ℕ)
    (𝓝 (inner ℂ y (π b Ω))) at hw
  have hn := (innerSL ℂ y).continuous.continuousAt.tendsto.comp
    (hx.mono_left (Ultrafilter.of_le atTop))
  exact tendsto_nhds_unique hw (by simpa only [Function.comp_def,innerSL_apply_apply,he] using hn)

theorem traceFreeHilbertIntoClosure_symmetrize (a : M.toStarSubalgebra) :
    ρ (traceSymmetrize a) = traceSymmetrize (ρ a) := by
  simp only [traceSymmetrize,map_smul,map_add,map_star]

theorem traceFreeHilbertIntoClosure_clip (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    ρ (traceClip a C) = traceClip (ρ a) C := by
  rw [traceClip_cfc a ha C,traceClip_cfc _ (ha.map ρ) C]
  exact (ρ).map_cfc (fun t : ℝ => -min (-min t C) C) a
    (by fun_prop) (by fun_prop) ha (ha.map ρ)

theorem traceFreeHilbertClosure_selfAdjoint_approximation
    (x : (N).toStarSubalgebra) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : M.toStarSubalgebra, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖x‖ ∧ (σ).norm₂ (ρ a-x) < ε := by
  obtain ⟨v,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp
    (traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit (x.val Ω)) ε hε
  have ha' : (σ).norm₂ (ρ a-x) < ε := by
    change ‖π a Ω-x.val Ω‖ < ε
    simpa only [dist_eq_norm,norm_sub_rev] using ha
  let b := traceSymmetrize a
  have hb : IsSelfAdjoint b := traceSymmetrize_selfAdjoint a
  have hb' : (σ).norm₂ (ρ b-x) ≤ (σ).norm₂ (ρ a-x) := by
    have he : ρ b-x = traceSymmetrize (ρ a-x) := by
      rw [traceSymmetrize_sub,traceSymmetrize_eq_self x hx]
      exact congrArg (fun z => z-x) (traceFreeHilbertIntoClosure_symmetrize hfactor hdiff hfinite hunit a)
    rw [he]
    exact traceSymmetrize_norm₂_le σ _
  refine ⟨traceClip b ‖x‖,traceClip_selfAdjoint b hb _,traceClip_norm_le b hb _ (norm_nonneg _),?_⟩
  rw [traceFreeHilbertIntoClosure_clip hfactor hdiff hfinite hunit b hb]
  exact (traceClip_distance σ (ρ b) x (hb.map ρ) hx).trans_lt (hb'.trans_lt ha')

theorem traceFreeHilbertClosure_selfAdjoint_preimage (x : (N).toStarSubalgebra)
    (hx : IsSelfAdjoint x) : ∃ a : M.toStarSubalgebra, ρ a = x := by
  have hm : x.val Ω ∈ traceFreeHilbertVectorBall hfactor hdiff hfinite hunit ‖x‖ := by
    apply (traceFreeHilbertVectorBall_isClosed hfactor hdiff hfinite hunit ‖x‖).closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,ha,hax⟩ := traceFreeHilbertClosure_selfAdjoint_approximation hfactor hdiff hfinite hunit x hx ε hε
    exact ⟨π a Ω,⟨a,ha,rfl⟩,by
      change ‖π a Ω-x.val Ω‖ < ε at hax
      simpa only [dist_eq_norm,norm_sub_rev] using hax⟩
  obtain ⟨a,_,ha⟩ := hm
  refine ⟨a,?_⟩
  apply sub_eq_zero.mp
  apply (σ).separating
  change π a Ω-x.val Ω = 0
  exact sub_eq_zero.mpr ha

theorem traceFreeHilbertIntoClosure_surjective : Function.Surjective ρ := by
  intro x
  obtain ⟨a,ha⟩ := traceFreeHilbertClosure_selfAdjoint_preimage hfactor hdiff hfinite hunit (ℜ x) (ℜ x).property
  obtain ⟨b,hb⟩ := traceFreeHilbertClosure_selfAdjoint_preimage hfactor hdiff hfinite hunit (ℑ x) (ℑ x).property
  refine ⟨a+Complex.I • b,?_⟩
  rw [map_add,map_smul,ha,hb]
  exact realPart_add_I_smul_imaginaryPart x

theorem traceFreeHilbertIntoClosure_injective : Function.Injective ρ := by
  intro a b hab
  exact traceFreeHilbertAction_injective hfactor hdiff hfinite hunit (congrArg Subtype.val hab)

def traceFreeHilbertEquiv : M.toStarSubalgebra ≃⋆ₐ[ℂ] (N).toStarSubalgebra :=
  StarAlgEquiv.ofBijective ρ ⟨traceFreeHilbertIntoClosure_injective hfactor hdiff hfinite hunit,
    traceFreeHilbertIntoClosure_surjective hfactor hdiff hfinite hunit⟩

end

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
attribute [local instance] OAI.Generator.Tracial.traceHilbertTransportCStar
local instance traceHilbertTransportOrder_r683021_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertTransportStarOrder_r683021_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceHilbertTransportOperatorCStar_r683021_1 : CStarAlgebra (K →L[ℂ] K) := {}
local instance traceHilbertTransportClosureCStar : CStarAlgebra (N).toStarSubalgebra := {}

local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

theorem traceFreeHilbertEquiv_norm (a : M.toStarSubalgebra) : ‖e a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (e).toStarAlgHom (e).injective a

def traceFreeHilbertIsometry : M.toStarSubalgebra ≃ₗᵢ[ℂ] (N).toStarSubalgebra :=
  { (e).toAlgEquiv.toLinearEquiv with
    norm_map' := traceFreeHilbertEquiv_norm hfactor hdiff hfinite hunit }

end Tracial

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

local instance traceSubalgebraBallOperatorCStar_r683021_1 : CStarAlgebra (K →L[ℂ] K) := {}
variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraBallCStar
local instance traceSubalgebraBallOrder_r683021_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraBallStarOrder_r683021_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceSubalgebraBallClosureCStar_r683021_1 : CStarAlgebra (N).toStarSubalgebra := {}
def traceFreeSubalgebraWeakBall (C : ℝ) : Set (K →WOT[ℂ] K) :=
  {T | ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ‖a‖ ≤ C ∧
    ContinuousLinearMapWOT.ofCLM (π a) = T}

def traceFreeSubalgebraVectorBall (C : ℝ) : Set K :=
  {x | ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ‖a‖ ≤ C ∧ π a Ω = x}

end Tracial

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local instance traceSubalgebraImageOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

end

/-! Generation pullback for the actual constructed trace representation. -/

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_OriginalUnitary
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

/- Normalized trace-two topology on actual unitaries of the original factor.
   The wrapper avoids Mathlib's existing operator-norm topology on unitary S. -/
open scoped Topology
namespace Generator
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}

open Tracial
variable (S) (hS : IsII1Factor S)
local notation "hf" => hS.factor_smul
local notation "hu" => hS.one_ne_zero
local notation "σ" => traceFreeHilbertClosureTrace hf hS.diffuse hS.finite hu
local notation "e" => traceFreeHilbertEquiv hf hS.diffuse hS.finite hu
local notation "π" => traceFreeHilbertAction hf hS.diffuse hS.finite hu
local notation "Ω" => traceFreeHilbertVector hf hS.diffuse hS.finite hu

/- Supply the already constructed Hilbert instances explicitly: inference does
   not reconstruct the original von Neumann algebra from its subtype here. -/
local instance factorTracePreNormed :
    NormedAddCommGroup (TraceFreePreHilbert hf hS.diffuse hS.finite hu) :=
  traceFreePreHilbertNormedAddCommGroup hf hS.diffuse hS.finite hu
local instance factorTracePreInner :
    InnerProductSpace ℂ (TraceFreePreHilbert hf hS.diffuse hS.finite hu) :=
  traceFreePreHilbertInnerProductSpace hf hS.diffuse hS.finite hu

/-- The constructed faithful normalized trace on the original factor. -/
def normalizedFactorTrace : S →L[ℂ] ℂ := traceFreeTrace hf hS.diffuse hS.finite hu

namespace FactorTraceUnitary

def represented (u : FactorTraceUnitary S hS) : TraceUnitary σ :=
  ⟨⟨e (u.algebra S hS),Unitary.map_mem e u.toUnitary.property⟩⟩

def representedEquiv : FactorTraceUnitary S hS ≃ TraceUnitary σ where
  toFun := represented S hS
  invFun v := ⟨⟨(e).symm (v.algebra σ),Unitary.map_mem (e).symm v.toUnitary.property⟩⟩
  left_inv u := by
    cases u
    simp only [represented,algebra,TraceUnitary.algebra,StarAlgEquiv.symm_apply_apply]
  right_inv v := by
    cases v
    simp only [represented,algebra,TraceUnitary.algebra,StarAlgEquiv.apply_symm_apply]

instance instMetricSpace : MetricSpace (FactorTraceUnitary S hS) :=
  MetricSpace.induced (represented S hS) (representedEquiv S hS).injective inferInstance

def representedIsometryEquiv : FactorTraceUnitary S hS ≃ᵢ TraceUnitary σ :=
  { representedEquiv S hS with isometry_toFun := fun _ _ => rfl }

def representedHomeomorph : FactorTraceUnitary S hS ≃ₜ TraceUnitary σ :=
  (representedIsometryEquiv S hS).toHomeomorph

/-- The metric is literally the normalized trace two-norm of the difference. -/
theorem dist_eq_trace (u v : FactorTraceUnitary S hS) :
    dist u v = Real.sqrt ((normalizedFactorTrace S hS)
      (star (u.algebra S hS-v.algebra S hS)*(u.algebra S hS-v.algebra S hS))).re := by
  change dist (represented S hS u) (represented S hS v) = _
  rw [TraceUnitary.dist_eq]
  change ‖(π (u.algebra S hS)-π (v.algebra S hS)) Ω‖ = _
  rw [← map_sub,traceFreeHilbertAction_vector,LinearIsometry.norm_map]
  rw [normalizedFactorTrace,← traceFreeCopy_norm_sq hf hS.diffuse hS.finite hu,Real.sqrt_sq (norm_nonneg _)]

/-- The transported metric topology agrees with the trace-ball topology on genuine unitaries. -/
def traceHomeomorph :
    @Homeomorph (FactorTraceUnitary S hS) (unitary S) inferInstance
      (RelativeGeneration.traceTopology S (normalizedFactorTrace S hS)) :=
  RelativeGeneration.traceUnitaryHomeomorph S (normalizedFactorTrace S hS)
    (unitaryEquiv S hS) (fun left right => dist_eq_trace S hS left right)

end FactorTraceUnitary
end Generator

end

end OAI
end


