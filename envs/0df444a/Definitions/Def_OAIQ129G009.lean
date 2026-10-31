-- Prove2me | Definitions.Def_OAIQ129G009
-- name    : OAIQ129G009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:24:46.350845+00:00
-- url     : https://prove2.me/theorems/eb754070-73de-4b75-a755-e5fb0f3121f2
-- title:
--   Definitions bundle OAIQ129G009 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 8 definitions, 14 instances and 11 theorems. The definitions and types are `OAI.Generator.Tracial.CornerPartition.blockIndices`, `OAI.Generator.Tracial.CornerPartition.includeUnit`, `OAI.Generator.Tracial.CornerPartition.mapInclusion`, `OAI.Generator.Tracial.CornerPartition.refineBlocks`, `OAI.Generator.Tracial.boundedMap`, `OAI.Generator.Tracial.coordinateTraceLinear`, `OAI.Generator.Tracial.unitResidualPatch`, `OAI.UltrapowerBridge.quotientStarAlgHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_LocalPatches`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalPatches.lean), [`FactorGeneration_LocalQuantization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalQuantization.lean), [`FactorGeneration_LongWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LongWords.lean), [`FactorGeneration_Pinching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Pinching.lean), [`FactorGeneration_ProjectionLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProjectionLimits.lean), [`FactorGeneration_QuotientRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/QuotientRepresentation.lean), [`FactorGeneration_SpectralApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralApproximation.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean), [`FactorGeneration_Ultrapower`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Ultrapower.lean).
--
--   **Imports.** It imports the bundles `OAIQ129G003`, `OAIQ129G004` and `OAIQ129G005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G011` and `OAIQ129G012`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ129G003
import Definitions.Def_OAIQ129G004
import Definitions.Def_OAIQ129G005

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

theorem quotientMap_eq_iff (a b : Bounded M) :
    quotientMap τ l a = quotientMap τ l b ↔ TraceRel τ l a b := Quotient.eq

instance instStarRingTracialQuotient : StarRing (TracialQuotient τ l) where
  star_involutive a := Quotient.inductionOn a (fun a => by
    change quotientMap τ l (star (star a)) = quotientMap τ l a
    rw [star_star])
  star_mul a b := Quotient.inductionOn₂ a b (fun a b => by
    change quotientMap τ l (star (a*b)) = quotientMap τ l (star b*star a)
    rw [star_mul])
  star_add a b := Quotient.inductionOn₂ a b (fun a b => by
    change quotientMap τ l (star (a+b)) = quotientMap τ l (star a+star b)
    rw [star_add])

instance instStarModuleComplexTracialQuotient : StarModule ℂ (TracialQuotient τ l) where
  star_smul c a := Quotient.inductionOn a (fun a =>
    congrArg (quotientMap τ l) (star_smul c a))

def quotientStarAlgHom : Bounded M →⋆ₐ[ℂ] TracialQuotient τ l where
  __ := quotientMap τ l
  commutes' _ := rfl
  map_star' := quotientMap_star τ l

/- Shortcut instances (q129): named, high-priority copies of the quotient's instances, so that
terms over `TracialQuotient τ l` and its unitary group carry small instance arguments. -/
instance (priority := high) q129Ring : Ring (TracialQuotient τ l) := inferInstance
instance (priority := high) q129NUNAS : NonUnitalNonAssocSemiring (TracialQuotient τ l) := inferInstance
instance (priority := high) q129NAS : NonAssocSemiring (TracialQuotient τ l) := inferInstance
instance (priority := high) q129Monoid : Monoid (TracialQuotient τ l) := inferInstance
instance (priority := high) q129MulOneClass : MulOneClass (TracialQuotient τ l) := inferInstance
instance (priority := high) q129Zero : Zero (TracialQuotient τ l) := inferInstance
instance (priority := high) q129Neg : Neg (TracialQuotient τ l) := inferInstance
instance (priority := high) q129Sub : Sub (TracialQuotient τ l) := inferInstance
instance (priority := high) q129AddCommGroup : AddCommGroup (TracialQuotient τ l) := inferInstance
instance (priority := high) q129Module : Module ℂ (TracialQuotient τ l) := inferInstance
instance (priority := high) q129StarRing : StarRing (TracialQuotient τ l) := inferInstance

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem projection_trace_sq (p : M.toStarSubalgebra) (hp : IsStarProjection p) :
    (τ.trace p).re = τ.norm₂ p ^ 2 := by
  have h := congrArg Complex.re (τ.trace_star_mul p)
  simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

theorem exists_half_trace_subprojection
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ p*q = q ∧ q*p = q ∧
      (τ.trace q).re ≤ (τ.trace p).re/2 := by
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hdiff p hp hne
  by_cases hsmall : (τ.trace q).re ≤ (τ.trace p).re/2
  · exact ⟨q,hq,hq0,hpq,hqp',hsmall⟩
  · refine ⟨p-q, ?_, sub_ne_zero.mpr hqp.symm, ?_, ?_, ?_⟩
    · exact hq.sub_of_mul_eq_right hp hpq
    · rw [mul_sub, hp.isIdempotentElem.eq, hpq]
    · rw [sub_mul, hp.isIdempotentElem.eq, hqp']
    · have ht : τ.trace (p-q) = τ.trace p-τ.trace q := inner_sub_right _ _ _
      rw [ht, Complex.sub_re]
      linarith

theorem exists_geometric_trace_subprojection
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0) (n : ℕ) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ p*q = q ∧ q*p = q ∧
      (τ.trace q).re ≤ (1/2 : ℝ)^n * (τ.trace p).re := by
  induction n with
  | zero => exact ⟨p,hp,hne,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq,by simp⟩
  | succ n ih =>
    obtain ⟨q,hq,hq0,hpq,hqp,htq⟩ := ih
    obtain ⟨r,hr,hr0,hqr,hrq,htr⟩ := exists_half_trace_subprojection τ hdiff q hq hq0
    refine ⟨r,hr,hr0,?_,?_,?_⟩
    · calc p*r = p*(q*r) := by rw [hqr]
           _ = (p*q)*r := (mul_assoc _ _ _).symm
           _ = r := by rw [hpq,hqr]
    · calc r*p = (r*q)*p := by rw [hrq]
           _ = r*(q*p) := mul_assoc _ _ _
           _ = r := by rw [hqp,hrq]
    · rw [pow_succ]
      nlinarith

end

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- A bounded increasing net of actual projections has a projection upper bound
with the same trace bound. No projection-lattice completeness is assumed. -/
theorem monotone_projection_upper_bound (τ : TracialRepresentation M)
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a) (r : ℝ)
    (hr : ∀ i, (τ.trace (a i).val).re ≤ r) :
    ∃ b : AlgebraProjection M, (∀ i, a i ≤ b) ∧ (τ.trace b.val).re ≤ r ∧
      ∀ p : AlgebraProjection M, (∀ i, a i ≤ p) → b ≤ p := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, hT, ht⟩ := exists_weak_operator_ultralimit ω
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
  refine ⟨⟨b, ⟨hid, hself⟩⟩, hba, ?_, ?_⟩
  · exact le_of_tendsto ((Complex.continuous_re.tendsto _).comp (hb τ.vector τ.vector))
      (Eventually.of_forall hr)
  · intro p hp
    change p.val * b = b
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hh := hb x (star (p.val : H →L[ℂ] H) y)
    simp only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at hh
    exact tendsto_nhds_unique hh ((hb x y).congr (fun i =>
      (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (hp i)).symm))

end

/-! Exact trace cuts in a diffuse coordinate algebra. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_maximal_trace_subprojection (p : AlgebraProjection M)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ (τ.trace q.val).re ≤ r ∧
      ∀ s : AlgebraProjection M, s ≤ p → (τ.trace s.val).re ≤ r → q ≤ s → s ≤ q := by
  let S : Set (AlgebraProjection M) := {q | q ≤ p ∧ (τ.trace q.val).re ≤ r}
  obtain ⟨q,hq⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · let : Nonempty c := hne.to_subtype
      let : IsDirected c (· ≤ ·) := ⟨by
        intro x y
        obtain ⟨z,hz,hxz,hyz⟩ := hchain.directedOn x.val x.property y.val y.property
        exact ⟨⟨z,hz⟩,hxz,hyz⟩⟩
      obtain ⟨b,hb,hbr,hmin⟩ := monotone_projection_upper_bound τ
        (fun x : c => x.val) (fun _ _ h => h) r (fun x => (hc x.property).2)
      exact ⟨b, ⟨hmin p (fun x => (hc x.property).1),hbr⟩,
        fun z hz => hb ⟨z,hz⟩⟩
    · refine ⟨⟨0,IsStarProjection.zero _⟩, ⟨?_,?_⟩, ?_⟩
      · change p.val * 0 = 0
        exact mul_zero _
      · simpa [TracialRepresentation.trace] using hr
      · intro z hz
        exact (hne ⟨z,hz⟩).elim)
  exact ⟨q,hq.1.1,hq.1.2,fun s hsp hsr hqs => hq.2 ⟨hsp,hsr⟩ hqs⟩

end

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def coordinateTraceLinear (τ : TracialRepresentation M) : M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun := τ.trace
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
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

variable (Q : CornerPartition p) (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem blockFamily_orthogonal (a b : (i : Fin Q.size) × Fin (R i).size) (hab : a ≠ b) :
    ((R a.1).piece a.2).val * ((R b.1).piece b.2).val = 0 := by
  by_cases h : a.1=b.1
  · obtain ⟨i,j⟩ := a
    obtain ⟨k,l⟩ := b
    dsimp at h ⊢
    subst k
    exact (R i).orthogonal j l (fun h => hab (by cases h; rfl))
  · exact orthogonal_subprojections (Q.orthogonal a.1 b.1 h)
      ((R a.1).piece_le a.2) ((R b.1).piece_le b.2)

/-- All blocks are replaced by their chosen finite subpartitions. -/
def refineBlocks : CornerPartition p :=
  ofFamily (fun a : (i : Fin Q.size) × Fin (R i).size => (R a.1).piece a.2)
    (Q.blockFamily_orthogonal R) (Q.blockFamily_total R)

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

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

def blockIndices (i : Fin Q.size) : Finset (Fin (Q.refineBlocks R).size) :=
  Finset.univ.filter fun j =>
    ((Fintype.equivFin ((k : Fin Q.size) × Fin (R k).size)).symm j).1=i

end CornerPartition

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LocalQuantization
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! An actual irreducible subalgebra and its constructed conditional
expectation give finite pinching partitions with energy arbitrarily close
to the expectation energy. No partition or expectation is supplied. -/
open scoped BigOperators

/-! Convert the source's decreasing irreducible chain into actual finite
pinching partitions. The chain and its irreducibility are explicit inputs;
its existence in an arbitrary factor is not asserted. -/
open scoped BigOperators

/-! Restrict a compatible unit partition to an actual corner, retaining
all pieces and the exact compression. -/
open scoped BigOperators

/-! Complete a corner partition by the complementary projection. This lets
the existing compatible refinement construction act on an actual p-corner. -/
open scoped BigOperators

/-! Transfer actual corner partitions along a concrete von Neumann
subalgebra inclusion, preserving pieces, pinching and tracial energy. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection N} (Q : CornerPartition p)

def mapInclusion (hNM : N ≤ M) : CornerPartition (includedProjection hNM p) where
  size := Q.size
  piece i := includedProjection hNM (Q.piece i)
  orthogonal i j hij := by
    change coordinateInclusion hNM (Q.piece i).val*coordinateInclusion hNM (Q.piece j).val=0
    rw [← map_mul,Q.orthogonal i j hij,map_zero]
  total := by
    change (∑ i,coordinateInclusion hNM (Q.piece i).val)=coordinateInclusion hNM p.val
    rw [← map_sum,Q.total]

/-- Unit partitions use the ambient identity, with no transport of the
underlying finite index set. -/
def includeUnit (Q : CornerPartition (identityProjection N)) (hNM : N ≤ M) :
    CornerPartition (identityProjection M) where
  size := Q.size
  piece := (Q.mapInclusion hNM).piece
  orthogonal := (Q.mapInclusion hNM).orthogonal
  total := (Q.mapInclusion hNM).total

end CornerPartition
end

/-! The two applications of orthogonal refinement in Popa A.1.2, equations
(2) and (3). The inner decreasing chain need only be irreducible in N;
irreducibility of its terms in the ambient M is not imposed. -/
open scoped BigOperators

/-! Nonzero local projections obtained from the constructed nested-chain
partition. This implements the finite squared-energy selection at the end
of A.1.2, while retaining the chain as a structural premise. -/
open scoped BigOperators

/-! Local quantization by finite matrix approximation and Bell pinching under represented trace-vector separability. -/
open scoped BigOperators
open UltrapowerBridge FiniteMatrixStage

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LocalPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Construct local patches in the actual f=1 residual. Both residual trace
terms are retained. Admissibility of the full extended word family is not asserted. -/

/-! A single actual residual patch controls every finite internal word of the
source family. All scalar moment premises are proved from admissibility. -/

/-! Trace estimates for each actual binary-mask term, using the constructed
finite families. No moment estimate or middle-family extraction is assumed. -/

/-! Strict support growth for the actual f=1 admissible set. The single patch
is chosen from the finite coefficient families before any word is tested. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def unitResidualPatch (v : PartialUnitary M) (q : AlgebraProjection M) (w : CornerUnitary q)
    (hq : q ≤ unitResidual v) : PartialUnitary M :=
  ⟨⟨v.support.val+q.val,v.support.property.add q.property (unitResidual_orthogonal v q hq)⟩,
    v.unitary.patch w (unitResidual_orthogonal v q hq)⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/
section
open scoped BigOperators
open Generator.CoefficientOrder
variable {G : Type*} [Monoid G]

@[simp] theorem normCoefficients_zero : normCoefficients (0 : MonoidAlgebra ℂ G) = 0 := by
  ext w; simp

@[simp] theorem normCoefficients_one : normCoefficients (1 : MonoidAlgebra ℂ G) = 1 := by
  classical
  ext w
  simp only [normCoefficients_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split_ifs <;> norm_num

omit [Monoid G] in
@[simp] theorem normCoefficients_single (g : G) (c : ℂ) :
    normCoefficients (MonoidAlgebra.single g c) = MonoidAlgebra.single g ‖c‖ := by
  classical
  ext w
  simp only [normCoefficients_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

end

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Forget continuity (automatic on the discrete index set) and retain boundedness. -/
def boundedMap : Sequences M →⋆ₐ[ℂ] Bounded M where
  toFun a := ⟨a, ⟨‖a‖, norm_nonneg a, a.norm_coe_le_norm⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem boundedMap_surjective : Function.Surjective (boundedMap (M := M)) := by
  intro a
  obtain ⟨C, _, hC⟩ := a.property
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete a.val C hC, ?_⟩
  apply Subtype.ext
  funext n
  rfl

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

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

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
attribute [local instance] OAI.Generator.Tracial.traceHilbertCStar
attribute [local instance] OAI.Generator.Tracial.traceHilbertOrder
attribute [local instance] OAI.Generator.Tracial.traceHilbertStarOrder
instance traceFreePreHilbertStarModule : StarModule ℂ E :=
  inferInstanceAs (StarModule ℂ M.toStarSubalgebra)

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


