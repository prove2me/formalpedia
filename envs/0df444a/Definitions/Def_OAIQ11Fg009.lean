-- Prove2me | Definitions.Def_OAIQ11Fg009
-- name    : OAIQ11Fg009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:41:34.482813+00:00
-- url     : https://prove2.me/theorems/82db9b86-a9c0-4282-8ece-dca63b6bc70f
-- title:
--   Definitions bundle OAIQ11Fg009 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 27 definitions, 4 instances and 42 theorems. The definitions and types are `OAI.Generator.Tracial.PatchingAdmissible`, `OAI.Generator.Tracial.PatchingAdmissibleIn`, `OAI.Generator.Tracial.RelativePolynomial.eval`, `OAI.Generator.Tracial.RelativePolynomial.sectionVector`, `OAI.Generator.Tracial.RelativePolynomial.valueAlgebra`, `OAI.Generator.Tracial.coordinateTraceLinear`, `OAI.Generator.Tracial.cyclicCoefficient`, `OAI.Generator.Tracial.cyclicPredual`, `OAI.Generator.Tracial.cyclicPredualEvaluation`, `OAI.Generator.Tracial.cyclicPredualEvaluationIsometry`, `OAI.Generator.Tracial.cyclicPredualLinearEquiv`, `OAI.Generator.Tracial.dyadicCornerUnitary`, `OAI.Generator.Tracial.dyadicEval`, `OAI.Generator.Tracial.dyadicProjection`, `OAI.Generator.Tracial.dyadicRademacher`, `OAI.Generator.Tracial.halfTraceCut`, `OAI.Generator.Tracial.predualWeakBall`, `OAI.Generator.Tracial.predualWeakEvaluation`, `OAI.Generator.Tracial.relativeGenerators`, `OAI.Generator.Tracial.splitProjection`, `OAI.Generator.Tracial.traceCyclicHom`, `OAI.Generator.Tracial.traceCyclicLinearIsometry`, `OAI.Generator.Tracial.traceCyclicVector`, `OAI.Generator.Tracial.zeroPartialUnitary`, `OAI.Generator.negativeLetterPair`, `OAI.Generator.perturbationRow`, `OAI.Generator.positiveLetterPair`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CyclicPredual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CyclicPredual.lean), [`FactorGeneration_Expectations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Expectations.lean), [`FactorGeneration_HilbertLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HilbertLimits.lean), [`FactorGeneration_LongWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LongWords.lean), [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_PartialUnitaries`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PartialUnitaries.lean), [`FactorGeneration_PatchingWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PatchingWords.lean), [`FactorGeneration_PredualRange`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualRange.lean), [`FactorGeneration_ProjectionLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProjectionLimits.lean), [`FactorGeneration_RelativeGeneration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/RelativeGeneration.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg003`, `OAIQ11Fg004` and `OAIQ11Fg005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg012` and `OAIQ11Fg014`; the statements `OAI_Generator_FiniteMatrixStage_exists_matrix_approximated_centered_partition`, `OAI_Generator_FiniteMatrixStage_two_generators_of_tensor_extensions`, `OAI_Generator_Tracial_betweenWord_integerValue`, `OAI_Generator_Tracial_exists_coordinate_haar_endpoints`, `OAI_Generator_Tracial_exists_matrix_generated_ambient_centered_partition`, `OAI_Generator_Tracial_integerValueWord_blocks`, `OAI_Generator_Tracial_integerValueWord_closedSpan`, `OAI_Generator_Tracial_integerValueWord_inv`, `OAI_Generator_Tracial_integerValueWord_mul_power`, `OAI.Generator.Tracial.predualFunctional_mem_cyclicPredual` and `OAI_Generator_Tracial_reduced_integer_gap_functional`; the proofs of `OAI.Generator.FiniteMatrixStage.generated_isII1`, `OAI_Generator_FiniteMatrixStage_two_generators_of_tensor_extensions`, `OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra`, `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget`, `OAI_Generator_Tracial_betweenWord_integerValue`, `OAI_Generator_Tracial_exists_coordinate_haar_endpoints`, `OAI_Generator_Tracial_exists_irreducible_centered_partition`, `OAI.Generator.Tracial.exists_matrixUnits_for_partition`, `OAI.Generator.Tracial.exists_normal_matrix_approximation`, `OAI_Generator_Tracial_integerValueWord_blocks`, `OAI_Generator_Tracial_integerValueWord_closedSpan`, `OAI_Generator_Tracial_integerValueWord_inv`, `OAI_Generator_Tracial_integerValueWord_mul_power`, `OAI.Generator.Tracial.predual_small_of_small_trace_sandwich` and `OAI_Generator_Tracial_reduced_integer_gap_functional`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg003
import Definitions.Def_OAIQ11Fg004
import Definitions.Def_OAIQ11Fg005

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

theorem projection_trace_pos (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0) :
    0 < (τ.trace p).re := by
  rw [projection_trace_sq τ p hp]
  exact sq_pos_of_ne_zero (fun h => hne ((τ.norm₂_eq_zero_iff p).mp h))

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

theorem exists_small_trace_subprojection
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ p*q = q ∧ q*p = q ∧
      0 < (τ.trace q).re ∧ (τ.trace q).re < ε := by
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n * (τ.trace p).re) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).mul_const (τ.trace p).re
  have he : ∀ᶠ n : ℕ in atTop, (1/2 : ℝ)^n * (τ.trace p).re < ε := ht (Iio_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  obtain ⟨q,hq,hq0,hpq,hqp,hbound⟩ := exists_geometric_trace_subprojection τ hdiff p hp hne n
  exact ⟨q,hq,hq0,hpq,hqp,projection_trace_pos τ q hq hq0,hbound.trans_lt hn⟩

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

/-- Every projection can be cut to any smaller prescribed real trace. -/
theorem exists_exact_trace_subprojection
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (r : ℝ) (hr : 0 ≤ r) (hrp : r ≤ (τ.trace p).re) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ p*q = q ∧ q*p = q ∧
      τ.trace q = (r : ℂ) := by
  obtain ⟨q,hqp,hqr,hmax⟩ := exists_maximal_trace_subprojection τ ⟨p,hp⟩ r hr
  have hpq : p*q.val = q.val := hqp
  have hqp' : q.val*p = q.val := projection_mul_of_le hqp
  have htrace : (τ.trace q.val).re = r := by
    by_contra hne
    have hlt : (τ.trace q.val).re < r := lt_of_le_of_ne hqr hne
    have hres : IsStarProjection (p-q.val) := q.property.sub_of_mul_eq_right hp hpq
    have hres0 : p-q.val ≠ 0 := by
      intro he
      have he' : p=q.val := sub_eq_zero.mp he
      rw [he'] at hrp
      exact (not_lt_of_ge hrp) hlt
    obtain ⟨s,hs,hs0,hps,hsp,hst,hsmall⟩ := exists_small_trace_subprojection τ hdiff
      (p-q.val) hres hres0 (r-(τ.trace q.val).re) (sub_pos.mpr hlt)
    have hqs : q.val*s = 0 := by
      calc q.val*s = q.val*((p-q.val)*s) := by rw [hps]
           _ = (q.val*(p-q.val))*s := (mul_assoc _ _ _).symm
           _ = 0 := by rw [mul_sub,hqp',q.property.isIdempotentElem.eq,sub_self,zero_mul]
    have hsq : s*q.val = 0 := by
      simpa only [star_mul,hs.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hqs
    have hps' : p*s=s := by
      have he : p*(p-q.val)=p-q.val := by rw [mul_sub,hp.isIdempotentElem.eq,hpq]
      calc p*s = p*((p-q.val)*s) := by rw [hps]
           _ = (p*(p-q.val))*s := (mul_assoc _ _ _).symm
           _ = s := by rw [he,hps]
    let t : AlgebraProjection M := ⟨q.val+s,q.property.add hs hqs⟩
    have htp : t ≤ ⟨p,hp⟩ := by
      change p*(q.val+s)=q.val+s
      rw [mul_add,hpq,hps']
    have hqt : q ≤ t := by
      change (q.val+s)*q.val=q.val
      rw [add_mul,q.property.isIdempotentElem.eq,hsq,add_zero]
    have htt : (τ.trace t.val).re ≤ r := by
      change (τ.trace (q.val+s)).re ≤ r
      have he : τ.trace (q.val+s)=τ.trace q.val+τ.trace s := inner_add_right _ _ _
      rw [he,Complex.add_re]
      linarith
    have heq : t=q := le_antisymm (hmax t htp htt hqt) hqt
    have he : q.val+s=q.val := congrArg Subtype.val heq
    have : s=0 := add_left_cancel (he.trans (add_zero q.val).symm)
    exact hs0 this
  refine ⟨q.val,q.property,hpq,hqp',?_⟩
  have he := τ.trace_star_mul q.val
  rw [q.property.isSelfAdjoint.star_eq,q.property.isIdempotentElem.eq] at he
  rw [he,← Complex.ofReal_pow]
  congr 1
  rw [← projection_trace_sq τ q.val q.property,htrace]

end

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

include hdiff in
theorem exists_half_trace_cut (p : AlgebraProjection M) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ τ.trace q.val = ((τ.trace p.val).re/2 : ℝ) := by
  have ht : 0 ≤ (τ.trace p.val).re := by
    rw [projection_trace_sq τ p.val p.property]
    positivity
  obtain ⟨q,hq,hpq,hqp,htr⟩ := exists_exact_trace_subprojection τ hdiff p.val p.property
    ((τ.trace p.val).re/2) (by positivity) (by linarith)
  exact ⟨⟨q,hq⟩,hpq,htr⟩

def halfTraceCut (p : AlgebraProjection M) : AlgebraProjection M :=
  (exists_half_trace_cut τ hdiff p).choose

theorem halfTraceCut_le (p : AlgebraProjection M) : halfTraceCut τ hdiff p ≤ p :=
  (exists_half_trace_cut τ hdiff p).choose_spec.1

/-- Both halves belong to the original algebra. -/
def splitProjection (p : AlgebraProjection M) (b : Bool) : AlgebraProjection M :=
  if b then ⟨p.val-(halfTraceCut τ hdiff p).val,
    (halfTraceCut τ hdiff p).property.sub_of_mul_eq_right p.property (halfTraceCut_le τ hdiff p)⟩
  else halfTraceCut τ hdiff p

theorem splitProjection_le (p : AlgebraProjection M) (b : Bool) :
    splitProjection τ hdiff p b ≤ p := by
  cases b
  · exact halfTraceCut_le τ hdiff p
  · change p.val*(p.val-(halfTraceCut τ hdiff p).val)=p.val-(halfTraceCut τ hdiff p).val
    rw [mul_sub,p.property.isIdempotentElem.eq,halfTraceCut_le τ hdiff p]

theorem splitProjection_sum (p : AlgebraProjection M) :
    (splitProjection τ hdiff p false).val+(splitProjection τ hdiff p true).val=p.val := by
  simp [splitProjection]

theorem splitProjection_orthogonal (p : AlgebraProjection M) :
    (splitProjection τ hdiff p false).val*(splitProjection τ hdiff p true).val=0 := by
  change (halfTraceCut τ hdiff p).val*(p.val-(halfTraceCut τ hdiff p).val)=0
  rw [mul_sub,projection_mul_of_le (halfTraceCut_le τ hdiff p),
    (halfTraceCut τ hdiff p).property.isIdempotentElem.eq,sub_self]

def dyadicProjection (p : AlgebraProjection M) : (n : ℕ) → DyadicIndex n → AlgebraProjection M
  | 0, _ => p
  | n+1, i => splitProjection τ hdiff (dyadicProjection p n i.1) i.2

theorem dyadicProjection_le_parent (p : AlgebraProjection M) (n : ℕ) (i : DyadicIndex (n+1)) :
    dyadicProjection τ hdiff p (n+1) i ≤ dyadicProjection τ hdiff p n i.1 :=
  splitProjection_le τ hdiff _ _

theorem dyadicProjection_sum (p : AlgebraProjection M) (n : ℕ) :
    ∑ i : DyadicIndex n, (dyadicProjection τ hdiff p n i).val = p.val := by
  induction n with
  | zero => change (∑ _ : Unit, p.val)=p.val; simp
  | succ n ih =>
    change (∑ i : DyadicIndex n × Bool,
      (splitProjection τ hdiff (dyadicProjection τ hdiff p n i.1) i.2).val)=p.val
    rw [Fintype.sum_prod_type]
    simpa only [Fintype.sum_bool,add_comm,splitProjection_sum] using ih

theorem dyadicProjection_orthogonal (p : AlgebraProjection M) (n : ℕ)
    (i j : DyadicIndex n) (hij : i ≠ j) :
    (dyadicProjection τ hdiff p n i).val*(dyadicProjection τ hdiff p n j).val=0 := by
  induction n with
  | zero => exact (hij (@Subsingleton.elim Unit _ i j)).elim
  | succ n ih =>
    by_cases he : i.1=j.1
    · obtain ⟨i,b⟩ := i
      obtain ⟨j,c⟩ := j
      dsimp at he
      subst j
      cases b <;> cases c
      · exact (hij rfl).elim
      · exact splitProjection_orthogonal τ hdiff _
      · have h := congrArg star (splitProjection_orthogonal τ hdiff (dyadicProjection τ hdiff p n i))
        simpa only [dyadicProjection,star_mul,star_zero,(splitProjection τ hdiff _ false).property.isSelfAdjoint.star_eq,
          (splitProjection τ hdiff _ true).property.isSelfAdjoint.star_eq] using h
      · exact (hij rfl).elim
    · exact orthogonal_subprojections (ih i.1 j.1 he)
        (dyadicProjection_le_parent τ hdiff p n i) (dyadicProjection_le_parent τ hdiff p n j)

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def coordinateTraceLinear (τ : TracialRepresentation M) : M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun := τ.trace
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

variable {ι : Type*} [Fintype ι]

variable (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

abbrev dyadicEval (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :=
  projectionSum (dyadicProjection τ hdiff p n) c

theorem dyadicEval_one (p : AlgebraProjection M) (n : ℕ) :
    dyadicEval τ hdiff p n (fun _ => 1)=p.val := by
  simpa only [dyadicEval,projectionSum,one_smul] using dyadicProjection_sum τ hdiff p n

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed _root_.OAI.Generator.predualFunctionals_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/

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

def traceCyclicVector : traceCyclicSpace τ := ⟨τ.vector,mem_vectorOrbitClosure _ _⟩

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
-- module Solutions.OAIQ11_FG.FactorGeneration_CyclicPredual
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed _root_.OAI.Generator.predualFunctionals_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

theorem cyclicCoefficient_norm_le (ξ η : traceCyclicSpace τ) :
    ‖cyclicCoefficient τ ξ η‖ ≤ ‖ξ‖*‖η‖ := by
  apply (cyclicCoefficient τ ξ η).opNorm_le_bound (M := ‖ξ‖*‖η‖) (mul_nonneg (norm_nonneg ξ) (norm_nonneg η))
  intro a
  calc
    ‖cyclicCoefficient τ ξ η a‖ ≤ ‖ξ‖*‖traceCyclicHom τ a η‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖*(‖traceCyclicHom τ a‖*‖η‖) :=
      mul_le_mul_of_nonneg_left ((traceCyclicHom τ a).le_opNorm η) (norm_nonneg _)
    _ = (‖ξ‖*‖η‖)*‖a‖ := by rw [traceCyclicHom_norm]; ring

abbrev cyclicPredual : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) :=
  (Submodule.span ℂ (Set.range (fun p : traceCyclicSpace τ × traceCyclicSpace τ =>
    cyclicCoefficient τ p.1 p.2))).topologicalClosure

instance cyclicPredual_normed : NormedAddCommGroup (cyclicPredual τ) := inferInstance

instance cyclicPredual_normedSpace : NormedSpace ℂ (cyclicPredual τ) := inferInstance

instance cyclicPredual_complete : CompleteSpace (cyclicPredual τ) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (Set.range
    (fun p : traceCyclicSpace τ × traceCyclicSpace τ => cyclicCoefficient τ p.1 p.2))).topologicalClosure)

theorem cyclicCoefficient_mem (ξ η : traceCyclicSpace τ) :
    cyclicCoefficient τ ξ η ∈ cyclicPredual τ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(ξ,η),rfl⟩)

def cyclicPredualEvaluation (a : M.toStarSubalgebra) : StrongDual ℂ (cyclicPredual τ) :=
  (ContinuousLinearMap.apply ℂ ℂ a).domRestrict (cyclicPredual τ)

@[simp] theorem cyclicPredualEvaluation_apply (a : M.toStarSubalgebra) (f : cyclicPredual τ) :
    cyclicPredualEvaluation τ a f=f.val a := rfl

theorem cyclicPredualEvaluation_norm_le (a : M.toStarSubalgebra) :
    ‖cyclicPredualEvaluation τ a‖ ≤ ‖a‖ := by
  apply (cyclicPredualEvaluation τ a).opNorm_le_bound (M := ‖a‖) (norm_nonneg a)
  intro f
  exact (f.val.le_opNorm a).trans_eq (mul_comm _ _)

theorem cyclicPredualEvaluation_norm (a : M.toStarSubalgebra) :
    ‖cyclicPredualEvaluation τ a‖=‖a‖ := by
  apply le_antisymm (cyclicPredualEvaluation_norm_le τ a)
  rw [← traceCyclicHom_norm τ a]
  apply (traceCyclicHom τ a).opNorm_le_bound
    (M := ‖cyclicPredualEvaluation τ a‖) (ContinuousLinearMap.opNorm_nonneg _)
  intro η
  let ξ := traceCyclicHom τ a η
  let f : cyclicPredual τ := ⟨cyclicCoefficient τ ξ η,cyclicCoefficient_mem τ ξ η⟩
  have h : ‖inner ℂ ξ ξ‖ ≤ ‖cyclicPredualEvaluation τ a‖*(‖ξ‖*‖η‖) :=
    ((cyclicPredualEvaluation τ a).le_opNorm f).trans
      (mul_le_mul_of_nonneg_left (cyclicCoefficient_norm_le τ ξ η) (norm_nonneg _))
  have hs : ‖inner ℂ ξ ξ‖=‖ξ‖^2 := by
    rw [inner_self_eq_norm_sq_to_K,norm_pow]
    simp
  rw [hs] at h
  change ‖ξ‖ ≤ ‖cyclicPredualEvaluation τ a‖*‖η‖
  by_cases hz : ‖ξ‖=0
  · rw [hz]; positivity
  · have hp : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

def cyclicPredualEvaluationIsometry : M.toStarSubalgebra →ₗᵢ[ℂ] StrongDual ℂ (cyclicPredual τ) where
  toFun := cyclicPredualEvaluation τ
  map_add' _ _ := by ext f; exact map_add f.val _ _
  map_smul' _ _ := by ext f; exact map_smul f.val _ _
  norm_map' := cyclicPredualEvaluation_norm τ

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

include τ in
 theorem cyclicPredual_le_ballContinuousFunctionals (C : ℝ) :
    cyclicPredual τ ≤ ballContinuousFunctionals M C := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro f ⟨⟨ξ,η⟩,rfl⟩
    change Continuous (fun T : weakOperatorBall M C => inner ℂ ξ.val (T.val η.val))
    exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val η.val ξ.val
  · exact ballContinuousFunctionals_isClosed M C

theorem cyclicPredual_ball_continuous (C : ℝ) (f : cyclicPredual τ) :
    Continuous (fun T : weakOperatorBall M C => f.val ⟨T.val.toCLM,T.property.1⟩) :=
  cyclicPredual_le_ballContinuousFunctionals τ C f.property

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

def predualWeakEvaluation : M.toStarSubalgebra →ₗ[ℂ] WeakDual ℂ (cyclicPredual τ) :=
  StrongDual.toWeakDual.toLinearMap.comp (cyclicPredualEvaluationIsometry τ).toLinearMap

def predualWeakBall (C : ℝ) : Set (WeakDual ℂ (cyclicPredual τ)) :=
  predualWeakEvaluation τ '' {a | ‖a‖ ≤ C}

theorem predualWeakBall_isCompact (C : ℝ) : IsCompact (predualWeakBall τ C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  let f : weakOperatorBall M C → WeakDual ℂ (cyclicPredual τ) :=
    fun T => predualWeakEvaluation τ ⟨T.val.toCLM,T.property.1⟩
  have hf : Continuous f := by
    apply WeakBilin.continuous_of_continuous_eval
    intro z
    exact cyclicPredual_ball_continuous τ C z
  have he : predualWeakBall τ C=Set.range f := by
    ext T
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,ha⟩⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨⟨a.val.toCLM,a.property.1⟩,a.property.2,rfl⟩
  rw [he]
  exact isCompact_range hf

theorem predualWeakBall_convex (C : ℝ) : Convex ℝ (predualWeakBall τ C) := by
  have h : Convex ℝ {a : M.toStarSubalgebra | ‖a‖ ≤ C} := by
    simpa only [Metric.closedBall,dist_zero_right] using convex_closedBall (0 : M.toStarSubalgebra) C
  exact h.linear_image ((predualWeakEvaluation τ).restrictScalars ℝ)

theorem cyclicPredualEvaluation_unitBall_surjective
    (φ : StrongDual ℂ (cyclicPredual τ)) (hφ : ‖φ‖ ≤ 1) :
    ∃ a : M.toStarSubalgebra,‖a‖ ≤ 1 ∧ cyclicPredualEvaluation τ a=φ := by
  have hm : StrongDual.toWeakDual φ ∈ predualWeakBall τ 1 := by
    by_contra hnot
    obtain ⟨g,u,hgu,hug⟩ := weakDual_separation
      (predualWeakBall_convex τ 1) (predualWeakBall_isCompact τ 1).isClosed hnot
    obtain ⟨f,hf⟩ := LinearMap.dualEmbedding_surjective
      (topDualPairing ℂ (cyclicPredual τ)) g
    have he (a : M.toStarSubalgebra) : g (predualWeakEvaluation τ a)=f.val a := by
      rw [← hf]
      rfl
    have heφ : g (StrongDual.toWeakDual φ)=φ f := by
      rw [← hf]
      rfl
    have hu : 0 < u := by
      have h := hgu (predualWeakEvaluation τ 0) ⟨0,by simp,rfl⟩
      simpa only [he,map_zero,Complex.zero_re] using h
    have hn : ‖f.val‖ ≤ u := dual_norm_le_of_re_unitBall f.val u hu.le (fun a ha => by
      have hh := (hgu (predualWeakEvaluation τ a) ⟨a,ha,rfl⟩).le
      rw [he] at hh
      exact hh)
    have hb : (φ f).re ≤ u := by
      calc
        (φ f).re ≤ ‖φ f‖ := Complex.re_le_norm _
        _ ≤ ‖φ‖*‖f‖ := φ.le_opNorm f
        _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg f)
        _ = ‖f‖ := one_mul _
        _ ≤ u := hn
    rw [heφ] at hug
    exact (not_lt_of_ge hb) hug
  obtain ⟨a,ha,he⟩ := hm
  exact ⟨a,ha,congrArg WeakDual.toStrongDual he⟩

end

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
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x y : M.toStarSubalgebra}
theorem sub (hx : TraceOrthogonal τ P x) (hy : TraceOrthogonal τ P y) :
    TraceOrthogonal τ P (x-y) := by
  intro a
  rw [mul_sub,trace_sub,hx a,hy a,sub_self]
theorem eq_zero (hx : TraceOrthogonal τ P x) (hP : x ∈ P) : x=0 := by
  have h := hx ⟨star x,P.star_mem' hP⟩
  change τ.trace (star x*x)=0 at h
  have hr := congrArg Complex.re h
  rw [← norm₂_sq_trace τ] at hr
  exact (τ.norm₂_eq_zero_iff x).mp (sq_eq_zero_iff.mp hr)
end TraceOrthogonal

theorem subalgebra_representative_unique (x y z : M.toStarSubalgebra)
    (hy : y.val ∈ N) (hz : z.val ∈ N)
    (hxy : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y))
    (hxz : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-z)) : y=z := by
  have h := hxz.sub τ hxy
  have he : (x-z)-(x-y)=y-z := by abel
  rw [he] at h
  exact sub_eq_zero.mp (h.eq_zero τ (N.sub_mem hy hz))

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
-- module Solutions.OAIQ11_FG.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/
section
open scoped BigOperators
open Generator.CoefficientOrder Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G

attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions_1
attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions_2
def positiveLetterPair (p : G) : MonoidAlgebra ℝ F :=
  MonoidAlgebra.single (letter (p, true)) 1 + MonoidAlgebra.single (letter (p, false)) 1

def negativeLetterPair (p : G) : MonoidAlgebra ℂ F :=
  MonoidAlgebra.single (letter (p, true)) 1 - MonoidAlgebra.single (letter (p, false)) 1

def perturbationRow {n : ℕ} (α : ℝ) (k : Fin n) : MonoidAlgebra ℂ F × MonoidAlgebra ℝ F :=
  ((α / (2 * n)) • ∑ j : Fin n, negativeLetterPair (pairRatio (k, j)),
   (α / (2 * n)) • ∑ j : Fin n, positiveLetterPair (pairRatio (k, j)))

end

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ

local instance instDecidableEqFreeGroupNat_solutions_3_r566d78_1 : DecidableEq G := Classical.decEq _
@[simp] theorem finitePerturbationRow_embed {n : ℕ} (α : ℝ) (k : Fin n) :
    prefixRingEmbedding n (finitePerturbationRow α k) = (perturbationRow α k).1 := by
  have hs (c : ℝ) (f : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n))) :
      prefixRingEmbedding n (c • f) = c • prefixRingEmbedding n f :=
    map_smul ((prefixRingEmbedding n).restrictScalars ℝ).toLinearMap c f
  simp only [finitePerturbationRow, perturbationRow, hs, map_sum, map_sub,
    prefixRingEmbedding_single]
  congr 1

end

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
local instance stateDimensionPreorder_r566d78_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.stateDimensionLE
attribute [local instance] OAI.Generator.Tracial.stateDimensionStarOrder
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

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

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
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/
section
open Filter
open scoped Topology BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

def dyadicRademacher (p : AlgebraProjection M) (n : ℕ) : M.toStarSubalgebra :=
  dyadicEval τ hdiff p (n+1) (dyadicSign n)

theorem dyadicRademacher_star (p : AlgebraProjection M) (n : ℕ) :
    star (dyadicRademacher τ hdiff p n)=dyadicRademacher τ hdiff p n := by
  unfold dyadicRademacher dyadicEval
  rw [projectionSum_star]
  congr 1
  funext i
  cases h : i.2 <;> simp [dyadicSign,h]

theorem dyadicRademacher_sq (p : AlgebraProjection M) (n : ℕ) :
    dyadicRademacher τ hdiff p n*dyadicRademacher τ hdiff p n=p.val := by
  unfold dyadicRademacher dyadicEval
  rw [projectionSum_mul _ (dyadicProjection_orthogonal τ hdiff p (n+1))]
  have he : (fun i : DyadicIndex (n+1) => dyadicSign n i*dyadicSign n i) = fun _ => 1 := by
    funext i
    cases h : i.2 <;> simp [dyadicSign,h]
  rw [he]
  exact dyadicEval_one τ hdiff p (n+1)

def dyadicCornerUnitary (p : AlgebraProjection M) (n : ℕ) : CornerUnitary p where
  val := dyadicRademacher τ hdiff p n
  initial := by rw [dyadicRademacher_star,dyadicRademacher_sq]
  final := by rw [dyadicRademacher_star,dyadicRademacher_sq]

end

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PatchingWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Ordered signed mixed words in Popa 1308.3982v3, Lemma 3.2.
The L2 continuity estimate keeps the order of every coefficient. -/

/-! The scalar-commutant specialization of the error-constrained chain and
Zorn step in Popa 1308.3982v3 Lemma 3.2. The internal coefficients are in F;
only the two endpoints may be 1. No local-quantization or growth assumption. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def PatchingAdmissible (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (n : ℕ) (ε : ℕ → ℝ) (v : PartialUnitary M) : Prop :=
  v.support ≤ f ∧ ∀ x₀ ∈ F ∪ {1}, ∀ xs : List (Bool × M.toStarSubalgebra),
    1 ≤ xs.length → xs.length ≤ n → patchingCoefficients F xs →
      ‖τ.trace (x₀*patchingWord v.val xs)‖ ≤ ε xs.length*(τ.trace v.support.val).re

def zeroPartialUnitary : PartialUnitary M :=
  ⟨⟨0,IsStarProjection.zero _⟩,⟨0,by simp,by simp⟩⟩

end

/-! The error-constrained partial unitaries stay in the prescribed algebra P,
while all word coefficients and the trace live in M. This prevents replacing
the source inclusion P subset M by the trivial inclusion M subset M. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

include hPM

def PatchingAdmissibleIn (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (n : ℕ) (ε : ℕ → ℝ) (v : PartialUnitary M) : Prop :=
  PatchingAdmissible τ f F n ε v ∧ v.val.val ∈ P

end

/-! Finite enumeration of the actual ordered word family. Only endpoints may
be 1. The middle segments retain all signs and their precise lengths. -/

/-! The two moment bounds in Popa Lemma 3.2 equation (6), derived from
admissibility for the actual signed internal segment, including length zero. -/

/-! Actual noncommutative binary expansion in Popa Lemma 3.2, equation (1).
Each list entry retains the number of patch letters used and its ordered
operator product. There is no commuting-coefficient hypothesis. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PredualRange
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! An actual separable Banach predual for the constructed matrix-generated
factor. The existential convention is exactly Generator.HasSeparablePredual. -/
section
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem cyclicPredualEvaluation_surjective : Function.Surjective (cyclicPredualEvaluationIsometry τ) := by
  intro φ
  let c : ℂ := (‖φ‖+1 : ℝ)
  have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast ne_of_gt (by positivity : 0 < ‖φ‖+1)
  have hnorm : ‖c⁻¹ • φ‖ ≤ 1 := by
    rw [norm_smul,norm_inv]
    have hn : ‖c‖=‖φ‖+1 := by dsimp [c]; rw [Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    rw [hn]
    exact (inv_mul_le_one₀ (by positivity : 0 < ‖φ‖+1)).mpr (by linarith)
  obtain ⟨a,_,ha⟩ := cyclicPredualEvaluation_unitBall_surjective τ (c⁻¹ • φ) hnorm
  refine ⟨c • a,?_⟩
  rw [map_smul]
  change c • cyclicPredualEvaluation τ a=φ
  rw [ha,smul_smul,mul_inv_cancel₀ hc,one_smul]

def cyclicPredualLinearEquiv : M.toStarSubalgebra ≃ₗᵢ[ℂ] StrongDual ℂ (cyclicPredual τ) :=
  LinearIsometryEquiv.ofSurjective (cyclicPredualEvaluationIsometry τ)
    (cyclicPredualEvaluation_surjective τ)

end Tracial

end

/-! Separability of the actual cyclic predual implies separability of the
trace-vector orbit. This does not identify an arbitrary given Banach predual
with the cyclic predual. -/

/-! The given predual as a closed separating subspace of the algebra norm dual, with its evaluation duality. -/

/-! Hahn–Banach comparison of preduals from normal-functional membership and evaluation surjectivity. -/

/-! Conditional comparison with the constructed cyclic predual. Membership
of the given-predual evaluations in that space is an explicit unproved input;
it is not obtained merely from their order-limit convergence. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_RelativeGeneration
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)
namespace RelativePolynomial

def eval : Generator.RelativePolynomial N.toStarSubalgebra → TraceUnitary τ → M.toStarSubalgebra
  | .coeff a, _ => coordinateInclusion hNM a
  | .indeterminate, u => u.algebra τ
  | .add p q, u => eval p u+eval q u
  | .mul p q, u => eval p u*eval q u
  | .smul z p, u => z • eval p u
  | .adjoint p, u => star (eval p u)

def sectionVector (p : Generator.RelativePolynomial N.toStarSubalgebra) (u : TraceUnitary τ) : H :=
  (eval τ hNM p u).val τ.vector

end RelativePolynomial
end Tracial

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeGenerators (u : TraceUnitary τ) : Set (H →L[ℂ] H) :=
  (N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}

namespace RelativePolynomial

def valueAlgebra (u : TraceUnitary τ) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarAlgebra.adjoin ℂ (relativeGenerators (N := N) τ u)

theorem eval_mem (p : Generator.RelativePolynomial N.toStarSubalgebra) (u : TraceUnitary τ) :
    (eval τ hNM p u).val ∈ valueAlgebra (N := N) τ u := by
  induction p with
  | coeff a => exact StarAlgebra.subset_adjoin ℂ _ (Or.inl a.property)
  | indeterminate => exact StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)
  | add p q hp hq => exact (valueAlgebra (N := N) τ u).add_mem hp hq
  | mul p q hp hq => exact (valueAlgebra (N := N) τ u).mul_mem hp hq
  | smul z p hp => exact (valueAlgebra (N := N) τ u).smul_mem hp z
  | adjoint p hp => exact (valueAlgebra (N := N) τ u).star_mem' hp

end RelativePolynomial

end Tracial

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end


