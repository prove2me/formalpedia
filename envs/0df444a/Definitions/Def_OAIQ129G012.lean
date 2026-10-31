-- Prove2me | Definitions.Def_OAIQ129G012
-- name    : OAIQ129G012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:34:25.713444+00:00
-- url     : https://prove2.me/theorems/9864aa2a-a20a-4416-a8d9-0a55cb20b530
-- title:
--   Definitions bundle OAIQ129G012 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 21 definitions, 5 instances and 29 theorems. The definitions and types are `OAI.Generator.Tracial.boundedPartialResidual`, `OAI.Generator.Tracial.cyclicPredualEvaluationIsometry`, `OAI.Generator.Tracial.cyclicPredualLinearEquiv`, `OAI.Generator.Tracial.dyadicCornerUnitary`, `OAI.Generator.Tracial.dyadicEval`, `OAI.Generator.Tracial.dyadicProjection`, `OAI.Generator.Tracial.dyadicRademacher`, `OAI.Generator.Tracial.functionalSubspaceEvaluationLinear`, `OAI.Generator.Tracial.functionalSubspaceWeakBall`, `OAI.Generator.Tracial.functionalSubspaceWeakEvaluation`, `OAI.Generator.Tracial.halfTraceCut`, `OAI.Generator.Tracial.normalizedCornerVector`, `OAI.Generator.Tracial.norm₁`, `OAI.Generator.Tracial.predualWeakBall`, `OAI.Generator.Tracial.predualWeakEvaluation`, `OAI.Generator.Tracial.relativeUnitaryWord`, `OAI.Generator.Tracial.representedCornerTrace`, `OAI.Generator.Tracial.splitProjection`, `OAI.Generator.Tracial.traceAbs`, `OAI.Generator.Tracial.traceFunctionalSlice`, `OAI.Generator.Tracial.traceOrbitHull`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CornerTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CornerTrace.lean), [`FactorGeneration_CyclicPredual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CyclicPredual.lean), [`FactorGeneration_Expectations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Expectations.lean), [`FactorGeneration_HilbertLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HilbertLimits.lean), [`FactorGeneration_PartialUnitaries`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PartialUnitaries.lean), [`FactorGeneration_PredualRange`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualRange.lean), [`FactorGeneration_ProjectionLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProjectionLimits.lean), [`FactorGeneration_RelativeGeneration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/RelativeGeneration.lean), [`FactorGeneration_RepresentedCorners`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/RepresentedCorners.lean), [`FactorGeneration_ResidualCompletion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean), [`FactorGeneration_TraceTopology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTopology.lean).
--
--   **Imports.** It imports the bundles `OAIQ129G008` and `OAIQ129G009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ129G014`; the statements `OAI.Generator.Tracial.boundedPartialResidual_mem_q129`, `OAI_Generator_Tracial_exists_residual_quotient_increment_q129` and `OAI.Generator.Tracial.exists_unitResidual_local_compression_q129`; the proofs of `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget_q129`, `OAI.Generator.Tracial.boundedPartialResidual_mem_q129`, `OAI.Generator.Tracial.exists_commuting_matrix_extension_q129`, `OAI.Generator.Tracial.exists_finite_partial_independence_q129`, `OAI.Generator.Tracial.exists_normal_matrix_approximation_q129`, `OAI_Generator_Tracial_exists_quotient_corner_partial_sequence_q129`, `OAI.Generator.Tracial.representedCorner_irreducible_q129` and `OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ129G008
import Definitions.Def_OAIQ129G009

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

def traceOrbitHull (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) : Set H :=
  closure (convexHull ℝ (baseVector τ '' algebraOrbit G b))

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.signedCornerUnitary_val _root_.OAI.Generator.Tracial.traceCyclicOperator_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
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

theorem projection_trace_pos (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hne : p ≠ 0) :
    0 < (τ.trace p).re := by
  rw [projection_trace_sq τ p hp]
  exact sq_pos_of_ne_zero (fun h => hne ((τ.norm₂_eq_zero_iff p).mp h))

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

/-! Exact trace cuts in a diffuse coordinate algebra. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
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
variable (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
def traceAbs (x : M.toStarSubalgebra) : M.toStarSubalgebra := CFC.sqrt (star x*x)
def norm₁ (x : M.toStarSubalgebra) : ℝ := (τ.trace (traceAbs x)).re

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def traceFunctionalSlice (f : M.toStarSubalgebra →L[ℝ] ℝ) (r : ℝ) : Set H :=
  {ξ | ∃ a : M.toStarSubalgebra, ‖a‖ ≤ 1 ∧ f a ≤ r ∧ a.val τ.vector = ξ}

end Tracial

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
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

theorem cyclicCoefficient_norm_le (ξ η : traceCyclicSpace τ) :
    ‖cyclicCoefficient τ ξ η‖ ≤ ‖ξ‖*‖η‖ := by
  apply (cyclicCoefficient τ ξ η).opNorm_le_bound (M := ‖ξ‖*‖η‖) (mul_nonneg (norm_nonneg ξ) (norm_nonneg η))
  intro a
  calc
    ‖cyclicCoefficient τ ξ η a‖ ≤ ‖ξ‖*‖traceCyclicHom τ a η‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖*(‖traceCyclicHom τ a‖*‖η‖) :=
      mul_le_mul_of_nonneg_left ((traceCyclicHom τ a).le_opNorm η) (norm_nonneg _)
    _ = (‖ξ‖*‖η‖)*‖a‖ := by rw [traceCyclicHom_norm]; ring

instance cyclicPredual_normed : NormedAddCommGroup (cyclicPredual τ) := inferInstance

instance cyclicPredual_normedSpace : NormedSpace ℂ (cyclicPredual τ) := inferInstance

instance cyclicPredual_complete : CompleteSpace (cyclicPredual τ) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (Set.range
    (fun p : traceCyclicSpace τ × traceCyclicSpace τ => cyclicCoefficient τ p.1 p.2))).topologicalClosure)

theorem cyclicCoefficient_mem (ξ η : traceCyclicSpace τ) :
    cyclicCoefficient τ ξ η ∈ cyclicPredual τ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(ξ,η),rfl⟩)

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

instance predualWeakLocallyConvex : LocallyConvexSpace ℝ (WeakDual ℂ (cyclicPredual τ)) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ (cyclicPredual τ))))

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
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (F : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra))

@[simp] theorem functionalSubspaceEvaluation_apply (a : M.toStarSubalgebra) (f : F) :
    functionalSubspaceEvaluation F a f = f.val a := rfl

def functionalSubspaceEvaluationLinear : M.toStarSubalgebra →ₗ[ℂ] StrongDual ℂ F where
  toFun := functionalSubspaceEvaluation F
  map_add' a b := by ext f; exact map_add f.val a b
  map_smul' c a := by ext f; exact map_smul f.val c a

def functionalSubspaceWeakEvaluation : M.toStarSubalgebra →ₗ[ℂ] WeakDual ℂ F :=
  StrongDual.toWeakDual.toLinearMap.comp (functionalSubspaceEvaluationLinear F)

def functionalSubspaceWeakBall (C : ℝ) : Set (WeakDual ℂ F) :=
  functionalSubspaceWeakEvaluation F '' {a | ‖a‖ ≤ C}

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x y : M.toStarSubalgebra}
theorem eq_zero (hx : TraceOrthogonal τ P x) (hP : x ∈ P) : x=0 := by
  have h := hx ⟨star x,P.star_mem' hP⟩
  change τ.trace (star x*x)=0 at h
  have hr := congrArg Complex.re h
  rw [← norm₂_sq_trace τ] at hr
  exact (τ.norm₂_eq_zero_iff x).mp (sq_eq_zero_iff.mp hr)
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
-- module Solutions.OAIQ129_RG2.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualRange
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
attribute [-simp] _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_RelativeGeneration
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeUnitaryWord (u : TraceUnitary τ) (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) :
    M.toStarSubalgebra :=
  coordinateInclusion hNM (t 0 : N.toStarSubalgebra)*
    ((List.range ell).map (fun j => u.algebra τ*
      coordinateInclusion hNM (t (j+1) : N.toStarSubalgebra))).prod

end Tracial

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_RepresentedCorners
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual corner on pH. Extension by zero identifies its operators with
supported ambient operators; weak closedness is proved by WOT continuity. -/

/-! The normalized faithful vector trace on the actual corner pH. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

theorem corner_norm₂_pos (hp : p.val ≠ 0) : 0 < τ.norm₂ p.val :=
  lt_of_le_of_ne (norm_nonneg _) (fun h => hp ((τ.norm₂_eq_zero_iff _).mp h.symm))

def normalizedCornerVector : cornerSpace p :=
  ((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector

theorem normalizedCornerVector_norm (hp : p.val ≠ 0) : ‖normalizedCornerVector τ p‖=1 := by
  change ‖((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector‖=1
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ τ.norm₂ p.val from norm_nonneg _)]
  change (τ.norm₂ p.val)⁻¹*τ.norm₂ p.val=1
  exact inv_mul_cancel₀ (corner_norm₂_pos τ p hp).ne'

theorem normalizedCornerVector_pairing (a : (representedCorner p).toStarSubalgebra) :
    inner ℂ (normalizedCornerVector τ p) (a.val (normalizedCornerVector τ p))=
      ((τ.norm₂ p.val : ℂ)^2)⁻¹ * τ.trace (cornerEmbedding p a) := by
  simp only [normalizedCornerVector,map_smul,inner_smul_left,inner_smul_right,
    map_inv₀,Complex.conj_ofReal]
  rw [cornerProject_inner]
  change (τ.norm₂ p.val : ℂ)⁻¹*((τ.norm₂ p.val : ℂ)⁻¹*τ.trace (cornerEmbedding p a))=_
  ring

def representedCornerTrace (hp : p.val ≠ 0) : TracialRepresentation (representedCorner p) where
  vector := normalizedCornerVector τ p
  norm_vector := normalizedCornerVector_norm τ p hp
  cyclic a b := by
    change inner ℂ (normalizedCornerVector τ p) ((a*b).val (normalizedCornerVector τ p))=
      inner ℂ (normalizedCornerVector τ p) ((b*a).val (normalizedCornerVector τ p))
    rw [normalizedCornerVector_pairing,normalizedCornerVector_pairing,map_mul,map_mul,τ.trace_mul_comm]
  separating a ha := by
    apply cornerEmbedding_injective p
    rw [map_zero]
    apply τ.separating
    have h : ((τ.norm₂ p.val : ℂ)⁻¹) • (a.val (cornerProject p τ.vector))=0 := by
      simpa only [normalizedCornerVector,map_smul] using ha
    have hscalar : (τ.norm₂ p.val : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (corner_norm₂_pos τ p hp).ne')
    have hz := (smul_eq_zero.mp h).resolve_left hscalar
    exact congrArg Subtype.val hz

end

/-! Subcorner inclusion, inherited diffuseness/irreducibility, and L2 separability. -/

/-! Transport actual unit partitions on pH to ambient partitions of p. -/

/-! Actual centered pNp pinching partitions and local pieces. The corner,
normalized trace, structural properties, and separability are constructed. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def boundedPartialResidual (v : ℕ → PartialUnitary M) : Bounded M :=
  1-boundedPartialSupport v

end

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end


