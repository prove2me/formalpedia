-- Prove2me | Definitions.Def_OAIQ075A014
-- name    : OAIQ075A014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:04:44.559978+00:00
-- url     : https://prove2.me/theorems/e916c67a-3ebd-4c36-b2b8-5765ccfa4aa0
-- title:
--   Definitions bundle OAIQ075A014 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 8 definitions, 2 instances and 33 theorems. The definitions and types are `OAI.Generator.Tracial.coordinateTraceLinear`, `OAI.Generator.Tracial.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.polarCStar`, `OAI.Generator.Tracial.tracePairingOrder`, `OAI.Generator.Tracial.tracePairingPreorder`, `OAI.Generator.Tracial.truncationLE`, `OAI.Generator.Tracial.truncationOrder`, `OAI.KadisonSimilarity.completeNorm`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BoundedHochschild_PartialUnitaries`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/PartialUnitaries.lean), [`FactorGeneration_CornerTrace`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/CornerTrace.lean), [`FactorGeneration_MatrixAlgebras`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixAlgebras.lean), [`FactorGeneration_MatrixRefinement`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean), [`FactorGeneration_MatrixUnits`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixUnits.lean), [`FactorGeneration_PartialIsometries`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/PartialIsometries.lean), [`FactorGeneration_Pinching`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Pinching.lean), [`FactorGeneration_ProjectionLimits`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/ProjectionLimits.lean), [`FactorGeneration_SpectralTruncation`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/SpectralTruncation.lean), [`FactorGeneration_Supports`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Supports.lean), [`FactorGeneration_UniformPartitions`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/UniformPartitions.lean), [`KadisonSimilarity_Similarity_CompleteNorm`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Similarity/CompleteNorm.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A007`, `OAIQ075A008`, `OAIQ075A009` and `OAIQ075A010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A019`, `OAIQ075A020`, `OAIQ075A021`, `OAIQ075A022` and `OAIQ075A024`; the proof of `OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A007
import Definitions.Def_OAIQ075A008
import Definitions.Def_OAIQ075A009
import Definitions.Def_OAIQ075A010

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialUnitaries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial unitaries, ordered limits and trace estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PartialUnitary
instance instPartialOrder : PartialOrder (PartialUnitary M) := inferInstanceAs (PartialOrder {v : PartialIso M // v.final=v.initial})
end PartialUnitary
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder







open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
-- module Solutions.OAIQ075_KS.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem trace_sub (x y : M.toStarSubalgebra) :
    τ.trace (x-y) = τ.trace x - τ.trace y := inner_sub_right _ _ _

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions_re7c52c_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions_re7c52c_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

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
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

instance algebra_finiteDimensional : FiniteDimensional ℂ E.algebra := by
  change FiniteDimensional ℂ E.hom.toAlgHom.range
  exact FiniteDimensional.of_surjective E.hom.toAlgHom.rangeRestrict.toLinearMap
    E.hom.toAlgHom.rangeRestrict_surjective

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

theorem algebra_le_product_left : E.algebra ≤ (E.product F hc).algebra := by
  apply (E.algebra_le_iff _).mpr
  intro i j
  rw [← E.product_sum_left F hc i j]
  exact (E.product F hc).algebra.sum_mem fun k _ => (E.product F hc).entry_mem _ _

theorem algebra_le_product_right : F.algebra ≤ (E.product F hc).algebra := by
  apply (F.algebra_le_iff _).mpr
  intro k l
  rw [← E.product_sum_right F hc k l]
  exact (E.product F hc).algebra.sum_mem fun i _ => (E.product F hc).entry_mem _ _

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem entry_mul_amplify (o i j : ι) (x : A) :
    E.entry i j * E.amplify o x = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.mul_sum,← mul_assoc,E.mul_entry]
  simp [ite_mul]

omit [StarModule ℂ A] in
theorem amplify_mul_entry (o i j : ι) (x : A) :
    E.amplify o x * E.entry i j = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.sum_mul,mul_assoc,E.mul_entry]
  simp [mul_ite]

theorem amplify_mem (o : ι) (x : A) : E.amplify o x ∈ E.commutant := by
  intro i j
  show E.entry i j * E.amplify o x = E.amplify o x * E.entry i j
  rw [E.entry_mul_amplify,E.amplify_mul_entry]

omit [StarModule ℂ A] in
theorem amplify_star (o : ι) (x : A) : star (E.amplify o x)=E.amplify o (star x) := by
  simp only [amplify,star_sum,star_mul,E.star_entry,mul_assoc]

omit [StarModule ℂ A] in
theorem amplify_corner (o i j : ι) (x : A) :
    E.entry i o*E.amplify o x*E.entry o j = E.entry i o*x*E.entry o j := by
  rw [E.entry_mul_amplify]
  simp only [mul_assoc,E.mul_entry,ite_true]

omit [StarModule ℂ A] in
theorem amplify_mul (o : ι) (x y : A) :
    E.amplify o x*E.amplify o y=E.amplify o (x*E.entry o o*y) := by
  simp only [amplify,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change (E.entry i o*x*E.entry o i)*E.amplify o y = _
  rw [mul_assoc,E.entry_mul_amplify]
  simp only [mul_assoc]

theorem amplify_compression (o : ι) (x : A) (hx : x ∈ E.commutant) :
    E.amplify o (E.entry o o*x)=x := by
  simp only [amplify]
  calc _ = ∑ i, E.entry i i*x := by
             apply Finset.sum_congr rfl
             intro i hi
             rw [← mul_assoc,E.mul_entry,ite_eq_left rfl,mul_assoc,← (hx o i).eq,
               ← mul_assoc,E.mul_entry,ite_eq_left rfl]
       _ = x := by rw [← Finset.sum_mul,E.total,one_mul]

omit [StarModule ℂ A] in
theorem reconstruct (o : ι) (x : A) :
    (∑ i, ∑ j, E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j)=x := by
  simp only [E.amplify_corner]
  have h (i j : ι) : E.entry i o*(E.entry o i*x*E.entry j o)*E.entry o j=
      E.entry i i*x*E.entry j j := by
    calc _ = (E.entry i o*E.entry o i)*x*(E.entry j o*E.entry o j) := by
               simp only [mul_assoc]
         _ = _ := by simp only [E.mul_entry,ite_true]
  simp only [h,← Finset.mul_sum,E.total,mul_one,← Finset.sum_mul,one_mul]

/-- The commutant of a full unital matrix algebra in a scalar-center algebra
has scalar center. The finite matrix decomposition is constructed above. -/
theorem commutant_scalar_center (o : ι)
    (hfactor : ∀ c : A, (∀ a : A,a*c=c*a) → ∃ z : ℂ,c=z • (1 : A))
    (c : E.commutant) (hc : ∀ a : E.commutant,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.commutant) := by
  obtain ⟨z,hz⟩ := hfactor c.val (by
    intro x
    have h (i j : ι) : Commute
        (E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j) c.val := by
      have hm : Commute (E.amplify o (E.entry o i*x*E.entry j o)) c.val :=
        congrArg Subtype.val (hc ⟨_,E.amplify_mem o _⟩)
      exact ((c.property i o).mul_left hm).mul_left (c.property o j)
    rw [← E.reconstruct o x]
    simp only [Finset.sum_mul,Finset.mul_sum,(h _ _).eq])
  exact ⟨z,Subtype.ext hz⟩

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem amplify_projection (o : ι) (q : A) (hq : IsStarProjection q)
    (hs : q*E.entry o o=q) : IsStarProjection (E.amplify o q) := by
  constructor
  · show E.amplify o q*E.amplify o q=E.amplify o q
    rw [E.amplify_mul,hs,hq.isIdempotentElem.eq]
  · show star (E.amplify o q)=E.amplify o q
    rw [E.amplify_star,hq.isSelfAdjoint.star_eq]

theorem commutant_diffuse (o : ι)
    (hdiff : ∀ p : A,IsStarProjection p → p ≠ 0 →
      ∃ q : A,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.commutant) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.commutant,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  have hpA : IsStarProjection p.val := hp.map E.commutant.subtype
  let r : A := E.entry o o*p.val
  have hr : IsStarProjection r := (E.diagonal_projection o).mul hpA (p.property o o)
  have hr0 : r ≠ 0 := by
    intro h
    have he := E.amplify_compression o p.val p.property
    rw [show E.entry o o*p.val=0 from h,E.amplify_zero] at he
    exact hp0 (Subtype.ext he.symm)
  obtain ⟨q,hq,hq0,hqr,hrq,hqr'⟩ := hdiff r hr hr0
  have hqs : q*E.entry o o=q := by
    have hre : r*E.entry o o=r := by
      dsimp [r]
      rw [mul_assoc,← (p.property o o).eq,← mul_assoc,
        (E.diagonal_projection o).isIdempotentElem.eq]
    calc q*E.entry o o = (q*r)*E.entry o o := by rw [hqr']
         _ = q*r := by rw [mul_assoc,hre]
         _ = q := hqr'
  have hsq : E.entry o o*q=q := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,E.star_entry] using congrArg star hqs
  let Q : E.commutant := ⟨E.amplify o q,E.amplify_mem o q⟩
  have hQ : IsStarProjection Q := by
    constructor
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isIdempotentElem.eq
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isSelfAdjoint.star_eq
  have hrec : E.entry o o*Q.val*E.entry o o=q := by
    change E.entry o o*E.amplify o q*E.entry o o=q
    rw [E.amplify_corner,hsq,hqs]
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · intro h
    have hz : Q.val=0 := congrArg Subtype.val h
    rw [hz,mul_zero,zero_mul] at hrec
    exact hq0 hrec.symm
  · intro h
    have hz : Q.val=p.val := congrArg Subtype.val h
    rw [hz,mul_assoc,← (p.property o o).eq,← mul_assoc,
      (E.diagonal_projection o).isIdempotentElem.eq] at hrec
    exact hqr hrec.symm
  · apply Subtype.ext
    change p.val*E.amplify o q=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul]
    congr 1
    rw [mul_assoc,hsq]
    exact hrq
  · apply Subtype.ext
    change E.amplify o q*p.val=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul,hqs]
    exact congrArg (E.amplify o) hqr'

open scoped BigOperators

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_PartialIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem norm_le_one (v : PartialIsometry M) : ‖v.val‖ ≤ 1 := by
  have he : ‖v.val‖*‖v.val‖=‖v.support.val‖ := by
    rw [← CStarRing.norm_star_mul_self,v.initial]
  have hp := v.support.property.norm_le
  nlinarith [norm_nonneg v.val]

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Orthogonal patching with distinct source and target supports. -/

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
-- module Solutions.OAIQ075_KS.FactorGeneration_Supports
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

theorem trace_total : (∑ i, (τ.trace (Q.piece i).val).re) = (τ.trace p.val).re := by
  rw [← Complex.re_sum]
  change (∑ i, coordinateTraceLinear τ (Q.piece i).val).re = _
  rw [← map_sum, Q.total]
  rfl

end CornerPartition

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
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/
variable {ι A B : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

omit [StarModule ℂ A] [StarModule ℂ B] in
theorem commute_mapped_of_amplify (E : MatrixUnitSystem ι A) (o : ι)
    (f : A →⋆ₐ[ℂ] B) (y : B)
    (hE : ∀ i j,Commute (f (E.entry i j)) y)
    (hamp : ∀ a : A,Commute (f (E.amplify o a)) y) (x : A) : Commute (f x) y := by
  rw [← E.reconstruct o x,map_sum]
  apply Commute.sum_left
  intro i hi
  rw [map_sum]
  apply Commute.sum_left
  intro j hj
  rw [map_mul,map_mul]
  exact ((hE i o).mul_left (hamp _)).mul_left (hE o j)

open UltrapowerBridge Tracial

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
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
local instance tracePairingOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracePairingPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance tracePairingCStar_re7c52c_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance tracePairingLE_re7c52c_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance tracePairingStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance truncationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance truncationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance truncationCStar_re7c52c_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance truncationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_UniformPartitions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite equal-trace partitions in an actual diffuse algebra, constructed
by repeated exact trace cuts. No matrix units or comparison theorem are
assumed. These partitions do not yet approximate an arbitrary given
spectral partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

include hdiff in
theorem exists_uniform_trace_partition (n : ℕ) (p : AlgebraProjection M)
    (r : ℝ) (hr : 0 ≤ r) (ht : τ.trace p.val=((n : ℝ)*r : ℂ)) :
    ∃ Q : CornerPartition p,Q.size=n ∧ ∀ i,τ.trace (Q.piece i).val=(r : ℂ) := by
  induction n generalizing p with
  | zero =>
    have hp0 : p.val=0 := by
      by_contra h
      have hpos := projection_trace_pos τ p.val p.property h
      simp only [Nat.cast_zero,zero_mul,Complex.ofReal_zero] at ht
      rw [ht,Complex.zero_re] at hpos
      exact (lt_irrefl 0 hpos)
    refine ⟨⟨0,Fin.elim0,fun i => Fin.elim0 i,?_⟩,rfl,fun i => Fin.elim0 i⟩
    simpa only [Finset.univ_eq_empty,Finset.sum_empty] using hp0.symm
  | succ n ih =>
    have hrp : r ≤ (τ.trace p.val).re := by
      have htR := congrArg Complex.re ht
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,sub_zero,Nat.cast_succ] at htR
      rw [htR]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨q,hq,hpq,hqp,hqt⟩ :=
      exists_exact_trace_subprojection τ hdiff p.val p.property r hr hrp
    let s : AlgebraProjection M := ⟨p.val-q,hq.sub_of_mul_eq_right p.property hpq⟩
    have hst : τ.trace s.val=((n : ℝ)*r : ℂ) := by
      change τ.trace (p.val-q)=_
      rw [trace_sub,ht,hqt]
      push_cast
      ring
    obtain ⟨Q,hsize,hQ⟩ := ih s hst
    have hleft (i : Fin Q.size) : q*(Q.piece i).val=0 := by
      have hle : (p.val-q)*(Q.piece i).val=(Q.piece i).val := Q.piece_le i
      calc q*(Q.piece i).val = q*((p.val-q)*(Q.piece i).val) := by rw [hle]
        _ = 0 := by rw [← mul_assoc,mul_sub,hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]
    have hright (i : Fin Q.size) : (Q.piece i).val*q=0 := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq,
        (Q.piece i).property.isSelfAdjoint.star_eq,star_zero] using congrArg star (hleft i)
    let a : Fin (Q.size+1) → AlgebraProjection M := Fin.cons ⟨q,hq⟩ Q.piece
    have ha (i j : Fin (Q.size+1)) (hij : i ≠ j) : (a i).val*(a j).val=0 := by
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          exact hleft j
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact hright i
        · intro hij
          exact Q.orthogonal i j (fun h => hij (congrArg Fin.succ h))
    have hat : (∑ i,(a i).val)=p.val := by
      rw [Fin.sum_univ_succ]
      change q+(∑ i,(Q.piece i).val)=p.val
      rw [Q.total]
      change q+(p.val-q)=p.val
      abel
    let R : CornerPartition p := ⟨Q.size+1,a,ha,hat⟩
    refine ⟨R,congrArg (fun k => k+1) hsize,?_⟩
    intro i
    exact Fin.cases hqt hQ i

/-! Complete finitely many orthogonal grid-trace projections to an actual
equal-trace unit partition, retaining explicit disjoint groups of pieces. -/

include hdiff in
theorem exists_uniform_trace_extension {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j,i ≠ j → (q i).val*(q j).val=0)
    (n : ℕ) (hn : 0 < n) (m : ι → ℕ) (hm : ∑ i,m i ≤ n)
    (ht : ∀ i,τ.trace (q i).val=(((m i : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ)) :
    ∃ R : CornerPartition (identityProjection M), R.size=n ∧
      (∀ j,τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : ι → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        ∀ i,(∑ j ∈ J i,(R.piece j).val)=(q i).val := by
  classical
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  obtain ⟨C,e,he,hrem⟩ := exists_completed_orthogonal_family q hq
  let count : Option ι → ℕ := fun a => a.elim (n-∑ i,m i) m
  have hsum : τ.trace (∑ i,(q i).val)=
      ((((∑ i,m i : ℕ) : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    change coordinateTraceLinear τ (∑ i,(q i).val)=_
    rw [map_sum]
    change (∑ i,τ.trace (q i).val)=_
    simp only [ht]
    push_cast
    rw [Finset.sum_mul]
  have hc (a : Option ι) : τ.trace (C.piece (e a)).val=
      (((count a : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    cases a with
    | some i => simpa only [he,count,Option.elim_some] using ht i
    | none =>
      rw [hrem,trace_sub,τ.trace_one,hsum]
      dsimp [count]
      rw [Nat.cast_sub hm]
      push_cast
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR
      field_simp
  have hC (j : Fin C.size) : τ.trace (C.piece j).val=
      (((count (e.symm j) : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa only [Equiv.apply_symm_apply] using hc (e.symm j)
  choose D hDsize hDt using fun j => exists_uniform_trace_partition τ hdiff
    (count (e.symm j)) (C.piece j) (n : ℝ)⁻¹ (by positivity) (by simpa only [Complex.ofReal_mul] using hC j)
  let R := C.refineBlocks D
  have hRt (j : Fin R.size) : τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact hDt _ _
  have hsize : R.size=n := by
    have htotal := R.trace_total τ
    have heq : (R.size : ℝ)*(n : ℝ)⁻¹=1 := by
      simpa only [hRt,Complex.ofReal_re,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,identityProjection,τ.trace_one,Complex.one_re] using htotal
    have hmul := mul_inv_cancel₀ hnR
    have hreal : (R.size : ℝ)=(n : ℝ) :=
      (mul_right_cancel₀ (inv_ne_zero hnR)) (heq.trans hmul.symm)
    exact_mod_cast hreal
  refine ⟨R,hsize,hRt,fun i => C.blockIndices D (e (some i)),?_,?_⟩
  · intro i j hij
    apply C.blockIndices_disjoint
    intro h
    exact hij (Option.some.inj (e.injective h))
  · intro i
    exact (C.sum_blockIndices D (e (some i))).trans (congrArg Subtype.val (he i))

/-! Quantitative equal-trace approximation by rounding down spectral pieces.
All projections and partitions are constructed in the given diffuse algebra. -/

include hdiff in
theorem exists_rounded_trace_subprojection (p : AlgebraProjection M)
    (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, ∃ q : AlgebraProjection M, q ≤ p ∧
      τ.trace q.val=(((m : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) ∧
      τ.norm₂ (p.val-q.val)^2 < (n : ℝ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let t := (τ.trace p.val).re
  have ht : 0 ≤ t := by
    dsimp [t]
    rw [projection_trace_sq τ p.val p.property]
    positivity
  let m := ⌊t*(n : ℝ)⌋₊
  have hlow : (m : ℝ)*(n : ℝ)⁻¹ ≤ t := by
    apply (mul_le_mul_iff_left₀ hnR).mp
    have h := Nat.floor_le (mul_nonneg ht hnR.le)
    dsimp [m]
    field_simp
    nlinarith
  have herror : t-(m : ℝ)*(n : ℝ)⁻¹ < (n : ℝ)⁻¹ := by
    have h := Nat.lt_floor_add_one (t*(n : ℝ))
    apply (mul_lt_mul_iff_left₀ hnR).mp
    dsimp [m]
    field_simp
    nlinarith
  obtain ⟨q,hq,hpq,_,hqt⟩ := exists_exact_trace_subprojection τ hdiff p.val p.property
    ((m : ℝ)*(n : ℝ)⁻¹) (by positivity) hlow
  refine ⟨m,⟨q,hq⟩,hpq,hqt,?_⟩
  rw [← projection_trace_sq τ _ (hq.sub_of_mul_eq_right p.property hpq),
    trace_sub,hqt,Complex.sub_re,Complex.ofReal_re]
  exact herror

end

/-! A finite commuting self-adjoint family admits simultaneous L2 spectral
approximation on one constructed dyadic equal-trace partition. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_finset_sum_le {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) :
    τ.norm₂ (∑ i ∈ F,x i) ≤ ∑ i ∈ F,τ.norm₂ (x i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (τ.norm₂_add_le _ _).trans (add_le_add le_rfl ih)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem reindex_algebra (E : MatrixUnitSystem ι A) (e : κ ≃ ι) :
    (E.reindex e).algebra=E.algebra := by
  apply le_antisymm
  · exact ((E.reindex e).algebra_le_iff _).mpr (fun i j => E.entry_mem _ _)
  · apply (E.algebra_le_iff _).mpr
    intro i j
    simpa only [reindex,Equiv.apply_symm_apply] using
      (E.reindex e).entry_mem (e.symm i) (e.symm j)

open UltrapowerBridge

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompleteNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least nonnegative complete bound. Kirchberg's proof uses a
similarity attaining this bound, rather than an arbitrary similarity. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def completeNorm (f : A → (H →L[ℂ] H)) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ CompleteBound f C}

end KadisonSimilarity

end

end OAI
end


