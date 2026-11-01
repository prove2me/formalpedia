-- Prove2me | Definitions.Def_OAIQ075A022
-- name    : OAIQ075A022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:16:29.808569+00:00
-- url     : https://prove2.me/theorems/ee781c61-0a21-4f72-9407-eb8848f117e1
-- title:
--   Definitions bundle OAIQ075A022 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 10 definitions, 2 instances and 57 theorems. The definitions and types are `OAI.Generator.FiniteMatrixStage.generated`, `OAI.Generator.FiniteMatrixStage.generatedTrace`, `OAI.Generator.FiniteMatrixStage.generatedVonNeumann`, `OAI.Generator.FiniteMatrixStage.stageUnion`, `OAI.Generator.MatrixUnitSystem.wotLinearMap`, `OAI.Generator.Tracial.dyadicEval`, `OAI.Generator.Tracial.dyadicProjection`, `OAI.Generator.Tracial.dyadicRademacher`, `OAI.Generator.Tracial.halfTraceCut`, `OAI.Generator.Tracial.splitProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_Corners`, `BoundedHochschild_DiffuseProjections`, `BoundedHochschild_FiniteMoments`, `BoundedHochschild_MatrixSystems`, `BoundedHochschild_PartialIsometries`, `BoundedHochschild_PartialUnitaries`, `FactorGeneration_EnergyDescent`, `FactorGeneration_Expectations`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixRefinement`, `FactorGeneration_MatrixSequence`, `FactorGeneration_PartialUnitaries`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_TracialInclusion`.
--
--   **Imports.** It imports the bundles `OAIQ075A013`, `OAIQ075A014`, `OAIQ075A015` and `OAIQ075A016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A026`, `OAIQ075A027` and `OAIQ075A028`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A013
import Definitions.Def_OAIQ075A014
import Definitions.Def_OAIQ075A015
import Definitions.Def_OAIQ075A016

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_DiffuseProjections
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diffuse projections of prescribed trace and conjugation estimates. -/

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
open Filter Topology
open scoped ComplexOrder
namespace HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ)



section Dual
open BoundedHochschild HochschildRigidity
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hL hτ htr hfaith in
theorem projection_chain_upper {p : M} (hp : IsStarProjection p) (t : ℝ)
    (c : Set M) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ q ∈ c, IsStarProjection q ∧ q ≤ p ∧ (τ q).re ≤ t) :
    ∃ s : M, IsStarProjection s ∧ s ≤ p ∧ (τ s).re ≤ t ∧ ∀ q ∈ c, q ≤ s := by
  classical
  let T : Set ℝ := (fun q : M => (τ q).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨t,by rintro _ ⟨q,hq,rfl⟩; exact (hs q hq).2.2⟩
  obtain ⟨v,hvm,_hvL,hvt,hv⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hav using hv
  change ∀ n, (τ (a n)).re=v n at hav
  have ham : Monotone a := by
    intro m n hmn
    apply projection_le_of_comparable_trace_le τ hfaith (hs _ (ha m)).1 (hs _ (ha n)).1
      (hc.total (ha m) (ha n))
    rw [hav,hav]
    exact hvm hmn
  obtain ⟨s,hsp,ht,hns,hsl⟩ := exists_monotone_projection_limit e τ hL hτ htr hfaith
    a (fun n => (hs _ (ha n)).1) ham
  have htrace : (τ s).re=sSup T := by
    have htd := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
        (fun n => (hs _ (ha n)).1.norm_le _) ht)
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp htd)
    simpa only [Function.comp_def,hav] using hvt
  refine ⟨s,hsp,hsl p hp (fun n => (hs _ (ha n)).2.1),?_,?_⟩
  · rw [htrace]
    apply csSup_le hTne
    rintro _ ⟨q,hq,rfl⟩
    exact (hs q hq).2.2
  · intro q hq
    by_cases hex : ∃ n, q ≤ a n
    · obtain ⟨n,hn⟩ := hex
      exact hn.trans (hns n)
    · have hanq : ∀ n, a n ≤ q := by
        intro n
        exact (hc.total (ha n) hq).resolve_right (fun h => hex ⟨n,h⟩)
      apply projection_le_of_comparable_trace_le τ hfaith (hs q hq).1 hsp
        (Or.inr (hsl q (hs q hq).1 hanq))
      rw [htrace]
      exact le_csSup hTbd ⟨q,hq,rfl⟩
include e hL hτ htr hfaith in
 

theorem exists_projection_of_trace (hdiff : NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (t : ℝ) (ht0 : 0 ≤ t) (htp : t ≤ (τ p).re) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ (τ q).re=t := by
  classical
  let S : Set M := {q | IsStarProjection q ∧ q ≤ p ∧ (τ q).re ≤ t}
  have h0 : (0 : M) ∈ S := ⟨IsStarProjection.zero M,hp.nonneg,by simpa only [map_zero,Complex.zero_re]⟩
  obtain ⟨q,_hq0,hqm⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s,hsp,hsp_le,hst,hsup⟩ := projection_chain_upper τ e hL hτ htr hfaith
      hp t c hchain ⟨y,hy⟩ (fun z hz => hc hz)
    exact ⟨s,⟨hsp,hsp_le,hst⟩,hsup⟩) 0 h0
  have hq : IsStarProjection q := hqm.1.1
  have hqp : q ≤ p := hqm.1.2.1
  have hqt : (τ q).re ≤ t := hqm.1.2.2
  refine ⟨q,hq,hqp,le_antisymm hqt ?_⟩
  by_contra hle
  have hlt : (τ q).re<t := lt_of_not_ge hle
  have hpq : IsStarProjection (p-q) := (hq.le_iff_sub hp).mp hqp
  have hpq0 : p-q ≠ 0 := by
    intro he
    have hh := congrArg (fun a : M => (τ a).re) (sub_eq_zero.mp he)
    linarith
  obtain ⟨r,hr,hrpq,hr0,hrt⟩ := exists_small_subprojection τ hdiff hpq hpq0
    (t-(τ q).re) (sub_pos.mpr hlt)
  have hqr : q*r=0 := by
    have hh := (hr.le_iff_mul_eq_right hpq).mp hrpq
    calc
      q*r=q*((p-q)*r) := by rw [hh]
      _=(q*p-q*q)*r := by noncomm_ring
      _=0 := by rw [(hq.le_iff_mul_eq_left hp).mp hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]
  have hsum : q+r ∈ S := by
    refine ⟨hq.add hr hqr,?_,?_⟩
    · calc
        q+r ≤ q+(p-q) := add_le_add_right hrpq q
        _=p := by abel
    · rw [map_add,Complex.add_re]
      linarith
  have hback : q+r ≤ q := hqm.2 hsum (le_add_of_nonneg_right hr.nonneg)
  apply hr0
  apply le_antisymm _ hr.nonneg
  apply le_of_add_le_add_left (a := q)
  simpa only [add_zero] using hback

end Dual

end HochschildDiffuse

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.BoundedHochschild.WeakAlgebra.traceRestriction_apply _root_.OAI.HochschildComparison.Frame.zero_part _root_.OAI.HochschildComparison.PartialIso.ofProjection_coe _root_.OAI.HochschildComparison.PartialIso.ofProjection_final _root_.OAI.HochschildComparison.PartialIso.ofProjection_initial _root_.OAI.HochschildComparison.PartialIso.restrict_coe _root_.OAI.HochschildComparison.PartialIso.restrict_initial _root_.OAI.HochschildComparison.PartialUnitary.coe_orthogonalSum _root_.OAI.HochschildComparison.PartialUnitary.coe_zero _root_.OAI.HochschildPatching.asPartialUnitary_coe _root_.OAI.HochschildPatching.ofCornerUnitary_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.PopaCenter.expectation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial isometries and comparison of equal-trace projections. -/

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
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity HochschildDixmier
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

namespace PartialIso

include e hL hτ htr hfaith in
lemma chain_upper {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ v ∈ c, v.initial ≤ p ∧ v.final ≤ q) :
    ∃ s : PartialIso M, s.initial ≤ p ∧ s.final ≤ q ∧ ∀ v ∈ c, v ≤ s := by
  classical
  let T : Set ℝ := (fun v : PartialIso M => (τ v.initial).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨(τ p).re,by
    rintro _ ⟨v,hv,rfl⟩
    exact Complex.re_le_re (τ.monotone (hs v hv).1)⟩
  obtain ⟨b,hbm,_hbub,hbt,hb⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hab using hb
  change ∀ n, (τ (a n).initial).re=b n at hab
  have ham : Monotone a := by
    intro m n hmn
    apply le_of_comparable_trace_le τ hfaith (hc.total (ha m) (ha n))
    rw [hab,hab]
    exact hbm hmn
  obtain ⟨s,ht,has,hsleast⟩ := exists_monotone_limit e τ hL hτ htr hfaith a ham
  have hi := (ht.star τ htr).mul τ htr ht 1
    (fun n => by simpa only [norm_star] using (a n).norm_le_one)
  have hf := ht.mul τ htr (ht.star τ htr) 1 (fun n => (a n).norm_le_one)
  change GNSTendsto τ (fun n => (a n).initial) atTop s.initial at hi
  change GNSTendsto τ (fun n => (a n).final) atTop s.final at hf
  have htrace : (τ s.initial).re=sSup T := by
    have hz := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
        (fun n => (a n).initial_proj.norm_le _) hi)
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp hz)
    simpa only [Function.comp_def,hab] using hbt
  refine ⟨s,?_,?_,?_⟩
  · apply (s.initial_proj.le_iff_mul_eq_left hp).mpr
    apply GNSTendsto.unique τ hfaith
      (hi.mul τ htr (GNSTendsto.const τ p atTop) 1 (fun n => (a n).initial_proj.norm_le _))
    simpa only [((a _).initial_proj.le_iff_mul_eq_left hp).mp (hs _ (ha _)).1] using hi
  · apply (s.final_proj.le_iff_mul_eq_left hq).mpr
    apply GNSTendsto.unique τ hfaith
      (hf.mul τ htr (GNSTendsto.const τ q atTop) 1 (fun n => (a n).final_proj.norm_le _))
    simpa only [((a _).final_proj.le_iff_mul_eq_left hq).mp (hs _ (ha _)).2] using hf
  · intro z hz
    by_cases hex : ∃ n, z ≤ a n
    · obtain ⟨n,hn⟩ := hex
      exact hn.trans (has n)
    · have haz : ∀ n, a n ≤ z := fun n =>
        (hc.total (ha n) hz).resolve_right (fun h => hex ⟨n,h⟩)
      apply le_of_comparable_trace_le τ hfaith (Or.inr (hsleast z haz))
      rw [htrace]
      exact le_csSup hTbd ⟨z,hz,rfl⟩
end PartialIso

include e hτ htr hfaith in
 

theorem exists_partialIso_of_equal_trace [CompleteSpace X] (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) (ht : τ p=τ q) :
    ∃ v : M, star v*v=p ∧ v*star v=q := by
  classical
  let L := HochschildSakai.mul_hasPreadjoint e
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hzero : (0 : PartialIso M) ∈ S := by
    exact ⟨by simpa using hp.nonneg,by simpa using hq.nonneg⟩
  obtain ⟨v,_hzero,hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s,hsp,hsq,hsup⟩ := PartialIso.chain_upper e τ L hτ htr hfaith hp hq
      c hchain ⟨y,hy⟩ (fun z hz => hc hz)
    exact ⟨s,⟨hsp,hsq⟩,hsup⟩) 0 hzero
  have hvp : v.initial ≤ p := hmax.1.1
  have hvq : v.final ≤ q := hmax.1.2
  have hfull : v.initial=p ∨ v.final=q := by
    by_contra hnot
    push Not at hnot
    have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
    have hq' := (v.final_proj.le_iff_sub hq).mp hvq
    obtain ⟨a,ha⟩ := exists_nonzero_corner e τ L hτ htr hfaith h1 hfactor
      hq' hp' (sub_ne_zero.mpr hnot.2.symm) (sub_ne_zero.mpr hnot.1.symm)
    obtain ⟨w,hw0,hwp,hwq⟩ := partialIso_of_nonzero_corner e hq' hp'
      ((q-v.final)*a*(p-v.initial)) ha
      (by rw [← mul_assoc,← mul_assoc,hq'.isIdempotentElem.eq])
      (by rw [mul_assoc,hp'.isIdempotentElem.eq])
    have hi := projection_orthogonal_of_le_sub hp v.initial_proj w.initial_proj hvp hwp
    have hf := projection_orthogonal_of_le_sub hq v.final_proj w.final_proj hvq hwq
    have hs : v.orthogonalSum w hi hf ∈ S := by
      constructor
      · rw [PartialIso.orthogonalSum_initial]
        calc
          v.initial+w.initial ≤ v.initial+(p-v.initial) := add_le_add_right hwp _
          _ = p := by abel
      · rw [PartialIso.orthogonalSum_final]
        calc
          v.final+w.final ≤ v.final+(q-v.final) := add_le_add_right hwq _
          _ = q := by abel
    have hle := v.le_orthogonalSum w hi hf
    have he := le_antisymm (hmax.2 hs hle) hle
    have hvw : (v : M)+w=v := congrArg (fun z : PartialIso M => (z : M)) he
    exact hw0 (add_eq_left.mp hvw)
  have he : τ v.initial=τ v.final := htr _ _
  rcases hfull with hi|hf
  · have hback : q ≤ v.final := by
      apply HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith hq v.final_proj
        (Or.inr hvq)
      rw [← he,hi,ht]
    exact ⟨v,hi,le_antisymm hvq hback⟩
  · have hback : p ≤ v.initial := by
      apply HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith hp v.initial_proj
        (Or.inr hvp)
      rw [he,hf,ht]
    exact ⟨v,le_antisymm hvp hback,hf⟩

end HochschildComparison
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixSystems
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.BoundedHochschild.WeakAlgebra.traceRestriction_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.PopaCenter.expectation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix systems, expectations and rational projection approximation. -/

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
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma exists_partition_trace (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (n : ℕ) {p : M} (hp : IsStarProjection p) {t : ℝ} (ht : 0 ≤ t)
    (hpt : (τ p).re = (n : ℝ)*t) :
    ∃ q : Fin n → M, (∀ i, IsStarProjection (q i)) ∧
      (∀ i, q i ≤ p) ∧ (∀ i j, i ≠ j → q i*q j=0) ∧
      (∑ i, q i)=p ∧ ∀ i, (τ (q i)).re=t := by
  induction n generalizing p with
  | zero =>
    have htp : τ p=0 := by
      apply Complex.ext
      · simpa using hpt
      · exact (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).2.symm
    have hp0 : p=0 := hfaith p (by simpa only [hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq] using htp)
    subst p
    exact ⟨Fin.elim0, by simp, by simp, by simp, by simp, by simp⟩
  | succ n ih =>
    have hle : t ≤ (τ p).re := by
      rw [hpt, Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) ht]
    obtain ⟨a,ha,hap,hat⟩ := HochschildDiffuse.exists_projection_of_trace τ e
      (HochschildSakai.mul_hasPreadjoint e) hτ htr hfaith hdiff hp t ht hle
    have hpa := (ha.le_iff_sub hp).mp hap
    have hpat : (τ (p-a)).re = (n : ℝ)*t := by
      rw [map_sub,Complex.sub_re,hpt,hat,Nat.cast_add,Nat.cast_one]
      ring
    obtain ⟨q,hq,hqp,hqo,hqs,hqt⟩ := ih hpa hpat
    refine ⟨Fin.cases a q,?_,?_,?_,?_,?_⟩
    · intro i
      exact Fin.cases ha hq i
    · intro i
      exact Fin.cases hap (fun j => (hqp j).trans (sub_le_self _ ha.nonneg)) i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          exact projection_orthogonal_of_le_sub hp ha (hq j) hap (hqp j)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          have hh := projection_orthogonal_of_le_sub hp ha (hq i) hap (hqp i)
          simpa only [star_mul, (hq i).isSelfAdjoint.star_eq, ha.isSelfAdjoint.star_eq,
            star_zero,Fin.cases_zero,Fin.cases_succ] using congrArg star hh
        · intro hij
          exact hqo i j (fun he => hij (congrArg Fin.succ he))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero,Fin.cases_succ,hqs]
      abel
    · intro i
      exact Fin.cases hat hqt i


end HochschildMatrixSystems

 

 

 

open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma exists_matrixSystem_of_partition (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    {n : ℕ} (hn : 0<n) (p : Fin n → M) (hp : ∀ i, IsStarProjection (p i))
    (hpo : ∀ i j, i ≠ j → p i*p j=0) (hps : ∑ i, p i=1)
    (ht : ∀ i j, τ (p i)=τ (p j)) :
    ∃ E : MatrixSystem M n, ∀ i, E.entry i i=p i := by
  classical
  let i0 : Fin n := ⟨0,hn⟩
  choose v hv0 hv using fun i => exists_partialIso_of_equal_trace e τ hτ htr hfaith
    h1 hfactor (hp i0) (hp i) (ht i0 i)
  have hvi : ∀ i, v i*p i0=v i := by
    intro i
    apply sub_eq_zero.mp
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    calc
      star (v i*p i0-v i)*(v i*p i0-v i) =
          p i0*(star (v i)*v i)*p i0-p i0*(star (v i)*v i)-
            (star (v i)*v i)*p i0+star (v i)*v i := by
              simp only [star_sub,star_mul,(hp i0).isSelfAdjoint.star_eq]
              noncomm_ring
      _ = 0 := by simp only [hv0,(hp i0).isIdempotentElem.eq,sub_self,zero_sub,neg_add_cancel]
  have hvf : ∀ i, p i*v i=v i := by
    intro i
    rw [← hv i,mul_assoc,hv0 i,hvi i]
  have hvs : ∀ i, star (v i)*p i=star (v i) := by
    intro i
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg star (hvf i)
  have hcross : ∀ i j, i ≠ j → star (v i)*v j=0 := by
    intro i j hij
    calc
      star (v i)*v j = (star (v i)*p i)*(p j*v j) := by rw [hvs,hvf]
      _ = star (v i)*(p i*p j)*v j := by simp only [mul_assoc]
      _ = 0 := by rw [hpo i j hij,mul_zero,zero_mul]
  refine ⟨⟨fun i j => v i*star (v j),?_,?_,?_⟩,?_⟩
  · intro i j
    simp only [star_mul,star_star]
  · intro i j k l
    by_cases h : j=k
    · subst k
      rw [ite_eq_left rfl]
      calc
        (v i*star (v j))*(v j*star (v l)) = v i*(star (v j)*v j)*star (v l) := by
          simp only [mul_assoc]
        _ = v i*star (v l) := by rw [hv0,hvi]
    · rw [ite_eq_right h]
      calc
        (v i*star (v j))*(v k*star (v l)) = v i*(star (v j)*v k)*star (v l) := by
          simp only [mul_assoc]
        _ = 0 := by rw [hcross j k h,mul_zero,zero_mul]
  · simpa only [hv] using hps
  · exact hv

include e hτ htr hfaith in
lemma exists_rational_subprojection (hdiff : HochschildDiffuse.NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (n : ℕ) (hn : 0<n) (h1 : τ 1=1) :
    ∃ (k : ℕ) (q : M), k ≤ n ∧ IsStarProjection q ∧ q ≤ p ∧
      (τ q).re=(k : ℝ)/(n : ℝ) ∧
      ‖τ.toPreGNS (p-q)‖^2 < (n : ℝ)⁻¹ := by
  let t : ℝ := (τ p).re
  have ht0 : 0 ≤ t := (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1
  have ht1 : t ≤ 1 := by
    have hh := Complex.re_le_re (τ.monotone hp.le_one)
    change (τ p).re ≤ (τ 1).re at hh
    simpa only [h1,Complex.one_re] using hh
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  let k : ℕ := ⌊(n : ℝ)*t⌋₊
  have hklo : (k : ℝ) ≤ (n : ℝ)*t := Nat.floor_le (mul_nonneg hnR.le ht0)
  have hkhi : (n : ℝ)*t < (k : ℝ)+1 := Nat.lt_floor_add_one _
  have hkn : k ≤ n := by
    apply Nat.cast_le.mp (le_trans hklo _)
    exact mul_le_of_le_one_right hnR.le ht1
  have hkt : (k : ℝ)/(n : ℝ) ≤ t := (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hklo)
  obtain ⟨q,hq,hqp,hqt⟩ := HochschildDiffuse.exists_projection_of_trace τ e
    (HochschildSakai.mul_hasPreadjoint e) hτ htr hfaith hdiff hp
    ((k : ℝ)/(n : ℝ)) (div_nonneg (Nat.cast_nonneg k) hnR.le) hkt
  refine ⟨k,q,hkn,hq,hqp,hqt,?_⟩
  have hr := (hq.le_iff_sub hp).mp hqp
  rw [MatrixSystem.norm_sq,hr.isSelfAdjoint.star_eq,hr.isIdempotentElem.eq,
    map_sub,Complex.sub_re,hqt]
  change t-(k : ℝ)/(n : ℝ) < (n : ℝ)⁻¹
  apply (mul_lt_mul_iff_left₀ hnR).mp
  rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hnR),inv_mul_cancel₀ (ne_of_gt hnR)]
  linarith

include e hτ htr hfaith in
 

lemma exists_rational_partition (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (h1 : τ 1=1) {q : M} (hq : IsStarProjection q) {n k : ℕ} (hn : 0<n)
    (hkn : k ≤ n) (hqt : (τ q).re=(k : ℝ)/(n : ℝ)) :
    ∃ p : Fin (k+(n-k)) → M,
      (∀ i, IsStarProjection (p i)) ∧ (∀ i j, i ≠ j → p i*p j=0) ∧
      (∑ i, p i)=1 ∧ (∀ i, (τ (p i)).re=(n : ℝ)⁻¹) ∧
      (∑ i : Fin k, p (Fin.castAdd (n-k) i))=q := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  obtain ⟨a,ha,haq,hao,has,hat⟩ := exists_partition_trace e τ hτ htr hfaith hdiff
    k hq (inv_nonneg.mpr hnR.le) (by simpa only [div_eq_mul_inv] using hqt)
  have hqc : IsStarProjection (1-q) := hq.one_sub
  have hqct : (τ (1-q)).re = ((n-k : ℕ) : ℝ)*(n : ℝ)⁻¹ := by
    rw [map_sub,h1,Complex.sub_re,Complex.one_re,hqt,Nat.cast_sub hkn]
    field_simp
  obtain ⟨b,hb,hbq,hbo,hbs,hbt⟩ := exists_partition_trace e τ hτ htr hfaith hdiff
    (n-k) hqc (inv_nonneg.mpr hnR.le) hqct
  let p : Fin (k+(n-k)) → M := Fin.addCases a b
  have hcross : ∀ i j, a i*b j=0 := by
    intro i j
    calc
      a i*b j = (a i*q)*((1-q)*b j) := by
        rw [(ha i).le_iff_mul_eq_left hq |>.mp (haq i),
          (hb j).le_iff_mul_eq_right hqc |>.mp (hbq j)]
      _ = 0 := by rw [mul_assoc,← mul_assoc q, mul_sub,mul_one,hq.isIdempotentElem.eq,
        sub_self,zero_mul,mul_zero]
  refine ⟨p,?_,?_,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [p,Fin.addCases_left] using ha i
    · simpa only [p,Fin.addCases_right] using hb i
  · intro i j
    refine Fin.addCases ?_ ?_ i <;> intro i <;> refine Fin.addCases ?_ ?_ j <;> intro j hij
    · simpa only [p,Fin.addCases_left] using hao i j (fun h => hij (congrArg (Fin.castAdd (n-k)) h))
    · simpa only [p,Fin.addCases_left,Fin.addCases_right] using hcross i j
    · simpa only [p,Fin.addCases_left,Fin.addCases_right,star_mul,star_zero,(hb i).isSelfAdjoint.star_eq,
        (ha j).isSelfAdjoint.star_eq] using congrArg star (hcross j i)
    · simpa only [p,Fin.addCases_right] using hbo i j (fun h => hij (congrArg (Fin.natAdd k) h))
  · simp only [p,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,has,hbs]
    abel
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [p,Fin.addCases_left] using hat i
    · simpa only [p,Fin.addCases_right] using hbt i
  · simpa only [p,Fin.addCases_left] using has

include e hτ htr hfaith in
 

theorem exists_matrix_projection_approx (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    {p : M} (hp : IsStarProjection p) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (E : MatrixSystem M n) (s : Finset (Fin n)), 0<n ∧
      IsStarProjection (∑ i ∈ s, E.entry i i) ∧ (∑ i ∈ s, E.entry i i) ≤ p ∧
      ‖τ.toPreGNS (p-∑ i ∈ s, E.entry i i)‖ < ε := by
  classical
  obtain ⟨n,hnR⟩ := exists_nat_gt ((ε^2)⁻¹)
  have hn : 0<n := by
    exact_mod_cast (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg ε)) hnR)
  have hnRpos : (0:ℝ)<n := by exact_mod_cast hn
  have hinv : (n:ℝ)⁻¹<ε^2 := (inv_lt_comm₀ hnRpos (sq_pos_of_pos hε)).mpr hnR
  obtain ⟨k,q,hkn,hq,hqp,hqt,herr⟩ := exists_rational_subprojection e τ hτ htr hfaith
    hdiff hp n hn h1
  obtain ⟨a,ha,hao,has,hat,haq⟩ := exists_rational_partition e τ hτ htr hfaith
    hdiff h1 hq hn hkn hqt
  have hn' : 0<k+(n-k) := by omega
  have ht : ∀ i j, τ (a i)=τ (a j) := by
    intro i j
    rw [projection_trace_real τ _ (ha i),projection_trace_real τ _ (ha j),hat,hat]
  obtain ⟨E,hE⟩ := exists_matrixSystem_of_partition e τ hτ htr hfaith h1 hfactor hn'
    a ha hao has ht
  let s : Finset (Fin (k+(n-k))) := Finset.univ.map (Fin.castAddEmb (n-k))
  have hs : (∑ i ∈ s, E.entry i i)=q := by
    simp only [s,Finset.sum_map,hE]
    exact haq
  refine ⟨k+(n-k),E,s,hn',hs ▸ hq,hs ▸ hqp,?_⟩
  rw [hs]
  have hh := herr.trans hinv
  nlinarith [norm_nonneg (τ.toPreGNS (p-q))]

end HochschildMatrixSystems
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Corners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.CStarCorner.instAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral corners, corner preduals and factor structure. -/

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
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

include e hp in
lemma exists_matrix_diagonal_below
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (hp0 : p ≠ 0) :
    ∃ (n : ℕ) (E : MatrixSystem M n) (i : Fin n), E.entry i i ≤ p := by
  classical
  have hnorm : 0<‖τ.toPreGNS p‖ := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hp0 ((preGNS_norm_eq_zero_iff τ hfaith p).mp h.symm))
  obtain ⟨n,E,s,hn,hs,hsp,herr⟩ := exists_matrix_projection_approx e τ hτ htr
    hfaith hdiff h1 hfactor hp hnorm
  have hsn : s.Nonempty := by
    by_contra h
    have hz : s=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hz,Finset.sum_empty,sub_zero] at herr
    exact lt_irrefl _ herr
  obtain ⟨i,hi⟩ := hsn
  refine ⟨n,E,i,le_trans ?_ hsp⟩
  exact Finset.single_le_sum (fun j hj => (E.diagonal_proj j).nonneg) hi

include e hp in
lemma corner_factor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (hp0 : p ≠ 0) :
    ∀ b : Corner p hp, (∀ x : Corner p hp, Commute b x) → ∃ c : ℂ, b=c • (1 : Corner p hp) := by
  obtain ⟨n,E,i,hi⟩ := exists_matrix_diagonal_below p hp e τ hτ h1 htr hfaith hfactor hdiff hp0
  exact corner_factor_of_matrix_diagonal p hp E i hi hfactor

end HochschildCorners
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialUnitaries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr in
lemma power_tendsto {I : Type*} {l : Filter I} {v : I → PartialUnitary M} {w : PartialUnitary M}
    (h : GNSTendsto τ (fun i => (v i : M)) l (w : M)) (k : Bool × ℕ) :
    GNSTendsto τ (fun i => (v i).power k) l (w.power k) := by
  have hbase : GNSTendsto τ (fun i => if k.1 then star (v i : M) else (v i : M)) l
      (if k.1 then star (w : M) else (w : M)) := by split <;> first | exact h.star τ htr | exact h
  have hn : ∀ i, ‖if k.1 then star (v i : M) else (v i : M)‖≤1 := by
    intro i; split <;> simpa only [norm_star] using (v i).norm_le_one
  have hp (n : ℕ) : GNSTendsto τ (fun i => (if k.1 then star (v i : M) else (v i : M))^n) l
      ((if k.1 then star (w : M) else (w : M))^n) := by
    induction n with
    | zero => simpa only [pow_zero] using GNSTendsto.const τ (1 : M) l
    | succ n ih =>
      simpa only [pow_succ'] using hbase.mul τ htr ih 1 hn
  exact hp _
end PartialUnitary
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
namespace PartialUnitary
include e hL hτ htr hfaith in
lemma exists_monotone_limit (v : ℕ → PartialUnitary M) (hv : Monotone v) :
    ∃ w : PartialUnitary M, GNSTendsto τ (fun n => (v n : M)) atTop (w : M) ∧
      (∀ n, v n ≤ w) ∧ ∀ z : PartialUnitary M, (∀ n, v n ≤ z) → w ≤ z := by
  obtain ⟨w,ht,hvw,hwleast⟩ := PartialIso.exists_monotone_limit e τ hL hτ htr hfaith
    (fun n => (v n).val) hv
  have hf := ht.mul τ htr (ht.star τ htr) 1 (fun n => (v n).norm_le_one)
  have hi := (ht.star τ htr).mul τ htr ht 1 (fun n => by simpa only [norm_star] using (v n).norm_le_one)
  have he : w.final=w.initial := by
    apply GNSTendsto.unique τ hfaith hf
    change GNSTendsto τ (fun n => (v n).val.final) atTop w.initial
    simpa only [(v _).property,PartialIso.initial] using hi
  exact ⟨⟨w,he⟩,ht,hvw,fun z hz => hwleast z.val hz⟩

 

include e hL hτ htr hfaith in
lemma chain_limit (c : Set (PartialUnitary M)) (hc : IsChain (·  ≤  ·) c) (hne : c.Nonempty) :
    ∃ a : ℕ → PartialUnitary M, (∀ n, a n ∈ c) ∧ Monotone a ∧
      ∃ s : PartialUnitary M, GNSTendsto τ (fun n => (a n : M)) atTop (s : M) ∧
        (∀ v  ∈  c, v ≤ s) ∧ ∀ z : PartialUnitary M, (∀ v  ∈  c, v ≤ z) → s ≤ z := by
  classical
  let T : Set ℝ := (fun v : PartialUnitary M => (τ v.support).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨(τ 1).re,by
    rintro _ ⟨v,hv,rfl⟩
    exact Complex.re_le_re (τ.monotone v.support_proj.le_one)⟩
  obtain ⟨b,hbm,_hbub,hbt,hb⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hab using hb
  change ∀ n, (τ (a n).support).re=b n at hab
  have ham : Monotone a := by
    intro m n hmn
    apply PartialIso.le_of_comparable_trace_le τ hfaith (hc.total (ha m) (ha n))
    rw [hab,hab]
    exact hbm hmn
  obtain ⟨s,ht,has,hsleast⟩ := exists_monotone_limit e τ hL hτ htr hfaith a ham
  have hi := (ht.star τ htr).mul τ htr ht 1
    (fun n => by simpa only [norm_star] using (a n).norm_le_one)
  change GNSTendsto τ (fun n => (a n).support) atTop s.support at hi
  have htrace : (τ s.support).re=sSup T := by
    have hz := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
        (fun n => (a n).support_proj.norm_le _) hi)
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp hz)
    simpa only [Function.comp_def,hab] using hbt
  refine ⟨a,ha,ham,s,ht,?_,fun z hz => hsleast z (fun n => hz _ (ha n))⟩
  intro z hz
  by_cases hex : ∃ n, z ≤ a n
  · obtain ⟨n,hn⟩ := hex
    exact hn.trans (has n)
  · have haz : ∀ n, a n ≤ z := fun n =>
      (hc.total (ha n) hz).resolve_right (fun h => hex ⟨n,h⟩)
    apply PartialIso.le_of_comparable_trace_le τ hfaith (Or.inr (hsleast z haz))
    rw [htrace]
    exact le_csSup hTbd ⟨z,hz,rfl⟩

include e hL hτ htr hfaith in
lemma maximal_of_sequentially_closed (P : PartialUnitary M → Prop) (h0 : P 0)
    (hclosed : ∀ (a : ℕ → PartialUnitary M) (s : PartialUnitary M),
      Monotone a → (∀ n, P (a n)) →
      GNSTendsto τ (fun n => (a n : M)) atTop (s : M) → P s) :
    ∃ v : PartialUnitary M, Maximal P v := by
  apply zorn_le₀
  intro c hc hchain
  by_cases hne : c.Nonempty
  · obtain ⟨a,ha,ham,s,ht,hs,_⟩ := chain_limit e τ hL hτ htr hfaith c hchain hne
    exact ⟨s,hclosed a s ham (fun n => hc (ha n)) ht,hs⟩
  · exact ⟨0,h0,fun v hv => (hne ⟨v,hv⟩).elim⟩
end PartialUnitary
end HochschildComparison

 

 

 

open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small unitary moments, reindexing and simultaneous moment sequences. -/

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
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} {K L : ℕ}

lemma wordCoeff_map (F : J → M) (f : I → J) (a : Option I) :
    wordCoeff F (a.map f)=wordCoeff (F ∘ f) a := by cases a <;> rfl
end HochschildPatching

 

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem halfTraceCut_trace (p : AlgebraProjection M) :
    τ.trace (halfTraceCut τ hdiff p).val = ((τ.trace p.val).re/2 : ℝ) :=
  (exists_half_trace_cut τ hdiff p).choose_spec.2

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

theorem splitProjection_trace (p : AlgebraProjection M) (b : Bool) :
    τ.trace (splitProjection τ hdiff p b).val = ((τ.trace p.val).re/2 : ℝ) := by
  cases b
  · exact halfTraceCut_trace τ hdiff p
  · change τ.trace (p.val-(halfTraceCut τ hdiff p).val)=_
    have he : τ.trace (p.val-(halfTraceCut τ hdiff p).val)=
        τ.trace p.val-τ.trace (halfTraceCut τ hdiff p).val := inner_sub_right _ _ _
    have hreal : τ.trace p.val = ((τ.trace p.val).re : ℂ) := by
      have h := τ.trace_star_mul p.val
      rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
      rw [h,← Complex.ofReal_pow,Complex.ofReal_re]
    rw [he,halfTraceCut_trace,hreal]
    simp only [Complex.ofReal_re]
    push_cast
    ring

def dyadicProjection (p : AlgebraProjection M) : (n : ℕ) → DyadicIndex n → AlgebraProjection M
  | 0, _ => p
  | n+1, i => splitProjection τ hdiff (dyadicProjection p n i.1) i.2

theorem dyadicProjection_le_parent (p : AlgebraProjection M) (n : ℕ) (i : DyadicIndex (n+1)) :
    dyadicProjection τ hdiff p (n+1) i ≤ dyadicProjection τ hdiff p n i.1 :=
  splitProjection_le τ hdiff _ _

theorem dyadicProjection_trace (p : AlgebraProjection M) (n : ℕ) (i : DyadicIndex n) :
    (τ.trace (dyadicProjection τ hdiff p n i).val).re = (τ.trace p.val).re/(2:ℝ)^n := by
  induction n with
  | zero => simp [dyadicProjection]
  | succ n ih =>
    change (τ.trace (splitProjection τ hdiff (dyadicProjection τ hdiff p n i.1) i.2).val).re = _
    rw [splitProjection_trace,Complex.ofReal_re,ih,pow_succ]
    ring

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

theorem projectionSum_trace (τ : TracialRepresentation M)
    (a : ι → AlgebraProjection M) (c : ι → ℂ) :
    τ.trace (projectionSum a c)=∑ i, c i*τ.trace (a i).val := by
  change coordinateTraceLinear τ (∑ i, c i • (a i).val)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (coordinateTraceLinear τ).map_smul (c i) (a i).val

variable (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

abbrev dyadicEval (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :=
  projectionSum (dyadicProjection τ hdiff p n) c

theorem dyadicEval_one (p : AlgebraProjection M) (n : ℕ) :
    dyadicEval τ hdiff p n (fun _ => 1)=p.val := by
  simpa only [dyadicEval,projectionSum,one_smul] using dyadicProjection_sum τ hdiff p n

theorem dyadicEval_refine (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :
    dyadicEval τ hdiff p (n+1) (fun i => c i.1)=dyadicEval τ hdiff p n c := by
  change (∑ i : DyadicIndex n × Bool, c i.1 •
    (splitProjection τ hdiff (dyadicProjection τ hdiff p n i.1) i.2).val)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool,add_comm,← smul_add,splitProjection_sum]

theorem dyadicEval_lift (p : AlgebraProjection M) {m n : ℕ} (hmn : m ≤ n)
    (c : DyadicIndex m → ℂ) :
    ∃ d : DyadicIndex n → ℂ, dyadicEval τ hdiff p m c=dyadicEval τ hdiff p n d := by
  induction n,hmn using Nat.le_induction with
  | base => exact ⟨c,rfl⟩
  | succ n hmn ih =>
    obtain ⟨d,hd⟩ := ih
    exact ⟨fun i => d i.1,hd.trans (dyadicEval_refine τ hdiff p n d).symm⟩

theorem dyadicEval_trace (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :
    τ.trace (dyadicEval τ hdiff p n c)=
      ∑ i, c i*((τ.trace p.val).re/(2:ℝ)^n : ℝ) := by
  rw [projectionSum_trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [projection_trace_real,dyadicProjection_trace]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem insideAlgebra_closed : IsClosed (insideAlgebra (M := M) (P := P) : Set M.toStarSubalgebra) :=
  (base_norm_closed P).preimage continuous_subtype_val

instance insideAlgebra_complete : CompleteSpace (insideAlgebra (M := M) (P := P)) :=
  (insideAlgebra_closed (M := M) (P := P)).completeSpace_coe

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_EnergyDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Quantitative descent for a finite spectral pinching, and actual unitary
displacement from irreducibility. A compatible spectral partition in a
residual corner is not postulated as a local-quantization theorem. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem displacement_le_commutator (u : unitary M.toStarSubalgebra)
    (x : M.toStarSubalgebra) :
    τ.norm₂ (conjugateLinear u x-x) ≤ τ.norm₂ ((u : M.toStarSubalgebra)*x-x*(u : M.toStarSubalgebra)) := by
  have he : conjugateLinear u x-x=
      ((u : M.toStarSubalgebra)*x-x*(u : M.toStarSubalgebra))*star (u : M.toStarSubalgebra) := by
    change (u : M.toStarSubalgebra)*x*star (u : M.toStarSubalgebra)-x=_
    rw [sub_mul,mul_assoc x,u.property.2,mul_one]
  rw [he]
  exact (τ.norm₂_mul_le_right _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (unitary_norm_le _ (by simp)))

end

/-! The one-step energy decrease has pieces in the prescribed von Neumann
subalgebra. Irreducibility supplies the unitary, not an assumed energy budget. -/

/-! Strict displacement from zero in the actual closed convex orbit hull,
without imposing a scalar commutant on a block diagonal algebra. -/

/-! Actual compatible 63/64 descent for the orthogonal component of Popa
A.1.1 in an irreducible inclusion. Both displacement and finite spectral
partitions are constructed, and all pieces remain in the prescribed N. -/

/-! Geometric iteration and finite-family small-energy partitions for the
orthogonal component. No energy budget or block displacement is assumed. -/

/-! Assembly of the orthogonal budget with an explicitly controlled
subalgebra component. This constructs the further refinement; constructing
the initial subalgebra-component budget is not asserted here. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem expectation_trace_adjoint (x : M.toStarSubalgebra) : τ.trace (star x)=star (τ.trace x) := by
  change τ.trace (star x)=(starRingEnd ℂ) (τ.trace x)
  have h := inner_conj_symm (𝕜 := ℂ) (baseVector τ x) (baseVector τ 1)
  simpa only [baseVector_inner_trace,star_one,one_mul,mul_one] using h.symm

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x : M.toStarSubalgebra}
theorem mul_left (hx : TraceOrthogonal τ P x) (a : M.toStarSubalgebra) (ha : a ∈ P) :
    TraceOrthogonal τ P (a*x) := by
  intro b
  exact mul_assoc (b : M.toStarSubalgebra) a x ▸ hx ⟨(b : M.toStarSubalgebra)*a,P.mul_mem b.property ha⟩
theorem mul_right (hx : TraceOrthogonal τ P x) (a : M.toStarSubalgebra) (ha : a ∈ P) :
    TraceOrthogonal τ P (x*a) := by
  intro b
  rw [← mul_assoc,τ.trace_mul_comm,← mul_assoc]
  exact hx ⟨a*(b : M.toStarSubalgebra),P.mul_mem ha b.property⟩
theorem adjoint (hx : TraceOrthogonal τ P x) : TraceOrthogonal τ P (star x) := by
  intro a
  have h := congrArg star (hx ⟨star (a : M.toStarSubalgebra),P.star_mem' a.property⟩)
  change star (τ.trace (star (a : M.toStarSubalgebra)*x))=star (0 : ℂ) at h
  rw [← expectation_trace_adjoint,star_mul,star_star,star_zero,τ.trace_mul_comm] at h
  exact h
end TraceOrthogonal

end

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.expectationPosCStar
attribute [local instance] OAI.Generator.Tracial.expectationPosOrder
local instance expectationPosPreorder_r1db954_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.expectationPosLE
attribute [local instance] OAI.Generator.Tracial.expectationPosStarOrder
theorem negPart_mem_inside (c : M.toStarSubalgebra) (hc : c.val ∈ N) :
    c⁻ ∈ insideAlgebra (M := M) (P := N) := by
  rw [CFC.negPart_def,cfcₙ_eq_cfc]
  let : IsClosed (insideAlgebra (M := M) (P := N) : Set M.toStarSubalgebra) :=
    insideAlgebra_closed (M := M) (P := N)
  exact cfc_mem (𝕜' := ℂ) (s := insideAlgebra (M := M) (P := N)) (fun t : ℝ => t⁻) hc

end

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
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

instance concrete_finiteDimensional : FiniteDimensional ℂ E.concreteAlgebra := by
  change FiniteDimensional ℂ E.concreteHom.toAlgHom.range
  exact FiniteDimensional.of_surjective E.concreteHom.toAlgHom.rangeRestrict.toLinearMap
    E.concreteHom.toAlgHom.rangeRestrict_surjective

def wotLinearMap : Matrix ι ι ℂ →ₗ[ℂ] (H →WOT[ℂ] H) :=
  (ContinuousLinearMap.WOTofCLM.toLinearMap).comp E.concreteHom.toAlgHom.toLinearMap

theorem concreteAlgebra_wotClosed : WOTClosed E.concreteAlgebra := by
  have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ E.concreteAlgebra} =
      (E.wotLinearMap.range : Set (H →WOT[ℂ] H)) := by
    ext T
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a, congrArg ContinuousLinearMapWOT.ofCLM ha⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,congrArg ContinuousLinearMapWOT.toCLM ha⟩
  unfold WOTClosed
  rw [heq]
  exact E.wotLinearMap.range.closed_of_finiteDimensional

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
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/
namespace Tracial
open scoped BigOperators

/-! A constructed full matrix algebra reduces the actual relative-commutant
expectation energy by a uniform factor for a centered nonzero element. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N D M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem commutator_norm₂_bound (a b : M.toStarSubalgebra) :
    τ.norm₂ (a*b-b*a) ≤ 2*‖a‖*τ.norm₂ b := by
  have h := norm_sub_le (baseVector τ (a*b)) (baseVector τ (b*a))
  change τ.norm₂ (a*b-b*a) ≤ τ.norm₂ (a*b)+τ.norm₂ (b*a) at h
  have hl := τ.norm₂_mul_le a b
  have hr := τ.norm₂_mul_le_right b a
  nlinarith

theorem commutator_norm₂_approximation (u v x z : M.toStarSubalgebra)
    (hc : v*z=z*v) :
    τ.norm₂ (u*x-x*u) ≤ 2*‖u‖*τ.norm₂ (x-z)+2*‖z‖*τ.norm₂ (u-v) := by
  have he : u*x-x*u=(u*(x-z)-(x-z)*u)- (z*(u-v)-(u-v)*z) := by
    simp only [mul_sub,sub_mul]
    rw [hc]
    abel
  rw [he]
  have h := norm_sub_le (baseVector τ (u*(x-z)-(x-z)*u))
    (baseVector τ (z*(u-v)-(u-v)*z))
  change τ.norm₂ ((u*(x-z)-(x-z)*u)-(z*(u-v)-(u-v)*z)) ≤
    τ.norm₂ (u*(x-z)-(x-z)*u)+τ.norm₂ (z*(u-v)-(u-v)*z) at h
  exact h.trans (add_le_add (commutator_norm₂_bound τ u (x-z))
    (commutator_norm₂_bound τ z (u-v)))

end Tracial

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/
section
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_countable_norm₂_dense (S : Set M.toStarSubalgebra)
    (hne : S.Nonempty) (hsep : TopologicalSpace.IsSeparable (baseVector τ '' S)) :
    ∃ a : ℕ → M.toStarSubalgebra,(∀ n,a n ∈ S) ∧
      ∀ b ∈ S,∀ ε : ℝ,0 < ε → ∃ n,τ.norm₂ (b-a n) < ε := by
  let T := baseVector τ '' S
  let : TopologicalSpace.SeparableSpace T := hsep.separableSpace
  let : Nonempty T := ⟨⟨baseVector τ hne.choose,Set.mem_image_of_mem _ hne.choose_spec⟩⟩
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq (α := T)
  have hex (n : ℕ) : ∃ a ∈ S,baseVector τ a=(v n).val := (v n).property
  choose a ha he using hex
  refine ⟨a,ha,?_⟩
  intro b hb ε hε
  let z : T := ⟨baseVector τ b,Set.mem_image_of_mem _ hb⟩
  obtain ⟨w,⟨n,rfl⟩,hw⟩ := Metric.mem_closure_iff.mp (hv z) ε hε
  refine ⟨n,?_⟩
  change ‖baseVector τ (b-a n)‖ < ε
  rw [map_sub,he n]
  simpa only [Subtype.dist_eq,dist_eq_norm] using hw

end Tracial

end

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

theorem stage_le_generated (A : ℕ → FiniteMatrixStage N) (n : ℕ) :
    (A n).units.concreteAlgebra ≤ generated A := by
  intro x hx
  exact subset_wstar _ (Set.mem_iUnion.mpr ⟨n,hx⟩)

theorem generated_le (A : ℕ → FiniteMatrixStage N) : generated A ≤ N.toStarSubalgebra := by
  apply wstar_le (vonNeumann_wotClosed N)
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact (A n).units.concreteAlgebra_le hn

theorem generated_minimal (A : ℕ → FiniteMatrixStage N)
    (R : StarSubalgebra ℂ (H →L[ℂ] H)) (hR : WOTClosed R)
    (h : ∀ n,(A n).units.concreteAlgebra ≤ R) : generated A ≤ R := by
  apply wstar_le hR
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact h n hn

theorem generated_relative_scalar (A : ℕ → FiniteMatrixStage N)
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ (A n).commutant hNM) →
      c=τ.trace c • (1 : M.toStarSubalgebra))
    (c : M.toStarSubalgebra)
    (hc : ∀ a : generated A,a.val*c.val=c.val*a.val) :
    c=τ.trace c • (1 : M.toStarSubalgebra) := by
  apply hirr c
  intro n
  apply (((A n).units.map (coordinateInclusion hNM)).relativeStar_mem c.val).mpr
  refine ⟨c.property,?_⟩
  intro i j
  have hi : ((A n).units.entry i j).val ∈ (A n).units.concreteAlgebra := by
    exact ((A n).units.mem_concreteAlgebra _).mpr ((A n).units.entry_mem i j)
  exact hc ⟨((A n).units.entry i j).val,stage_le_generated A n hi⟩

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def generatedVonNeumann (A : ℕ → FiniteMatrixStage N) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed (generated A) (generated_closed A)

theorem generatedVonNeumann_le (A : ℕ → FiniteMatrixStage N) : generatedVonNeumann A ≤ N :=
  generated_le A

def generatedTrace (A : ℕ → FiniteMatrixStage N) (τ : TracialRepresentation M) (hNM : N ≤ M) :
    TracialRepresentation (generatedVonNeumann A) :=
  restrictedTrace τ ((generatedVonNeumann_le A).trans hNM)

end FiniteMatrixStage

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {N M : VonNeumannAlgebra H}

def stageUnion (A : ℕ → FiniteMatrixStage N) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  ⨆ n,(A n).units.concreteAlgebra

theorem stageUnion_coe (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    (stageUnion A : Set (H →L[ℂ] H))=⋃ n,((A n).units.concreteAlgebra : Set (H →L[ℂ] H)) :=
  StarSubalgebra.coe_iSup_of_directed hA.directed_le

theorem generated_eq_wstar_union (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    generated A=wstar (stageUnion A : Set (H →L[ℂ] H)) := by
  rw [stageUnion_coe A hA]
  rfl

theorem exists_stage_strong_approximation (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) (T : generated A)
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ n,∃ a : (A n).units.concreteAlgebra,∀ x ∈ s,‖T.val x-a.val x‖ < ε := by
  have hT : T.val ∈ Set.centralizer (Set.centralizer (stageUnion A : Set (H →L[ℂ] H))) := by
    rw [← bicommutantVonNeumann_coe]
    change T.val ∈ (bicommutantVonNeumann (stageUnion A)).toStarSubalgebra
    rw [← wstar_starAlgebra_eq_bicommutant,← generated_eq_wstar_union A hA]
    exact T.property
  obtain ⟨a,ha⟩ := bicommutant_finite_strong_approximation (stageUnion A) T.val hT s ε hε
  have hm := a.property
  rw [← SetLike.mem_coe,stageUnion_coe A hA] at hm
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hm
  exact ⟨n,⟨a.val,hn⟩,ha⟩

end FiniteMatrixStage

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The next sign is centered even after multiplication by an arbitrary
member of the previous finite dyadic algebra. -/
theorem dyadicRademacher_centered_over_previous (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    τ.trace (dyadicEval τ hdiff p n c*dyadicRademacher τ hdiff p n)=0 := by
  rw [← dyadicEval_refine τ hdiff p n c]
  unfold dyadicRademacher dyadicEval
  rw [projectionSum_mul _ (dyadicProjection_orthogonal τ hdiff p (n+1))]
  rw [dyadicEval_trace]
  change (∑ i : DyadicIndex n × Bool,
    (c i.1*dyadicSign n i)*((τ.trace p.val).re/(2:ℝ)^(n+1) : ℝ))=0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  rw [Fintype.sum_bool]
  simp [dyadicSign]

theorem dyadicRademacher_trace_mul_of_lt (p : AlgebraProjection M) {m n : ℕ} (hmn : m < n) :
    τ.trace (dyadicRademacher τ hdiff p m*dyadicRademacher τ hdiff p n)=0 := by
  obtain ⟨c,hc⟩ := dyadicEval_lift τ hdiff p (Nat.succ_le_iff.mpr hmn) (dyadicSign m)
  change τ.trace (dyadicEval τ hdiff p (m+1) (dyadicSign m)*_)=0
  rw [hc]
  exact dyadicRademacher_centered_over_previous τ hdiff p n c

theorem dyadicRademacher_trace_mul_of_ne (p : AlgebraProjection M) {m n : ℕ} (hmn : m ≠ n) :
    τ.trace (dyadicRademacher τ hdiff p m*dyadicRademacher τ hdiff p n)=0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · exact dyadicRademacher_trace_mul_of_lt τ hdiff p h
  · rw [τ.trace_mul_comm]
    exact dyadicRademacher_trace_mul_of_lt τ hdiff p h

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


