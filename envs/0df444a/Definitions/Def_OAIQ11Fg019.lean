-- Prove2me | Definitions.Def_OAIQ11Fg019
-- name    : OAIQ11Fg019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:42:20.883608+00:00
-- url     : https://prove2.me/theorems/8b6ec6c3-07df-41f4-a424-6777f08f119e
-- title:
--   Definitions bundle OAIQ11Fg019 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 14 definitions and 13 theorems. The definitions and types are `OAI.Generator.Tracial.traceFreeHilbertClosureTrace`, `OAI.Generator.Tracial.traceFreeHilbertEquiv`, `OAI.Generator.Tracial.traceFreeHilbertIsometry`, `OAI.Generator.Tracial.traceFreeHilbertVectorBall`, `OAI.Generator.Tracial.traceFreeHilbertWeakBall`, `OAI.Generator.Tracial.traceFreeSubalgebraClosure`, `OAI.Generator.Tracial.traceFreeSubalgebraInclusion`, `OAI.Generator.Tracial.traceFreeSubalgebraVectorBall`, `OAI.Generator.Tracial.traceFreeSubalgebraWeakBall`, `OAI.Generator.Tracial.traceGenerationTransportOperatorCStar`, `OAI.Generator.Tracial.traceHilbertImageClosureCStar`, `OAI.Generator.Tracial.traceHilbertTransportClosureCStar`, `OAI.Generator.Tracial.traceSubalgebraImageClosureCStar`, `OAI.Generator.Tracial.traceSubalgebraImageOperatorCStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean), [`FactorGeneration_TraceTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTransport.lean).
--
--   **Imports.** It imports the bundle `OAIQ11Fg018` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ11Fg031`; the statements `OAI_Generator_Tracial_SuccessiveCoordinateHaar_commonPerturbation_norm_sq`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_coordinateLabels_quotient`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_coordinateTarget_quotient`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_coordinateVariables_quotient`, `OAI_Generator_Tracial_common_relative_projection_continuity_algebra`, `OAI_Generator_Tracial_cyclicResidualFamily_centered`, `OAI_Generator_Tracial_cyclicResidualFamily_supported`, `OAI_Generator_Tracial_exists_exact_residual_iteration`, `OAI_Generator_Tracial_quotientResidualTrace_antitone`, `OAI_Generator_Tracial_quotient_geometric_upper_completion` and `OAI_Generator_Tracial_quotient_partial_distance_sq`; the proofs of `OAI_Generator_Tracial_SuccessiveCoordinateHaar_coordinateLabels_quotient`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_coordinateTarget_quotient`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_coordinateVariables_quotient`, `OAI_Generator_Tracial_common_relative_projection_continuity_algebra`, `OAI_Generator_Tracial_cyclicResidualFamily_centered`, `OAI_Generator_Tracial_cyclicResidualFamily_supported`, `OAI_Generator_Tracial_exists_exact_residual_iteration`, `OAI_Generator_Tracial_exists_full_support_ordered_independence`, `OAI_Generator_Tracial_exists_scalar_pinching_for_matrixUnits`, `OAI_Generator_Tracial_exists_unitResidual_controlled_patch`, `OAI_Generator_Tracial_quotientResidualTrace_antitone`, `OAI_Generator_Tracial_quotient_geometric_upper_completion`, `OAI_Generator_Tracial_quotient_partial_distance_sq`, `OAI_Generator_Tracial_represented_two_selfAdjoint_generators`, `OAI_Generator_Tracial_traceClip_mem_original`, `OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback`, `OAI_Generator_finitePerturbationRows_degree_bound` and `OAI.Generator.single_generation_of_II1_separable_predual`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ11Fg018

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertClosureOperatorCStar
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

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertWOTOperatorCStar
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
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
local instance traceHilbertImageOrder_r7246ac_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertImageStarOrder_r7246ac_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceHilbertImageOperatorCStar_r7246ac_1 : CStarAlgebra (K →L[ℂ] K) := {}
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
local instance traceHilbertTransportOrder_r7246ac_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertTransportStarOrder_r7246ac_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceHilbertTransportOperatorCStar_r7246ac_1 : CStarAlgebra (K →L[ℂ] K) := {}
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

local instance traceSubalgebraBallOperatorCStar_r7246ac_1 : CStarAlgebra (K →L[ℂ] K) := {}
variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraBallCStar
local instance traceSubalgebraBallOrder_r7246ac_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraBallStarOrder_r7246ac_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceSubalgebraBallClosureCStar_r7246ac_1 : CStarAlgebra (N).toStarSubalgebra := {}
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

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageCStar
local instance traceSubalgebraImageOrder_r7246ac_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraImageStarOrder_r7246ac_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceSubalgebraImageClosureCStar : CStarAlgebra (N).toStarSubalgebra := {}

variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

local notation "P" => StarSubalgebra.map π (StarSubalgebra.comap
  (StarSubalgebra.subtype (VonNeumannAlgebra.toStarSubalgebra M)) Q)

/-- The double commutant of the represented intersection with Q. -/
def traceFreeSubalgebraClosure : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (P : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        (P : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))) =
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        (P : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    simp only [Set.centralizer_centralizer_centralizer]

local notation "R" => traceFreeSubalgebraClosure hfactor hdiff hfinite hunit Q

theorem traceFreeSubalgebraClosure_mem_iff (T : K →L[ℂ] K) :
    T ∈ R ↔ T ∈ Set.centralizer (Set.centralizer (P : Set (K →L[ℂ] K))) := by
  change T ∈ (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (P : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) ↔ _
  simp only [← SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq,Set.union_self]

theorem traceFreeSubalgebraClosure_le : (R).toStarSubalgebra ≤ (N).toStarSubalgebra := by
  intro T hT
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit T).mpr
  have ht := (traceFreeSubalgebraClosure_mem_iff hfactor hdiff hfinite hunit Q T).mp hT
  intro a ha
  apply ht a
  rintro b ⟨c,_,rfl⟩
  exact ha (π c) ⟨c,rfl⟩

def traceFreeSubalgebraInclusion : (R).toStarSubalgebra →⋆ₐ[ℂ] (N).toStarSubalgebra :=
  StarSubalgebra.inclusion (traceFreeSubalgebraClosure_le hfactor hdiff hfinite hunit Q)

end

/-! Generation pullback for the actual constructed trace representation. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local instance traceGenerationTransportOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

end Tracial

end Generator

end

end OAI
end


