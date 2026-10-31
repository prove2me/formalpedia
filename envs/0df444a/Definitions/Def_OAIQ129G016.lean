-- Prove2me | Definitions.Def_OAIQ129G016
-- name    : OAIQ129G016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:20:47.539474+00:00
-- url     : https://prove2.me/theorems/f931c7a3-36ad-4a54-8e65-18ecdbc85b87
-- title:
--   Definitions bundle OAIQ129G016 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 7 definitions and 11 theorems. The definitions and types are `OAI.Generator.Tracial.traceFreeRelativeImage`, `OAI.Generator.Tracial.traceFreeRelativeImageEquiv`, `OAI.Generator.Tracial.traceFreeRelativeImageHom`, `OAI.Generator.Tracial.traceFreeSubalgebraClosure`, `OAI.Generator.Tracial.traceFreeSubalgebraInclusion`, `OAI.Generator.Tracial.traceGenerationTransportOperatorCStar`, `OAI.Generator.Tracial.traceSubalgebraImageClosureCStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_TraceTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTransport.lean), [`RelativeGeneration_InclusionTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RelativeGeneration/InclusionTransport.lean).
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`; the bundle `OAIQ129G015` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.Generator.single_generation_of_II1_separable_predual` and `OAI.RelativeGeneration.main_theorem`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G015

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

local instance traceSubalgebraBallOperatorCStar_r10538a_1 : CStarAlgebra (K →L[ℂ] K) := {}
variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraBallCStar
local instance traceSubalgebraBallOrder_r10538a_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraBallStarOrder_r10538a_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceSubalgebraBallClosureCStar_r10538a_1 : CStarAlgebra (N).toStarSubalgebra := {}
theorem traceFreeSubalgebraWeakBall_isCompact (hQ : WOTClosed Q) (C : ℝ) :
    IsCompact (traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  have hc : IsCompact {T : weakOperatorBall M C | T.val.toCLM ∈ Q} :=
    (hQ.preimage continuous_subtype_val).isCompact
  have he : traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C =
      traceFreeHilbertBallMap hfactor hdiff hfinite hunit C ''
        {T : weakOperatorBall M C | T.val.toCLM ∈ Q} := by
    ext T
    constructor
    · rintro ⟨a,ha,hn,rfl⟩
      exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,hn⟩⟩,ha,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a.val.toCLM,a.property.1⟩,ha,a.property.2,rfl⟩
  rw [he]
  exact hc.image (traceFreeHilbertBallMap_continuous hfactor hdiff hfinite hunit C)

theorem traceFreeSubalgebraVectorBall_isClosed (hQ : WOTClosed Q) (C : ℝ) :
    IsClosed (traceFreeSubalgebraVectorBall hfactor hdiff hfinite hunit Q C) := by
  apply IsSeqClosed.isClosed
  intro v x hv hx
  choose a hQmem ha he using hv
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T,hT,ht⟩ := (traceFreeSubalgebraWeakBall_isCompact hfactor hdiff hfinite hunit Q hQ C).ultrafilter_le_nhds
    (ω.map (fun n => ContinuousLinearMapWOT.ofCLM (π (a n)))) (by
      apply le_principal_iff.mpr
      change ∀ᶠ n in (ω : Filter ℕ), ContinuousLinearMapWOT.ofCLM (π (a n)) ∈
        traceFreeSubalgebraWeakBall hfactor hdiff hfinite hunit Q C
      exact Eventually.of_forall (fun n => ⟨a n,hQmem n,ha n,rfl⟩))
  obtain ⟨b,hbQ,hb,rfl⟩ := hT
  refine ⟨b,hbQ,hb,?_⟩
  apply ext_inner_left ℂ
  intro y
  have hw := (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp ht) Ω y
  change Tendsto (fun n => inner ℂ y (π (a n) Ω)) (ω : Filter ℕ)
    (𝓝 (inner ℂ y (π b Ω))) at hw
  have hn := (innerSL ℂ y).continuous.continuousAt.tendsto.comp
    (hx.mono_left (Ultrafilter.of_le atTop))
  exact tendsto_nhds_unique hw (by simpa only [Function.comp_def,innerSL_apply_apply,he] using hn)

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

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageCStar
local instance traceSubalgebraImageOrder_r10538a_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraImageStarOrder_r10538a_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageOperatorCStar
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

local notation "j" => traceFreeSubalgebraInclusion hfactor hdiff hfinite hunit Q

theorem traceFreeSubalgebra_selfAdjoint_approximation
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) (hx : IsSelfAdjoint x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖j x‖ ∧
      (σ).norm₂ (ρ a-j x) < ε := by
  classical
  obtain ⟨v,hv⟩ := bicommutant_finite_strong_approximation P x.val
    ((traceFreeSubalgebraClosure_mem_iff hfactor hdiff hfinite hunit Q x.val).mp x.property)
    {Ω} ε hε
  obtain ⟨a,haQ,ha⟩ := v.property
  change π a = v.val at ha
  have ha' : (σ).norm₂ (ρ a-j x) < ε := by
    change ‖π a Ω-x.val Ω‖ < ε
    have happrox := hv Ω (Finset.mem_singleton_self Ω)
    change ‖x.val Ω-v.val Ω‖ < ε at happrox
    rw [← ha] at happrox
    simpa only [norm_sub_rev] using happrox
  let b := traceSymmetrize a
  have hb : IsSelfAdjoint b := traceSymmetrize_selfAdjoint a
  have hbQ : b.val ∈ Q := traceSymmetrize_mem_original Q a haQ
  have hJ : IsSelfAdjoint (j x) := hx.map j
  have hb' : (σ).norm₂ (ρ b-j x) ≤ (σ).norm₂ (ρ a-j x) := by
    have he : ρ b-j x = traceSymmetrize (ρ a-j x) := by
      rw [traceSymmetrize_sub,traceSymmetrize_eq_self (j x) hJ]
      exact congrArg (fun z => z-j x)
        (traceFreeHilbertIntoClosure_symmetrize hfactor hdiff hfinite hunit a)
    rw [he]
    exact traceSymmetrize_norm₂_le σ _
  refine ⟨traceClip b ‖j x‖,
    traceClip_mem_original Q hQ b hbQ hb _,
    traceClip_selfAdjoint b hb _,traceClip_norm_le b hb _ (norm_nonneg _),?_⟩
  rw [traceFreeHilbertIntoClosure_clip hfactor hdiff hfinite hunit b hb]
  exact (traceClip_distance σ (ρ b) (j x) (hb.map ρ) hJ).trans_lt (hb'.trans_lt ha')

theorem traceFreeSubalgebra_selfAdjoint_preimage
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ρ a = j x := by
  have hm : x.val Ω ∈ traceFreeSubalgebraVectorBall hfactor hdiff hfinite hunit Q ‖j x‖ := by
    apply (traceFreeSubalgebraVectorBall_isClosed hfactor hdiff hfinite hunit Q hQ ‖j x‖).closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,haQ,_,ha,hax⟩ := traceFreeSubalgebra_selfAdjoint_approximation
      hfactor hdiff hfinite hunit Q hQ x hx ε hε
    exact ⟨π a Ω,⟨a,haQ,ha,rfl⟩,by
      change ‖π a Ω-x.val Ω‖ < ε at hax
      simpa only [dist_eq_norm,norm_sub_rev] using hax⟩
  obtain ⟨a,haQ,_,ha⟩ := hm
  refine ⟨a,haQ,?_⟩
  apply sub_eq_zero.mp
  apply (σ).separating
  change π a Ω-x.val Ω = 0
  exact sub_eq_zero.mpr ha

theorem traceFreeSubalgebraClosure_preimage
    (hQ : WOTClosed Q) (x : (R).toStarSubalgebra) :
    ∃ a : M.toStarSubalgebra, a.val ∈ Q ∧ ρ a = j x := by
  obtain ⟨a,haQ,ha⟩ := traceFreeSubalgebra_selfAdjoint_preimage hfactor hdiff hfinite hunit Q hQ
    (ℜ x) (ℜ x).property
  obtain ⟨b,hbQ,hb⟩ := traceFreeSubalgebra_selfAdjoint_preimage hfactor hdiff hfinite hunit Q hQ
    (ℑ x) (ℑ x).property
  refine ⟨a+Complex.I • b,Q.add_mem haQ (Q.smul_mem hbQ _),?_⟩
  rw [map_add,map_smul,ha,hb,← map_smul,← map_add]
  exact congrArg j (realPart_add_I_smul_imaginaryPart x)

theorem traceFreeSubalgebraImage_eq_closure (hQ : WOTClosed Q) :
    P = (R).toStarSubalgebra := by
  apply le_antisymm
  · intro T hT
    apply (traceFreeSubalgebraClosure_mem_iff hfactor hdiff hfinite hunit Q T).mpr
    exact fun a ha => (ha T hT).symm
  · intro T hT
    obtain ⟨a,haQ,ha⟩ := traceFreeSubalgebraClosure_preimage hfactor hdiff hfinite hunit Q hQ ⟨T,hT⟩
    exact ⟨a,haQ,congrArg Subtype.val ha⟩

/-- Every original WOT-closed subalgebra has WOT-closed represented intersection.
No cyclicity of its orbit, factor hypothesis on Q, or full WOT continuity is used. -/
theorem traceFreeSubalgebraImage_wotClosed (hQ : WOTClosed Q) :
    WOTClosed ((Q.comap M.toStarSubalgebra.subtype).map π) := by
  rw [traceFreeSubalgebraImage_eq_closure hfactor hdiff hfinite hunit Q hQ]
  exact traceHilbertVonNeumann_wotClosed R

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

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_InclusionTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

/- Actual image inclusion, algebra equivalence, hypotheses, and relative generation. -/
namespace Generator.Tracial
open UltrapowerBridge
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
local notation "R" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

/-- The actual WOT-closed image of the original given subalgebra. -/
def traceFreeRelativeImage (P : StarSubalgebra ℂ (H →L[ℂ] H)) (hP : WOTClosed P) :
    VonNeumannAlgebra K :=
  vonNeumannOfWOTClosed ((P.comap M.toStarSubalgebra.subtype).map π)
    (traceFreeSubalgebraImage_wotClosed hfactor hdiff hfinite hunit P hP)

variable (P : StarSubalgebra ℂ (H →L[ℂ] H)) (hP : WOTClosed P)
local notation "N" => traceFreeRelativeImage hfactor hdiff hfinite hunit P hP

theorem traceFreeRelativeImage_le : N ≤ R := by
  rintro a ⟨b,hb,rfl⟩
  exact traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit b

variable (hPM : P ≤ M.toStarSubalgebra)

def traceFreeRelativeImageHom : P →⋆ₐ[ℂ] (N).toStarSubalgebra :=
  ((π).comp (StarSubalgebra.inclusion hPM)).codRestrict (N).toStarSubalgebra
    (fun a => ⟨StarSubalgebra.inclusion hPM a,a.property,rfl⟩)

theorem traceFreeRelativeImageHom_bijective :
    Function.Bijective (traceFreeRelativeImageHom hfactor hdiff hfinite hunit P hP hPM) := by
  constructor
  · intro a b h
    apply Subtype.ext
    have he := traceFreeHilbertAction_injective hfactor hdiff hfinite hunit
      (congrArg Subtype.val h)
    exact congrArg (fun x : M.toStarSubalgebra => x.val) he
  · rintro ⟨b,c,hc,rfl⟩
    exact ⟨⟨c.val,hc⟩,rfl⟩

def traceFreeRelativeImageEquiv : P ≃⋆ₐ[ℂ] (N).toStarSubalgebra :=
  StarAlgEquiv.ofBijective (traceFreeRelativeImageHom hfactor hdiff hfinite hunit P hP hPM)
    (traceFreeRelativeImageHom_bijective hfactor hdiff hfinite hunit P hP hPM)

end Generator.Tracial

end

end OAI
end


