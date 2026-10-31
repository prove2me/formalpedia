-- Prove2me | Definitions.Def_OAIQ129Rg000
-- name    : OAIQ129Rg000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:44:16.500567+00:00
-- url     : https://prove2.me/theorems/0dfb7079-5742-488b-9ef7-9ab96d432d32
-- title:
--   Definitions bundle OAIQ129Rg000 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 17 definitions, 1 inductive type or structure, 1 instance and 15 theorems. The definitions and types are `OAI.Generator.FactorTraceUnitary`, `OAI.Generator.FactorTraceUnitary.algebra`, `OAI.Generator.FactorTraceUnitary.represented`, `OAI.Generator.FactorTraceUnitary.representedEquiv`, `OAI.Generator.FactorTraceUnitary.representedHomeomorph`, `OAI.Generator.FactorTraceUnitary.representedIsometryEquiv`, `OAI.Generator.FactorTraceUnitary.traceHomeomorph`, `OAI.Generator.FactorTraceUnitary.unitaryEquiv`, `OAI.Generator.Tracial.relativeDistance`, `OAI.Generator.Tracial.traceFreeRelativeImage`, `OAI.Generator.Tracial.traceFreeRelativeImageEquiv`, `OAI.Generator.Tracial.traceFreeRelativeImageHom`, `OAI.Generator.concretePreimage`, `OAI.Generator.factorTracePreInner`, `OAI.Generator.factorTracePreNormed`, `OAI.Generator.factorVonNeumann`, `OAI.Generator.normalizedFactorTrace`, `OAI.RelativeGeneration.traceUnitaryHomeomorph`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_TraceTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTransport.lean), [`RelativeGeneration_InclusionTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RelativeGeneration/InclusionTransport.lean), [`RelativeGeneration_LocusTopology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RelativeGeneration/LocusTopology.lean), [`RelativeGeneration_OriginalUnitary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RelativeGeneration/OriginalUnitary.lean), [`RelativeGeneration_Topology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RelativeGeneration/Topology.lean).
--
--   **Imports.** It imports the published bundles `Def_FactorGeneration` and `Def_RelativeGeneration`; the bundle `OAIQ11Fg019` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.Generator.Tracial.traceFreeRelativeGeneration_iff`; the proofs of `OAI.Generator.Tracial.traceFreeRelativeGeneration_iff` and `OAI.RelativeGeneration.main_theorem`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_RelativeGeneration
import Definitions.Def_OAIQ11Fg019

section
-- module Solutions.OAIQ129_RG.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
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
section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}
  {T : StarSubalgebra ℂ (K →L[ℂ] K)}

/-- Ambient concrete inverse image, contained in S. -/
def concretePreimage (φ : S →⋆ₐ[ℂ] T)
    (Q : StarSubalgebra ℂ (K →L[ℂ] K)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (Q.comap (T.subtype.comp φ)).map S.subtype

/-! Transport of the unchanged finite diffuse factor predicate.
The algebraic fields use the actual star isomorphism; target WOT closedness
is explicit. No trace or separability conclusion is inferred. -/

end

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

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

theorem traceHilbertVonNeumann_wotClosed {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (P : VonNeumannAlgebra J) : WOTClosed P.toStarSubalgebra := by
  change IsClosed {T : J →WOT[ℂ] J | T.toCLM ∈ (P : Set (J →L[ℂ] J))}
  rw [← P.centralizer_centralizer]
  change IsClosed {T : J →WOT[ℂ] J |
    ∀ S ∈ Set.centralizer (P : Set (J →L[ℂ] J)),S*T.toCLM=T.toCLM*S}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro hS
  have he : {T : J →WOT[ℂ] J | S*T.toCLM=T.toCLM*S} =
      {T : J →WOT[ℂ] J |
        (ContinuousLinearMapWOT.equiv.symm S)*T=T*(ContinuousLinearMapWOT.equiv.symm S)} := by
    ext T
    let e : (J →WOT[ℂ] J) ≃ (J →L[ℂ] J) := ContinuousLinearMapWOT.equiv
    exact e.injective.eq_iff
  rw [he]
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

end

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/

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

local instance traceSubalgebraBallOperatorCStar_r376d0f_1 : CStarAlgebra (K →L[ℂ] K) := {}
variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraBallCStar
local instance traceSubalgebraBallOrder_r376d0f_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraBallStarOrder_r376d0f_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceSubalgebraBallClosureCStar_r376d0f_1 : CStarAlgebra (N).toStarSubalgebra := {}
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

theorem traceSymmetrize_mem_original (a : M.toStarSubalgebra) (ha : a.val ∈ Q) :
    (traceSymmetrize a).val ∈ Q := by
  have hs : star a.val ∈ Q := star_mem ha
  exact Q.smul_mem (Q.add_mem ha hs) _

theorem traceClip_mem_original (hQ : WOTClosed Q) (a : M.toStarSubalgebra)
    (haQ : a.val ∈ Q) (ha : IsSelfAdjoint a) (C : ℝ) : (traceClip a C).val ∈ Q := by
  let P := Q.comap M.toStarSubalgebra.subtype
  let : IsClosed (P : Set M.toStarSubalgebra) :=
    (hQ.preimage ContinuousLinearMapWOT.continuous_ofCLM).preimage continuous_subtype_val
  change traceClip a C ∈ P
  rw [traceClip_cfc a ha C]
  exact cfc_mem (𝕜' := ℂ) (fun t : ℝ => -min (-min t C) C) haQ

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

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageOperatorCStar
variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

local notation "P" => StarSubalgebra.map π (StarSubalgebra.comap
  (StarSubalgebra.subtype (VonNeumannAlgebra.toStarSubalgebra M)) Q)

local notation "R" => traceFreeSubalgebraClosure hfactor hdiff hfinite hunit Q

local notation "j" => traceFreeSubalgebraInclusion hfactor hdiff hfinite hunit Q

attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageCStar
local instance traceSubalgebraImageOrder_r376d0f_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraImageStarOrder_r376d0f_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.Generator.Tracial.traceSubalgebraImageClosureCStar
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

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG.RelativeGeneration_InclusionTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

section
-- module Solutions.OAIQ129_RG.RelativeGeneration_LocusTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

open scoped Topology

namespace Generator.Tracial

open UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeDistance (ξ : H) (unitary : TraceUnitary τ) : ℝ :=
  Metric.infDist ξ (relativeTraceSpace (N := N) τ unitary : Set H)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG.RelativeGeneration_Topology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

universe level

namespace RelativeGeneration

variable {Hilbert : Type level} [NormedAddCommGroup Hilbert]
  [InnerProductSpace ℂ Hilbert] [CompleteSpace Hilbert]

/-- A metric presentation with the trace two-distance gives precisely the trace-ball topology
on all genuine unitaries. -/
def traceUnitaryHomeomorph (algebra : StarSubalgebra ℂ (Hilbert →L[ℂ] Hilbert))
    (trace : algebra →L[ℂ] ℂ) {UnitarySpace : Type*} [MetricSpace UnitarySpace]
    (unitaryEquiv : UnitarySpace ≃ unitary algebra)
    (distance_eq : ∀ first second, dist first second =
      traceDistance algebra trace (unitaryEquiv first) (unitaryEquiv second)) :
    @Homeomorph UnitarySpace (unitary algebra) inferInstance (traceTopology algebra trace) := by
  letI : TopologicalSpace (unitary algebra) := traceTopology algebra trace
  refine { unitaryEquiv with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_generateFrom_iff.mpr
    rintro ball ⟨center, radius, _, rfl⟩
    have preimage_ball : unitaryEquiv ⁻¹'
        {point | traceDistance algebra trace center point < radius} =
        Metric.ball (unitaryEquiv.symm center) radius := by
      ext point
      change traceDistance algebra trace center (unitaryEquiv point) < radius ↔
        dist point (unitaryEquiv.symm center) < radius
      rw [dist_comm, distance_eq, unitaryEquiv.apply_symm_apply]
    change IsOpen (unitaryEquiv ⁻¹' {point | traceDistance algebra trace center point < radius})
    rw [preimage_ball]
    exact Metric.isOpen_ball
  · apply continuous_def.mpr
    intro openSet isOpenSet
    refine isOpen_iff_forall_mem_open.mpr ?_
    intro point point_mem
    obtain ⟨radius, radius_pos, ball_subset⟩ :=
      Metric.isOpen_iff.mp isOpenSet (unitaryEquiv.symm point) point_mem
    refine ⟨{candidate | traceDistance algebra trace point candidate < radius}, ?_,
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨point, radius, radius_pos, rfl⟩, ?_⟩
    · intro candidate candidate_mem
      apply ball_subset
      change dist (unitaryEquiv.symm candidate) (unitaryEquiv.symm point) < radius
      rw [dist_comm, distance_eq, unitaryEquiv.apply_symm_apply, unitaryEquiv.apply_symm_apply]
      exact candidate_mem
    · change traceDistance algebra trace point point < radius
      calc
        traceDistance algebra trace point point =
            dist (unitaryEquiv.symm point) (unitaryEquiv.symm point) := by
          simpa only [unitaryEquiv.apply_symm_apply] using
            (distance_eq (unitaryEquiv.symm point) (unitaryEquiv.symm point)).symm
        _ = 0 := dist_self _
        _ < radius := radius_pos

end RelativeGeneration

end

end OAI
end

section
-- module Solutions.OAIQ129_RG.RelativeGeneration_OriginalUnitary
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

/- Normalized trace-two topology on actual unitaries of the original factor.
   The wrapper avoids Mathlib's existing operator-norm topology on unitary S. -/
open scoped Topology
namespace Generator
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}

abbrev factorVonNeumann (hS : IsII1Factor S) : VonNeumannAlgebra H where
  toStarSubalgebra := S
  centralizer_centralizer' := wotClosed_bicommutant S hS.weaklyClosed

theorem IsII1Factor.factor_smul (hS : IsII1Factor S) :
    ∀ c : (factorVonNeumann hS).toStarSubalgebra,
      (∀ a : (factorVonNeumann hS).toStarSubalgebra, a*c=c*a) →
      ∃ z : ℂ,c=z • (1 : (factorVonNeumann hS).toStarSubalgebra) := by
  intro c hc
  obtain ⟨z,hz⟩ := hS.factor c hc
  exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩

theorem IsII1Factor.one_ne_zero (hS : IsII1Factor S) :
    (1 : (factorVonNeumann hS).toStarSubalgebra) ≠ 0 := by
  intro h
  exact hS.nonzero (congrArg Subtype.val h).symm

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

/-- Same unitaries, with trace topology rather than the operator-norm topology. -/
structure FactorTraceUnitary (S : StarSubalgebra ℂ (H →L[ℂ] H)) (_hS : IsII1Factor S) where
  toUnitary : unitary S

namespace FactorTraceUnitary

def algebra (u : FactorTraceUnitary S hS) : S := u.toUnitary

/-- Forgetting the metric wrapper preserves every genuine unitary of the original factor. -/
def unitaryEquiv : FactorTraceUnitary S hS ≃ unitary S where
  toFun := toUnitary
  invFun element := ⟨element⟩
  left_inv element := by cases element; rfl
  right_inv element := rfl

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


