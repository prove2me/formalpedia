-- Prove2me | Definitions.Def_OAIQ089A011
-- name    : OAIQ089A011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T03:22:33.411851+00:00
-- url     : https://prove2.me/theorems/8eeb501a-3655-45df-a482-372e15c3a78d
-- title:
--   Definitions bundle OAIQ089A011 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 5 definitions and 49 theorems. The definitions and types are `OAI.ContingencyTables.SmallGraphProfiles.FeasibleCode`, `OAI.ContingencyTables.SmallGraphProfiles.FeasibleOutcome`, `OAI.ContingencyTables.SmallGraphProfiles.encodedShortStep`, `OAI.ContingencyTables.SmallGraphProfiles.exactBoxScale`, `OAI.ContingencyTables.SmallGraphProfiles.scheduledCountsLaw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Machines_CachedDecisionSemantics`, `ContingencyTables_Machines_ScheduledCountSemantics`, `ContingencyTables_Machines_ScheduledResidualLaw`, `ContingencyTables_Sampling_AllSamplingAccuracy`, `ContingencyTables_Sampling_AllSmallBoolean`, `ContingencyTables_Sampling_AllSmallChain`, `ContingencyTables_Sampling_AllSmallOuter`, `ContingencyTables_Sampling_AllSmallRational`, `ContingencyTables_Sampling_CompiledResidualCorrection`, `ContingencyTables_Sampling_ExactPrefixFeasibility`, `ContingencyTables_Sampling_FirstPaperFullVariance`, `ContingencyTables_Sampling_FirstPaperIdealRejection`, `ContingencyTables_Sampling_FirstPaperPhysicalVariance`, `ContingencyTables_Sampling_FirstPaperRationalMixing`, `ContingencyTables_Sampling_FirstPaperSmallChain`, `ContingencyTables_Sampling_FirstPaperSmallMixing`, `ContingencyTables_Sampling_FirstPaperStationaryMass`, `ContingencyTables_Sampling_FirstPaperSuccessRatio`, `ContingencyTables_Sampling_FirstPaperTransversalVariance`, `ContingencyTables_Sampling_PhysicalContextVariance`, `ContingencyTables_Sampling_PhysicalGraphVertices`, `ContingencyTables_Sampling_PhysicalPrefixEnergies`, `ContingencyTables_Sampling_PhysicalRepairGraph`, `ContingencyTables_Sampling_PhysicalSmallEnergy`, `ContingencyTables_Sampling_SmallProfileEncoding`, `ContingencyTables_Sampling_SmallRepairWords`, `ContingencyTables_Transport_BalancedCompletionMass`, `ContingencyTables_Transport_ContextGraphEnergy`, `ContingencyTables_Transport_ContextGraphMembership`, `ContingencyTables_Transport_ListedKernelAccuracy`, `ContingencyTables_Transport_ListedScheduledSampler`, `ContingencyTables_Transport_ResidualBoxScale`, `ContingencyTables_Transport_WordContextVariance`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A009` and `OAIQ089A010` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound` and `OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual`; the proofs of `OAI.ContingencyTables.ExactGatePublic.failure`, `OAI.ContingencyTables.ExactGatePublic.table_prefix`, `OAI.ContingencyTables.ExactPublicCost.table_prefix`, `OAI.ContingencyTables.ExactPublicLaw.tableMass_limit`, `OAI.ContingencyTables.ExactPublicPrefix.prefix_correct`, `OAI.ContingencyTables.ExactTablePrefix.failure_bound`, `OAI.ContingencyTables.SmallGraphProfiles.exact_public_correction_bound`, `OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound`, `OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual` and `OAI.ContingencyTables.boundedSampling`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009
import Definitions.Def_OAIQ089A010

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextGraphMembership
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Context leaf vertices are actual balanced or single-defect states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

/-- Every box-valid transport leaf has exactly an allowed physical
small-graph pattern. No multi-defect vertex enters the local energy. -/
theorem leaf_pattern (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U l : ℕ)
    (hU : 1 ≤ U) (hlU : l ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (x : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (hx : x ∈ leafVertices _ (rootDisplay U l))
    (hbox : InBox (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))) x) :
    Pattern small B (assemble small s hs σ U e x) := by
  obtain ⟨q,_,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  have hi' := (Finset.mem_filter.mp hi).2
  have hb := assemble_bounded small s hs σ U hσ e _ hbox
  rw [assemble_removeOne] at hb ⊢
  apply pattern_after_one_removal small B U hU hB s hs
    (assemble small s hs σ U e (embedding _ (rootDisplay U l) q))
    (base_pair_total small s hs σ U l hlU hσ e q)
    (contextEquiv small s hs e U (.inr i)) _ hb
  rw [assemble_apply]
  exact hi'

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalGraphVertices
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite physical vertices containing every contextual transport leaf -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Every vertex used by the common conditional energy is an actual
bounded allowed small-graph profile after the physical coordinate map. -/
theorem context_vertex_mem (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (x : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (hx : x ∈ contextVertices U n)
    (hbox : InBox (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))) x) :
    assemble small s hs σ U e x ∈ vertices small B := by
  obtain ⟨l,_,hx⟩ := Finset.mem_biUnion.mp hx
  apply (mem_vertices_iff small B _).mpr
  refine ⟨?_,leaf_pattern small B s hs σ U l.val hU (Nat.le_of_lt_succ l.isLt) hB hσ e x hx hbox⟩
  intro a
  rw [hB _ _ a.1.property]
  exact assemble_bounded small s hs σ U hσ e x hbox a

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextGraphEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Contextual transport energy embeds in the actual physical graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The actual conditional variance energy uses physical allowed states
and ordinary exchange edges in its fixed row-major prefix only. -/
theorem context_graphEnergy_le (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (H : SmallProfile small → ℝ) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    integerGraphEnergy ((contextVertices U n).filter
      (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum))
      f (fun x => H (assemble small s hs σ U e x)) ≤
      physicalContextEnergy small B s σ (hardMarginal small B r c L) H := by
  dsimp only
  let V := (contextVertices U n).filter
    (fun x => InBox (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))) x ∧
      (∑ i, x i)=U+(widths (fun _ : Fin n => U)).sum)
  let E := (V ×ˢ V).filter (fun p => IntegerExchangeAdjacent p.1 p.2)
  let j : ((Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)×
      (Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)) →
      (SmallProfile small×SmallProfile small) :=
    fun p => (assemble small s hs σ U e p.1,assemble small s hs σ U e p.2)
  have hj : Function.Injective j := by
    intro a b he
    apply Prod.ext
    · exact assemble_injective small s hs σ U e (congrArg Prod.fst he)
    · exact assemble_injective small s hs σ U e (congrArg Prod.snd he)
  have hmem (x) (hx : x ∈ V) : assemble small s hs σ U e x ∈ vertices small B := by
    obtain ⟨hx,hbox,_⟩ := Finset.mem_filter.mp hx
    exact context_vertex_mem small B s hs σ U hU hB hσ e x hx hbox
  have hsub : E.image j ⊆ physicalContextEdges small B s σ := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq,hadj⟩ := Finset.mem_filter.mp hq
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hq
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hmem _ hx,hmem _ hy⟩,
      assemble_exchange_adjacent small s hs σ U e _ _ hadj,
      assemble_physicalPrefix small s hs σ U e _,assemble_physicalPrefix small s hs σ U e _⟩
  unfold integerGraphEnergy physicalContextEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  change (∑ p ∈ E, edgeTerm (hardMarginal small B r c L) H (j p)) ≤ _
  calc
    _ = ∑ p ∈ E.image j, edgeTerm (hardMarginal small B r c L) H p :=
      (Finset.sum_image (fun a _ b _ he => hj he)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
      mul_nonneg (le_min (hardMarginal_nonnegative small B r c L _)
        (hardMarginal_nonnegative small B r c L _)) (sq_nonneg _))

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalContextVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual physical context variance, including zero-mass contexts -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal FiniteExposureVariance
open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physicalContextEnergy_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (f H : SmallProfile small → ℝ) (hf : ∀ z,0 ≤ f z) :
    0 ≤ physicalContextEnergy small B s σ f H := by
  unfold physicalContextEnergy
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _))

/-- No positivity assumption is needed on the whole context. Its child
variance is bounded by its actual physical prefix exchange energy. -/
theorem physical_context_variance (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hU : 2 ≤ U) (hB : ∀ i j,small i j=true → B i j=U)
    (hlarge : ∀ i j,small i j=false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L),∀ i j,T.val.val i j ≤ B i j)
    (H : SmallProfile small → ℝ) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let z := fun j : Fin (U+1) => eliminate Ms f (childProfile U j.val)
    let μ := fun j : Fin (U+1) =>
      eliminate Ms (fun p => f p*H (assemble small s hs σ U e p)) (childProfile U j.val)/z j
    variance z μ ≤ ((U:ℝ)+1)^4*(2+2*n*((U:ℝ)+1)^2)*
      physicalContextEnergy small B s σ (hardMarginal small B r c L) H := by
  dsimp only
  let Ms := widths (fun _ : Fin n => U)
  let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
  let z := fun j : Fin (U+1) => eliminate Ms f (childProfile U j.val)
  have hz : ∀ j,0 ≤ z j := fun j => eliminate_nonnegative Ms f
    (contextHard_nonnegative small B r c L Ms _ _) (childProfile U j.val)
  have hc : 0 ≤ ((U:ℝ)+1)^4*(2+2*n*((U:ℝ)+1)^2) := by positivity
  by_cases hZ : 0 < ∑ j,z j
  · have hv := physical_child_variance small B r c L s hs σ U hU hB hlarge hσ e hcap
      (fun p => H (assemble small s hs σ U e p)) hZ
    have he := context_graphEnergy_le small B r c L s hs σ U (by omega) hB hσ e H
    dsimp only at hv he
    exact hv.trans (mul_le_mul_of_nonneg_left he hc)
  · have hzero : (∑ j,z j)=0 := le_antisymm (le_of_not_gt hZ) (Finset.sum_nonneg (fun j _ => hz j))
    have hzw := zero_mass_weights z hz hzero
    change variance z _ ≤ _
    unfold variance
    simp only [hzw,zero_mul,Finset.sum_const_zero]
    exact mul_nonneg hc (physicalContextEnergy_nonnegative small B s σ _ H
      (hardMarginal_nonnegative small B r c L))

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPrefixEnergies
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical prefix contexts use each exchange edge at most once -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physicalContextEdges_eq_filter (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (U : ℕ) (hB : ∀ i j,small i j=true → B i j=U)
    (τ : Earlier small s → Fin (U+1)) :
    physicalContextEdges small B s (prefixExtension small s U τ)=
      (physicalEdges small B).filter (fun p =>
        prefixValues small s U p.1=prefixValues small s U p.2 ∧ prefixValues small s U p.1=τ) := by
  ext p
  simp only [physicalContextEdges,physicalEdges,Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨⟨hx,hy⟩,ha,hpx,hpy⟩
    have hxb := (mem_vertices_iff small B p.1).mp hx
    have hyb := (mem_vertices_iff small B p.2).mp hy
    have hvx := (physicalPrefix_iff_values small s U τ p.1 (fun a => by
      simpa only [hB _ _ a.val.property] using hxb.1 (a.val,false))).mp hpx
    have hvy := (physicalPrefix_iff_values small s U τ p.2 (fun a => by
      simpa only [hB _ _ a.val.property] using hyb.1 (a.val,false))).mp hpy
    exact ⟨⟨⟨hx,hy⟩,ha⟩,hvx.trans hvy.symm,hvx⟩
  · rintro ⟨⟨⟨hx,hy⟩,ha⟩,hv,hτ⟩
    have hxb := (mem_vertices_iff small B p.1).mp hx
    have hyb := (mem_vertices_iff small B p.2).mp hy
    refine ⟨⟨hx,hy⟩,ha,?_,?_⟩
    · exact (physicalPrefix_iff_values small s U τ p.1 (fun a => by
        simpa only [hB _ _ a.val.property] using hxb.1 (a.val,false))).mpr hτ
    · exact (physicalPrefix_iff_values small s U τ p.2 (fun a => by
        simpa only [hB _ _ a.val.property] using hyb.1 (a.val,false))).mpr (hv.symm.trans hτ)

lemma sum_physicalContextEdgeTerms_le (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (U : ℕ) (hB : ∀ i j,small i j=true → B i j=U)
    (f H : SmallProfile small → ℝ) (hf : ∀ z,0 ≤ f z) :
    (∑ τ : Earlier small s → Fin (U+1), ∑ p ∈
      physicalContextEdges small B s (prefixExtension small s U τ), edgeTerm f H p) ≤
      ∑ p ∈ physicalEdges small B,edgeTerm f H p := by
  simp_rw [physicalContextEdges_eq_filter small B s U hB]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  by_cases h : prefixValues small s U p.1=prefixValues small s U p.2
  · simp only [h,true_and,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    exact le_rfl
  · simpa only [h,false_and,↓reduceIte,Finset.sum_const_zero,edgeTerm] using
      mul_nonneg (le_min (hf p.1) (hf p.2)) (sq_nonneg (H p.1-H p.2))

/-- At a fixed exposed cell, prefix contexts partition eligible physical
edges. Nonnegative exchange energy is therefore counted at most once. -/
theorem sum_physicalContextEnergy_le (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (U : ℕ) (hB : ∀ i j,small i j=true → B i j=U)
    (f H : SmallProfile small → ℝ) (hf : ∀ z,0 ≤ f z) :
    (∑ τ : Earlier small s → Fin (U+1),
      physicalContextEnergy small B s (prefixExtension small s U τ) f H) ≤
      physicalEnergy small B f H := by
  unfold physicalContextEnergy physicalEnergy
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (sum_physicalContextEdgeTerms_le small B s U hB f H hf) (by norm_num)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_WordContextVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical transport bounds the literal word-prefix child variance -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport
open FirstPaperContextTransport FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem word_context_variance (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hU : 2 ≤ U) (hB : ∀ i j,small i j=true → B i j=U)
    (hlarge : ∀ i j,small i j=false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables small r c (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L),∀ i j,T.val.val i j ≤ B i j)
    (k : Fin (Fintype.card (Cells small))) (τ : Fin k.val → Fin (U+1))
    (H : SmallProfile small → ℝ) :
    let w := wordWeight small B r c L U
    let G := wordObservable small U H
    let cw := fun j : Fin (U+1) => fibreWeight
      (fibreWeight w (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
    let σ := prefixExtension small (enumeration small k).val U (earlierWordChoices small U k τ)
    variance (fun j => ∑ a,cw j a) (fun j => mean (cw j) G) ≤
      ((U:ℝ)+1)^4*(2+2*((Fintype.card (Cells small)-k.val-1:ℕ):ℝ)*((U:ℝ)+1)^2)*
        physicalContextEnergy small B (enumeration small k).val σ (hardMarginal small B r c L) H := by
  dsimp only
  let s := (enumeration small k).val
  let hs := (enumeration small k).property
  let σ := prefixExtension small s U (earlierWordChoices small U k τ)
  let e := laterEnumeration small k
  let Ms := widths (fun _ : Fin (Fintype.card (Cells small)-k.val-1) => U)
  let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
  let cw := fun j : Fin (U+1) => fibreWeight
    (fibreWeight (wordWeight small B r c L U) (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
  have hz (j : Fin (U+1)) : (∑ a,cw j a)=eliminate Ms f (childProfile U j.val) := by
    exact (eliminate_context_eq_word_fibre small B U hB k τ j (hardMarginal small B r c L)).symm
  have hm (j : Fin (U+1)) : (∑ a,cw j a*wordObservable small U H a)=
      eliminate Ms (fun p => f p*H (assemble small s hs σ U e p)) (childProfile U j.val) := by
    have h := eliminate_context_eq_word_fibre small B U hB k τ j
      (fun x => hardMarginal small B r c L x*H x)
    calc
      _ = ∑ a,fibreWeight (fibreWeight
          (fun a => wordWeight small B r c L U a*wordObservable small U H a)
          (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a := by
        apply Finset.sum_congr rfl
        intro a _
        exact (double_fibreWeight_mul _ _ _ _ _ _ a).symm
      _ = _ := h.symm
  have hμ (j : Fin (U+1)) : mean (cw j) (wordObservable small U H)=
      eliminate Ms (fun p => f p*H (assemble small s hs σ U e p)) (childProfile U j.val)/
        eliminate Ms f (childProfile U j.val) := by
    unfold mean
    rw [hm,hz]
  change variance (fun j => ∑ a,cw j a) (fun j => mean (cw j) (wordObservable small U H)) ≤ _
  simp_rw [hz,hμ]
  exact physical_context_variance small B r c L s hs σ U hU hB hlarge
    (prefixExtension_bounded small s U (earlierWordChoices small U k τ)) e hcap H

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperTransversalVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global transversal variance for the literal first-paper profiles -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport
open FirstPaperContextTransport FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem firstPaper_word_context_variance (r : I → ℕ) (c : J → ℕ)
    (k : Fin (Fintype.card (Cells (paperSmall r c))))
    (τ : Fin k.val → Fin ((dimensionAllowance (I := I) (J := J))^20+1))
    (H : SmallProfile (paperSmall r c) → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) U
    let w := wordWeight small B r c (d^12) U
    let G := wordObservable small U H
    let cw := fun j : Fin (U+1) => fibreWeight
      (fibreWeight w (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
    let σ := prefixExtension small (enumeration small k).val U (earlierWordChoices small U k τ)
    variance (fun j => ∑ a,cw j a) (fun j => mean (cw j) G) ≤
      4*d*((U:ℝ)+1)^6*
        physicalContextEnergy small B (enumeration small k).val σ (hardMarginal small B r c (d^12)) H := by
  dsimp only
  have hd : 2 ≤ dimensionAllowance (I := I) (J := J) := by unfold dimensionAllowance; omega
  have hU : 2 ≤ (dimensionAllowance (I := I) (J := J))^20 :=
    hd.trans (Nat.le_self_pow (by decide) _)
  have hv := word_context_variance (paperSmall r c)
    (paperCapacity (paperSmall r c) r (dimensionAllowance (I := I) (J := J))
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20))
    r c _ _ hU
    (fun i j hij => by simp only [paperCapacity,hij,ite_true, if_true])
    (fun i j hij => by simp only [paperCapacity,hij,Bool.false_eq_true,ite_false]; omega)
    (paper_residual_capacity r c _ _ _ dimension_le_allowance) k τ H
  dsimp only at hv
  refine hv.trans (mul_le_mul_of_nonneg_right
    (exposure_coefficient _ _ _ (by omega)
      (later_card_le_allowance _ _ (laterEnumeration (paperSmall r c) k))) ?_)
  exact physicalContextEnergy_nonnegative _ _ _ _ _ H (hardMarginal_nonnegative _ _ r c _)

lemma firstPaper_prefixContribution_le (r : I → ℕ) (c : J → ℕ)
    (k : Fin (Fintype.card (Cells (paperSmall r c))))
    (H : SmallProfile (paperSmall r c) → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) U
    prefixContribution (wordWeight small B r c (d^12) U) (wordObservable small U H) k ≤
      4*d*((U:ℝ)+1)^6*physicalEnergy small B (hardMarginal small B r c (d^12)) H := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let small := paperSmall r c
  let B := paperCapacity small r d (d^12) U
  let K : ℝ := 4*d*((U:ℝ)+1)^6
  let E := fun τ : Earlier small (enumeration small k).val → Fin (U+1) =>
    physicalContextEnergy small B (enumeration small k).val
      (prefixExtension small (enumeration small k).val U τ) (hardMarginal small B r c (d^12)) H
  have hs : (∑ τ : Fin k.val → Fin (U+1),E (earlierWordChoices small U k τ))=∑ τ,E τ := by
    apply Fintype.sum_equiv (earlierWordChoices small U k)
    intro τ
    rfl
  calc
    _ ≤ ∑ τ : Fin k.val → Fin (U+1),K*E (earlierWordChoices small U k τ) := by
      unfold prefixContribution partitionContribution
      apply Finset.sum_le_sum
      intro τ _
      exact firstPaper_word_context_variance r c k τ H
    _ = K*∑ τ,E τ := by rw [← Finset.mul_sum,hs]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_physicalContextEnergy_le small B (enumeration small k).val U
        (fun i j hij => by simp only [B,paperCapacity,hij,ite_true, if_true])
        (hardMarginal small B r c (d^12)) H (hardMarginal_nonnegative _ _ _ _ _)) (by positivity)

/-- Actual first-paper balanced choices, weighted by every physical
large completion, satisfy the paper's global transversal variance bound. -/
theorem firstPaper_transversal_variance (r : I → ℕ) (c : J → ℕ)
    (H : SmallProfile (paperSmall r c) → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) U
    variance (wordWeight small B r c (d^12) U) (wordObservable small U H) ≤
      4*(d:ℝ)^2*((U:ℝ)+1)^6*physicalEnergy small B (hardMarginal small B r c (d^12)) H := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let small := paperSmall r c
  let B := paperCapacity small r d (d^12) U
  let E := physicalEnergy small B (hardMarginal small B r c (d^12)) H
  have hq : Fintype.card (Cells small) ≤ d := (small_card_le_dimension small).trans dimension_le_allowance
  have hE : 0 ≤ E := graphEnergy_nonnegative (vertices small B) (hardMarginal small B r c (d^12)) H
    (hardMarginal_nonnegative small B r c (d^12))
  exact variance_le_polynomial_budget (wordWeight small B r c (d^12) U) (wordObservable small U H)
    (fun a => hardMarginal_nonnegative _ _ _ _ _ _) d U hq E hE
    (fun k => firstPaper_prefixContribution_le r c k H)

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual positive defects repair to the physical transversal words -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem repairWord_weight (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
    hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val) ≤
      wordWeight (firstPaperSmall r c U) B r c L U (repairWord r c U L B hB z) := by
  unfold wordWeight
  rw [repairWord_profile]
  exact physical_repair_weight_le r c U L B hB (naturalProfile z.val) (naturalProfile_bounded z.val)
    _ _ (defectLabels _ B r c L z).1.property (defectLabels _ B r c L z).2.property
    (defectLabels_spec _ B r c L z) hcap z.property.2

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRepairGraph
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small graph contains its exchanges and designated repairs -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem actual_repair_energy_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    (∑ z : PositiveDefects (firstPaperSmall r c U) B r c L,
      hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val)*
        (H (naturalProfile z.val)-wordObservable (firstPaperSmall r c U) U H (repairWord r c U L B hB z))^2) ≤
      fullEnergy r c U L B hB H := by
  let x := fun z : PositiveDefects (firstPaperSmall r c U) B r c L => naturalProfile z.val
  let y := fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
    rawChoice (firstPaperSmall r c U) U (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))
  have hx : Function.Injective x := by
    intro a b he
    apply Subtype.ext
    exact naturalProfile_injective _ B he
  have hxy : ∀ a b,x a≠y b := by
    intro a b he
    have hb := rawChoice_balanced (firstPaperSmall r c U) B U hB
      (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB b))
    have hdef := a.property.1
    change SingleDefect _ B (x a) at hdef
    rw [he] at hdef
    exact balanced_not_defect _ B _ hb hdef
  have he := repair_energy_le (fullEdges r c U L B hB)
    (hardMarginal (firstPaperSmall r c U) B r c L) H (hardMarginal_nonnegative _ _ _ _ _) x y hx hxy
    (fun z => Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)))
    (fun z => Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)))
  have hterm (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
      pairTerm (hardMarginal (firstPaperSmall r c U) B r c L) H (x z,y z)=
        hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val)*
          (H (naturalProfile z.val)-wordObservable (firstPaperSmall r c U) U H (repairWord r c U L B hB z))^2 := by
    change min (hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val))
      (wordWeight (firstPaperSmall r c U) B r c L U (repairWord r c U L B hB z)) *
      (H (naturalProfile z.val)-wordObservable (firstPaperSmall r c U) U H
        (repairWord r c U L B hB z))^2 = _
    rw [min_eq_left (repairWord_weight r c U L B hB hcap z)]
  simp_rw [hterm] at he
  exact he

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperFullVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source Poincare bound for the full literal physical small graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The literal physical encoding consists of the balanced transversal
words and the positive single-defect profiles. Zero-weight transversal
words may be retained; they contribute zero to both variance and energy. -/
theorem firstPaper_full_variance (r : I → ℕ) (c : J → ℕ)
    (H : SmallProfile (paperSmall r c) → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let L := d^12
    let small := paperSmall r c
    let B := paperCapacity small r d L U
    let hB := fun i j (hij : small i j=true) => show B i j=U by simp only [B,paperCapacity,hij,ite_true, if_true]
    let w := wordWeight small B r c L U
    let v := fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val)
    let G := wordObservable small U H
    let K := fun z : PositiveDefects small B r c L => H (naturalProfile z.val)
    variance (Sum.elim w v) (Sum.elim G K) ≤ 770*(d:ℝ)^4*(U:ℝ)^6*fullEnergy r c U L B hB H := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let small := paperSmall r c
  let B := paperCapacity small r d L U
  have hB : ∀ i j,small i j=true → B i j=U := fun i j hij => by simp only [B,paperCapacity,hij,ite_true, if_true]
  have hcap : ∀ T : ResidualTables small r c (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L),∀ i j,T.val.val i j ≤ B i j :=
    paper_residual_capacity r c d L U dimension_le_allowance
  let E := fullEnergy r c U L B hB H
  have hE : 0 ≤ E := fullEnergy_nonnegative r c U L B hB H
  have hd : 1 ≤ d := by dsimp only [d]; unfold dimensionAllowance; omega
  have hU : 1 ≤ U := hd.trans (Nat.le_self_pow (by decide) _)
  have hq : Fintype.card (Cells small) ≤ d := (small_card_le_dimension small).trans dimension_le_allowance
  have hT : Fintype.card (Cells small×Cells small) ≤ d^2 := by
    simpa only [Fintype.card_prod,pow_two] using Nat.mul_le_mul hq hq
  have hvar : variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      4*(d:ℝ)^2*((U:ℝ)+1)^6*E := by
    exact (firstPaper_transversal_variance r c H).trans
      (mul_le_mul_of_nonneg_left (physicalEnergy_le_full r c U L B hB H) (by positivity))
  exact variance_repaired_graph_budget (wordWeight small B r c L U)
    (fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val))
    (wordObservable small U H) (fun z => H (naturalProfile z.val))
    (repairWord r c U L B hB) (defectLabels small B r c L)
    (fun a => hardMarginal_nonnegative _ _ _ _ _ _) (fun z => le_of_lt z.property.2)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB)
    d U hd hU hT E hE hvar (actual_repair_energy_le r c U L B hB hcap H)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileEncoding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The variance encoding retains exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The completed graph variance proof concerns the literal bounded
physical profiles; the auxiliary encoding drops only zero-mass defects. -/
theorem encoding_variance_eq (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (H : SmallProfile small → ℝ) :
    variance
      (Sum.elim (wordWeight small B r c L U)
        (fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val)))
      (Sum.elim (wordObservable small U H) (fun z => H (naturalProfile z.val)))=
      variance (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
        (fun z => H (naturalProfile z.val)) := by
  convert variance_support_embedding (encodeProfile small B r c L U hB)
    (encodeProfile_injective small B r c L U hB)
    (fun z => hardMarginal small B r c L (naturalProfile z.val))
    (outside_encoding_weight_zero small B r c L U hB)
    (fun z => H (naturalProfile z.val)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1 <;> funext x <;> cases x <;> rfl

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Poincare inequality on the actual feasible small states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts SmallContextEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Zero-weight bounded profiles can be removed before applying the
full graph estimate, so this quantifies over every observable on the
actual positive-weight state space. -/
theorem firstPaper_physical_variance (r : I → ℕ) (c : J → ℕ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let L := d^12
    let small := paperSmall r c
    let B := paperCapacity small r d L U
    let hB := fun i j (hij : small i j=true) => show B i j=U by simp only [B,paperCapacity,hij,ite_true, if_true]
    ∀ H : PhysicalStates small B r c L → ℝ,
      variance (fun z => hardMarginal small B r c L (physicalProfile small B r c L z)) H ≤
        770*(d:ℝ)^4*(U:ℝ)^6*
          fullEnergy r c U L B hB (physicalExtension small B r c L H) := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let small := paperSmall r c
  let B := paperCapacity small r d L U
  have hB : ∀ i j,small i j=true → B i j=U := fun i j hij => by simp only [B,paperCapacity,hij,ite_true, if_true]
  intro H
  let G := physicalExtension small B r c L H
  have hext : ∀ z : PhysicalStates small B r c L,G (naturalProfile z.val.val)=H z :=
    physicalExtension_at small B r c L H
  have hv := variance_positive_support
    (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
    (fun z => G (naturalProfile z.val)) (fun _ => hardMarginal_nonnegative _ _ _ _ _ _)
  have hv' : variance (fun z : PhysicalStates small B r c L =>
      hardMarginal small B r c L (physicalProfile small B r c L z)) H =
      variance (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
        (fun z => G (naturalProfile z.val)) := by
    simpa only [physicalProfile,hext] using hv
  rw [hv',← encoding_variance_eq small B r c L U hB G]
  exact firstPaper_full_variance r c G

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalSmallEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact energy on the positive physical graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts SmallContextEnumeration RowMajorEnumeration
open IntegerWeightedTransport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Deleting zero-weight vertices preserves the exact unnormalized energy,
not merely an inequality for a restricted class of observables. -/
theorem fullEnergy_physical_eq (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (H : PhysicalStates (firstPaperSmall r c U) B r c L → ℝ) :
    fullEnergy r c U L B hB (physicalExtension _ B r c L H)=
      (∑ x,∑ y,if physicalAdjacent r c U L B hB x y then
        min (hardMarginal (firstPaperSmall r c U) B r c L (physicalProfile _ B r c L x))
          (hardMarginal (firstPaperSmall r c U) B r c L (physicalProfile _ B r c L y))*
          (H x-H y)^2 else 0)/2 := by
  have he := symmetricEnergy_restrict_observable (fullEdges r c U L B hB)
    (hardMarginal (firstPaperSmall r c U) B r c L) (physicalExtension _ B r c L H)
    (hardMarginal_nonnegative _ B r c L) (physicalProfile _ B r c L)
    (physicalProfile_injective _ B r c L) (by
      intro p hp
      have hv := fullEdges_vertices r c U L B hB p hp
      constructor
      · intro h
        exact positive_vertex_is_physical _ B r c L p.1 hv.1
          (lt_of_le_of_ne (hardMarginal_nonnegative _ B r c L p.1) (Ne.symm h))
      · intro h
        exact positive_vertex_is_physical _ B r c L p.2 hv.2
          (lt_of_le_of_ne (hardMarginal_nonnegative _ B r c L p.2) (Ne.symm h))) H (physicalExtension_at _ B r c L H)

  convert he using 1
  · rfl
  · apply congrArg (fun a : ℝ => a/2)
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    unfold physicalAdjacent
    split_ifs <;> rfl

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallChain
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal first-paper completion chain has the stated Poincare bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma paperSmallChain_energy_lower (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (H : PaperStates r c → ℝ) :
    smallProposal (dimensionAllowance (I := I) (J := J))/(2*(∑ z,stateWeight r c z))*
      stateGraphEnergy r c H ≤ (paperSmallChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let B := stateCapacity r c
  let R := referenceRows r c U L B i₀
  let P := referenceColumns r c U L B j₀
  have hcap := physical_paper_capacity (paperSmall r c) r c d L U dimension_le_allowance
  have hw (z : PaperStates r c) : stateWeight r c z=(blockCount R P z:ℝ) :=
    physical_weight_reference_block r c U L B i₀ j₀ z (hcap z)
  have hh := completionChain_energy_lower R P
    (fun z => reference_totals r c U L B i₀ j₀ z (hcap z))
    (physicalAdjacent r c U L B (stateCapacity_small r c))
    (physicalAdjacent_symmetric r c U L B (stateCapacity_small r c))
    (smallProposal d) ((smallProposal_bounds d (by dsimp [d,dimensionAllowance]; omega)).1.le)
    (5*d^2+1)
    (physicalAdjacent_degree_allowance r c U L B (stateCapacity_small r c))
    (smallProposal_degree d (by dsimp [d,dimensionAllowance]; omega))
    (reference_edge_acceptance r c U B (stateCapacity_small r c) i₀ j₀ hcap) H
  have hE := fullEnergy_physical_eq r c U L B (stateCapacity_small r c) H
  change stateGraphEnergy r c H=(∑ x,∑ y,
    if physicalAdjacent r c U L B (stateCapacity_small r c) x y then
      min (stateWeight r c x) (stateWeight r c y)*(H x-H y)^2 else 0)/2 at hE
  rw [hE]
  simp_rw [hw]
  exact hh

/-- Every observable on the actual positive completion states satisfies
 the source's `d^160` bound, with the actual dyadic proposal probability. -/
theorem paperSmallChain_poincare (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (H : PaperStates r c → ℝ) :
    (paperSmallChain r c i₀ j₀).variance H ≤
      (dimensionAllowance (I := I) (J := J):ℝ)^160*(paperSmallChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := 770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6
  have hv : variance (stateWeight r c) H ≤ K*stateGraphEnergy r c H :=
    firstPaper_physical_variance r c H
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hb := smallProposal_bounds d (by dsimp [d,dimensionAllowance]; omega)
  have hp := chain_poincare_of_weighted_graph (paperSmallChain r c i₀ j₀)
    (stateWeight r c) H (stateWeight_positive r c) (paperSmallChain_pi r c i₀ j₀)
    (stateGraphEnergy r c H) K (smallProposal d) hK hb.1 hv
    (paperSmallChain_energy_lower r c i₀ j₀ H)
  exact hp.trans (mul_le_mul_of_nonneg_right
    (smallProposal_poincare_budget d (reference_dimension_ge_fourteen r c _ i₀ j₀))
    ((paperSmallChain r c i₀ j₀).energy_nonneg H))

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallMixing
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Minimum mass and mixing of the actual small chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem paperSmallChain_point_mixing (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (n : ℕ) (x y : PaperStates r c) :
    let C := paperSmallChain r c i₀ j₀
    |C.iterate n (C.pointDensity y) x-1| ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
        Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160) := by
  have hd : (1:ℝ) ≤ dimensionAllowance (I := I) (J := J) := by
    exact_mod_cast (show 1 ≤ dimensionAllowance (I := I) (J := J) by
      unfold dimensionAllowance
      omega)
  have h := (paperSmallChain r c i₀ j₀).point_mixing_exp
    ((dimensionAllowance (I := I) (J := J):ℝ)^160)
    (1/(((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))))
    (one_le_pow₀ hd) (by positivity) (paperSmallChain_pi_lower r c i₀ j₀)
    (paperSmallChain_poincare r c i₀ j₀) n x y
  simpa only [one_div, div_eq_mul_inv, one_mul, inv_inv, mul_comm] using h

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperRationalMixing
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing in total variation for the actual rational small-walk law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- This is the rational finite-walk distribution, rather than a bound
only on real observables of an abstract chain. -/
theorem smallWalkLaw_variation (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) (n : ℕ) :
    (variation (smallWalkLaw r c i₀ j₀ x n) (smallStationaryLaw r c i₀ j₀):ℝ) ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
        Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160) := by
  let C := paperSmallChain r c i₀ j₀
  let δ := ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
    Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160)
  have hpoint (y : PaperStates r c) : |(C.kernel.power n).P x y-C.π y| ≤ C.π y*δ := by
    have h := paperSmallChain_point_mixing r c i₀ j₀ n x y
    change |C.iterate n (C.pointDensity y) x-1| ≤ δ at h
    rw [←C.kernel_power_density] at h
    calc
      _ = C.π y*|(C.kernel.power n).P x y/C.π y-1| := by
        calc
          _ = |C.π y*((C.kernel.power n).P x y/C.π y-1)| := by
            congr 1
            field_simp [(C.positive y).ne']
          _ = _ := by rw [abs_mul,abs_of_pos (C.positive y)]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (C.positive y).le
  have hsum := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hpoint y)
  rw [←Finset.sum_mul,C.normalized,one_mul] at hsum
  unfold variation
  simp only [Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat,
    smallWalkLaw_cast,smallStationaryLaw,smallStationaryRat_cast]
  change (∑ y,|(C.kernel.power n).P x y-C.π y|)/2 ≤ δ
  have hd : 0 ≤ δ := by dsimp only [δ]; positivity
  linarith

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperStationaryMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completion-retaining repair bounds the stationary normalizer -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physical_mass_eq_words_defects (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
      (physicalProfile small B r c L z))=
      (∑ a,wordWeight small B r c L U a)+
      ∑ z : PositiveDefects small B r c L,hardMarginal small B r c L (naturalProfile z.val) := by
  rw [physical_mass_eq_profiles]
  have he := Fintype.sum_of_injective (encodeProfile small B r c L U hB)
    (encodeProfile_injective small B r c L U hB)
    (fun z => hardMarginal small B r c L (naturalProfile (encodeProfile small B r c L U hB z).val))
    (fun z => hardMarginal small B r c L (naturalProfile z.val))
    (outside_encoding_weight_zero small B r c L U hB) (fun _ => rfl)
  rw [← he,Fintype.sum_sum_type]
  rfl

/-- The repair preserves all completions and has at most one preimage per
ordered defect label. Thus defect mass costs at most |S| squared. -/
lemma defect_mass_le_words (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j) :
    (∑ z : PositiveDefects (firstPaperSmall r c U) B r c L,
      hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val)) ≤
      (Fintype.card (Cells (firstPaperSmall r c U)×Cells (firstPaperSmall r c U)):ℝ)*
        ∑ a,wordWeight (firstPaperSmall r c U) B r c L U a := by
  have h := repair_center_mass (wordWeight (firstPaperSmall r c U) B r c L U)
    (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
      hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val))
    (fun _ => (1:ℝ)) (repairWord r c U L B hB) (defectLabels _ B r c L)
    (fun _ => hardMarginal_nonnegative _ _ _ _ _ _)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB) 0
  simpa only [sub_zero,one_pow,mul_one] using h

/-- The normalizer of the actual small chain is bounded by balanced
completion mass times the manuscript's polynomial defect factor. -/
theorem state_mass_le_balanced (r : I → ℕ) (c : J → ℕ) :
    (∑ z,stateWeight r c z) ≤
      (1+(dimensionAllowance (I := I) (J := J):ℝ)^2)*
        ∑ a,wordWeight (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := I) (J := J))^12)
          ((dimensionAllowance (I := I) (J := J))^20) a := by
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let small := paperSmall r c
  let B := stateCapacity r c
  have hB : ∀ i j,small i j=true → B i j=U := stateCapacity_small r c
  have hcap := paper_residual_capacity r c d L U dimension_le_allowance
  have hmass := physical_mass_eq_words_defects small B r c L U hB
  have hdef := defect_mass_le_words r c U L B hB hcap
  have hq : Fintype.card (Cells small) ≤ d :=
    (small_card_le_dimension small).trans dimension_le_allowance
  have hT : (Fintype.card (Cells small×Cells small):ℝ) ≤ (d:ℝ)^2 := by
    exact_mod_cast (show Fintype.card (Cells small×Cells small) ≤ d^2 by
      simpa only [Fintype.card_prod,pow_two] using Nat.mul_le_mul hq hq)
  have hw : 0 ≤ ∑ a,wordWeight small B r c L U a :=
    Finset.sum_nonneg (fun _ _ => hardMarginal_nonnegative _ _ _ _ _ _)
  have hm := mul_le_mul_of_nonneg_right hT hw
  change (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
    (physicalProfile small B r c L z)) ≤ (1+(d:ℝ)^2)*∑ a,wordWeight small B r c L U a
  rw [hmass]
  linarith

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedCompletionMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Balanced profile/completion pairs inject into padded tables -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

variable [LinearOrder I] [LinearOrder J]

lemma word_mass_eq_balancedJoint_card (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    (∑ a,wordWeight small B r c L U a)=(Fintype.card (BalancedJoint small B r c L U):ℝ) := by
  rw [Fintype.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact hardMarginal_eq_fibre_card small B r c L _ (rawChoice_bounded small B U hB _)

/-- This inequality retains all large-cell multiplicities and counts every
balanced word exactly once. -/
theorem word_mass_le_padded_count (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    (∑ a,wordWeight small B r c L U a) ≤
      (Fintype.card (Table (fun i => r i+rowLargeCount small i*L)
        (fun j => c j+columnLargeCount small j*L)):ℝ) := by
  rw [word_mass_eq_balancedJoint_card small B r c L U hB]
  exact_mod_cast Fintype.card_le_of_injective _ (balancedJointTable_injective small B r c L U hB)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSuccessRatio
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stationary successful-pair ratio of the first sampler -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal PhysicalCompletionFibres PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The numerator counts original tables through the padding bijection;
the denominator counts all actual small-state/completion pairs. -/
theorem state_mass_le_original_count (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i,r i=∑ j,c j) (hd : 14 ≤ dimensionAllowance (I := I) (J := J)) :
    (∑ z,stateWeight r c z) ≤
      2*(1+(dimensionAllowance (I := I) (J := J):ℝ)^2)*(Fintype.card (Table r c):ℝ) := by
  have h₁ := state_mass_le_balanced r c
  have h₂ := word_mass_le_padded_count (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)
    (stateCapacity_small r c)
  have h₃ := paper_padded_count_le r c htotal hd
  have h := h₁.trans (mul_le_mul_of_nonneg_left (h₂.trans h₃) (by positivity))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem stationary_success_ratio (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (htotal : ∑ i,r i=∑ j,c j) (hd : 14 ≤ dimensionAllowance (I := I) (J := J)) :
    1/(2*(1+(dimensionAllowance (I := I) (J := J):ℝ)^2)) ≤
      (Fintype.card (Table r c):ℝ)/(∑ z,stateWeight r c z) := by
  have hm : 0 < ∑ z,stateWeight r c z :=
    Finset.sum_pos (fun z _ => stateWeight_positive r c z) Finset.univ_nonempty
  apply (div_le_div_iff₀ (by positivity) hm).mpr
  simpa only [one_mul,mul_comm] using state_mass_le_original_count r c htotal hd

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedDecisionSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cached completions implement the same outer-profile transition -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

def encodedShortStep (h : ℕ) (x : PaperStates r c) (word : Fin s → Bool) : ShortStep :=
  (((stateCodeData r c e x,d^12),(d,h)),List.ofFn word)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperIdealRejection
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual stationary outer rejection law and its polynomial trial budget -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

/-- No approximate draw is conditioned on success. Ideal complete trials
have fallback error exactly bounded by their geometric failure tail. -/
theorem ideal_outer_variation [Nonempty (PaperStates r c)] [Nonempty (Table r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (htotal : ∑ i,r i=∑ j,c j) (fallback : Table r c) (n : ℕ) :
    (variation (retryLaw (stationaryJointLaw r c i₀ j₀) (stateTrial r c) fallback n)
      (uniformLaw (α := Table r c)):ℝ) ≤
      Real.exp (-(n:ℝ)/(2*(1+(dimensionAllowance (I := I) (J := J):ℝ)^2))) := by
  rw [stationaryJointLaw_uniform]
  apply uniform_partial_retry_exp (StateJointSuccess r c) (originalStateSuccessEquiv r c)
    fallback n (2*(1+(dimensionAllowance (I := I) (J := J):ℝ)^2))
  rw [paperStateJoint_card]
  exact stationary_success_ratio r c htotal (reference_dimension_fourteen r c _ i₀ j₀)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedKernelAccuracy
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing with the computed, canonically initialized completion draw -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits CompletionTranslation CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none

variable (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
  (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
variable (hCheeger : PublishedInputs.FiniteCheeger
  (GridBoundary.Grid (I := Fin (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
    (4*(dimensionAllowance (I := Fin m) (J := Fin n))^8)))

include hPL hCheeger


variable [Nonempty (PaperStates r c)]

/-- The implemented draw incurs one dyadic error per transition and
one more for the independent terminal completion. -/
theorem listedJointLaw_variation (x : PaperStates r c) (steps : ℕ) :
    (variation (listedJointLaw r c hr hc b h hb x steps) (stationaryJointLaw r c i₀ j₀):ℝ) ≤
      ((steps:ℝ)+1)/(2:ℝ)^h+
        ((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(steps:ℝ)/(d:ℝ)^160) := by
  have hj := variation_dependentJoint_uniform
    (walkLaw (listedSmallKernel r c hr hc b h hb) x steps) (smallStationaryLaw r c i₀ j₀)
    (listedFibreLaw r c hr hc b h hb) (fun z => uniformLaw (α := PaperFibre r c z)) (1/(2:ℚ)^h)
    (listedFibreLaw_variation r c hr hc b h hb hPL hCheeger)
  have hw := walkLaw_variation (listedSmallKernel r c hr hc b h hb)
    (smallTransitionLaw r c i₀ j₀) (1/(2:ℚ)^h)
    (listedSmallKernel_variation r c hr hc b h hb hPL hCheeger) x steps
  have ht := variation_triangle
    (walkLaw (listedSmallKernel r c hr hc b h hb) x steps)
    (smallWalkLaw r c i₀ j₀ x steps) (smallStationaryLaw r c i₀ j₀)
  have he : variation (listedJointLaw r c hr hc b h hb x steps)
      (stationaryJointLaw r c i₀ j₀) ≤
      ((steps:ℚ)+1)*(1/(2:ℚ)^h)+
        variation (smallWalkLaw r c i₀ j₀ x steps) (smallStationaryLaw r c i₀ j₀) := by
    change variation (walkLaw (listedSmallKernel r c hr hc b h hb) x steps)
      (smallWalkLaw r c i₀ j₀ x steps) ≤ _ at hw
    change variation (listedJointLaw r c hr hc b h hb x steps)
      (stationaryJointLaw r c i₀ j₀) ≤ _ at hj
    linarith
  have heR := (Rat.cast_le (K := ℝ)).mpr he
  simp only [Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat,mul_one_div] at heR
  exact heR.trans (add_le_add_right (smallWalkLaw_variation r c i₀ j₀ x steps) _)

/-- This is the manuscript's three-term bound for the actual finite
completion subroutine, ideal mixing, and first-success fallback. -/
theorem listedOuterLaw_variation [Nonempty (Table r c)]
    (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c) :
    (variation (retryLaw (listedJointLaw r c hr hc b h hb x n)
      (stateTrial r c) z₀ J₀) (uniformLaw (α := Table r c)):ℝ) ≤
      Real.exp (-(J₀:ℝ)/(2*(1+(d:ℝ)^2)))+
      (J₀:ℝ)*(((n:ℝ)+1)/(2:ℝ)^h+
        ((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(n:ℝ)/(d:ℝ)^160)) := by
  have hretry := retryLaw_variation (listedJointLaw r c hr hc b h hb x n)
    (stationaryJointLaw r c i₀ j₀) (stateTrial r c) z₀ J₀
  have ht := variation_triangle
    (retryLaw (listedJointLaw r c hr hc b h hb x n) (stateTrial r c) z₀ J₀)
    (retryLaw (stationaryJointLaw r c i₀ j₀) (stateTrial r c) z₀ J₀) (uniformLaw (α := Table r c))
  have hrR := (Rat.cast_le (K := ℝ)).mpr hretry
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_natCast] at hrR htR
  have hj := mul_le_mul_of_nonneg_left
    (listedJointLaw_variation r c hr hc b h hb hPL hCheeger x n)
    (show (0:ℝ) ≤ J₀ by positivity)
  have hi := ideal_outer_variation r c i₀ j₀ htotal z₀ J₀
  linarith


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallChain
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-state walk when no dense completion remains

Every retained completion then has weight one. The same local graph is
sampled by accepting every valid proposal; no reference row is chosen.
-/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts CommonBasesFPRAS FiniteExposureVariance

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
local notation "d" => dimensionAllowance (I := I) (J := J)

local notation "Adj" => physicalAdjacent r c (d^20) (d^12) (stateCapacity r c) (stateCapacity_small r c)

local instance instDecidableEqPaperStates_r104b66_1 : DecidableEq (PaperStates r c) := Classical.decEq _
omit [Nonempty (PaperStates r c)] in
lemma stateGraphEnergy_allSmall (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (H : PaperStates r c → ℝ) :
    stateGraphEnergy r c H=(∑ x,∑ y,if Adj x y then (H x-H y)^2 else 0)/2 := by
  have he := fullEnergy_physical_eq r c (d^20) (d^12) (stateCapacity r c) (stateCapacity_small r c) H
  change stateGraphEnergy r c H=(∑ x,∑ y,if Adj x y then
    min (stateWeight r c x) (stateWeight r c y)*(H x-H y)^2 else 0)/2 at he
  simpa only [stateWeight_allSmall r c hsmall,min_self,one_mul] using he

lemma unitSmallChain_energy_lower
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (H : PaperStates r c → ℝ) :
    (smallProposal d)/(2*(∑ z,stateWeight r c z))*stateGraphEnergy r c H ≤
      (unitSmallChain r c).energy H := by
  have hsum : (∑ z,stateWeight r c z)=(Fintype.card (PaperStates r c):ℝ) := by
    simp only [stateWeight_allSmall r c hsmall,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have hi := unitSmallChain_energy r c H
  rw [←stateGraphEnergy_allSmall r c hsmall H] at hi
  rw [hsum]
  calc
    _ = ((smallProposal d/(Fintype.card (PaperStates r c):ℝ))*stateGraphEnergy r c H)/2 := by ring
    _ = (unitSmallChain r c).energy H/2 := by rw [hi]
    _ ≤ (unitSmallChain r c).energy H := by linarith [(unitSmallChain r c).energy_nonneg H]

/-- The full graph bound includes the empty large rectangle. -/
theorem unitSmallChain_poincare [Nonempty I] [Nonempty J]
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (H : PaperStates r c → ℝ) :
    (unitSmallChain r c).variance H ≤ (d:ℝ)^160*(unitSmallChain r c).energy H := by
  let K : ℝ := 770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6
  have hβ := (smallProposal_bounds d (by unfold dimensionAllowance; omega)).1
  have hv : variance (stateWeight r c) H ≤ K*stateGraphEnergy r c H :=
    firstPaper_physical_variance r c H
  have hp := chain_poincare_of_weighted_graph (unitSmallChain r c) (stateWeight r c) H
    (stateWeight_positive r c) (unitSmallChain_pi_weight r c hsmall)
    (stateGraphEnergy r c H) K (smallProposal d) (by dsimp [K]; positivity) hβ hv
    (unitSmallChain_energy_lower r c hsmall H)
  exact hp.trans (mul_le_mul_of_nonneg_right
    (smallProposal_poincare_budget d allowance_fourteen) ((unitSmallChain r c).energy_nonneg H))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallRational
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rational walk on an empty large rectangle -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)

variable [Nonempty (PaperStates r c)]

attribute [local instance] OAI.ContingencyTables.SmallGraphProfiles.instDecidableEqPaperStates_1
theorem unitSmallWalk_variation [Nonempty I] [Nonempty J]
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (x : PaperStates r c) (n : ℕ) :
    (variation (walkLaw (unitSmallStep r c) x n)
      (uniformLaw (α := PaperStates r c)):ℝ) ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(n:ℝ)/(d:ℝ)^160) := by
  have hd : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by unfold dimensionAllowance; omega)
  have hm := (unitSmallChain r c).point_mixing_exp ((d:ℝ)^160)
    (1/(((stateBound r c+1:ℕ):ℝ)^(2*d))) (one_le_pow₀ hd) (by positivity)
    (unitSmallChain_pi_lower r c hsmall) (unitSmallChain_poincare r c hsmall) n x
  apply rationalWalk_variation (unitSmallStep r c) (unitSmallChain r c)
    (unitSmallStep_cast r c) (uniformLaw (α := PaperStates r c))
    (fun y => ?_) x n _ (by positivity)
  · simpa only [one_div,div_eq_mul_inv,one_mul,inv_inv,mul_comm] using hm
  · simp only [uniformLaw,uniformMass,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,
      unitSmallChain_pi]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallBoolean
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boolean implementation when all cells are retained -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits CompletionTranslation CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "s" => smallProposalBits (I := I) (J := J)

attribute [local instance] OAI.ContingencyTables.SmallGraphProfiles.instDecidableEqPaperStates_2
theorem unitJointDraw_variation [Nonempty I] [Nonempty J] [Nonempty (PaperStates r c)]
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n : ℕ) :
    (variation (mapLaw (uniformLaw (α := Fin (n*s) → Bool))
      (unitJointDraw r c fallback x n)) (uniformLaw (α := PaperStateJoint r c)):ℝ) ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
        Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160) := by
  rw [unitJointDraw_law]
  have hv := variation_map (walkLaw (unitSmallStep r c) x n)
    (uniformLaw (α := PaperStates r c)) (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c))
  rw [uniform_singleton_joint r c hsmall fallback] at hv
  exact ((Rat.cast_le (K := ℝ)).mpr hv).trans (unitSmallWalk_variation r c hsmall x n)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallOuter
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete finite rejection sampling when the large rectangle is empty -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "s" => smallProposalBits (I := I) (J := J)

attribute [local instance] OAI.ContingencyTables.SmallGraphProfiles.instDecidableEqPaperStates_3
lemma unitOuterDraw_error [Nonempty I] [Nonempty J] [Nonempty (PaperStates r c)]
    [Nonempty (Table r c)] (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j)
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c) :
    (variation (mapLaw (uniformLaw (α := Fin (M*(n*s)) → Bool))
      (unitOuterDraw r c fallback x n M z₀)) (uniformLaw (α := Table r c)):ℝ) ≤
      Real.exp (-(M:ℝ)/(2*(1+(d:ℝ)^2)))+
      M*(((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(n:ℝ)/(d:ℝ)^160)) := by
  have hd : 14 ≤ d := by
    have hi := Fintype.card_pos (α := I)
    have hj := Fintype.card_pos (α := J)
    unfold dimensionAllowance
    nlinarith
  let p := mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (unitJointDraw r c fallback x n)
  let q := uniformLaw (α := PaperStateJoint r c)
  have hj := unitJointDraw_variation r c hsmall fallback x n
  have hr := retryLaw_variation p q (stateTrial r c) z₀ M
  have hi : (variation (retryLaw q (stateTrial r c) z₀ M)
      (uniformLaw (α := Table r c)):ℝ) ≤ Real.exp (-(M:ℝ)/(2*(1+(d:ℝ)^2))) := by
    apply uniform_partial_retry_exp (StateJointSuccess r c) (originalStateSuccessEquiv r c)
      z₀ M (2*(1+(d:ℝ)^2))
    rw [paperStateJoint_card]
    exact stationary_success_ratio r c htotal hd
  have ht := variation_triangle (retryLaw p (stateTrial r c) z₀ M)
    (retryLaw q (stateTrial r c) z₀ M) (uniformLaw (α := Table r c))
  rw [unitOuterDraw_law]
  have hrR : (variation (retryLaw p (stateTrial r c) z₀ M)
      (retryLaw q (stateTrial r c) z₀ M):ℝ) ≤ M*(variation p q:ℝ) := by
    exact_mod_cast hr
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_add] at htR
  exact htR.trans (by nlinarith)

/-- The all-small branch reaches the same requested error as the branch
with a nonempty large rectangle, using no completion-sampling oracle. -/
theorem unitOuterDraw_accuracy [Nonempty I] [Nonempty J] [Nonempty (PaperStates r c)]
    [Nonempty (Table r c)] (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) (hk : 1 ≤ k)
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (z₀ : Table r c) :
    (variation (mapLaw (uniformLaw (α := Fin (outerTrials d k*(outerSteps d (smallBinaryLength r c) k*s)) → Bool))
      (unitOuterDraw r c fallback x (outerSteps d (smallBinaryLength r c) k) (outerTrials d k) z₀))
      (uniformLaw (α := Table r c)):ℝ) ≤ 1/(2:ℝ)^k := by
  have hd : 14 ≤ d := by
    have hi := Fintype.card_pos (α := I)
    have hj := Fintype.card_pos (α := J)
    unfold dimensionAllowance
    nlinarith
  have he := outer_total_error d (smallBinaryLength r c) k (stateBound r c) hd
    (smallBinaryLength_parameters r c).2.1 hk (smallBinaryLength_parameters r c).2.2
  have hv := unitOuterDraw_error r c hsmall htotal fallback x
    (outerSteps d (smallBinaryLength r c) k) (outerTrials d k) z₀
  apply hv.trans
  have hn : 0 ≤ (outerTrials d k:ℝ)*(outerSteps d (smallBinaryLength r c) k+1)/
      (2:ℝ)^(outerAccuracy d (smallBinaryLength r c) k) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by
      exact add_nonneg (Nat.cast_nonneg _) zero_le_one)) (le_of_lt (pow_pos (by norm_num) _))
  nlinarith

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedScheduledSampler
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the fully computed listed sampler schedule -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

variable (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
  (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
variable (hCheeger : PublishedInputs.FiniteCheeger
  (GridBoundary.Grid (I := Fin (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
    (4*(dimensionAllowance (I := Fin m) (J := Fin n))^8)))

include hPL hCheeger

/-- The executable, canonically initialized completion subroutine satisfies
exactly the three-error budget from the manuscript. -/
theorem listedScheduledDraw_accuracy (htotal : (∑ i,r i)=∑ j,c j)
    (x : PaperStates r c) (fallback : Table r c) (k : ℕ) (hk : 1≤k) :
    let _ : Nonempty (Table r c) := ⟨fallback⟩
    (variation (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c k) → Bool))
      (listedOuterDraw r c e hr hc b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
        x (outerSteps d b k) (outerTrials d k) fallback))
      (uniformLaw (α := Table r c)):ℝ)≤1/(2:ℝ)^k := by
  let : Nonempty (Table r c) := ⟨fallback⟩
  let : Nonempty (PaperStates r c) := ⟨x⟩
  dsimp only
  rw [listedOuterDraw_law r c e hr hc b (outerAccuracy d b k)
    (smallBinaryLength_parameters r c).1 htotal]
  have hv := listedOuterLaw_variation r c hr hc b (outerAccuracy d b k)
    (smallBinaryLength_parameters r c).1 hPL hCheeger htotal x
    (outerSteps d b k) (outerTrials d k) fallback
  have he := outer_total_error d b k (stateBound r c)
    (listed_dimension_fourteen r c hr hc) (smallBinaryLength_parameters r c).2.1 hk
    (smallBinaryLength_parameters r c).2.2
  apply hv.trans
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingAccuracy
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the single computed sampler for arbitrary margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

/-- Only the two cited published inputs on the completion grid are used.
The small and zero-dimensional branches need neither input. -/
theorem scheduledTableDraw_accuracy
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) (hk : 1≤k) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
    (variation (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c k) → Bool))
      (scheduledTableDraw r c htotal k)) (uniformLaw (α := Table r c)):ℝ)≤1/(2:ℝ)^k := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  let : Nonempty (PaperStates r c) := ⟨tableState r c (GreedyFeasibleTable.table r c htotal)⟩
  dsimp only
  unfold scheduledTableDraw
  split_ifs with h
  · exact listedScheduledDraw_accuracy r c (computedCellEquiv r c)
      ((hasLargeRectangle_spec r c k).mp h).1 ((hasLargeRectangle_spec r c k).mp h).2
      hPL hCheeger htotal (tableState r c (GreedyFeasibleTable.table r c htotal))
      (GreedyFeasibleTable.table r c htotal) k hk
  · have hs := allSmall_of_no_large r c k h
    rcases isEmpty_or_nonempty (Fin m) with hm|hm
    · let := hm
      let : Subsingleton (Table r c) := ⟨fun X Y => Subtype.ext (by funext i; exact isEmptyElim i)⟩
      rw [variation_uniform_of_subsingleton,Rat.cast_zero]
      positivity
    · rcases isEmpty_or_nonempty (Fin n) with hn|hn
      · let := hn
        let : Subsingleton (Table r c) := ⟨fun X Y => Subtype.ext (by funext i j; exact isEmptyElim j)⟩
        rw [variation_uniform_of_subsingleton,Rat.cast_zero]
        positivity
      · let := hm
        let := hn
        rw [padded_draw_law,unitCodeOuterDraw_law r c (computedCellEquiv r c) htotal]
        exact unitOuterDraw_accuracy r c hs htotal k hk (allSmallFibre r c hs)
          (tableState r c (GreedyFeasibleTable.table r c htotal)) (GreedyFeasibleTable.table r c htotal)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledCountSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scheduled executable numerator vector is the public sampler's law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] scheduledTrialDenominator scheduledTrialWidth
  scheduledCounts scheduledOuterInput listedOuterCounts unitOuterCounts matrixInput
  scheduledTableDraw listedOuterDraw unitCodeOuterDraw


variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma scheduledTrialDenominator_dense (k : ℕ)
    (hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true) :
    scheduledTrialDenominator ((List.ofFn r,List.ofFn c),k)=
      (2^(s+25*(d+b+outerAccuracy d b k+1)^62))^(outerSteps d b k)*
        2^(25*(d+b+outerAccuracy d b k+1)^62) := by
  rw [scheduledTrialDenominator,BinaryPowerPrograms.power_eq,scheduledTrialWidth,hlarge]
  simp only [ite_true, if_true,scheduledDenseWidth,parameterSteps_ofFn,parameterProposalWidth_ofFn,parameterCompletionWidth_ofFn]
  exact dyadic_trialDenom _ _ _

lemma scheduledTrialDenominator_unit (k : ℕ)
    (hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)≠true) :
    scheduledTrialDenominator ((List.ofFn r,List.ofFn c),k)=(2^s)^(outerSteps d b k) := by
  rw [scheduledTrialDenominator,BinaryPowerPrograms.power_eq,scheduledTrialWidth,ite_eq_right hlarge]
  rw [scheduledUnitWidth,parameterSteps_ofFn,parameterProposalWidth_ofFn,←pow_mul,Nat.mul_comm]

lemma scheduledTrialDenominator_pos (z : SamplingParameters) : 0 < scheduledTrialDenominator z := by
  rw [scheduledTrialDenominator,BinaryPowerPrograms.power_eq]
  positivity

/-- No extra table oracle: this is the integer law of the ordinary public branch. -/
def scheduledCountsLaw (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    IntegerLaw (Table r c)
      ((scheduledTrialDenominator ((List.ofFn r,List.ofFn c),k))^(outerTrials d k)) :=
  if hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true then
    (listedOuterCounts r c (computedCellEquiv r c)
      ((hasLargeRectangle_spec r c k).mp hlarge).1 ((hasLargeRectangle_spec r c k).mp hlarge).2
      b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
      (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
      (GreedyFeasibleTable.table r c htotal)).rebase
      (congrArg (fun Q => Q^(outerTrials d k)) (scheduledTrialDenominator_dense r c k hlarge).symm)
  else
    (unitOuterCounts r c (computedCellEquiv r c) (allSmall_of_no_large r c k hlarge)
      (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
      (GreedyFeasibleTable.table r c htotal)).rebase
      (congrArg (fun Q => Q^(outerTrials d k)) (scheduledTrialDenominator_unit r c k hlarge).symm)

lemma scheduledDraw_dense (htotal : ∑ i,r i=∑ j,c j) (k : ℕ)
    (hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true) :
    scheduledTableDraw r c htotal k=
      listedOuterDraw r c (computedCellEquiv r c)
        ((hasLargeRectangle_spec r c k).mp hlarge).1 ((hasLargeRectangle_spec r c k).mp hlarge).2
        b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
        (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
        (GreedyFeasibleTable.table r c htotal) := by
  funext bits
  unfold scheduledTableDraw
  rw [dite_eq_left hlarge]

lemma scheduledDraw_unit (htotal : ∑ i,r i=∑ j,c j) (k : ℕ)
    (hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)≠true) :
    scheduledTableDraw r c htotal k=fun bits =>
      unitCodeOuterDraw r c (computedCellEquiv r c) (allSmallFibre r c (allSmall_of_no_large r c k hlarge))
        (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
        (GreedyFeasibleTable.table r c htotal) (prefixWord (unitCodeBits_le r c k) bits) := by
  funext bits
  unfold scheduledTableDraw
  rw [dite_eq_right hlarge]

lemma scheduledCountsLaw_law (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    (scheduledCountsLaw r c htotal k).toRational
      (pow_pos (scheduledTrialDenominator_pos _) _)=
      mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c k) → Bool))
        (scheduledTableDraw r c htotal k) := by
  unfold scheduledCountsLaw
  split_ifs with hlarge
  · rw [scheduledDraw_dense r c htotal k hlarge]
    exact (IntegerLaw.toRational_rebase _ _ (by positivity) _).trans
      (listedOuterCounts_law r c _ _ _ _ _ _ htotal _ _ _ _)
  · rw [scheduledDraw_unit r c htotal k hlarge]
    exact (IntegerLaw.toRational_rebase _ _ (by positivity) _).trans
      ((unitOuterCounts_law r c _ htotal _ _ _ _ _).trans
        (padded_draw_law (unitCodeBits_le r c k) _).symm)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_CompiledResidualCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residual correction for the compiled public draw -/

namespace ContingencyTables.SmallGraphProfiles
open ResidualMixture FirstSuccess CompletionCounts ProfilePrograms Algorithms
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "D" => correctionPrecision r c
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

/-- The residual uses the compiled sampler's finite output law. -/
theorem scheduled_residual_correction
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
    ∃ residual : RationalLaw (Table r c),∀ X,
      (1-1/(2:ℚ)^D)*
        (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c (2*D)) → Bool))
          (scheduledTableDraw r c htotal (2*D))).mass X+
        (1/(2:ℚ)^D)*residual.mass X=uniformMass (α := Table r c) := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  have hD := correctionPrecision_pos r c
  apply residual_from_variation
  · positivity
  · exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  · exact correction_card_mass r c
  · have hpow : (1/(2:ℚ)^D)^2=1/(2:ℚ)^(2*D) := by
      rw [div_pow,one_pow,←pow_mul,Nat.mul_comm D 2]
    rw [hpow]
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using
      scheduledTableDraw_accuracy r c hPL hCheeger htotal (2*D) (by omega)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledResidualLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness and positivity of the executed correction vector -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms OriginalTableBox ResidualMixture FirstSuccess CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "D" => correctionPrecision r c
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

lemma scheduledCounts_domination
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
    ∀ X,(1-1/((2^D:ℕ):ℚ))*
      ((scheduledCountsLaw r c htotal (2*D)).toRational
        (pow_pos (scheduledTrialDenominator_pos _) _)).mass X≤uniformMass (α := Table r c) := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  dsimp only
  rw [scheduledCountsLaw_law]
  obtain ⟨residual,hr⟩ := scheduled_residual_correction r c hPL hCheeger htotal
  intro X
  have hn : 0≤(1/(2:ℚ)^D)*residual.mass X :=
    mul_nonneg (by positivity) (residual.nonnegative X)
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  linarith [hr X]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPrefixFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Feasibility is preserved on both branches and every finite retry prefix -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS.PhysicalStream
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
attribute [local irreducible] exactOrdinary correctionPrefix exactMatrixInput
  ExactCoreProgram.prefixExperiment scheduledTableDraw ExactIntegerOnline.trial
  scheduledResidualCounts originalCandidates

def FeasibleCode (X : MatrixCode) : Prop := ∃ T : Table r c,X=matrixCode T.val

def FeasibleOutcome (o : Option MatrixCode) : Prop := o.elim True (FeasibleCode r c)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ResidualBoxScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One scale for all boxes in the rare exact correction -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] profilePaddedMargins

def exactBoxScale {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) : ℕ :=
  2^(40*((dimensionAllowance (I := Fin m) (J := Fin n))^3*smallBinaryLength r c))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end


