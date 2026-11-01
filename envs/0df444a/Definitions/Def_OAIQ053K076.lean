-- Prove2me | Definitions.Def_OAIQ053K076
-- name    : OAIQ053K076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:24:10.56485+00:00
-- url     : https://prove2.me/theorems/e55256aa-5117-4b0a-b064-e893221d852a
-- title:
--   Definitions bundle OAIQ053K076 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 47 declarations of OpenAI's Lean: 26 definitions and 21 theorems. The definitions and types are `OAI.MetricKMedian.InstanceProgram.zeroOutputProgram`, `OAI.MetricKMedian.InstanceProgram.zeroTestProgram`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.padGraph`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.regularGraph`, `OAI.MetricKMedian.PCP.CookLevin.firstWord`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.geometryProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.repInputProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.repProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.supplierRawProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.supplierInputProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.suppliersProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.unitProgram`, `OAI.MetricKMedian.RoundingProgram.SignedRound.boundProgram`, `OAI.MetricKMedian.RoundingProgram.SignedRound.program`, `OAI.MetricKMedian.RoundingProgram.Terminal.program`, `OAI.MetricKMedian.SparseCounts.Program.compressProgram`, `OAI.MetricKMedian.SparseCounts.Program.runStateProgram`, `OAI.MetricKMedian.SparseCounts.Program.stepProgram`, `OAI.MetricKMedian.SparseOuterLaw.Program.Input.result`, `OAI.MetricKMedian.SparsePrepared.Program.bundleInputProgram`, `OAI.MetricKMedian.SparsePrepared.Program.outerInputProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.result`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput.result`, `OAI.MetricKMedian.SparseSignedPreparation.Program.bernoulliProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.kernelProgram`, `OAI.MetricKMedian.SparseStarActivation.Program.program`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_RegularSpec`, `KMedian_CookLevin_CookLevin`, `KMedian_Expanders_CloudEmbedding`, `KMedian_Expanders_CloudSpec`, `KMedian_Machines_LocalSpec`, `KMedian_Machines_MatchingSpec`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Process_CountRunProgram`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_InstanceZeroProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitGeometryProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedRoundProgram`, `KMedian_Rounding_SignedTerminalProgram`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K070`, `OAIQ053K071`, `OAIQ053K072` and `OAIQ053K073` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K080` and `OAIQ053K081`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K070
import Definitions.Def_OAIQ053K071
import Definitions.Def_OAIQ053K072
import Definitions.Def_OAIQ053K073

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type}
variable (t : CSPTable A) (h : t.WellFormed)
lemma active_test (v : Fin t.1.length) :
    (!(incident t v.val).isEmpty)=decide (v∈Set.range (CloudCopies.endpoint (C t h))) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true',List.isEmpty_eq_false_iff_exists_mem,Bool.decide_iff,incident,
    List.mem_filter,darts_eq,List.mem_map]
  constructor
  · rintro ⟨d,⟨⟨e,he,rfl⟩,hh⟩⟩
    exact ⟨e,Fin.ext (by simpa only [Bool.decide_iff,endpoint_eq t h] using hh)⟩
  · rintro ⟨e,he⟩
    refine ⟨dartCode t e,⟨⟨e,(dartOrder (EO t)).all e,rfl⟩,?_⟩⟩
    simp only [endpoint_eq t h,he]
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudEmbedding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudEmbedding
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type}
variable (t : CSPTable A) (h : t.WellFormed)
lemma emb_code (d : CloudCopies.Dart (E := Fin t.2.length)) :
    nodeCode (C t h) (VO t) (emb t h d)=
      ((CloudCopies.endpoint (C t h) d).val,
        ((incidentOrder (C t h) (EO t) (CloudCopies.owner (C t h) d)).equiv ⟨d,rfl⟩).val) := by
  rw [nodeCode_eq]
  apply Prod.ext
  · rfl
  change (ExpanderFamily.vertexEquiv _ (cloudEmbed (C t h) (EO t) _ ⟨d,rfl⟩)).val=_
  rw [cloudEmbed_index]
  simp only [Ordered.equiv_val,List.idxOf]
  congr 1
  funext x
  simp only [Bool.beq_eq_decide_eq]
lemma emb_get (d : CloudCopies.Dart (E := Fin t.2.length)) :
    (incident t (nodeCode (C t h) (VO t) (emb t h d)).1)[(nodeCode (C t h) (VO t) (emb t h d)).2]?=some (dartCode t d) := by
  rw [emb_code t h d]
  change (incident t (CloudCopies.owner (C t h) d).val.val)[_]?=_
  rw [incident_eq t h]
  exact Ordered.get_coded _ (fun e : CloudCopies.Incident (C t h) (CloudCopies.owner (C t h) d) => dartCode t e.val) ⟨d,rfl⟩
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudEmbedding

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_MatchingSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPMatchingSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder RegularProgram

variable {A : Type}
variable (t : CSPTable A) (h : t.WellFormed)
variable [Fintype A] [DecidableEq A]
lemma matchAllowed_image (d : CloudCopies.Dart (E := Fin t.2.length)) :
    matchAllowed t (nodeCode (C t h) (VO t) (emb t h d))=(CloudCopies.dartCSP (C t h)).allowed (d,()) := by
  have hl := emb_code_lt t h d
  have hg := emb_get t h d
  simp only [matchAllowed,ite_eq_left hl,hg,Option.getD_some,dartCode,row_allowed t h]
  rcases d with ⟨e,b⟩
  cases b
  · simp only [Bool.false_eq_true,↓reduceIte,CloudCopies.dartCSP,Finset.filter_mem_eq_inter,Finset.univ_inter]
  · simp only [↓reduceIte,CloudCopies.dartCSP]
    apply Finset.ext
    rintro ⟨a,b⟩
    simp only [Finset.mem_image,Prod.exists,Finset.mem_filter,Finset.mem_univ,true_and,Prod.swap_prod_mk,Prod.mk.injEq]
    constructor
    · rintro ⟨x,y,hxy,hya,hxb⟩
      subst x; subst y; exact hxy
    · intro hab
      exact ⟨b,a,hab,rfl,rfl⟩
lemma matchAllowed_correct (p : CloudCopies.Node (C t h)) :
    matchAllowed t (nodeCode (C t h) (VO t) p)=
      (FlexibleCloud.matchingCSP (C t h) (cloudEmbed (C t h) (EO t))).allowed (p,()) := by
  by_cases hp : p∈Set.range (emb t h)
  · obtain ⟨d,rfl⟩ := hp
    rw [matchAllowed_image t h]
    exact (FlexibleCloud.matching_allowed_image (C t h) (cloudEmbed (C t h) (EO t)) d).symm
  · have hn := mt (emb_range t h p).mpr hp
    have hn' : ¬(nodeCode (C t h) (VO t) p).2<(incident t (nodeCode (C t h) (VO t) p).1).length := by
      rw [nodeCode_eq]; exact hn
    rw [matchAllowed,ite_eq_right hn']
    exact (FlexibleCloud.matching_allowed_outside (C t h) (cloudEmbed (C t h) (EO t)) p hp).symm
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPMatchingSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder RegularProgram

variable {A : Type} [Fintype A] [DecidableEq A]
variable (t : CSPTable A) (h : t.WellFormed)
lemma localAllowed_correct (p : CloudCopies.Node (C t h)) (d : RPort) :
    localAllowed t (nodeCode (C t h) (VO t) p) d=(localCSP t h).allowed (p,d) := by
  unfold localAllowed localCSP FlexibleCloud.regularCSP PortCSP.blend
  dsimp only
  split_ifs
  · exact matchAllowed_correct t h p
  · ext q
    simp only [CloudCopies.equalityCSP,Finset.mem_filter,Finset.mem_univ,true_and]
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPLocalSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRegularSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder RegularProgram

variable {A : Type} [Fintype A] [DecidableEq A]
variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable abbrev padGraph := FlexibleRegularization.padGraph (C t h) (cloudEmbed (C t h) (EO t)) (padding t h)
noncomputable abbrev regularGraph := FlexibleRegularization.graph (C t h) (cloudEmbed (C t h) (EO t)) (padding t h)
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPRegularSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitRepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
 theorem values_view {f j : ℕ} (U : RationalUnitInput f j) : values (view U)=List.ofFn U.V := by
  simp only [values,view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,decide_eq_true_eq,List.sum_ofFn,← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rfl

 theorem repData_view (M : ℚ) (x : Input) : repData M x.raw=(x.rep M).raw := by
  unfold repData
  rw [show values x.raw=List.ofFn x.U.V from values_view x.U]
  simp only [Input.rep,RationalRepresentatives.Program.Input.raw,Input.raw,view,setView,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact (decide_eq_true (Finset.mem_univ i)).symm

noncomputable def repInputProgram (M : ℚ) : PolyProgram Input.encode RationalRepresentatives.Program.Input.encode (Input.rep M) :=
  (repData_poly M).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (repData_view M x))
noncomputable def repProgram (M : ℚ) : PolyProgram Input.encode (enc : Row → List Bool)
    (fun x => setView (x.U.representatives M)) :=
  (repInputProgram M |>.comp RationalRepresentatives.Program.program).congr _ (fun _ => rfl)

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitGeometryProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

 theorem geometryData_view {f j : ℕ} (U : RationalUnitInput f j) (M : ℚ) :
    geometryData (view U,setView (U.representatives M))=
      RationalBundles.Program.view (fun t u => U.dd (U.ridx M t) (U.ridx M u))
        (fun t a => U.dc (U.ridx M t) a) (fun t => U.F (U.ridx M t)) U.y := by
  unfold geometryData
  rw [ranks_view]
  simp only [view,ridx,pullbackMatrix_view,pickRows_view,setView,RationalBundles.Program.view]
  rfl

noncomputable def geometryProgram (M : ℚ) : PolyProgram Input.encode enc
    (fun x => geometryData (x.raw,setView (x.U.representatives M))) :=
  ((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.fanout (repProgram M)).comp geometryData_poly.program

 theorem suppliersData_view {f j : ℕ} (U : RationalUnitInput f j) {X : Type} [PseudoMetricSpace X]
    (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ) :
    suppliersData p.δ p.γ (geometryData (view U,setView (U.representatives p.M)))=
      RationalSuppliers.Program.supplierView (U.suppliers R p) := by
  rw [geometryData_view]
  unfold suppliersData
  rw [RationalBundles.Program.bundlesData_view,RationalBundles.Program.missingData_view]
  simp only [RationalBundles.Program.view,RationalBundles.Program.massData_view]
  rfl

noncomputable def supplierRawProgram {η τ : ℝ} (p : RationalAllParameters η τ) : PolyProgram Input.encode enc
    (fun x => suppliersData p.δ p.γ (geometryData (x.raw,setView (x.U.representatives p.M)))) :=
  geometryProgram p.M |>.comp (suppliersData_poly p.δ p.γ).program
end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)
noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et) Input.result := by
  let get : PolyProgram SparseGraph.Program.State.encode (ed SparseGraph.ListOperation.et)
      (fun x : SparseGraph.Program.State => (x.raw SparseGraph.Program.view).2) :=
    (snd SparseGraph.Program.Context.encode (ed SparseGraph.ListOperation.et)).recode
      (SparseIntegerLaw.DependentProgram.Bundle.raw SparseGraph.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (graphProgram.comp SparseGraph.Program.runStateProgram |>.comp get).congr _ (fun _ => rfl)
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedTerminalProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

noncomputable def program : PolyProgram Input.encode (ed erow) result := by
  let bs := bernoulliInputProgram.comp (SparseBernoulli.Program.runStateProgram 2)
  let bl := bs.comp (SparseIntegerLaw.DependentProgram.lawProgram
    SparseBernoulli.Program.Context.encode ber SparseBernoulli.Program.view)
  let rows := bs.comp (SparseIntegerLaw.DependentProgram.statesProgram
    SparseBernoulli.Program.Context.encode ber SparseBernoulli.Program.view)
  let ctx : PolyProgram Input.encode (encodePair erow erow) (@Input.raw true) :=
    (PolyProgram.identity _).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  let mapped := (ctx.fanout rows).comp (boolState_poly.program.listMapWith [] [])
  exact (bl.fanout mapped).congr _ (fun x => by
    simp only [result,RationalSignedTerminal.terminal,SparseIntegerLaw.map,Vector.toList_map,List.map_map]
    dsimp only [Function.comp_def,bernoulliInput,SparseBernoulli.Program.Input.state,
      SparseBernoulli.Program.view,Input.raw]
    simp only [List.map_map,Function.comp_def,boolState_list])

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

noncomputable def boundProgram : PolyProgram Input.encode State.encode boundState := by
  let part :=  runProgram true
  let law := part.comp ((snd erow (ed erow)).comp (fst el (encodeList erow)) |>.recode (@State.raw true) State.encode_raw (fun _ => rfl))
  let kernels := partialInputsProgram.comp (Terminal.program.listMap emptyInput)
  let bound := (law.fanout kernels).comp SparseIntegerLaw.BinarySparse.bindData_poly.program
  let β := (fst erow erow).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  exact (β.fanout bound).recode id (fun _ => rfl) (fun x => by
    rw [← State.encode_raw]
    change encodePair erow (ed erow) (List.ofFn x.β,
      bindData (((SparseSignedPartial.run x.β x.p x.n).law.denominator,
        List.ofFn (SparseSignedPartial.run x.β x.p x.n).law.numerator),
        (partialInputs x).map Terminal.result))=_
    simp only [partialInputs,List.map_ofFn,Function.comp_def]
    change encodePair erow (ed erow) (List.ofFn x.β,
      bindData ((raw (SparseSignedPartial.run x.β x.p x.n)).1,
        List.ofFn (fun i => ((raw (SparseSignedRounding.kernel x.β x.p x.feasible i)).1,
          (SparseSignedRounding.kernel x.β x.p x.feasible i).states.toList.map Vector.toList))))=_
    rw [bindData_raw]
    rfl)

noncomputable def program : PolyProgram Input.encode State.encode result :=
  (boundProgram.comp (compressProgram true)).congr _ (fun _ => rfl)

end SignedRound
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedPreparationProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
noncomputable def bernoulliProgram : PolyProgram KernelInput.encode (ed SparseBernoulli.Program.er)
    (fun x => (((SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.denominator,
      List.ofFn (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.numerator),
      (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).states.toList.map List.ofFn)) := by
  let get : PolyProgram SparseBernoulli.Program.State.encode (ed SparseBernoulli.Program.er)
      (fun x : SparseBernoulli.Program.State => (x.raw SparseBernoulli.Program.view).2) :=
    (snd SparseBernoulli.Program.Context.encode (ed SparseBernoulli.Program.er)).recode
      (SparseIntegerLaw.DependentProgram.Bundle.raw SparseBernoulli.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (bernoulliInputProgram.comp (SparseBernoulli.Program.runStateProgram 2) |>.comp get).congr _ (fun _ => rfl)

def KernelInput.result (x : KernelInput) : Data StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (kernel x.D x.p x.feasible)).1,(kernel x.D x.p x.feasible).states.toList.map view)
 theorem kernel_raw (x : KernelInput) :
    attach (x.p.toList,prodData (x.star.result,
       (((SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.denominator,
         List.ofFn (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.numerator),
       (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).states.toList.map List.ofFn)))=x.result := by
  simp only [KernelInput.star,SparseStarActivation.Program.Input.result,attach,prodData,
    KernelInput.result,kernel,SparseIntegerLaw.BinarySparse.raw,SparseIntegerLaw.prod,
    states_list,List.flatMap_def,List.map_ofFn,Function.comp_def,
    RoundingList.ofFn_product,Vector.toList_ofFn,view]
  rfl

noncomputable def kernelProgram : PolyProgram KernelInput.encode (enc : Data StateRaw → List Bool) KernelInput.result := by
  let p : PolyProgram KernelInput.encode enc (fun x : KernelInput => x.p.toList) :=
    ((snd enc enc).comp (snd enc enc)).recode KernelInput.raw (fun _ => rfl) (fun _ => rfl)
  exact (p.fanout ((starInputProgram.comp SparseStarActivation.Program.program).fanout bernoulliProgram
    |>.comp prodData_poly.program) |>.comp attach_poly.program).congr _ kernel_raw

 theorem beta_input (x : Input) : beta x.raw=List.ofFn (SparseSignedPreparation.signed x.D x.c) := by
  simp only [beta,Input.raw,SparseGraph.ListOperation.indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  congr 1
  funext e
  rw [Completion.Rational.BestProgram.card_view]
  rfl
def Input.result (x : Input) : Data StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.p x.feasible x.c_unit)).1,
    (law x.D x.c x.p x.feasible x.c_unit).states.toList.map view)
theorem result_bind (x : Input) : x.result=
    ((SparseIntegerLaw.BinarySparse.raw (x.μ.bindIndexed (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible))).1,
      (x.μ.bindIndexed (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible)).states.toList.map view) := rfl
 theorem bind_result (x : Input) :
    bindData ((SparseIntegerLaw.BinarySparse.raw x.μ).1,x.kernels.map KernelInput.result)=x.result := by
  rw [result_bind]
  unfold Input.kernels
  simp only [List.map_ofFn,Function.comp_def,KernelInput.result,Input.ker]
  exact bindData_raw x.μ (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible) view

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedDataOperations
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView indices)

theorem activationData_view (x : KernelInput) (e : Fin x.m) (j : Fin x.n) :
    activationData x.raw e.val j.val=SparseOuterLaw.activationCount x.D x.q x.z e j := by
  simp only [activationData,KernelInput.raw,KernelInput.base,SparseSignedPreparation.Program.view,
    SparseGraph.ListOperation.view,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    decide_eq_true_eq,Fin.eta,SparseOuterLaw.activationCount,SparseGridRounding.base]

theorem totalData_view (x : KernelInput) (j : Fin x.n) :
    totalData x.raw j.val=total x.D x.q x.Δ x.z j := by
  unfold totalData
  simp only [KernelInput.raw,KernelInput.base,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change x.Δ-min ((List.ofFn (fun e => activationData x.raw e.val j.val)).sum) (x.Δ/2)=_
  simp only [activationData_view,List.sum_ofFn,total]

theorem pieces_view (x : KernelInput) : pieces x.raw=
    List.ofFn (fun j => List.ofFn (fun i => SparseRescaledInner.piece x.P x.y x.p (total x.D x.q x.Δ x.z) i j)) := by
  simp only [pieces,KernelInput.raw,KernelInput.base,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,setView,decide_eq_true_eq,Fin.eta]
  change (List.ofFn (fun j : Fin x.n => List.ofFn (fun i : Fin x.f => if i∈x.P j then
    (totalData x.raw j.val:ℚ)*x.y i/x.p j else 0)))=_
  simp only [totalData_view,SparseRescaledInner.piece]
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

noncomputable def compressProgram : PolyProgram State.encode State.encode
    (Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m)) (fun _ => features)) :=
  SparseIntegerLaw.DependentProgram.compressProgram Context.encode et view [] _ (fun _ => features)
    (fun x => ListOperation.featureList (x.1.input.raw.1,x.2))
    (fun _ G => ListOperation.featureList_view G) dimensionsProgram featuresProgram

noncomputable def stepProgram : PolyProgram State.encode State.encode State.step :=
  ((PolyProgram.ite activeProgram (identity State.encode) (productProgram.comp compressProgram)).comp incrementProgram).congr _
    (fun x => by simp only [State.step,Function.comp_def,decide_eq_true_eq,id_eq])
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)

noncomputable def runStateProgram : PolyProgram Input.encode State.encode (fun x => x.state x.m) :=
  (stepProgram.repeatFrom startProgram countProgram X sizePolynomial
    (fun x => by simpa using (input_bounds x).2.1)
    (fun x t ht => by rw [state_iterate]; exact state_size x t ht)).congr _ (fun x => state_iterate x _)
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedKernelProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

noncomputable def bundleInputProgram : PolyProgram KernelInput.encode SparseBundles.Program.QInput.encode KernelInput.bundles :=
  bundleData_poly.program.recode KernelInput.raw (fun _ => rfl) (fun x => by
    unfold bundleData
    rw [pieces_view]
    simp only [KernelInput.raw,KernelInput.base,List.map_const',List.length_ofFn,
      SparseBundles.Program.QInput.encode,SparseBundles.Program.QInput.raw,KernelInput.bundles]
    rfl)
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
def Input.result (x : Input) : Data SparseSignedPreparation.Program.StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.q x.c_unit x.q_nonnegative)).1,
    (law x.D x.c x.q x.c_unit x.q_nonnegative).states.toList.map SparseSignedPreparation.Program.view)
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedLawProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)
noncomputable def outerInputProgram : PolyProgram Input.encode SparseOuterLaw.Program.Input.encode Input.outer :=
  outerData_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [outerData,Input.raw,Input.base,List.map_const',List.length_ofFn,
      SparseOuterLaw.Program.Input.encode,SparseOuterLaw.Program.Input.raw,Input.outer])
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Preparation.RationalUnitInput.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open Program
variable {η τ : ℝ} (p : RationalAllParameters η τ)
 theorem postData_view (x : Input) :
    postData (x.raw,suppliersData p.δ p.γ (geometryData (view x.U,setView (x.U.representatives p.M))))=(x.sup p).raw := by
  let := x.metric
  unfold postData
  rw [suppliersData_view x.U x.R p]
  rfl
noncomputable def unitProgram : PolyProgram Input.encode Program.Input.encode Input.unit :=
  (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def suppliersProgram : PolyProgram Input.encode enc
    (fun x => suppliersData p.δ p.γ (geometryData (view x.U,setView (x.U.representatives p.M)))) :=
  (unitProgram.comp (Program.supplierRawProgram p)).congr _ (fun _ => rfl)
noncomputable def supplierInputProgram : PolyProgram Input.encode RationalSuppliers.Program.ScanInput.encode (Input.sup p) :=
  (((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.fanout (suppliersProgram p)).comp postData_poly.program).recode
    id (fun _ => rfl) (fun x => congrArg enc (postData_view p x))
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceZeroProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
open Completion.Rational.BestProgram (card card_view)
 theorem zeroTestData_view (I : Instance) : zeroTestData (view I)=decide I.zeroTest := by
  apply Bool.eq_iff_iff.mpr
  simp only [zeroTestData,view,subsetRaw_view,card_view,Bool.and_eq_true,decide_eq_true_eq]
  rfl
noncomputable def zeroTestProgram : PolyProgram encode encodeBool (fun I => decide I.zeroTest) :=
  zeroTestData_poly.program.recode view (fun _ => rfl) (fun I => congrArg encodeBool (zeroTestData_view I))

 theorem singletonData_view (I : Instance) : singletonData (view I)=setView {I.facilities.min' I.facilities_nonempty} := by
  unfold singletonData view
  rw [first_view,singletonRaw_view]
 theorem zeroOutputData_view (I : Instance) : zeroOutputData (view I)=setView I.zeroOutput := by
  unfold zeroOutputData Instance.zeroOutput
  change (if (setView I.clients).any id then setView I.clients else singletonData (view I))=_
  rw [Completion.Rational.PackingProgram.any_view]
  simp only [decide_eq_true_eq]
  split_ifs
  · rfl
  · exact singletonData_view I
noncomputable def zeroOutputProgram : PolyProgram encode (enc : Row → List Bool) (fun I => setView I.zeroOutput) :=
  zeroOutputData_poly.program.recode view (fun _ => rfl) (fun I => congrArg enc (zeroOutputData_view I))
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookLevin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookLevin

namespace MetricKMedian.PCP.CookLevin
open Turing Turing.TM2 Function Finset
open Complexity Tableau
open scoped Classical

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_rfd248b_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_rfd248b_1 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_rfd248b_1 : Fintype P.tm.σ := P.tm.σFin
def firstWord (x : Word) : Word := encodeNat x.length++x
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookLevin

end OAI
end


