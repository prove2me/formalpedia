-- Prove2me | Definitions.Def_OAIQ053K080
-- name    : OAIQ053K080
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:28:13.979984+00:00
-- url     : https://prove2.me/theorems/e8a317b4-2049-4320-ac58-11061a600ace
-- title:
--   Definitions bundle OAIQ053K080 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 28 definitions and 17 theorems. The definitions and types are `OAI.MetricKMedian.InstanceProgram.nonzeroPseudoProgram`, `OAI.MetricKMedian.InstanceProgram.nonzeroRoundProgram`, `OAI.MetricKMedian.InstanceProgram.pseudoProgram`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.vertexEquiv`, `OAI.MetricKMedian.PCP.CookLevin.inputPrefix`, `OAI.MetricKMedian.PCP.CookLevin.inputSize`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.masksProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.program`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanInputProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanRawPairProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanRawProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanTablesProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.tablesProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.program`, `OAI.MetricKMedian.Reduction.Program.Branch.encode`, `OAI.MetricKMedian.SparseBundles.Program.inputProgram`, `OAI.MetricKMedian.SparseBundles.Program.lawProgram`, `OAI.MetricKMedian.SparseOuterLaw.Program.program`, `OAI.MetricKMedian.SparseOuterLaw.Program.signedProgram`, `OAI.MetricKMedian.SparsePrepared.Program.kernelProgram`, `OAI.MetricKMedian.SparsePrepared.Program.kernelsProgram`, `OAI.MetricKMedian.SparsePrepared.Program.program`, `OAI.MetricKMedian.SparsePrepared.Program.weightsProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.kernelsProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.program`, `OAI.MetricKMedian.SparseSignedPreparation.Program.signedInputProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.weightsProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_PaddingSpec`, `KMedian_Amplification_PowerTable`, `KMedian_Amplification_RegularSpec`, `KMedian_CookLevin_CookLevin`, `KMedian_Expanders_CloudSpec`, `KMedian_Machines_LocalSpec`, `KMedian_Machines_MatchingSpec`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Preparation_SupplierScanProgram`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_InstanceRoundProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_SignedPreparationProgram`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K075`, `OAIQ053K076` and `OAIQ053K077` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K082` and `OAIQ053K083`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K075
import Definitions.Def_OAIQ053K076
import Definitions.Def_OAIQ053K077

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
lemma active_eq : active t=((activeOrder (C t h) (VO t)).entries.map (fun v => v.val.val)) := by
  unfold active activeOrder
  change _=List.map (Fin.val ∘ Subtype.val) _
  rw [← List.map_map]
  have hv := @Ordered.filter_val (Fin t.1.length) (VO t) (fun v => v∈Set.range (CloudCopies.endpoint (C t h))) (Classical.decPred _)
  rw [hv,← finRange_val t.1.length,List.filter_map]
  congr 1
  congr 1
  funext v
  have hv := active_test t h v
  apply Bool.eq_iff_iff.mpr
  simpa only [Function.comp_def,Bool.decide_iff] using Bool.eq_iff_iff.mp hv
lemma nodes_eq : nodes t=((nodeOrder (C t h) (VO t)).entries.map (nodeCode (C t h) (VO t))) := by
  unfold nodes
  rw [active_eq t h,List.flatMap_map]
  unfold nodeOrder Ordered.sigma
  simp only [List.sigma,List.map_flatMap,List.map_map]
  apply congrArg (fun f : CloudCopies.Active (C t h) → List (ℕ × ℕ) => ((activeOrder (C t h) (VO t)).entries).flatMap f)
  funext v
  rw [cloud_length t h v]
  unfold copyOrder Ordered.map Ordered.fin
  simp only [List.map_map,Function.comp_def,nodeCode_eq,Equiv.apply_symm_apply]
  rw [← finRange_val]
  simp only [List.map_map,Function.comp_def]
lemma index_eq (p : CloudCopies.Node (C t h)) :
    index t (nodeCode (C t h) (VO t) p)=((nodeOrder (C t h) (VO t)).equiv p).val := by
  unfold index
  rw [nodes_eq t h]
  rw [Ordered.index_coded _ _ (nodeCode_injective (C t h) (VO t)) p]
  congr 1
  funext q
  simp only [Prod.ext_iff]
lemma global_table [Nonempty (Fin t.2.length)] :
    global t=RotationTable.table (ExpanderFamily.graph (GlobalRegularization.depth (C t h)))
      (ExpanderFamily.vertexEquiv (GlobalRegularization.depth (C t h))) := by
  unfold global
  rw [Expander.generate_table]
  have hn : (nodes t).length=Fintype.card (CloudCopies.Node (C t h)) := by
    rw [nodes_eq t h,List.length_map,Ordered.length_card]
  change (fun n => RotationTable.table (ExpanderFamily.graph n) (ExpanderFamily.vertexEquiv n)) _ = _
  congr 1
  simp only [GlobalRegularization.depth,List.length_map,List.length_tail,hn]
  apply congrArg ExpanderFamily.level
  apply congrArg (fun n : ℕ => n-1)
  exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PaddingSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPaddingSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_index (p : CloudCopies.Node (C t h)) :
    vertexCode t h (padding t h p)=index t (nodeCode (C t h) (VO t) p) := by
  rw [padding_code,index_eq t h]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_range (v : GlobalRegularization.Node (C t h)) :
    v∈Set.range (padding t h) ↔ vertexCode t h v<(nodes t).length := by
  rw [nodes_eq t h,List.length_map]
  constructor
  · rintro ⟨p,rfl⟩
    rw [padding_code]
    exact ((nodeOrder (C t h) (VO t)).equiv p).isLt
  · intro hv
    let p := (nodeOrder (C t h) (VO t)).equiv.symm ⟨vertexCode t h v,hv⟩
    refine ⟨p,?_⟩
    apply (ExpanderFamily.vertexEquiv _).injective
    apply Fin.ext
    change vertexCode t h (padding t h p)=vertexCode t h v
    rw [padding_code]
    simp only [p,Equiv.apply_symm_apply]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_get (p : CloudCopies.Node (C t h)) :
    (nodes t)[vertexCode t h (padding t h p)]?=some (nodeCode (C t h) (VO t) p) := by
  rw [nodes_eq t h,padding_code]
  exact Ordered.get_coded _ _ p
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_index_lt (p : CloudCopies.Node (C t h)) :
    vertexCode t h (padding t h p)<(nodes t).length :=
  (padding_range t h (padding t h p)).mp ⟨p,rfl⟩
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPPaddingSpec

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
lemma matchStep_image (d : CloudCopies.Dart (E := Fin t.2.length)) :
    matchStep t (nodeCode (C t h) (VO t) (emb t h d))=
      nodeCode (C t h) (VO t) (emb t h (CloudCopies.dartFlip d)) := by
  have hl := emb_code_lt t h d
  have hg := emb_get t h d
  simp only [matchStep,ite_eq_left hl,hg,Option.getD_some]
  change (endpoint t (dartCode t (CloudCopies.dartFlip d)),
    dartIndex t (endpoint t (dartCode t (CloudCopies.dartFlip d))) (dartCode t (CloudCopies.dartFlip d)))=_
  rw [endpoint_eq t h,emb_code t h]
  apply Prod.ext
  · rfl
  exact dartIndex_eq t h (CloudCopies.owner (C t h) (CloudCopies.dartFlip d)) ⟨CloudCopies.dartFlip d,rfl⟩
lemma matchStep_correct (p : CloudCopies.Node (C t h)) :
    matchStep t (nodeCode (C t h) (VO t) p)=nodeCode (C t h) (VO t)
      ((FlexibleCloud.matchingGraph (C t h) (cloudEmbed (C t h) (EO t))).step p ()) := by
  by_cases hp : p∈Set.range (emb t h)
  · obtain ⟨d,rfl⟩ := hp
    rw [matchStep_image t h]
    rw [FlexibleCloud.matching_step_image]
  · have hn := mt (emb_range t h p).mpr hp
    have hn' : ¬(nodeCode (C t h) (VO t) p).2<(incident t (nodeCode (C t h) (VO t) p).1).length := by
      rw [nodeCode_eq]; exact hn
    rw [matchStep,ite_eq_right hn']
    rw [FlexibleCloud.matching_step_outside _ _ p hp]
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPMatchingSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
omit [Fintype A] [DecidableEq A] in
lemma localRotate_correct (p : CloudCopies.Node (C t h)) (d : RPort) :
    localRotate t (nodeCode (C t h) (VO t) p) d=
      (nodeCode (C t h) (VO t) ((localGraph t h).step p d),(localGraph t h).back p d) := by
  unfold localGraph FlexibleCloud.regularGraph
  rw [PortGraph.blend_coded]
  rcases d with ⟨i,u,d⟩
  cases u
  by_cases hi : i=0
  · simp only [localRotate,ite_eq_left hi,matchStep_correct t h]
  · simp only [localRotate,ite_eq_right hi,nodeCode_eq t h,cloud_table t h,RotationTable.lookup_table]
    rfl
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPLocalSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
omit [Fintype A] [DecidableEq A] in
lemma paddedRotate_correct (v : GlobalRegularization.Node (C t h)) (d : RPort) :
    paddedRotate t (vertexCode t h v) d=
      (vertexCode t h ((padGraph t h).step v d),(padGraph t h).back v d) := by
  by_cases hv : v∈Set.range (padding t h)
  · obtain ⟨p,rfl⟩ := hv
    rw [paddedRotate,ite_eq_left (padding_index_lt t h p),padding_get t h,Option.getD_some]
    dsimp only
    rw [localRotate_correct t h]
    have he := FlexibleRegularization.padded_rotate_image (C t h) (cloudEmbed (C t h) (EO t)) (padding t h) p d
    change _=(vertexCode t h ((padGraph t h).rotate (padding t h p,d)).1,
      ((padGraph t h).rotate (padding t h p,d)).2)
    rw [he]
    rw [padding_index]
  · have hn := mt (padding_range t h v).mpr hv
    rw [paddedRotate,ite_eq_right hn]
    have he := FlexibleRegularization.padded_rotate_outside (C t h) (cloudEmbed (C t h) (EO t)) (padding t h) v d hv
    change (vertexCode t h v,d)=(vertexCode t h ((padGraph t h).rotate (v,d)).1,
      ((padGraph t h).rotate (v,d)).2)
    rw [he]
lemma paddedAllowed_correct (v : GlobalRegularization.Node (C t h)) (d : RPort) :
    paddedAllowed t (vertexCode t h v) d=(padCSP t h).allowed (v,d) := by
  by_cases hv : v∈Set.range (padding t h)
  · obtain ⟨p,rfl⟩ := hv
    rw [paddedAllowed,ite_eq_left (padding_index_lt t h p),padding_get t h,Option.getD_some,
      localAllowed_correct t h]
    exact (FlexibleRegularization.padded_allowed_image (C t h) (cloudEmbed (C t h) (EO t)) (padding t h) p d).symm
  · have hn := mt (padding_range t h v).mpr hv
    rw [paddedAllowed,ite_eq_right hn]
    exact (FlexibleRegularization.padded_allowed_outside (C t h) (cloudEmbed (C t h) (EO t)) (padding t h) v d hv).symm
omit [Fintype A] [DecidableEq A] in
lemma strongRotate_correct (v : GlobalRegularization.Node (C t h)) (d : GlobalRegularization.StrongPort) :
    strongRotate t (vertexCode t h v) d=
      (vertexCode t h ((GlobalRegularization.strong (C t h)).step v d),
        (GlobalRegularization.strong (C t h)).back v d) := by
  unfold strongRotate
  rw [global_table t h]
  exact RotationTable.fourthLookup_table _ _ v d
omit [Fintype A] [DecidableEq A] in
lemma rotate_correct (v : GlobalRegularization.Node (C t h)) (d : Port) :
    rotate t (vertexCode t h v) d=
      (vertexCode t h ((regularGraph t h).step v d),(regularGraph t h).back v d) := by
  rw [FlexibleRegularization.graph_coded]
  unfold rotate
  split_ifs
  · rw [paddedRotate_correct t h]
  · rw [strongRotate_correct t h]
lemma allowed_correct (v : GlobalRegularization.Node (C t h)) (d : Port) :
    allowed t (vertexCode t h v) d=(regularCSP t h).allowed (v,d) := by
  unfold regularCSP FlexibleRegularization.csp PortCSP.blend allowed
  dsimp only
  split_ifs
  · exact paddedAllowed_correct t h v d.2.1
  · rfl
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPRegularSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PowerTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPowerTable
namespace MetricKMedian.PCP.Compiler.PowerProgram
open Binary Binary.Automatic RegularProgram CloudSpec
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
variable (s : CSPTable A) (h : s.WellFormed) [Nonempty (Fin s.2.length)]
noncomputable def vertexEquiv : GlobalRegularization.Node (C s h) ≃ Fin (seeds s).length :=
  (ExpanderFamily.vertexEquiv _).trans (finCongr (by
    rw [seeds,List.length_map,global_table s h,RotationTable.table_length]))
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedPreparationProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
noncomputable def signedInputProgram : PolyProgram Input.encode RoundingProgram.Input.encode Input.signed := by
  let p : PolyProgram enc enc (fun x : Raw => (beta x,x.2.2.2)) := Poly.program (by fun_prop)
  exact p.recode Input.raw (fun _ => rfl) (fun x => by
    change enc (beta x.raw,x.p.toList)=_
    rw [beta_input]; rfl)

noncomputable def kernelsProgram : PolyProgram Input.encode (encodeList KernelInput.encode) Input.kernels := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let s := signedInputProgram.comp RoundingProgram.SignedRound.program
  let sr : PolyProgram RoundingProgram.State.encode enc (RoundingProgram.State.raw (s:=true)) :=
    (identity enc).recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun _ => rfl)
  exact (r.fanout (s.comp sr) |>.comp inputRows_poly.program).recode id (fun _ => rfl) (fun x => by
    change encodeList enc (inputRows (x.raw,(RoundingProgram.SignedRound.result x.signed).raw))=_
    simp only [inputRows,RoundingProgram.State.raw,states_list,List.map_ofFn,
      Function.comp_def]
    change encodeList enc (List.ofFn (fun i => (x.ker i).raw))=encodeList KernelInput.encode x.kernels
    rw [List.ofFn_comp',encodeList_map]; rfl)

noncomputable def weightsProgram : PolyProgram Input.encode el (fun x => (SparseIntegerLaw.BinarySparse.raw x.μ).1) := by
  let weights : PolyProgram RoundingProgram.State.encode el (fun x : RoundingProgram.State true => (x.raw).2.1) :=
    ((snd enc enc).comp (fst enc enc)).recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun _ => rfl)
  exact (signedInputProgram.comp RoundingProgram.SignedRound.program |>.comp weights).congr _ (fun _ => rfl)
noncomputable def program : PolyProgram Input.encode (enc : Data StateRaw → List Bool) Input.result :=
  (weightsProgram.fanout (kernelsProgram.comp (kernelProgram.listMap dummy)) |>.comp bindData_poly.program).congr _ bind_result

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BundlesProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram SparseCounts.Program

noncomputable def inputProgram : PolyProgram QInput.encode Input.encode QInput.input := by
  let n := (fst (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun _ => rfl)
  let cols := columnsProgram.comp (SparseGridRounding.Program.program.listMap emptyColumn)
  exact (n.fanout cols).recode id (fun _ => rfl) (fun x => by
    change ei (x.raw.1,x.columns.map SparseGridRounding.Program.Input.result)=Input.encode x.input
    simp only [QInput.columns,List.map_ofFn,Function.comp_def]
    rfl)

noncomputable def lawProgram : PolyProgram QInput.encode (ed SparseCounts.ListOperation.et) QInput.result := by
  let get : PolyProgram State.encode (ed SparseCounts.ListOperation.et) (fun x : State => (x.raw view).2) :=
    (snd Context.encode (ed SparseCounts.ListOperation.et)).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
  exact (inputProgram.comp runStateProgram |>.comp get).congr _ (fun _ => rfl)
end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedKernelProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

theorem kernel_result (x : KernelInput) :
    attach (SparseSignedPreparation.Program.view x.z,SparseBundles.Program.QInput.result x.bundles)=x.result := by
  simp only [attach,KernelInput.result,kernel,SparseIntegerLaw.map,SparseIntegerLaw.BinarySparse.raw,
    SparseBundles.Program.QInput.result,KernelInput.bundles,Vector.toList_map,List.map_map,Function.comp_def,view]
noncomputable def kernelProgram : PolyProgram KernelInput.encode (enc : Data PreparedRaw → List Bool) KernelInput.result := by
  let z : PolyProgram KernelInput.encode enc (fun x => SparseSignedPreparation.Program.view x.z) :=
    (snd enc enc).recode KernelInput.raw (fun _ => rfl) (fun _ => rfl)
  exact (z.fanout (bundleInputProgram.comp SparseBundles.Program.lawProgram) |>.comp attach_poly.program).congr _ kernel_result
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OuterLawProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
noncomputable def signedProgram : PolyProgram Input.encode SparseSignedPreparation.Program.Input.encode Input.signed :=
  post_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [post,Input.raw,SparseGridRounding.Program.fractionRow_list,
      SparseSignedPreparation.Program.Input.encode,SparseSignedPreparation.Program.Input.raw,Input.signed])
noncomputable def program : PolyProgram Input.encode (enc : Data SparseSignedPreparation.Program.StateRaw → List Bool) Input.result :=
  (signedProgram.comp SparseSignedPreparation.Program.program).congr _ (fun _ => rfl)
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedLawProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)
noncomputable def kernelsProgram : PolyProgram Input.encode (encodeList KernelInput.encode) Input.kernels := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (r.fanout (outerInputProgram.comp SparseOuterLaw.Program.program) |>.comp kernelRows_poly.program).recode id
    (fun _ => rfl) (fun x => by
      change encodeList enc (kernelRows (x.raw,SparseOuterLaw.Program.Input.result x.outer))=_
      simp only [kernelRows,SparseOuterLaw.Program.Input.result,states_list,List.map_ofFn,Function.comp_def]
      change encodeList enc (List.ofFn (fun i => (x.ker i).raw))=encodeList KernelInput.encode x.kernels
      rw [List.ofFn_comp',RoundingProgram.encodeList_map]; rfl)
noncomputable def weightsProgram : PolyProgram Input.encode el (fun x => (SparseIntegerLaw.BinarySparse.raw x.μ).1) :=
  (outerInputProgram.comp SparseOuterLaw.Program.program |>.comp (fst el (encodeList enc))).congr _ (fun _ => rfl)
noncomputable def program : PolyProgram Input.encode (enc : Data PreparedRaw → List Bool) Input.result :=
  (weightsProgram.fanout (kernelsProgram.comp (kernelProgram.listMap dummy)) |>.comp bindData_poly.program).congr _ bind_result
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierPreparationProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
open SparseIntegerLaw.BinarySparse
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
noncomputable def tablesProgram : PolyProgram Input.encode (enc : List (List ℕ) → List Bool)
    (fun x => (x.S.tables qR).map List.ofFn) := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let states := preparedInputProgram qR |>.comp SparsePrepared.Program.program |>.comp (snd el (encodeList enc))
  exact (r.fanout states |>.comp (tablesData_poly qR).program).congr _ (fun x => by
    simp only [Function.comp_def,tablesData,SparsePrepared.Program.Input.result,List.map_map]
    change ((x.S.law qR).states.toList.map (fun z => countsData qR (x.raw,SparsePrepared.Program.view z)))=_
    simp only [countsData_view,Data.tables,List.map_map,Function.comp_def])
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
noncomputable def scanTablesProgram : PolyProgram ScanInput.encode (enc : List (List ℕ) → List Bool)
    (fun x => (x.S.tables qR).map List.ofFn) :=
  (scanPrepProgram.comp (tablesProgram qR)).congr _ (by intro x; simp only [Function.comp_def,ScanInput.prep])
noncomputable def scanRawPairProgram : PolyProgram ScanInput.encode (enc : ScanRaw × List (List ℕ) → List Bool)
    (fun x => (x.raw,(x.S.tables qR).map List.ofFn)) :=
  ((identity enc).recode ScanInput.raw (fun _ => rfl) (fun _ => rfl)).fanout (scanTablesProgram qR)
noncomputable def scanRawProgram : PolyProgram ScanInput.encode enc
    (fun x => scanData (x.raw,(x.S.tables qR).map List.ofFn)) :=
  scanRawPairProgram qR |>.comp scanData_poly.program
noncomputable def scanInputProgram : PolyProgram ScanInput.encode FixedBatch.RationalParameters.PreparedScanProgram.Input.encode (ScanInput.scan qR) :=
  (scanRawProgram qR).recode id (fun _ => rfl) (fun x => congrArg enc (scanData_view qR x))
noncomputable def scanProgram : PolyProgram ScanInput.encode (enc : Table → List Bool)
    (fun x => ((x.S.scan qR x.df x.dc x.budget).map setView).toList) :=
  (scanInputProgram qR |>.comp (FixedBatch.RationalParameters.PreparedScanProgram.program qR)).congr _ (by
    intro x
    simp only [Function.comp_def,FixedBatch.RationalParameters.PreparedScanProgram.Input.result,ScanInput.scan,Data.scan]
    rfl)
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding
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
noncomputable def program : PolyProgram Input.encode (enc : Table → List Bool) (Input.result p) :=
  (supplierInputProgram p |>.comp (RationalSuppliers.Program.scanProgram p.round)).congr _ (by
    intro x
    simp only [Function.comp_def,Input.result,Input.sup,RationalUnitInput.scan])
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.FractionalRefinement.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
attribute [local irreducible] RationalUnitInput.ScanProgram.Input.result
variable {η τ : ℝ} (p : RationalAllParameters η τ)
noncomputable def masksProgram : PolyProgram Input.encode (enc : Table → List Bool)
    (fun z => RationalUnitInput.ScanProgram.Input.result p z.unit) :=
  @PolyProgram.comp Input RationalUnitInput.ScanProgram.Input Table Input.encode
    RationalUnitInput.ScanProgram.Input.encode enc Input.unit (RationalUnitInput.ScanProgram.Input.result p)
    unitProgram (RationalUnitInput.ScanProgram.program p)
noncomputable def program : PolyProgram Input.encode (enc : Table → List Bool) (Input.result p) :=
  (PolyProgram.comp (g:=imageData)
    (((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.comp (fst enc enc)).fanout (masksProgram p))
    imageData_poly.program).congr _ (imageData_view p)
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ)
attribute [local irreducible] FractionalRefinement.scan Instance.computedFractional
noncomputable def nonzeroRoundProgram : PolyProgram nzEncode (enc : Table → List Bool)
    (fun I => ((I.val.nonzeroRound I.property r hr p C).map setView).toList) :=
  ((((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl)).fanout
    ((scanInputProgram r hr C).comp (FractionalRefinement.ScanProgram.program p))).comp imageData_poly.program).congr
      _ (imageData_view r hr p C)

noncomputable def nonzeroPseudoProgram : PolyProgram nzEncode (enc : Row → List Bool)
    (fun I => setView ((I.val.nonzeroRound I.property r hr p C).getD {I.val.facilities.min' I.val.facilities_nonempty})) :=
  ((((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl)).fanout
    (nonzeroRoundProgram r hr p C)).comp fallbackData_poly.program).congr _ (by
      intro I
      simp only [Function.comp_def,fallbackData,id_eq,singletonData_view]
      cases I.val.nonzeroRound I.property r hr p C <;> rfl)
noncomputable def pseudoProgram : PolyProgram encode (enc : Row → List Bool)
    (fun I => setView (I.computedPseudo r hr p C)) :=
  (dependentIfTotal Instance.zeroTest zeroTestProgram
    (fun I h => setView ((I.nonzeroRound h r hr p C).getD {I.facilities.min' I.facilities_nonempty}))
    (fun I _ => setView I.zeroOutput) (nonzeroPseudoProgram r hr p C)
    (zeroOutputProgram.recode Subtype.val (fun _ => rfl) (fun _ => rfl))).congr _ (by
      intro I
      unfold Instance.computedPseudo
      split_ifs <;> rfl)
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BranchProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration
namespace Branch
def encode (B : Branch) : List Bool := enc B.view
end Branch
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookLevin
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited
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
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeσTmBool_solutions
def inputPrefix (x : Word) : List (P.tm.Γ P.tm.k₀) := (firstWord x).map P.inputAlphabet.invFun
def inputSize (x : Word) : ℕ := (firstWord x).length+p.eval x.length
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookLevin

end OAI
end


