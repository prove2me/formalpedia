-- Prove2me | Definitions.Def_OAIQ053K073
-- name    : OAIQ053K073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:22:46.675597+00:00
-- url     : https://prove2.me/theorems/61434792-7c3a-4b87-bff4-0d8e2ee37408
-- title:
--   Definitions bundle OAIQ053K073 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 30 definitions and 22 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.CloudSpec.emb`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.localCSP`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.padCSP`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.padding`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.regularCSP`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.choose`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.countProgram`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.program`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.startProgram`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.stepProgram`, `OAI.MetricKMedian.RoundingProgram.SignedRound.partialInputsProgram`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.lastProgram`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.program`, `OAI.MetricKMedian.SparseBundles.Program.QInput.result`, `OAI.MetricKMedian.SparseCounts.Program.activeProgram`, `OAI.MetricKMedian.SparseCounts.Program.productProgram`, `OAI.MetricKMedian.SparseGridRounding.Program.cardinalInputProgram`, `OAI.MetricKMedian.SparseOuterLaw.Program.Input.encode`, `OAI.MetricKMedian.SparseOuterLaw.Program.Input.raw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput.encode`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput.raw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.bernoulliInputProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.starInputProgram`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.encode`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.raw`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.result`, `OAI.MetricKMedian.SparseStarActivation.Program.columnsProgram`, `OAI.MetricKMedian.SparseStarActivation.Program.graphProgram`, `OAI.MetricKMedian.SparseTargetSubset.Program.Input.result`, `OAI.MetricKMedian.SparseTargetSubset.Program.program`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_PaddingSpec`, `KMedian_Amplification_RegularSpec`, `KMedian_Expanders_CloudEmbedding`, `KMedian_Expanders_CloudSpec`, `KMedian_Machines_LocalSpec`, `KMedian_Machines_MatchingSpec`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_InstanceZeroProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Projection_RepairProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedRoundProgram`, `KMedian_Rounding_TargetSubsetProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K063`, `OAIQ053K064`, `OAIQ053K066` and `OAIQ053K067` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K075`, `OAIQ053K076`, `OAIQ053K077`, `OAIQ053K078` and `OAIQ053K079`; the statement `OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection_s53`; the proof of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K063
import Definitions.Def_OAIQ053K064
import Definitions.Def_OAIQ053K066
import Definitions.Def_OAIQ053K067

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
lemma endpoint_eq (d : CloudCopies.Dart (E := Fin t.2.length)) :
    endpoint t (dartCode t d)=(CloudCopies.endpoint (C t h) d).val := by
  simp only [endpoint,dartCode,CloudCopies.endpoint,C,CSPTable.csp,CSPTable.row]
  rw [List.getElem?_eq_getElem d.1.isLt]
  cases d with
  | mk e b => cases b <;> rfl
lemma incident_eq (v : CloudCopies.Active (C t h)) :
    incident t v.val.val=((incidentOrder (C t h) (EO t) v).entries.map (fun d => dartCode t d.val)) := by
  unfold incident incidentOrder
  change _=List.map ((dartCode t) ∘ Subtype.val) _
  rw [← List.map_map,Ordered.filter_val,darts_eq,List.filter_map]
  congr 1
  congr 1
  funext d
  simp only [Function.comp_def,endpoint_eq t h,CloudCopies.owner,Subtype.ext_iff,Fin.ext_iff]
lemma nodeCode_eq (p : CloudCopies.Node (C t h)) :
    nodeCode (C t h) (VO t) p=(p.1.val.val,(ExpanderFamily.vertexEquiv _ p.2).val) := by
  unfold nodeCode VO
  apply Prod.ext
  · exact fin_equiv_val _ _ _
  · rfl
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
noncomputable abbrev padding := padEmbed (C t h) (VO t)
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPPaddingSpec

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
noncomputable abbrev emb := FlexibleCloud.dartEmbed (C t h) (cloudEmbed (C t h) (EO t))
lemma emb_incident (v : CloudCopies.Active (C t h)) (d : CloudCopies.Incident (C t h) v) :
    emb t h d.val=⟨v,cloudEmbed (C t h) (EO t) v d⟩ := by
  rcases d with ⟨d,hd⟩
  subst v
  rfl
lemma emb_range (p : CloudCopies.Node (C t h)) :
    p∈Set.range (emb t h) ↔ (ExpanderFamily.vertexEquiv _ p.2).val<(incident t p.1.val.val).length := by
  constructor
  · rintro ⟨d,rfl⟩
    rw [incident_eq t h,List.length_map]
    change (ExpanderFamily.vertexEquiv _ (cloudEmbed (C t h) (EO t) _ ⟨d,rfl⟩)).val<_
    rw [cloudEmbed_index]
    exact List.idxOf_lt_length_iff.mpr ((incidentOrder (C t h) (EO t) _).all ⟨d,rfl⟩)
  · intro hp
    rcases p with ⟨v,p⟩
    rw [incident_eq t h,List.length_map] at hp
    let d := (incidentOrder (C t h) (EO t) v).equiv.symm
      ⟨(ExpanderFamily.vertexEquiv _ p).val,hp⟩
    refine ⟨d.val,?_⟩
    rw [emb_incident t h v d]
    apply congrArg (Sigma.mk v)
    apply (ExpanderFamily.vertexEquiv _).injective
    apply Fin.ext
    rw [cloudEmbed_index]
    calc
      _ = ((incidentOrder (C t h) (EO t) v).equiv d).val := by
        simp only [Ordered.equiv_val,List.idxOf]
        congr 1
        funext x
        simp only [Bool.beq_eq_decide_eq]
      _ = _ := by simp only [d,Equiv.apply_symm_apply]
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
lemma emb_code_lt (d : CloudCopies.Dart (E := Fin t.2.length)) :
    (nodeCode (C t h) (VO t) (emb t h d)).2 <
      (incident t (nodeCode (C t h) (VO t) (emb t h d)).1).length := by
  rw [nodeCode_eq]
  exact (emb_range t h (emb t h d)).mp ⟨d,rfl⟩
lemma row_allowed (e : Fin t.2.length) : (CSPTable.row t e.val).2.2=(C t h).allowed e := by
  simp only [CSPTable.row,List.getElem?_eq_getElem e.isLt,Option.getD_some]
  rfl
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
noncomputable abbrev localCSP := FlexibleCloud.regularCSP (C t h) (cloudEmbed (C t h) (EO t))
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPLocalSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
noncomputable abbrev padCSP := FlexibleRegularization.padded (C t h) (cloudEmbed (C t h) (EO t)) (padding t h)
noncomputable abbrev regularCSP := FlexibleRegularization.csp (C t h) (cloudEmbed (C t h) (EO t)) (padding t h)
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPRegularSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

 theorem stepRaw_state (s : State) : stepRaw s.raw=(s.step).raw := by
  unfold stepRaw State.raw State.step advance
  rw [any_view]
  by_cases h : s.cut.1.Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,Input.raw,nearest_view s.input.R s.cut.1 h]
    apply Prod.ext
    · rfl
    apply Prod.ext
    · simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,
        dite_eq_left (Preparation.firstNearest _ _ h).isLt,mem_filter,Bool.decide_and]
    · simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_insert,Bool.decide_or]
      rw [Bool.or_comm]
      congr 1
      simp only [Fin.ext_iff]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]

noncomputable def stepProgram : PolyProgram State.encode State.encode State.step :=
  stepRaw_poly.program.recode State.raw (fun _ => rfl) (fun s => congrArg enc (stepRaw_state s))

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  have hp : Poly (fun x : Raw => (x,(x.2,x.2.map (fun _ => false)))) := by
    apply pair
    · fun_prop
    · apply pair
      · fun_prop
      · apply list_map <;> fun_prop
  exact hp.program.recode Input.raw (fun _ => rfl) (fun x => by
    change enc (x.raw,(setView x.U,(setView x.U).map (fun _ => false)))=enc (x.raw,(setView x.U,setView ∅))
    simp only [setView,List.map_ofFn,notMem_empty,decide_false,Function.comp_def]
    rfl)
noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n := by
  have hp : Poly (fun x : Raw => x.2.length) := by fun_prop
  exact hp.program.recode Input.raw (fun _ => rfl) (fun x => by simp only [Input.raw,setView,List.length_ofFn]; rfl)
 theorem input_bound (x : Input) : x.n≤x.encode.length := by
  have hh := EncodedList.length_le encodeBool (setView x.U)
  simp only [setView,List.length_ofFn] at hh
  have he : x.encode.length=2*(enc (x.raw.1)).length+1+(enc x.raw.2).length := encodePair_length _ _ _
  change x.n≤(enc (setView x.U)).length at hh
  change x.encode.length=2*(enc x.raw.1).length+1+(enc (setView x.U)).length at he
  omega
 theorem mask_length {n : ℕ} (U : Finset (Fin n)) : (enc (setView U)).length≤3*n := Completion.Rational.PackingProgram.mask_length U
 theorem state_size (x : Input) (t : ℕ) : (State.encode (x.state t)).length≤11*x.encode.length+2 := by
  have h1 := mask_length ((advance x)^[t] (x.U,∅)).1
  have h2 := mask_length ((advance x)^[t] (x.U,∅)).2
  have hn := input_bound x
  change (encodePair Input.encode (encodePair (encodeList encodeBool) (encodeList encodeBool))
    (x,(setView ((advance x)^[t] (x.U,∅)).1,setView ((advance x)^[t] (x.U,∅)).2))).length≤_
  rw [encodePair_length,encodePair_length]
  dsimp only at ⊢
  change (encodeList encodeBool _).length≤3*x.n at h1 h2
  omega

noncomputable def program : PolyProgram Input.encode (encodeList encodeBool)
    (fun x => setView (select x.d x.R x.M x.n x.U)) := by
  let run := stepProgram.repeatFrom startProgram countProgram X (11*X+2)
    (fun x => by simpa using input_bound x)
    (fun x t _ => by rw [state_iterate]; simpa using state_size x t)
  let out : PolyProgram State.encode (encodeList encodeBool) (fun s => setView s.cut.2) :=
    ((snd enc (encodePair (encodeList encodeBool) (encodeList encodeBool))).comp
      (snd (encodeList encodeBool) (encodeList encodeBool))).recode State.raw (fun _ => rfl) (fun _ => rfl)
  exact (run.comp out).congr _ (fun x => by
    dsimp only [Function.comp_def]
    rw [state_iterate]
    change setView (((advance x)^[x.n] (x.U,∅)).2)=_
    rw [advance_result,empty_union])
end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
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

theorem update_view (c : Context) (G : T c) (S : (Fin c.input.n → ℕ)) :
    ListOperation.nextTable ((c.t,view c G),ListOperation.setView S)=view c (update c G S) := by
  apply List.ext_getElem
  · simp only [ListOperation.nextTable,ListOperation.indices,view,ListOperation.view,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj hj'
    have hjm : j < c.input.m := by simpa only [view,ListOperation.view,List.length_ofFn] using hj'
    simp only [ListOperation.nextTable,ListOperation.indices,view,ListOperation.view,ListOperation.setView,List.getElem_map,
      List.getElem_range,List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hjm,Option.getD_some,update]
    split_ifs <;> rfl

theorem rawProduct_eq (x : State) :
    rawProduct (x.ctx.raw,(x.raw view).2)=((x.product).ctx.raw,((x.product).raw view).2) := by
  unfold rawProduct
  rw [rawColumn_eq]
  simp only [Bundle.raw,columnRaw,State.product,prodData,
    states_list,SparseIntegerLaw.prod,Vector.toList_ofFn,List.map_ofFn,List.flatMap_def,
    Function.comp_def,RoundingList.ofFn_product,Context.raw,update_view]
  rfl

noncomputable def productProgram : PolyProgram State.encode State.encode State.product := by
  have hc : Binary.Automatic.Poly rawColumn := by
    unfold rawColumn
    have hm : Binary.Automatic.Poly (fun x : InputRaw × ℕ => x.1.1.map (fun _ => 0)) := by
      apply Binary.Automatic.Poly.list_map <;> fun_prop
    fun_prop
  have hp : Binary.Automatic.Poly rawProduct := by
    unfold rawProduct
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.pair
      · fun_prop
      · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact hp.program.recode (fun x => (x.ctx.raw,(x.raw view).2)) (fun _ => rfl)
    (fun x => congrArg Binary.Automatic.enc (rawProduct_eq x))

noncomputable def activeProgram : PolyProgram State.encode encodeBool
    (fun x : State => decide (x.ctx.t<x.ctx.input.m)) := by
  let raw : PolyProgram (encodePair ei Nat.bits) encodeBool
      (fun x : InputRaw × ℕ => decide (x.2<x.1.2.length)) := Binary.Automatic.Poly.program (by fun_prop)
  let ctx : PolyProgram Context.encode encodeBool (fun c => decide (c.t < c.input.m)) := raw.recode Context.raw (fun _ => rfl)
    (fun c => by simp only [Context.raw,Input.raw,List.length_ofFn])
  exact (contextProgram Context.encode et view).comp ctx
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridRoundingProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
 theorem fractionRow_list {n : ℕ} (q : Fin n → ℚ) : fractionRow (List.ofFn q)=(fraction q).toList := by
  simp only [fractionRow,List.map_ofFn,fraction,base,Function.comp_def,Vector.toList_ofFn]
noncomputable def cardinalInputProgram : PolyProgram Input.encode SparseCardinalRounding.Program.encodeInput Input.cardinal :=
  fractionRow_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    rw [fractionRow_list]
    change enc ((fraction x.q).toList)=enc (List.ofFn (RationalWeightedStep.point (fraction x.q)))
    rw [ofFn_point])

 theorem counts_view {n : ℕ} (q : Fin n → ℚ) (p : Vector ℚ n) :
    counts (List.ofFn q,SparseGraph.ListOperation.setView (SparseCardinalRounding.selected p))=List.ofFn (SparseGridRounding.count q p) := by
  simp only [counts,SparseGraph.ListOperation.indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,Fin.eta,SparseCardinalRounding.selected,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
  rfl
end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BundlesProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram SparseCounts.Program
def QInput.result (x : QInput) : Data SparseCounts.ListOperation.Table :=
  (((SparseBundles.law x.q).law.denominator,List.ofFn (SparseBundles.law x.q).law.numerator),
    (SparseBundles.law x.q).states.toList.map SparseCounts.ListOperation.view)

end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceZeroProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
 theorem subsetRaw_view {n : ℕ} (S T : Finset (Fin n)) : subsetRaw (setView S,setView T)=decide (S⊆T) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subsetRaw,setView,Gaussian.ListOperation.zip_ofFn,List.all_eq_true,List.mem_ofFn,Bool.or_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_true_eq]
  constructor
  · intro h i hi
    have hh : i∉S ∨ i∈T := by simpa only [decide_eq_false_iff_not,decide_eq_true_eq] using h _ ⟨i,rfl⟩
    exact hh.resolve_left (not_not_intro hi)
  · intro h z hz
    obtain ⟨i,rfl⟩ := hz
    by_cases hi : i∈S
    · exact Or.inr (by simpa only [decide_eq_true_eq] using h hi)
    · exact Or.inl (by simpa only [decide_eq_false_iff_not] using hi)

 theorem singletonRaw_view {n : ℕ} (S : Finset (Fin n)) (a : Fin n) : singletonRaw (setView S,a.val)=setView {a} := by
  simp only [singletonRaw,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,mem_singleton,Fin.ext_iff]
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_LastFractionProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList.Last
open Binary Binary.Automatic Binary.Automatic.Poly Finset

 theorem probability_list {n : ℕ} (p : Vector ℚ n) : probability p.toList=RationalLastFraction.probability p := by
  unfold probability RationalLastFraction.probability
  rw [active_list]
  by_cases h : (RationalWeightedStep.fractional p).Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,first_list p h,List.getElem?_eq_getElem
      (show (RationalLastFraction.pick p h).val<p.toList.length by simp),
      Option.getD_some,Vector.getElem_toList,RationalWeightedStep.point]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]

 theorem endpoint_list {n : ℕ} (p : Vector ℚ n) (b : Fin 2) : endpoint (decide (b=1)) p.toList=(RationalLastFraction.endpoint p b).toList := by
  unfold endpoint RationalLastFraction.endpoint
  rw [active_list]
  by_cases h : (RationalWeightedStep.fractional p).Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,first_list p h,indices,Vector.length_toList,range_finRange,
      ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,Vector.toList_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_inj,List.getElem?_eq_getElem (show i.val<p.toList.length by simp),Option.getD_some,Vector.getElem_toList,RationalWeightedStep.point]
    fin_cases b <;> simp
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]
end MetricKMedian.RoundingList.Last

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

 theorem lastRaw_state (x : RoundingProgram.State false) : lastRaw x.raw=(State.last x).raw := by
  change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData _)
  apply congrArg (fun d => (List.ofFn x.β,d))
  exact vectorData_branch x.μ _ RationalLastFraction.probability_unit _ RoundingList.Last.probability
    (RoundingList.Last.endpoint false) (RoundingList.Last.endpoint true)
    RoundingList.Last.probability_list (fun p => RoundingList.Last.endpoint_list p 0)
    (fun p => RoundingList.Last.endpoint_list p 1)
noncomputable def lastProgram : PolyProgram RoundingProgram.State.encode RoundingProgram.State.encode State.last :=
  lastRaw_poly.program.recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun x => by
    rw [lastRaw_state]
    exact RoundingProgram.State.encode_raw _)

noncomputable def program : PolyProgram Input.encode RoundingProgram.State.encode result :=
  (runProgram false |>.comp lastProgram |>.comp (compressProgram false)).congr _ (fun _ => rfl)
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_TargetSubsetProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
 theorem prepare_input (x : Input) : prepare x.raw=x.weighted.raw := by
  simp only [prepare,Input.raw,setView,List.map_ofFn,Function.comp_def,Input.weighted,RoundingProgram.Input.raw,
    initial,Vector.toList_ofFn,decide_eq_true_eq]

def Input.result (x : Input) := SparseGraph.Program.columnRaw (law x.D x.q)
noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.er) Input.result := by
  let p : PolyProgram Input.encode RoundingProgram.Input.encode Input.weighted :=
    prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepare_input x))
  let get : PolyProgram RoundingProgram.State.encode (ed RoundingProgram.erow)
      (fun x : RoundingProgram.State false => RoundingProgram.vectorData x.μ) :=
    (snd RoundingProgram.erow (ed RoundingProgram.erow)).recode RoundingProgram.State.raw
      RoundingProgram.State.encode_raw (fun _ => rfl)
  let post : PolyProgram (ed RoundingProgram.erow) (ed SparseGraph.ListOperation.er)
      (fun x : Data (List ℚ) => (x.1,x.2.map SparseCardinalRounding.Program.selectedRow)) := by
    apply Poly.program
    apply pair
    · fun_prop
    · apply list_map <;> fun_prop
  exact (p.comp RoundingProgram.WeightedRound.program |>.comp get |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,Input.result,law,SparseGraph.Program.columnRaw,SparseIntegerLaw.map,RoundingProgram.vectorData,
      Vector.toList_map,List.map_map,SparseCardinalRounding.Program.selectedRow_eq]
    rfl)
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_StarActivationProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),List.ofFn x.q))
abbrev Input.encode (x : Input) := enc x.raw

 theorem prepare_input (x : Input) : prepare x.raw=x.columns.map SparseTargetSubset.Program.Input.raw := by
  simp only [prepare,Input.raw,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,Input.columns]
  rfl
noncomputable def columnsProgram : PolyProgram Input.encode (encodeList SparseTargetSubset.Program.Input.encode) Input.columns :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    change encodeList enc (prepare x.raw)=_
    rw [prepare_input,RoundingProgram.encodeList_map])

noncomputable def graphProgram : PolyProgram Input.encode SparseGraph.Program.Input.encode Input.graph := by
  let n : PolyProgram Input.encode enc (fun x : Input => x.raw.1) :=
    (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let columns := columnsProgram.comp (SparseTargetSubset.Program.program.listMap dummy)
  exact (n.fanout columns).recode id (fun _ => rfl) (fun x => by
    change SparseGraph.Program.ei (x.raw.1,x.columns.map SparseTargetSubset.Program.Input.result)=_
    simp only [Input.columns,List.map_ofFn,Function.comp_def]
    rfl)

def Input.result (x : Input) : Data Table :=
  (((law x.D x.q).law.denominator,List.ofFn (law x.D x.q).law.numerator),
    (law x.D x.q).states.toList.map SparseGraph.ListOperation.view)
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

noncomputable def partialInputsProgram : PolyProgram Input.encode (encodeList Input.encode) partialInputs := by
  let inputctx := (fst erow erow).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  let part :=  runProgram true
  let rows := part.comp (statesProgram true)
  let raw := (inputctx.fanout rows).comp ((PolyProgram.identity (encodePair erow erow)).listMapWith [] ([],[]))
  exact raw.recode id (fun _ => rfl) (fun x => by
    change encodeList (encodePair erow erow)
      (((x.run x.n).μ.states.toList.map Vector.toList).map (fun p => (List.ofFn x.β,p)))=_
    simp only [states_list,List.map_ofFn,Function.comp_def]
    change encodeList (encodePair erow erow) (List.ofFn fun i =>
      (Input.raw (partialInput x i)))=encodeList Input.encode (List.ofFn (partialInput x))
    rw [List.ofFn_comp',encodeList_map])

end SignedRound
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedPreparationProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
def KernelInput.raw (x : KernelInput) : KernelRaw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),x.p.toList))
abbrev KernelInput.encode (x : KernelInput) := enc x.raw

noncomputable def starInputProgram : PolyProgram KernelInput.encode SparseStarActivation.Program.Input.encode KernelInput.star :=
  (identity enc).recode KernelInput.raw (fun _ => rfl) (fun x => by
    simp only [SparseStarActivation.Program.Input.encode,SparseStarActivation.Program.Input.raw,
      KernelInput.star,point_list]; rfl)
noncomputable def bernoulliInputProgram : PolyProgram KernelInput.encode SparseBernoulli.Program.Input.encode KernelInput.bernoulli :=
  ((snd enc enc).comp (snd enc enc)).recode KernelInput.raw (fun _ => rfl) (fun x => by
    simp only [SparseBernoulli.Program.Input.encode,KernelInput.bernoulli,point_list]; rfl)

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OuterLawProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),(List.ofFn x.c,List.ofFn x.q)))
abbrev Input.encode (x : Input) := enc x.raw
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RepairProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRepairProgram
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic RegularProgram CloudProgram
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
noncomputable def choose (t : CSPTable A) (v : ℕ) (d : Port) : A×A :=
  (legal t v d).toList.headD default
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRepairProgram

end OAI
end


