-- Prove2me | Definitions.Def_OAIQ053K077
-- name    : OAIQ053K077
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:25:21.375386+00:00
-- url     : https://prove2.me/theorems/adbf1bc7-d6eb-42bf-b572-cd78ba67adaa
-- title:
--   Definitions bundle OAIQ053K077 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 21 definitions, 7 instances and 9 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM_1`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_1`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_2`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_3`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_1`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_2`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_3`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_1`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_2`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_3`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedKTmBool_solutions`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedQueryKTmBoolΓΛσM`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedValueKTmBoolΓΛσM`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.projection`, `OAI.MetricKMedian.PCP.CookLevin.instFintypeKTmBool_solutions`, `OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions`, `OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions_1`, `OAI.MetricKMedian.PCP.CookLevin.instFintypeσTmBool_solutions`, `OAI.MetricKMedian.Reduction.Program.Branch.view`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_Amplification_PaddingSpec`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/PaddingSpec.lean), [`KMedian_CookLevin_CookAmplify`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookAmplify.lean), [`KMedian_CookLevin_CookBoundaryProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookBoundaryProgram.lean), [`KMedian_CookLevin_CookBox`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookBox.lean), [`KMedian_CookLevin_CookClockProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookClockProgram.lean), [`KMedian_CookLevin_CookLevin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookLevin.lean), [`KMedian_CookLevin_CookTable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookTable.lean), [`KMedian_CookLevin_TableauRelationProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/TableauRelationProgram.lean), [`KMedian_Expanders_CloudEmbedding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Expanders/CloudEmbedding.lean), [`KMedian_Expanders_CloudSpec`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Expanders/CloudSpec.lean), [`KMedian_Programs_BranchProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/BranchProgram.lean), [`KMedian_Projection_RegularTable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/RegularTable.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K070`, `OAIQ053K072`, `OAIQ053K073` and `OAIQ053K074` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K080` and `OAIQ053K081`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K070
import Definitions.Def_OAIQ053K072
import Definitions.Def_OAIQ053K073
import Definitions.Def_OAIQ053K074

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
lemma cloud_table (v : CloudCopies.Active (C t h)) :
    cloud t v.val.val=RotationTable.table (ExpanderFamily.graph (CloudCopies.depth (C t h) v))
      (ExpanderFamily.vertexEquiv (CloudCopies.depth (C t h) v)) := by
  unfold cloud
  rw [Expander.generate_table]
  have hi : (incident t v.val.val).length=Fintype.card (CloudCopies.Incident (C t h) v) := by
    rw [incident_eq,List.length_map,Ordered.length_card]
  change (fun n => RotationTable.table (ExpanderFamily.graph n) (ExpanderFamily.vertexEquiv n)) _ = _
  congr 1
  simp only [CloudCopies.depth,List.length_map,List.length_tail,hi]
  apply congrArg ExpanderFamily.level
  apply congrArg (fun n : ℕ => n-1)
  exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
lemma cloud_length (v : CloudCopies.Active (C t h)) :
    (cloud t v.val.val).length=(Fintype.card ExpanderFamily.Branch)^(CloudCopies.depth (C t h) v) := by
  rw [cloud_table t h,RotationTable.table_length]
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
lemma padding_code (p : CloudCopies.Node (C t h)) :
    vertexCode t h (padding t h p)=((nodeOrder (C t h) (VO t)).equiv p).val := by
  simp only [vertexCode,padding,padEmbed,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply,Fin.castLEEmb_apply,Fin.val_castLE]
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPPaddingSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudEmbedding
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype
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
lemma dartIndex_eq (v : CloudCopies.Active (C t h)) (d : CloudCopies.Incident (C t h) v) :
    dartIndex t v.val.val (dartCode t d.val)=((incidentOrder (C t h) (EO t) v).equiv d).val := by
  unfold dartIndex
  rw [incident_eq t h]
  rw [Ordered.index_coded _ (fun e : CloudCopies.Incident (C t h) v => dartCode t e.val) ((dartCode_injective t).comp Subtype.val_injective) d]
  congr 1
  funext q
  simp only [Prod.ext_iff]
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudEmbedding

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BranchProgram
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
def view (B : Branch) : Raw × Row := (InstanceProgram.view B.original,setView B.facilities)
end Branch
end MetricKMedian.Reduction.Program
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
local instance instFintypeKTmBool_solutions : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions : Fintype P.tm.σ := P.tm.σFin
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookLevin

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookClockProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookClockProgram
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau
open scoped Classical

lemma poly_encodeNat : Poly (MetricKMedian.encodeNat) := by
  have hb : Poly Nat.bits := ⟨PolyProgram.natAsList⟩
  have ht : Poly (fun n : ℕ => n.bits.map (fun _=>true)) := Poly.list_map (Automatic.Poly.const _) hb
  apply poly_congr (Poly.list_append.comp (Poly.pair
    (Poly.list_append.comp (Poly.pair ht (Automatic.Poly.const [false]))) hb))
  intro n
  simp only [MetricKMedian.encodeNat,List.map_const',List.append_assoc]
variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
local instance instFintypeKTmBool_solutions_r2e09e9_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_r2e09e9_1 : Fintype P.tm.σ := P.tm.σFin
lemma poly_wordUnits : Poly (fun x : Word => x.map (fun _=>())) := Poly.list_map (Automatic.Poly.const _) Poly.identity
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookClockProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookBox
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookBox

namespace MetricKMedian.PCP.CookLevin
open Turing Turing.TM2 Function Finset
open Complexity Tableau
open scoped Classical

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_1_r2e09e9_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_1 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_1_r2e09e9_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable instance valueInhabited : Inhabited (Value P.tm.m) :=
  ⟨((none,P.tm.initialState),((none,P.tm.initialState),fun _ => ⟨[],by simp⟩),fun _ => none)⟩
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookBox

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRelationProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauRelationProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
omit [Fintype K] [DecidableEq K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma poly_category : Poly (category M) := by
  have hi : Poly (fun i : ℕ => min i (2*radius M)) := by fun_prop
  have hh := Poly.list_getD_comp (⟨0,by omega⟩ : Fin (2*radius M+1))
    (Automatic.Poly.const (List.finRange (2*radius M+1))) hi
  apply poly_congr hh
  intro i
  rw [List.getElem?_eq_getElem (by simp only [List.length_finRange]; omega)]
  simp only [Option.getD_some,List.getElem_finRange,category,Fin.ext_iff,Fin.val_cast]
variable {X : Type} [Coding X] [Coding K] [Hardcoded K]
lemma poly_rawAccept (B : X→Boundary (Γ := Γ) (Λ := Λ) (σ := σ))
    (hf : Poly (fun x => firstControlSet M (B x)))
    (hl : Poly (fun x => lastControlSet M (B x)))
    (hfc : Poly (fun p : (X×K)×ℕ => firstCellSet M (B p.1.1) p.1.2 p.2))
    (hlc : Poly (fun p : (X×K)×ℕ => lastCellSet M (B p.1.1) p.1.2 p.2)) :
    Poly (fun p : X×TC (K := K) => rawAccept M (B p.1) p.2) := by
  have he (i : Fin 9) : Poly (fun t : Fin 9 => decide (t=i)) := hardcoded _
  have hs : Poly (fun k : K => Finset.univ.filter (fun z : Query M→Value M => (z (q0 M)).2.2 k=none → (z (q1 M)).2.2 k=none)) := hardcoded _
  have hn : Poly (fun k : K => Finset.univ.filter (fun z : Query M→Value M => (z (q0 M)).2.2 k=none)) := hardcoded _
  have hu : Poly (fun p : K×Fin (2*radius M+1) => Finset.univ.filter (fun z : Query M→Value M =>
    (z (q1 M)).2.2 p.1=cellTable M p.1 p.2 ((z (q0 M)).2.1.2 p.1) (fun h => (z (qwin M h)).2.2 p.1))) := hardcoded _
  have hc := poly_category M
  have he' (i : Fin 9) : Poly (fun p : X×TC (K := K) => decide (p.2.1=i)) :=
    (he i).comp (by fun_prop)
  unfold rawAccept
  apply Poly.ite_prop (he' 0)
  · exact hs.comp (by fun_prop)
  apply Poly.ite_prop (he' 1)
  · exact hn.comp (by fun_prop)
  apply Poly.ite_prop (he' 2) (Automatic.Poly.const _)
  apply Poly.ite_prop (he' 3) (Automatic.Poly.const _)
  apply Poly.ite_prop (he' 4)
  · exact hu.comp (Poly.pair (by fun_prop) (hc.comp (by fun_prop)))
  apply Poly.ite_prop (he' 5) (hf.comp Poly.fst)
  apply Poly.ite_prop (he' 6) (hl.comp Poly.fst)
  exact Poly.ite_prop (he' 7) (hfc.comp (show Poly (fun p : X×TC (K := K) => ((p.1,p.2.2.2.1),p.2.2.2.2)) by fun_prop))
    (hlc.comp (show Poly (fun p : X×TC (K := K) => ((p.1,p.2.2.2.1),p.2.2.2.2)) by fun_prop))
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauRelationProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookBoundaryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookBoundaryProgram
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory FiniteList Turing Turing.TM2
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_1 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable instance tapeCoding : Coding P.tm.K := finiteCoding _
noncomputable instance tapeHardcoded : Hardcoded P.tm.K := ⟨fun _ _ _ f=>finite_function f⟩
noncomputable instance symbolCoding (k : P.tm.K) : Coding (P.tm.Γ k) := finiteCoding _
noncomputable instance symbolHardcoded (k : P.tm.K) : Hardcoded (P.tm.Γ k) := ⟨fun _ _ _ f=>finite_function f⟩
instance inputSymbolInhabited : Inhabited (P.tm.Γ P.tm.k₀) := ⟨P.inputAlphabet.invFun false⟩
instance outputSymbolInhabited : Inhabited (P.tm.Γ P.tm.k₁) := ⟨P.outputAlphabet.invFun false⟩
lemma poly_certificateBound : Poly (fun x : Word=>p.eval x.length) := by
  have h := Poly.list_length.comp ((poly_unaryPolynomial p).comp poly_wordUnits)
  apply poly_congr h
  intro x; simp only [List.length_replicate,List.length_map]
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookBoundaryProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookTable
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_2 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_2 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_2 : Fintype P.tm.σ := P.tm.σFin
local instance instInhabitedKTmBool_solutions : Inhabited P.tm.K := ⟨P.tm.k₀⟩
local instance instInhabitedValueKTmBoolΓΛσM : Inhabited (Value P.tm.m) := ⟨((none,P.tm.initialState),((none,P.tm.initialState),fun _=>⟨[],Nat.zero_le _⟩),fun _=>none)⟩
local instance instInhabitedQueryKTmBoolΓΛσM : Inhabited (Query P.tm.m) := ⟨q0 P.tm.m⟩
noncomputable local instance instDecidableEqQueryKTmBoolΓΛσM : DecidableEq (Query P.tm.m) := Classical.decEq _
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookAmplify
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookAmplify
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_3 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_3 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_3 : Fintype P.tm.σ := P.tm.σFin
noncomputable local instance instDecidableEqQueryKTmBoolΓΛσM_1 : DecidableEq (Query P.tm.m) := Classical.decEq _
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookAmplify

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RegularTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRegularTable
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic RegularProgram CloudProgram ProjectionTable
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] [Coding A] [Hardcoded A]

variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable def projection := (CloudSpec.regularCSP t h).projection
  (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRegularTable

end OAI
end


