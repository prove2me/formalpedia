-- Prove2me | Definitions.Def_OAIQ053K084
-- name    : OAIQ053K084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:34:44.844577+00:00
-- url     : https://prove2.me/theorems/bec5781a-5d14-422f-b2ef-60c89b62e81f
-- title:
--   Definitions bundle OAIQ053K084 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 4 definitions and 15 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.CookProgram.projection`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.projectionProgram`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.spaceUnits`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.timeUnits`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_CookLevin_CookAmplify`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookAmplify.lean), [`KMedian_CookLevin_CookBoundaryProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookBoundaryProgram.lean), [`KMedian_CookLevin_CookClockProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookClockProgram.lean), [`KMedian_CookLevin_CookTable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookTable.lean), [`KMedian_PCP_UniformProjection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/PCP/UniformProjection.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K082` and `OAIQ053K083` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete_s53`; the proofs of `OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53` and `OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K082
import Definitions.Def_OAIQ053K083

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookClockProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.testNonempty _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookClockProgram
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
local instance instFintypeKTmBool_solutions_r7d234b_1 : Fintype P.tm.K := P.tm.kFin
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions
local instance instFintypeσTmBool_solutions_r7d234b_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable def timeUnits (x : Word) : List Unit := List.replicate (time P p x) ()
noncomputable def spaceUnits (x : Word) : List Unit := List.replicate (space P p x) ()
lemma poly_inputUnits : Poly (inputUnits p) := by
  have h1 := poly_wordUnits.comp poly_firstWord
  have h2 := (poly_unaryPolynomial p).comp poly_wordUnits
  apply poly_congr (Poly.list_append.comp (Poly.pair h1 h2))
  intro x
  apply unitList_eq_length
  simp only [List.length_append,List.length_map,List.length_replicate,inputUnits,inputSize]
lemma poly_timeUnits : Poly (timeUnits P p) := by
  apply poly_congr ((poly_unaryPolynomial P.time).comp (poly_inputUnits p))
  intro x
  simp only [inputUnits,List.length_replicate,timeUnits,time]
lemma poly_spaceUnits : Poly (spaceUnits P p) := by
  have hr : Poly (fun x : Word => (timeUnits P p x).flatMap (fun _=>List.replicate (radius P.tm.m) ())) :=
    Poly.list_flatMap (Automatic.Poly.const _) (poly_timeUnits P p)
  apply poly_congr (Poly.list_append.comp (Poly.pair
    (Poly.list_append.comp (Poly.pair (poly_inputUnits p) hr)) (Automatic.Poly.const [()])))
  intro x
  apply unitList_eq_length
  simp only [List.length_append,List.length_singleton,spaceUnits,List.length_replicate,inputUnits]
  rw [length_flatMap_uniform _ _ (radius P.tm.m) (by intros; simp)]
  simp only [timeUnits,List.length_replicate,space,Nat.mul_comm]
lemma poly_time : Poly (time P p) := by
  apply poly_congr (Poly.list_length.comp (poly_timeUnits P p))
  intro x; simp only [timeUnits,List.length_replicate]
lemma poly_space : Poly (space P p) := by
  apply poly_congr (Poly.list_length.comp (poly_spaceUnits P p))
  intro x; simp only [spaceUnits,List.length_replicate]
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookClockProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookBoundaryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
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
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_1
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_1
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_1
lemma poly_firstCell :
    Poly (fun z : (Word×P.tm.K)×ℕ=>firstCellSet P.tm.m (boundary P p z.1.1) z.1.2 z.2) := by
  have he : Poly (fun k : P.tm.K => decide (k=P.tm.k₀)) := hardcoded _
  have hc : Poly (fun k : P.tm.K => Finset.univ.filter (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 k=none)) := hardcoded _
  have hh := Poly.ite_prop (he.comp (Poly.snd.comp Poly.fst : Poly (fun z : (Word×P.tm.K)×ℕ=>z.1.2)))
    ((poly_firstCell_fixed P p P.tm.k₀).comp (Poly.pair (Poly.fst.comp Poly.fst) Poly.snd))
    (hc.comp (Poly.snd.comp Poly.fst))
  apply poly_congr hh
  rintro ⟨⟨x,k⟩,i⟩
  by_cases hk : k=P.tm.k₀
  · simp only [hk,ite_true]
  · rw [ite_eq_right hk]
    ext a
    simp [firstCellSet,boundary,initList,prefixCell,hk]

lemma poly_lastCell_fixed (k : P.tm.K) :
    Poly (fun z : Word×ℕ=>lastCellSet P.tm.m (boundary P p z.1) k z.2) := by
  by_cases hk : k=P.tm.k₁
  · subst k
    have hh := FiniteList.poly_getFilter (fun _ : Word=>[P.outputAlphabet.invFun true])
      (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 P.tm.k₁) (Automatic.Poly.const _)
    apply poly_congr hh
    intro z
    ext a
    simp [lastCellSet,boundary,haltList]
  · apply poly_congr (Automatic.Poly.const (Finset.univ.filter (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 k=none)))
    intro z
    ext a
    simp [lastCellSet,boundary,haltList,hk]
lemma poly_lastCell :
    Poly (fun z : (Word×P.tm.K)×ℕ=>lastCellSet P.tm.m (boundary P p z.1.1) z.1.2 z.2) := by
  have he : Poly (fun k : P.tm.K => decide (k=P.tm.k₁)) := hardcoded _
  have hc : Poly (fun k : P.tm.K => Finset.univ.filter (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 k=none)) := hardcoded _
  have hh := Poly.ite_prop (he.comp (Poly.snd.comp Poly.fst : Poly (fun z : (Word×P.tm.K)×ℕ=>z.1.2)))
    ((poly_lastCell_fixed P p P.tm.k₁).comp (Poly.pair (Poly.fst.comp Poly.fst) Poly.snd))
    (hc.comp (Poly.snd.comp Poly.fst))
  apply poly_congr hh
  rintro ⟨⟨x,k⟩,i⟩
  by_cases hk : k=P.tm.k₁
  · simp only [hk,ite_true]
  · rw [ite_eq_right hk]
    ext a
    simp [lastCellSet,boundary,haltList,hk]

lemma poly_accept : Poly (fun z : Word×TC (K:=P.tm.K)=>rawAccept P.tm.m (boundary P p z.1) z.2) := by
  let : Inhabited P.tm.K := ⟨P.tm.k₀⟩
  apply poly_rawAccept P.tm.m (boundary P p)
  · change Poly (fun _ : Word => Finset.univ.filter (fun z : Query P.tm.m→Value P.tm.m => (z (q0 P.tm.m)).1=(some P.tm.main,P.tm.initialState)))
    exact Automatic.Poly.const _
  · change Poly (fun _ : Word => Finset.univ.filter (fun z : Query P.tm.m→Value P.tm.m => (z (q0 P.tm.m)).1=(none,P.tm.initialState)))
    exact Automatic.Poly.const _
  · exact poly_firstCell P p
  · exact poly_lastCell P p
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookBoundaryProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
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
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedValueKTmBoolΓΛσM
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedQueryKTmBoolΓΛσM
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma poly_vars : Poly (vars P p) := by
  apply poly_congr ((TableauDirectory.poly_vars P.tm.k₀).comp (Poly.pair (poly_timeUnits P p) (poly_spaceUnits P p)))
  intro x; simp only [vars,timeUnits,spaceUnits,List.length_replicate]
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma poly_tests : Poly (tests P p) := by
  apply poly_congr ((TableauDirectory.poly_tests P.tm.k₀).comp (Poly.pair (poly_timeUnits P p) (poly_spaceUnits P p)))
  intro x; simp only [tests,timeUnits,spaceUnits,List.length_replicate]
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma poly_query : Poly (fun z : (Word×TC (K:=P.tm.K))×Query P.tm.m =>query P p z.1.1 z.1.2 z.2) := by
  exact (poly_rawQuery P.tm.m P.tm.k₀).comp
    (Poly.pair (Poly.pair (Poly.pair ((poly_time P p).comp (Poly.fst.comp Poly.fst))
      ((poly_space P p).comp (Poly.fst.comp Poly.fst))) (Poly.snd.comp Poly.fst)) Poly.snd)
lemma poly_table : Poly (table P p) := by
  have ha : Poly (fun z : Word×TC (K:=P.tm.K)=>accept P p z.1 z.2) := by
    unfold accept
    with_reducible exact poly_accept P p
  unfold table
  with_reducible
    exact LocalCompiler.poly_table (X:=Word) (VC:=VC (K:=P.tm.K)) (TC:=TC (K:=P.tm.K))
      (Q:=Query P.tm.m) (A:=Value P.tm.m) (vars P p) (tests P p) (query P p) (accept P p)
      (poly_vars P p) (poly_tests P p) (poly_query P p) ha
      (poly_code_eq (K:=P.tm.K) 3) (poly_code_eq (K:=P.tm.K) 9)
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
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM_1
lemma poly_initial : Poly (initial P p) :=
  (InitialProgram.poly_table (FiniteCSP.Label (Q:=Query P.tm.m) (A:=Value P.tm.m))).comp (poly_table P p)
lemma poly_amplified : Poly (amplified P p) := AmplifierProgram.poly_generate.comp (poly_initial P p)
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookAmplify

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_UniformProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPUniformProjection
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_4_r7d234b_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_4_r7d234b_1 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_4_r7d234b_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable local instance instDecidableEqQueryKTmBoolΓΛσM_2_r7d234b_1 : DecidableEq (Query P.tm.m) := Classical.decEq _
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instNonemptyFinLengthCSPRowLabelSndListUnitAmplified
noncomputable def projection (n : ℕ) (x : Word) :
    Coverage.ProjectionInput (SeedProgram.Width n) (SeedProgram.LeftSize n) (SeedProgram.RightSize n) :=
  SeedProgram.output (amplified P p x) (amplified_valid P p x) n
noncomputable def projectionProgram (n : ℕ) :
    PolyProgram id Coverage.ProjectionInput.encode (projection P p n) :=
  (BooleanLists.packProgram.comp ((SeedProgram.poly_output_raw n).comp (poly_amplified P p)).program).recode
    id (fun _=>rfl) (fun x=>by
      change enc (ProjectionTable.raw (SeedProgram.leftOrder.nested n) (SeedProgram.rightOrder.nested n)
        (ProjectionTable.power (SeedProgram.seedTable (amplified P p x)) n))=enc (projection P p n x).raw
      rw [projection,SeedProgram.output_raw])
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPUniformProjection

end OAI
end


