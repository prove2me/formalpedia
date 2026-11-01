-- Prove2me | Definitions.Def_OAIQ053K083
-- name    : OAIQ053K083
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:31:18.124995+00:00
-- url     : https://prove2.me/theorems/af8deaa0-a92c-4e41-8deb-9548c129bbb0
-- title:
--   Definitions bundle OAIQ053K083 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 9 definitions and 11 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.SeedProgram.output`, `OAI.MetricKMedian.Reduction.Program.Branch.allowedProgram`, `OAI.MetricKMedian.Reduction.Program.Branch.restrictedProgram`, `OAI.MetricKMedian.Reduction.Program.allListProgram`, `OAI.MetricKMedian.Reduction.Program.branchListProgram`, `OAI.MetricKMedian.Reduction.Program.branchProgram`, `OAI.MetricKMedian.Reduction.Program.goodProgram`, `OAI.MetricKMedian.Reduction.Program.ordinaryProgram`, `OAI.MetricKMedian.Reduction.Program.selectedProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_CookLevin_SeedInput`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/SeedInput.lean), [`KMedian_Programs_BranchProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/BranchProgram.lean), [`KMedian_Projection_RegularTable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/RegularTable.lean), [`KMedian_Projection_RepairProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/RepairProgram.lean), [`KMedian_Projection_SeedSound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/SeedSound.lean), [`KMedian_Projection_SeedTables`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/SeedTables.lean), [`KMedian_Reduction_OrdinaryListProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/OrdinaryListProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K080` and `OAIQ053K081` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K084`; the statement `OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53`; the proofs of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53` and `OAI.MetricKMedian.factor_above_threshold_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K080
import Definitions.Def_OAIQ053K081

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RepairProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
variable [Coding A]
omit [Coding A]
variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
omit [Inhabited A] in
lemma legal_correct (v : GlobalRegularization.Node (CloudSpec.C t h)) (d : Port) (a : A×A) :
    a∈legal t (CloudSpec.vertexCode t h v) d ↔ (CloudSpec.regularCSP t h).Legal (v,d) a := by
  rw [legal,Finset.mem_filter,CloudSpec.allowed_correct,CloudSpec.rotate_correct]
  change a∈_ ∧ ((ExpanderFamily.vertexEquiv _ ((CloudSpec.regularGraph t h).rotate (v,d)).1).val=(ExpanderFamily.vertexEquiv _ v).val → a.1=a.2) ↔ _
  simp only [Fin.val_inj,Equiv.apply_eq_iff_eq,PortCSP.Legal]
lemma choose_legal (v : GlobalRegularization.Node (CloudSpec.C t h)) (d : Port) (hh : (legal t (CloudSpec.vertexCode t h v) d).Nonempty) :
    (CloudSpec.regularCSP t h).Legal (v,d) (choose t (CloudSpec.vertexCode t h v) d) := by
  apply (legal_correct t h v d _).mp
  unfold choose
  apply Finset.mem_toList.mp
  cases he : (legal t (CloudSpec.vertexCode t h v) d).toList with
  | nil => exact False.elim (hh.ne_empty (Finset.toList_eq_nil.mp he))
  | cons a as => simp only [List.headD_cons,List.mem_cons,eq_self,true_or]
lemma repair_correct (v : GlobalRegularization.Node (CloudSpec.C t h)) (d : Port) (a : A×A) :
    repair t (CloudSpec.vertexCode t h v) d a=(CloudSpec.regularCSP t h).repair
      (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2) (v,d) a := by
  unfold repair PortCSP.repair
  simp only [legal_correct t h]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma global_length : (global t).length=(Fintype.card ExpanderFamily.Branch)^(GlobalRegularization.depth (CloudSpec.C t h)) := by
  rw [CloudSpec.global_table t h]
  simp only [RotationTable.table,List.length_ofFn]
omit [Inhabited A] in
lemma allLegal_correct : allLegal t=true ↔ ∀ p : GlobalRegularization.Node (CloudSpec.C t h)×Port,
    (legal t (CloudSpec.vertexCode t h p.1) p.2).Nonempty := by
  simp only [allLegal,List.all_eq_true,List.mem_range,decide_eq_true_eq]
  rw [global_length t h]
  constructor
  · intro hh p
    exact hh _ (ExpanderFamily.vertexEquiv _ p.1).isLt _ ((Ordered.fixed Port).all p.2)
  · intro hh i hi d hd
    have h := hh ((ExpanderFamily.vertexEquiv _).symm ⟨i,hi⟩,d)
    simpa only [CloudSpec.vertexCode,Equiv.apply_symm_apply] using h
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRepairProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RegularTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

omit [Coding A] [Hardcoded A] in
lemma edgeRow_correct (v : GlobalRegularization.Node (CloudSpec.C t h)) (s : Port×Bool) :
    edgeRow t (CloudSpec.vertexCode t h v) s=
      ((rootEquiv t h ((projection t h).edge.symm (v,s)).1).val,(projection t h).project ((projection t h).edge.symm (v,s))) := by
  have hh := (SeedCombinators.numbered_correct (CloudSpec.regularGraph t h) (CloudSpec.regularCSP t h)
    (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2) (rotate (A:=A)) (repair (A:=A)) t
    (nodeEquiv t h) (Fintype.equivFin Port) (fun v d=>by simpa only [nodeEquiv,CloudSpec.vertexCode,PortGraph.step,PortGraph.back] using CloudSpec.rotate_correct t h v d) (fun v d a=>by simpa only [nodeEquiv,CloudSpec.vertexCode] using repair_correct t h v d a) v s)
  simpa only [edgeRow,rootEquiv,nodeEquiv,CloudSpec.vertexCode,projection] using hh

omit [Coding A] [Hardcoded A] in
lemma regularTable_build : regularTable t=build (projection t h) (rootEquiv t h) (nodeOrder t h) (Ordered.fixed (Port×Bool)) := by
  have hh := rows_build (projection t h) (m:=(Fintype.card ExpanderFamily.Branch)^(GlobalRegularization.depth (CloudSpec.C t h)))
    (k:=Fintype.card Port) (rootEquiv t h) (nodeEquiv t h) (Ordered.fixed (Port×Bool))
    (global t) (global_length t h) (edgeRow t)
    (fun v s=>by simpa only [nodeEquiv,CloudSpec.vertexCode] using edgeRow_correct t h v s)
  simpa only [regularTable,nodeOrder] using hh
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRegularTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedSound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedSound
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Amplifier ProjectionSeed CloudOrder
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
lemma chosen_legal (hl : allLegal t=true) : ∀ p, (CloudSpec.regularCSP t h).Legal p
    (choose t (CloudSpec.vertexCode t h p.1) p.2) := by
  intro p
  exact choose_legal t h p.1 p.2 ((allLegal_correct t h).mp hl p)
lemma good_consistent (hl : allLegal t=true) : (good t h).Consistent :=
  BiProjection.consistent_prod _ _ ((CloudSpec.regularCSP t h).projection_consistent _ (chosen_legal t h hl))
    (BiProjection.neutral_consistent _ _ _ _)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedSound

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedTables
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedTables
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
lemma goodTable_build : goodTable t=build (good t h) (goodRoot t h) (goodNodes t h) portOrder := by
  unfold goodTable
  rw [regularTable_build t h]
  exact product_build (projection t h) (BiProjection.neutral Bool Bool Bool Bool)
    (rootEquiv t h) (Fintype.equivFin Bool) (nodeOrder t h) (Ordered.fixed Bool)
    (Ordered.fixed (RegularProgram.Port×Bool)) (Ordered.fixed Bool)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_SeedInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedInput
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable def output (n : ℕ) : Coverage.ProjectionInput (Width n) (LeftSize n) (RightSize n) :=
  if hl : allLegal t=true then
    input ((good t h).power n) (nestedEquiv (goodRoot t h) n) ((goodNodes t h).nested n)
      (portOrder.nested n) (leftOrder.nested n) (rightOrder.nested n)
      ((good t h).consistent_power (good_consistent t h hl) n)
  else input (ProjectionSeed.bad.power n) (nestedEquiv badRoot n) (badNodes.nested n)
      (portOrder.nested n) (leftOrder.nested n) (rightOrder.nested n)
      (ProjectionSeed.bad.consistent_power ProjectionSeed.bad_consistent n)
lemma output_raw (n : ℕ) : (output t h n).raw=
    raw (leftOrder.nested n) (rightOrder.nested n) (power (seedTable t) n) := by
  unfold output seedTable
  split_ifs with hl
  · rw [input_raw,goodTable_build t h,power_build]
  · rw [input_raw,badTable,power_build]
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

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
noncomputable def allowedProgram : PolyProgram encode encodeBool (fun B => decide B.allowed) :=
  (by fun_prop : Poly (fun x : Raw × Row => decide (x.1.2.1 ≤ card x.2))).program.recode view (fun _ => rfl) (fun B => by
    apply congrArg encodeBool
    simp only [view,InstanceProgram.view,card_view,allowed]
    rfl)
noncomputable def restrictedProgram : PolyProgram (fun B : {B : Branch // B.allowed} => encode B.val) InstanceProgram.encode
    (fun B => B.val.restricted B.property) :=
  restrictedData_poly.program.recode
    (fun B : {B : Branch // B.allowed} => B.val.view) (fun _ => rfl)
    (fun B => congrArg enc (restrictedData_view B.val B.property))
end Branch
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
noncomputable def goodProgram : PolyProgram (fun B : {B : Branch // B.allowed} => Branch.encode B.val)
    (enc : Table → List Bool) (fun B => (outcomes B.val.original B.val.facilities
      ((B.val.restricted B.property).computedPseudo r hr p c) δ c b).map setView) :=
  (((identity enc).recode (fun B : {B : Branch // B.allowed} => B.val.view) (fun _ => rfl) (fun _ => rfl)).fanout
    (Branch.restrictedProgram.comp (InstanceProgram.pseudoProgram r hr p c)) |>.comp
      (by fun_prop : Poly (fun x : (Raw × Row) × Row => outcomesData δ c b (x.1.1,(x.1.2,x.2)))).program).congr
      _ (fun B => outcomesData_view B.val.original B.val.facilities _ δ c b)
noncomputable def branchProgram : PolyProgram Branch.encode (enc : Table → List Bool)
    (fun B => (branchOut r hr p c b δ B).map setView) :=
  (dependentIfTotal Branch.allowed Branch.allowedProgram (fun _ _ => ([] : Table))
    (fun B h => (outcomes B.original B.facilities ((B.restricted h).computedPseudo r hr p c) δ c b).map setView)
    (constant _ enc []) (goodProgram r hr p c b δ)).congr _ (by
      intro B
      unfold branchOut
      split_ifs <;> rfl)
noncomputable def branchListProgram : PolyProgram InstanceProgram.encode (encodeList Branch.encode) (branchList a) :=
  (by
    have h : Poly (fun x : Raw => (branchesData a (x,x.1.2)).map (fun F => (x,F))) := by
      apply list_map <;> fun_prop
    exact h.program.recode InstanceProgram.view (fun _ => rfl) (fun I => by
      unfold branchList
      change encodeList enc ((branchesData a (view I,setView I.facilities)).map (fun F => (view I,F)))=_
      rw [branchesData_view]
      simp only [encodeList_map,List.map_map,Function.comp_def,Branch.encode,Branch.view]))
noncomputable def allListProgram : PolyProgram InstanceProgram.encode (enc : Table → List Bool)
    (fun I => (allList r hr p c a b δ I).map setView) :=
  ((branchListProgram a).comp ((branchProgram r hr p c b δ).listMapTotal) |>.comp
    (listFlatten enc ([] : Row))).congr _ (by
      intro I
      simp only [Function.comp_def,branchList,List.map_map,List.flatMap,allList,List.map_flatten])
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_OrdinaryListProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.distance_client_facility
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
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
noncomputable def selectedProgram : PolyProgram InstanceProgram.encode (enc : Row → List Bool)
    (fun I => setView (selectList I (allList r hr p c a b δ I))) :=
  ((((identity enc).recode view (fun _ => rfl) (fun _ => rfl)).fanout (allListProgram r hr p c a b δ)).comp
    selectData_poly.program).congr _ (fun I => selectData_view I _)
noncomputable def ordinaryProgram : PolyProgram InstanceProgram.encode (enc : Row → List Bool)
    (fun I => setView (ordinarySet r hr p c a b δ I)) :=
  (PolyProgram.ite InstanceProgram.zeroTestProgram (selectedProgram r hr p c a b δ)
    InstanceProgram.zeroOutputProgram).congr _ (by
      intro I
      unfold ordinarySet
      by_cases h : I.zeroTest <;> simp [h])
end MetricKMedian.Reduction.Program
end

end OAI
end


