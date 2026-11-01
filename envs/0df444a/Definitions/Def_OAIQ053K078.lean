-- Prove2me | Definitions.Def_OAIQ053K078
-- name    : OAIQ053K078
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:25:10.522085+00:00
-- url     : https://prove2.me/theorems/26029baa-7217-402f-8f4c-f56aca8273ab
-- title:
--   Definitions bundle OAIQ053K078 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 11 definitions and 31 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.ProjectionTable.input`, `OAI.MetricKMedian.PCP.Compiler.ProjectionTable.raw`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.edgeRow`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.goodTable`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.regularTable`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.repair`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.seedTable`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.coupled`, `OAI.MetricKMedian.Preparation.RationalSuppliers.coupled`, `OAI.MetricKMedian.Reduction.Program.algorithm`, `OAI.MetricKMedian.Reduction.Program.branchList`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_CookLevin_SeedInput`, `KMedian_CookLevin_TableauDirectoryProgram`, `KMedian_CookLevin_TableauQueryProgram`, `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_RestrictionProgram`, `KMedian_Projection_PowerTable`, `KMedian_Projection_ProductTable`, `KMedian_Projection_RegularTable`, `KMedian_Projection_RepairProgram`, `KMedian_Projection_SeedTables`, `KMedian_Projection_Tables`, `KMedian_Reduction_LocalCompletionProgram`, `KMedian_Reduction_OrdinaryListProgram`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K070`, `OAIQ053K072`, `OAIQ053K073` and `OAIQ053K074` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K081`; the statement `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible_s53`; the proofs of `OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry_s53` and `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K070
import Definitions.Def_OAIQ053K072
import Definitions.Def_OAIQ053K073
import Definitions.Def_OAIQ053K074

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Tables
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionTables
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace ProjectionTable
variable {U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable (G : BiProjection U V D S A B) {nu : ℕ} (ue : U≃Fin nu) (vo : Ordered V) (so : Ordered S)
variable (ao : Ordered A) (bo : Ordered B)
noncomputable def raw (t : ProjectionTable A B) : Coverage.ProjectionRaw :=
  (t.1.map (fun _=>false),t.2.map (fun row => row.map (fun e =>
    (e.1,ao.entries.map (fun a => (bo.equiv (e.2 a)).val)))))
omit [DecidableEq A] in
lemma poly_raw [Nonempty B] : Poly (raw ao bo) := by
  let : Inhabited B := Classical.inhabited_of_nonempty inferInstance
  have hh : Poly (fun f : A→B => ao.entries.map (fun a => (bo.equiv (f a)).val)) := hardcoded _
  unfold raw
  apply Poly.pair
  · exact Poly.list_map (Automatic.Poly.const _) Poly.fst
  · apply Poly.list_map _ Poly.snd
    apply Poly.list_map _ Poly.snd
    exact Poly.pair (Poly.fst.comp Poly.snd) (hh.comp (Poly.snd.comp Poly.snd))
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
noncomputable def input (hc : G.Consistent) : Coverage.ProjectionInput so.entries.length ao.entries.length bo.entries.length :=
  (indexed G ue vo so ao bo).input (nu_pos ue) (order_pos vo) (order_pos so) (order_pos ao) (order_pos bo)
    (G.reindex_consistent _ _ _ _ _ _ hc)
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B] [Nonempty D] in
lemma input_raw (hc : G.Consistent) : (input G ue vo so ao bo hc).raw=raw ao bo (build G ue vo so) := by
  simp only [Coverage.ProjectionInput.raw,input,BiProjection.input,BiProjection.system,indexed,
    BiProjection.reindex,build,raw,List.map_replicate]
  simp only [Ordered.map_entries, List.map_ofFn, Function.comp_def, Prod.map, Prod.eta,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]
end ProjectionTable
end MetricKMedian.PCP.Compiler

end Inline_PCPProjectionTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_ProductTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionProductTable
namespace MetricKMedian.PCP.Compiler.ProjectionTable
open Binary Binary.Automatic
open scoped Classical

variable {A B A' B' : Type} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [Inhabited B] [Inhabited B']
lemma poly_combine : Poly (fun z : (ℕ×ProjectionRow A B)×ProjectionRow A' B' =>combine z.1.1 z.1.2 z.2) := by
  have hh : Poly (fun p : (A→B)×(A'→B') =>fun a : A×A'=>(p.1 a.1,p.2 a.2)) := hardcoded _
  exact Poly.pair (by fun_prop) (hh.comp (Poly.pair (Poly.snd.comp (Poly.snd.comp Poly.fst)) (Poly.snd.comp Poly.snd)))
lemma poly_product : Poly (fun p : ProjectionTable A B×ProjectionTable A' B' =>product p.1 p.2) := by
  unfold product
  apply Poly.pair
  · exact Poly.list_flatMap (by fun_prop) (by fun_prop)
  · apply Poly.list_flatMap _ (by fun_prop)
    apply Poly.list_map _ (by fun_prop)
    apply Poly.list_flatMap _ (by fun_prop)
    apply Poly.list_map _ (by fun_prop)
    exact poly_combine.comp (Poly.pair (Poly.pair (by fun_prop) (Poly.snd.comp (Poly.fst))) Poly.snd)
end MetricKMedian.PCP.Compiler.ProjectionTable

end Inline_PCPProjectionProductTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_PowerTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionPowerTable
namespace MetricKMedian.PCP
open scoped Classical

namespace Compiler
open Binary Binary.Automatic

namespace ProjectionTable
variable {A B : Type} [Fintype A] [Fintype B] [Inhabited B]
lemma poly_power (n : ℕ) : Poly (fun t : ProjectionTable A B=>power t n) := by
  induction n with
  | zero => exact Automatic.Poly.const _
  | succ n ih => exact poly_product.comp (Poly.pair Poly.identity ih)
end ProjectionTable
end Compiler
end MetricKMedian.PCP

end Inline_PCPProjectionPowerTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RepairProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
noncomputable def repair (t : CSPTable A) (v : ℕ) (d : Port) (a : A×A) : A×A :=
  if a∈legal t v d then a else choose t v d
variable [Coding A]
lemma poly_choose : Poly (fun z : (CSPTable A×ℕ)×Port =>choose z.1.1 z.1.2 z.2) := by
  have hh : Poly (fun s : Finset (A×A)=>s.toList.headD default) := hardcoded _
  exact hh.comp poly_legal
lemma poly_repair [Hardcoded A] : Poly (fun z : ((CSPTable A×ℕ)×Port)×(A×A) =>repair z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have hh : Poly (fun z : Finset (A×A)×(A×A) =>decide (z.2∈z.1)) := hardcoded _
  exact Poly.ite_prop (hh.comp (Poly.pair (poly_legal.comp Poly.fst) Poly.snd)) Poly.snd (poly_choose.comp Poly.fst)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRepairProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RegularTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

noncomputable def edgeRow (t : CSPTable A) (v : ℕ) (s : Port×Bool) : ProjectionRow (A×A) A :=
  SeedCombinators.numbered (rotate (A:=A)) (repair (A:=A)) (fun d : Port=>(Fintype.equivFin Port d).val)
    (Fintype.card Port) t v s
lemma poly_edgeRow : Poly (fun z : (CSPTable A×ℕ)×(Port×Bool) =>edgeRow z.1.1 z.1.2 z.2) := by
  have hi : Poly (fun d : Port=>(Fintype.equivFin Port d).val) := hardcoded _
  unfold edgeRow
  with_reducible exact (SeedCombinators.poly_numbered (T:=CSPTable A) (D:=Port) (A:=A)
    (rotate (A:=A)) (repair (A:=A)) _ _ (poly_rotate (A:=A)) (poly_repair (A:=A)) hi)

noncomputable def regularTable (t : CSPTable A) : ProjectionTable (A×A) A :=
  ((global t).flatMap (fun _=>List.replicate (Fintype.card Port) ()),
    (List.range (global t).length).map (fun v => (Ordered.fixed (Port×Bool)).entries.map (edgeRow t v)))
lemma poly_regularTable : Poly (regularTable (A:=A)) := by
  unfold regularTable
  apply Poly.pair
  · exact Poly.list_flatMap (Automatic.Poly.const _) (poly_global (A:=A))
  · exact Poly.list_map (Poly.list_map (poly_edgeRow (A:=A)) (Automatic.Poly.const _)) (Poly.list_indices.comp (poly_global (A:=A)))

end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRegularTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedTables
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedTables
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

noncomputable def goodTable (t : CSPTable Label) : ProjectionTable ProjectionSeed.LeftLabel ProjectionSeed.RightLabel :=
  product (regularTable t) neutralTable
lemma poly_goodTable : Poly goodTable := by
  exact (poly_product (A:=Label×Label) (B:=Label) (A':=Bool) (B':=Bool)).comp
    (Poly.pair (poly_regularTable (A:=Label)) (Automatic.Poly.const neutralTable))
noncomputable def seedTable (t : CSPTable Label) : ProjectionTable ProjectionSeed.LeftLabel ProjectionSeed.RightLabel :=
  if allLegal t then goodTable t else badTable
lemma poly_seedTable : Poly seedTable := Poly.ite (poly_allLegal (A:=Label)) poly_goodTable (Automatic.Poly.const badTable)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_SeedInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
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
lemma poly_output_raw (n : ℕ) : Poly (fun t : CSPTable Label=>
    raw (leftOrder.nested n) (rightOrder.nested n) (power (seedTable t) n)) :=
  (poly_raw _ _).comp ((poly_power n).comp poly_seedTable)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierPreparation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

noncomputable def coupled (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (p c : Fin n → ℚ) (γ g : ℚ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hm : ∀ t, ∑ i ∈ P t, y i=p t) (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/8) (hunit : ∀ t, p t+c t=1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hg : 0 < g) (heven : Even Δ) (hgrid : g*(Δ:ℚ)=1) :
    CoupledLaw (targets A) flag
      (weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ)
      P (fun i => (y i : ℝ)) (fun t => (p t : ℝ)) (fun t => (c t : ℝ))
      g γ (∑ i, (y i : ℝ)) Δ := by
  have hcR : ∀ t, ∑ i ∈ A t, (y i : ℝ)=(c t : ℝ) := by
    intro t
    exact_mod_cast hc t
  have huR : ∀ t, (p t : ℝ)+(c t : ℝ)=1 := by
    intro t
    exact_mod_cast hunit t
  have hmR : ∀ t, ∑ i ∈ P t, (y i : ℝ)=(p t : ℝ) := by
    intro t
    exact_mod_cast hm t
  have mean : ∀ t, (g : ℝ)*(SparseOuterLaw.targetMean (D A) (q y P A c γ g) t : ℝ) =
      (1+(γ:ℝ))*(c t : ℝ) := by
    intro t
    simp only [SparseOuterLaw.targetMean, Rat.cast_sum, mul_sum]
    calc
      _ = ∑ e, if t ∈ targets A (index e) then
          weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) else 0 := by
        apply sum_congr rfl
        intro e _
        change (g:ℝ) * ((if t ∈ targets A (index e) then q y P A c γ g e else 0 : ℚ):ℝ) = _
        split_ifs <;> simp only [scaled_q y P A c γ g hg.ne', Rat.cast_zero, mul_zero]
      _ = _ := by
        rw [(index (f:=f) (n:=n)).sum_comp (fun e => if t ∈ targets A e then
          weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ e else 0)]
        exact targeted_weight _ _ _ _ _ hP hcR t
  have planned : (g : ℝ) * (((n:ℚ)*(Δ:ℚ) +
      (∑ e, SparseSignedPreparation.signed (D A) a e * q y P A c γ g e) : ℚ) : ℝ) =
      (∑ i, (y i : ℝ)) - (γ:ℝ)*∑ t, (c t : ℝ) := by
    have hgR : (g:ℝ)*(Δ:ℝ)=1 := by exact_mod_cast hgrid
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sum, mul_add, mul_sum]
    have hf : (g:ℝ)*((n:ℝ)*(Δ:ℝ))=(n:ℝ) := by nlinarith only [hgR]
    rw [hf]
    have he : (∑ e, (g:ℝ) * ((SparseSignedPreparation.signed (D A) a e : ℝ) *
        (q y P A c γ g e : ℝ))) = ∑ e,
        (flag (index e) - ((targets A (index e)).card : ℝ)) *
        weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) := by
      apply sum_congr rfl
      intro e _
      rw [mul_left_comm, scaled_q y P A c γ g hg.ne']
      simp only [SparseSignedPreparation.signed, Rat.cast_sub, Rat.cast_natCast, D, a,
        Function.comp_apply, flag_cast]
    rw [he, (index (f:=f) (n:=n)).sum_comp (fun e =>
      (flag e - ((targets A e).card : ℝ)) *
        weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ e)]
    simpa only [Fintype.card_fin, mul_sum] using raw_identity (fun i => (y i : ℝ)) P A
      (fun t => (c t : ℝ)) (γ:ℝ) hP hcR (fun t => by rw [hmR]; exact huR t)
  let L := SparsePrepared.coupled (D A) a (q y P A c γ g) Δ P y p a_bounds
    (q_nonneg y P A c γ g hy hc0 hγ.le hg.le) g (fun t => (c t : ℝ)) γ
    (∑ i, (y i : ℝ)) hg (by exact_mod_cast hγ) (by exact_mod_cast hγ1) heven hgrid
    hy hp hm (fun t => by exact_mod_cast hc0 t) (fun t => by
      have hh : (c t : ℝ) ≤ ((1/8:ℚ):ℝ) := Rat.cast_le.mpr (hc1 t)
      norm_num at hh ⊢
      exact hh)
    huR mean planned
  have L' : CoupledLaw (targets A ∘ index) (flag ∘ index)
      (weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ ∘ index)
      P (fun i => (y i : ℝ)) (fun t => (p t : ℝ)) (fun t => (c t : ℝ))
      g γ (∑ i, (y i : ℝ)) Δ := by
    exact L.castWeights (funext (fun e => flag_cast (index e)))
      (funext (fun e => scaled_q y P A c γ g hg.ne' e))
  exact L'.reindexStars index

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

noncomputable def coupled (heven : Even qR.Δ) := RationalSuppliers.coupled D.y D.P D.A D.p D.c D.γ qR.g qR.Δ
  D.hy D.hp D.hP D.hm D.hc D.hc0 D.hc1 D.hunit D.hγ D.hγ1 (FixedParameters.positive qR) heven (FixedParameters.grid qR)

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BoundedEnumerationProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
 theorem choicesRaw_view {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : choicesRaw c (setView T)=
    ((words c (List.ofFn (T.orderEmbOfFin rfl))).map List.toFinset).map setView := by
  unfold choicesRaw
  rw [Preparation.RationalUnitInput.Program.ranks_view]
  have hr : List.ofFn (fun a => (T.orderEmbOfFin rfl a).val)=(List.ofFn (T.orderEmbOfFin rfl)).map Fin.val := by simp only [List.map_ofFn,Function.comp_def]
  rw [hr,words_map,List.map_map,List.map_map]
  apply List.map_congr_left
  intro ys _
  exact maskWord_view T ys
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RestrictionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
 theorem choicesRaw_choices {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : choicesRaw c (setView T)=(choices T c).map setView :=
  choicesRaw_view T c

 theorem arcpairs_view {n : ℕ} (T : Finset (Fin n)) : arcpairs (setView T)=(pairs T).map (fun p => (p.1.val,p.2.val)) := by
  unfold arcpairs
  rw [Preparation.RationalUnitInput.Program.ranks_view]
  have hr : List.ofFn (fun a => (T.orderEmbOfFin rfl a).val)=(List.ofFn (T.orderEmbOfFin rfl)).map Fin.val := by simp only [List.map_ofFn,Function.comp_def]
  rw [hr]
  simp only [pairs,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

 theorem restrictData_view (I : Instance) (F : Finset (Fin I.n)) (ps : List (Fin I.n × Fin I.n)) :
    restrictData (view I,(setView F,ps.map (fun p => (p.1.val,p.2.val))))=setView (witnessedRestriction I F ps.toFinset) := by
  simp only [restrictData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,Bool.and_eq_true,decide_eq_true_eq,
    witnessedRestriction,mem_filter,List.map_map,List.all_map,List.all_eq_true,id_eq,List.mem_toFinset]

 theorem branchesData_view (I : Instance) (F : Finset (Fin I.n)) (a : ℕ) :
    branchesData a (view I,setView F)=(branches I F a).map setView := by
  simp only [branchesData,arcpairs_view,words_map,List.map_map,Function.comp_def,branches,restrictData_view]
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_LocalCompletionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view insert insert_view)
open Enumeration

 theorem getDist_view (I : Instance) (i j : Fin I.n) : getDist (view I,(i.val,j.val))=I.distance i j := by
  simp only [getDist,view,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

 theorem candidatesData_view (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) (t : Fin I.n) :
    candidatesData (((view I,(setView F,setView B)),(List.ofFn r,δ)),t.val)=setView (rationalCandidates I F r δ t) := by
  simp only [candidatesData,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext a
  change (get (setView F) a.val && decide (getDist (view I,(t.val,a.val))≤δ*((List.ofFn r)[t.val]?.getD 0)))=decide _
  rw [get_view,getDist_view]
  simp only [List.getElem?_ofFn,dite_eq_left t.isLt,Option.getD_some,Fin.eta,rationalCandidates,mem_filter,Bool.decide_and]

 theorem pickData_view {n : ℕ} (w : Fin n → ℚ) (K : Finset (Fin n)) :
    pickData (List.ofFn w,setView K)=setView (pickSingleton K w) := by
  unfold pickData pickSingleton
  rw [Completion.Rational.PackingProgram.any_view]
  by_cases h : K.Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,nearest_view w K h,InstanceProgram.singletonRaw_view]
    rfl
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h,setView,List.map_ofFn,Function.comp_def,notMem_empty,decide_false]

end MetricKMedian.Reduction.Program
end

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
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def branchList (I : Instance) : List Branch := (branches I I.facilities a).map (fun F => ⟨I,F⟩)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_OrdinaryListProgram
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
def algorithm (I : Instance) : List Bool := setView (ordinarySet r hr p c a b δ I)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauDirectoryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauDirectoryProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic
open scoped Classical

@[fun_prop] lemma poly_append_comp {X A : Type} [Coding X] [Coding A] [Inhabited A]
    {f g : X→List A} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x++g x) :=
  Poly.list_append.comp (Poly.pair hf hg)
@[fun_prop] lemma poly_and_comp {X : Type} [Coding X] {f g : X→Bool}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => f x && g x) :=
  Poly.bool_and.comp (Poly.pair hf hg)
variable {K : Type} [Fintype K] [DecidableEq K] [Coding K] [Hardcoded K] [Inhabited K] (k0 : K)
@[fun_prop] lemma poly_range_succ : Poly (fun xs : List Unit => List.range (xs.length+1)) := by
  have h : Poly (fun xs : List Unit => List.range (xs++[()]).length) := Poly.list_indices.comp (Poly.list_append.comp (Poly.pair Poly.identity (Automatic.Poly.const [()])))
  simpa only [List.length_append,List.length_singleton] using h
@[fun_prop] lemma poly_range_comp {X A : Type} [Coding X] [Coding A] [Inhabited A]
    {f : X→List A} (hf : Poly f) : Poly (fun x => List.range (f x).length) := Poly.list_indices.comp hf
@[fun_prop] lemma poly_range_succ_comp {X : Type} [Coding X] {f : X→List Unit}
    (hf : Poly f) : Poly (fun x => List.range ((f x).length+1)) := poly_range_succ.comp hf
omit [DecidableEq K] [Hardcoded K] in
lemma poly_vars : Poly (fun p : List Unit×List Unit => vars k0 p.1.length p.2.length) := by
  have ht : Poly (fun p : List Unit×List Unit => List.range (p.1.length+1)) := poly_range_succ.comp Poly.fst
  have hl : Poly (fun p : List Unit×List Unit => List.range (p.2.length+1)) := poly_range_succ.comp Poly.snd
  have ht0 : Poly (fun p : List Unit×List Unit => List.range p.1.length) := Poly.list_indices.comp Poly.fst
  unfold vars
  repeat' first | assumption | exact Automatic.Poly.const _ | apply poly_append_comp | apply Poly.list_map | apply Poly.list_flatMap | assumption
  all_goals fun_prop
omit [DecidableEq K] [Hardcoded K] in
lemma poly_clauses : Poly (fun p : List Unit×List Unit => clauses k0 p.1.length p.2.length) := by
  have ht : Poly (fun p : List Unit×List Unit => List.range (p.1.length+1)) := poly_range_succ.comp Poly.fst
  have hl : Poly (fun p : List Unit×List Unit => List.range (p.2.length+1)) := poly_range_succ.comp Poly.snd
  have ht0 : Poly (fun p : List Unit×List Unit => List.range p.1.length) := Poly.list_indices.comp Poly.fst
  have hl0 : Poly (fun p : List Unit×List Unit => List.range p.2.length) := Poly.list_indices.comp Poly.snd
  unfold clauses
  repeat' first | assumption | exact Automatic.Poly.const _ | apply poly_append_comp | apply Poly.list_map | apply Poly.list_flatMap | assumption
  all_goals fun_prop
omit [DecidableEq K] [Hardcoded K] in
lemma poly_boundaries : Poly (fun xs : List Unit => boundaries k0 xs.length) := by
  have hl : Poly (fun xs : List Unit => List.range (xs.length+1)) := poly_range_succ
  unfold boundaries
  repeat' first | assumption | exact Automatic.Poly.const _ | apply poly_append_comp | apply Poly.list_map | apply Poly.list_flatMap | assumption
  all_goals fun_prop
omit [DecidableEq K] [Hardcoded K] in
lemma poly_tests : Poly (fun p : List Unit×List Unit => tests k0 p.1.length p.2.length) :=
  Poly.list_append.comp (Poly.pair (poly_clauses k0) ((poly_boundaries k0).comp Poly.snd))
omit [Inhabited K] in
lemma poly_code_eq (n : ℕ) : Poly (fun p : (Fin n×(ℕ×(K×ℕ)))×(Fin n×(ℕ×(K×ℕ))) => decide (p.1=p.2)) := by
  have hf : Poly (fun p : Fin n×Fin n => decide (p.1=p.2)) := hardcoded _
  have hk : Poly (fun p : K×K => decide (p.1=p.2)) := hardcoded _
  simpa only [Prod.ext_iff,Bool.decide_and] using
    (show Poly (fun p : (Fin n×(ℕ×(K×ℕ)))×(Fin n×(ℕ×(K×ℕ))) =>
      decide (p.1.1=p.2.1) && (decide (p.1.2.1=p.2.2.1) &&
        (decide (p.1.2.2.1=p.2.2.2.1) && decide (p.1.2.2.2=p.2.2.2.2)))) from by
      apply poly_and_comp
      · exact hf.comp (show Poly (fun p : (Fin n×(ℕ×(K×ℕ)))×(Fin n×(ℕ×(K×ℕ))) => (p.1.1,p.2.1)) by fun_prop)
      · apply poly_and_comp
        · fun_prop
        · apply poly_and_comp
          · exact hk.comp (show Poly (fun p : (Fin n×(ℕ×(K×ℕ)))×(Fin n×(ℕ×(K×ℕ))) => (p.1.2.2.1,p.2.2.2.1)) by fun_prop)
          · fun_prop)
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauDirectoryProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauQueryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauQueryProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
variable [Coding K] [Hardcoded K] [Inhabited K]
omit [Fintype σ] [∀ k, Fintype (Γ k)] [Hardcoded K] in
lemma poly_rawQuery : Poly (fun p : ((ℕ×ℕ)×TC (K := K))×Query M => rawQuery M k0 p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have he (i : Fin 9) : Poly (fun t : Fin 9 => decide (t=i)) := hardcoded _
  have he' (i : Fin 9) : Poly (fun p : (ℕ×ℕ)×TC (K := K) => decide (p.2.1=i)) :=
    (he i).comp (by fun_prop)
  have hb : ∀ q : Query M, Poly (fun p : (ℕ×ℕ)×TC (K := K) => rawQuery M k0 p.1.1 p.1.2 p.2 q) := by
    intro q
    unfold rawQuery
    apply Poly.ite_prop (he' 0)
    · split_ifs <;> fun_prop
    · apply Poly.ite_prop (he' 1) (by fun_prop)
      apply Poly.ite_prop (he' 2)
      · rcases q with ⟨⟩ | ⟨⟩ | ⟨k,j⟩ | h <;> dsimp only <;> fun_prop
      · apply Poly.ite_prop (he' 3)
        · split_ifs <;> fun_prop
        · apply Poly.ite_prop (he' 4)
          · rcases q with ⟨⟩ | ⟨⟩ | ⟨k,j⟩ | h <;> dsimp only <;> fun_prop
          · apply Poly.ite_prop (he' 5) (by fun_prop)
            apply Poly.ite_prop (he' 6) (by fun_prop)
            exact Poly.ite_prop (he' 7) (by fun_prop) (by fun_prop)
  exact (poly_finite_cases _ hb).comp (Poly.pair Poly.snd Poly.fst)
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauQueryProgram

end OAI
end


