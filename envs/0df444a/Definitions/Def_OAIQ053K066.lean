-- Prove2me | Definitions.Def_OAIQ053K066
-- name    : OAIQ053K066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:17:29.985892+00:00
-- url     : https://prove2.me/theorems/1d3e88de-eb44-489e-a08c-76ffe8a39091
-- title:
--   Definitions bundle OAIQ053K066 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 32 definitions and 20 theorems. The definitions and types are `OAI.MetricKMedian.InputParser.parseProgram`, `OAI.MetricKMedian.LPBinary.Repair.rawProgram`, `OAI.MetricKMedian.LPBinary.Scale.candidateProgram`, `OAI.MetricKMedian.LPBinary.Scale.feasibleProgram`, `OAI.MetricKMedian.LPBinary.Scale.selectedProgram`, `OAI.MetricKMedian.LPBinary.Scale.selectedScaleProgram`, `OAI.MetricKMedian.LPBinary.Scale.valueOfProgram`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.C`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.Input.raw`, `OAI.MetricKMedian.RoundingProgram.Terminal.result`, `OAI.MetricKMedian.SparseBernoulli.Program.probabilityProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.rowProbability`, `OAI.MetricKMedian.SparseBundles.Program.columnsProgram`, `OAI.MetricKMedian.SparseCounts.Program.Context.encode`, `OAI.MetricKMedian.SparseCounts.Program.Context.raw`, `OAI.MetricKMedian.SparseCounts.Program.Input.encode`, `OAI.MetricKMedian.SparseCounts.Program.Input.raw`, `OAI.MetricKMedian.SparseCounts.Program.InputRaw`, `OAI.MetricKMedian.SparseCounts.Program.State.encode`, `OAI.MetricKMedian.SparseCounts.Program.columnRaw`, `OAI.MetricKMedian.SparseCounts.Program.countProgram`, `OAI.MetricKMedian.SparseCounts.Program.dimensionsProgram`, `OAI.MetricKMedian.SparseCounts.Program.ei`, `OAI.MetricKMedian.SparseCounts.Program.featuresProgram`, `OAI.MetricKMedian.SparseCounts.Program.incrementProgram`, `OAI.MetricKMedian.SparseCounts.Program.rawColumn`, `OAI.MetricKMedian.SparseCounts.Program.rawProduct`, `OAI.MetricKMedian.SparseCounts.Program.startProgram`, `OAI.MetricKMedian.SparseCounts.Program.view`, `OAI.MetricKMedian.SparseGridRounding.Program.Input.encode`, `OAI.MetricKMedian.SparseTargetSubset.Program.Input.encode`, `OAI.MetricKMedian.SparseTargetSubset.Program.Input.raw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_NumericParserProgram`, `KMedian_Binary_SequentialParserProgram`, `KMedian_Expanders_CloudSpec`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_FractionalSelectProgram`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_CountListOperations`, `KMedian_Process_CountRunProgram`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_RationalSortProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Rounding_TargetSubsetProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K054`, `OAIQ053K055`, `OAIQ053K056`, `OAIQ053K057` and `OAIQ053K058` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K071`, `OAIQ053K072`, `OAIQ053K073` and `OAIQ053K074`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K054
import Definitions.Def_OAIQ053K055
import Definitions.Def_OAIQ053K056
import Definitions.Def_OAIQ053K057
import Definitions.Def_OAIQ053K058

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_NumericParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
 theorem ratRead_rest_length (xs : List Bool) : (ratRead xs).2.length≤xs.length :=
  (natRead_rest_length _).trans ((natRead_rest_length _).trans (by simp only [List.length_tail]; omega))
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_SequentialParserProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.finCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
section Generic
variable {α : Type} [Coding α] [Inhabited α] (read : List Bool → α × List Bool)
variable (P : PolyProgram enc enc read) (hrest : ∀ xs, (read xs).2.length≤xs.length)
noncomputable def parseProgram : PolyProgram enc enc (parse read) := by
  have h : Poly (fun x : List Unit × List Bool => (x.1,(x.2,([] : List α)))) := by fun_prop
  have hv : Poly (List.reverse : List α → List α) := ⟨listReverse enc default⟩
  have g : Poly (fun x : State (α:=α) => (x.2.reverse,x.1)) := pair (Poly.comp hv snd) fst
  exact h.program.comp (foldProgram read P hrest) |>.comp g.program
end Generic
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudSpec
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
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
noncomputable abbrev C := t.csp h
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
noncomputable def rawProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode eo (raw r) := by
  let ds := Program.inputRaw.comp (fst ers Nat.bits)
  let H := (Program.inputRaw.comp (Program.rawPenaltyProgram r)).comp ratOfNat
  let ρ := Program.inputRaw.comp (lossProgram r)
  let y := Program.optimizeProgram r hr
  let tr := (ds.fanout H).comp Program.truncateMatrixProgram
  let xs := (tr.fanout y).comp nearestRowsProgram
  exact (((y.fanout ρ).comp openingProgram).fanout ((ds.fanout xs).comp assignmentsProgram)).congr _ (fun _ => rfl)
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalSelectProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

noncomputable def candidateProgram (r : ℕ) (hr : 0 < r) :
    PolyProgram (encodePair Input.encode Ratio.encode) Repair.eo (fun x : Input × ℚ => candidate r x.1 x.2) := by
  let test := ((constant (encodePair Input.encode Ratio.encode) Ratio.encode 0).fanout (snd Input.encode Ratio.encode)).comp ratLT
  exact (ite test ((fst Input.encode Ratio.encode).comp Input.zeroOutputProgram)
    (Input.scaleProgram.comp (Repair.rawProgram r hr))).congr _ (fun _ => by
      simp only [Function.comp_apply,candidate,decide_eq_true_eq])

noncomputable def valueOfProgram (r : ℕ) (hr : 0 < r) :
    PolyProgram (encodePair Input.encode Ratio.encode) Ratio.encode (fun x : Input × ℚ => Repair.value (candidate r x.1 x.2) x.1.rows) :=
  (((candidateProgram r hr).fanout ((fst Input.encode Ratio.encode).comp (Program.inputRaw.comp (fst ers Nat.bits)))).comp Repair.valueProgram).congr _ (fun _ => rfl)

noncomputable def feasibleProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode er (feasible r) := by
  let k := (fst Input.encode Ratio.encode).comp (Program.inputRaw.comp (snd ers Nat.bits))
  let test := (((candidateProgram r hr).fanout k).comp Repair.validProgram)
  let guesses := (Program.inputRaw.comp (fst ers Nat.bits)).comp guessesProgram
  let emptyI : Input := ⟨1,1,1,by decide,by decide,by decide,le_rfl,fun _ _ => 0⟩
  exact (((identity Input.encode).fanout guesses).comp (test.listFilterWith 0 emptyI)).congr _ (fun _ => rfl)

noncomputable def selectedScaleProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode Ratio.encode (selectedScale r) := by
  let xs := feasibleProgram r hr
  let values := (((identity Input.encode).fanout xs).comp ((valueOfProgram r hr).listMapWith 0 0))
  let v := values.comp Program.minimumProgram
  let ec := encodePair Input.encode Ratio.encode
  let I := (fst ec Ratio.encode).comp (fst Input.encode Ratio.encode)
  let q := snd ec Ratio.encode
  let C := (I.fanout q).comp (valueOfProgram r hr)
  let V := (fst ec Ratio.encode).comp (snd Input.encode Ratio.encode)
  let test := (C.fanout V).comp ratEQ
  let emptyI : Input := ⟨1,1,1,by decide,by decide,by decide,le_rfl,fun _ _ => 0⟩
  let filtered := ((((identity Input.encode).fanout v).fanout xs).comp (test.listFilterWith 0 (emptyI,0)))
  exact (filtered.comp Program.minimumProgram).congr _ (fun _ => rfl)

noncomputable def selectedProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode Repair.eo (selected r) :=
  ((((identity Input.encode).fanout (selectedScaleProgram r hr)).comp (candidateProgram r hr))).congr _ (fun _ => rfl)

end Scale
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierListOperations
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.MaskProgram.get_view
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)

 theorem targetsData_view {f n : ℕ} (S : Data f n) :
    targetsData (supplierView S)=List.ofFn (fun e => setView (D S.A e)) := by
  rw [show (fun e => setView (D S.A e))=(fun e => setView (SupplierStars.targets S.A (index e))) by rfl,ofFn_star (fun e => setView (SupplierStars.targets S.A e))]
  simp only [targetsData,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    List.flatMap_def,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,SupplierStars.targets,
    setView,mem_filter,mem_univ,true_and,mem_singleton]
  simp only [Fin.val_inj]

 theorem flagsData_view {f n : ℕ} (S : Data f n) : flagsData (supplierView S)=List.ofFn (a (f:=f) (n:=n)) := by
  change _=List.ofFn (fun e => flagQ (index e))
  rw [ofFn_star]
  simp only [flagsData,supplierView,List.flatMap_def,List.map_ofFn,Function.comp_def,flagQ]

 theorem outsideData_view {f n : ℕ} (S : Data f n) (i : Fin f) :
    outsideData (supplierView S) i.val=decide (i∈SupplierStars.outside S.P) := by
  apply Bool.eq_iff_iff.mpr
  simp only [outsideData,supplierView,List.all_map,Function.comp_def,id_eq,List.all_eq_true,List.mem_ofFn,
    forall_exists_index,forall_apply_eq_imp_iff,setView,List.getElem?_ofFn,dite_eq_left i.isLt,
    Option.getD_some,Fin.eta,decide_eq_true_eq,SupplierStars.outside,
    mem_filter,mem_univ,true_and]
  simp

 theorem pairWeight_view {f n : ℕ} (S : Data f n) (s t : Fin n) :
    pairWeight (supplierView S) s.val t.val=∑ i∈S.A s∩S.P t,S.y i := by
  simp only [pairWeight,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,setView,Fin.eta,← Bool.decide_and,decide_eq_true_eq,List.sum_ofFn]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

 theorem weightsData_view {f n : ℕ} (S : Data f n) :
    weightsData (supplierView S)=List.ofFn (fun e => weightQ S.y S.P S.A S.c S.γ (index e)) := by
  rw [ofFn_star]
  simp only [weightsData,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    List.flatMap_def,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  change (List.ofFn (fun i => if outsideData (supplierView S) i.val then S.y i else 0) ++
     ((List.ofFn (fun s => List.ofFn (fun t => pairWeight (supplierView S) s.val t.val))).flatten ++
       List.ofFn (fun t => S.γ*S.c t)))=_
  simp only [outsideData_view,pairWeight_view,decide_eq_true_eq,weightQ]
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram

def rowProbability (x : Context × Row) : ℚ := x.1.raw.1[x.1.t]?.getD 0
 theorem probability_view (c : Context) (q : T c) : rowProbability (c,view c q)=probability c q := by
  simp only [rowProbability,probability,view,List.getElem?_ofFn]
  split_ifs <;> rfl

noncomputable def probabilityProgram : PolyProgram (encodePair Context.encode er) Ratio.encode rowProbability := by
  let raw : PolyProgram (encodePair (encodePair qr Nat.bits) er) Ratio.encode
      (fun x : (List ℚ × ℕ) × Row => x.1.1[x.1.2]?.getD 0) := by
    exact Binary.Automatic.Poly.program (by fun_prop)
  exact raw.recode (fun x => (x.1.raw,x.2)) (fun _ => rfl) (fun _ => rfl)

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_LastFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList.Last
open Binary Binary.Automatic Binary.Automatic.Poly Finset

 theorem active_list {n : ℕ} (p : Vector ℚ n) : active p.toList=decide (RationalWeightedStep.fractional p).Nonempty := by
  simp only [active,fractional_list,List.length_map,Finset.length_sort,card_pos]
end MetricKMedian.RoundingList.Last

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_TargetSubsetProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
def Input.raw (x : Input) : Raw := (setView x.D,x.q)
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedTerminalProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

def result (x : Input true) : Data Row :=
  let μ := RationalSignedTerminal.terminal x.β x.p x.feasible
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseCounts.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

 theorem edges_view {n m : ℕ} (G : SparseCounts.Table n m) :
    edges (List.replicate n (),view G)=List.ofFn (edgeCode G) := by
  simp only [edges,indices,List.length_replicate,RoundingList.range_finRange,view,
    List.flatMap_def,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map]
  simp only [List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some]
  rw [RoundingList.ofFn_product]
  rfl

 theorem featureList_view {n m : ℕ} (G : SparseCounts.Table n m) :
    featureList (List.replicate n (),view G)=List.ofFn (features G) := by
  simp only [featureList,edges_view,RoundingList.features,List.flatMap_def,List.map_ofFn,
    Function.comp_def,RoundingList.ofFn_product]
  rw [List.ofFn_add]
  congr 1
  · congr 1; funext i
    have hi : (Fin.castAdd ((n*m)*(n*m)) i : Fin (n*m+(n*m)*(n*m)))=finSumFinEquiv (Sum.inl i) := rfl
    change edgeCode G i = features G (Fin.castAdd ((n*m)*(n*m)) i)
    rw [hi]
    simp only [features,Equiv.symm_apply_apply,Sum.elim_inl]
  · congr 1; funext i
    have hi : (Fin.natAdd (n*m) i : Fin (n*m+(n*m)*(n*m)))=finSumFinEquiv (Sum.inr i) := by apply Fin.ext; simp [finSumFinEquiv]
    rw [hi]
    simp only [features,Equiv.symm_apply_apply,Sum.elim_inr]

 theorem dimensions_eq {n m : ℕ} (cs : Fin m → SparseIntegerLaw.BinarySparse.Data Row) :
    dimensions (List.replicate n (),List.ofFn cs)=List.replicate (n*m+(n*m)*(n*m)) () := by
  have h : (List.replicate n ()).flatMap (fun _ => (List.ofFn cs).map (fun _ => (0:ℚ)))=
      List.ofFn (fun _ : Fin (n*m) => (0:ℚ)) := by
    simp only [List.map_const',List.length_ofFn,List.flatMap_replicate,List.ofFn_const]
    simp [List.flatten_replicate_replicate]
  simp only [dimensions,h,RoundingList.dimensions_list]
end MetricKMedian.SparseCounts.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
abbrev InputRaw := List Unit × List (Data Row)
abbrev ei : InputRaw → List Bool := Binary.Automatic.enc

def columnRaw {n : ℕ} (μ : SparseIntegerLaw ((Fin n → ℕ))) : Data Row :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map ListOperation.setView)
def Input.raw (x : Input) : InputRaw := (List.replicate x.n (),List.ofFn fun i => columnRaw (x.columns i))
abbrev Input.encode (x : Input) := ei x.raw
def Context.raw (c : Context) : InputRaw × ℕ := (c.input.raw,c.t)
abbrev Context.encode (c : Context) := encodePair ei Nat.bits c.raw
abbrev view (c : Context) (G : T c) := ListOperation.view G
abbrev State.encode := Bundle.encode Context.encode et view

def rawColumn (x : InputRaw × ℕ) : Data Row :=
  if x.2 < x.1.2.length then x.1.2[x.2]?.getD ((1,[1]),[])
  else ((1,[1]),[x.1.1.map (fun _ => 0)])

theorem rawColumn_eq (c : Context) : rawColumn c.raw=columnRaw (column c) := by
  simp only [rawColumn,Context.raw,Input.raw,List.length_ofFn,List.getElem?_ofFn,column]
  split_ifs with h
  · rfl
  · simp only [columnRaw,SparseIntegerLaw.dirac,Vector.toList_replicate,
      List.map_replicate,List.ofFn_const,ListOperation.setView]
    rfl

def rawProduct (x : (InputRaw × ℕ) × Data ListOperation.Table) : (InputRaw × ℕ) × Data ListOperation.Table :=
  let p := prodData (x.2,rawColumn x.1)
  (x.1,(p.1,p.2.map (fun z => ListOperation.nextTable ((x.1.2,z.1),z.2))))

noncomputable def dimensionsProgram : PolyProgram Context.encode IntegerLaw.BinaryCompression.es
    (fun c => List.replicate (c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m)) ()) :=
  (((fst ei Nat.bits).comp ListOperation.dimensions_poly.program).recode Context.raw (fun _ => rfl)
    (fun c => congrArg _ (ListOperation.dimensions_eq (fun i => columnRaw (c.input.columns i)))))
noncomputable def featuresProgram : PolyProgram (encodePair Context.encode et) IntegerLaw.BinaryCompression.eqr
    (fun x => ListOperation.featureList (x.1.input.raw.1,x.2)) := by
  let p : PolyProgram (encodePair (encodePair ei Nat.bits) et) IntegerLaw.BinaryCompression.eqr
      (fun x : (InputRaw × ℕ) × ListOperation.Table => ListOperation.featureList (x.1.1.1,x.2)) := by
    apply Binary.Automatic.Poly.program
    fun_prop
  exact p.recode (fun x => (x.1.raw,x.2)) (fun _ => rfl) (fun _ => rfl)

noncomputable def incrementProgram : PolyProgram State.encode State.encode State.increment := by
  let old := fst Context.encode (ed et)
  let inp := old.comp ((fst ei Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let t := old.comp ((snd ei Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let inc := (t.fanout (constant _ Nat.bits 1)).comp natAdd
  let law := snd Context.encode (ed et)
  exact ((inp.fanout inc).fanout law).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
local notation "erB" => ListOperation.er

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  let raw : PolyProgram ei (encodePair (encodePair ei Nat.bits) (ed et))
      (fun x : InputRaw => ((x,0),(((1:ℤ),[(1:ℤ)]),[x.2.map (fun _ => x.1.map (fun _ => (0:ℕ)))]))) := by
    apply Binary.Automatic.Poly.program
    have hs : Binary.Automatic.Poly (fun x : InputRaw => x.2.map (fun _ => x.1.map (fun _ => (0:ℕ)))) := by
      apply Binary.Automatic.Poly.list_map
      · apply Binary.Automatic.Poly.list_map <;> fun_prop
      · fun_prop
    fun_prop
  exact raw.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.start,SparseIntegerLaw.dirac,
      List.map_const',Input.raw,List.length_ofFn,List.map_replicate,
      Vector.toList_replicate,List.ofFn_const,view,ListOperation.view]
    rfl)

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.m :=
  ((snd (encodeList (fun _ : Unit => [])) (encodeList (ed erB))).comp (listLength (ed erB) ((1,[1]),[]))).recode
    Input.raw (fun _ => rfl) (fun x => by simp only [Function.comp_def,Input.raw,List.length_ofFn])

theorem input_bounds (x : Input) :
    x.n≤x.encode.length ∧ x.m≤x.encode.length ∧
    (∀ i, (x.columns i).length≤x.encode.length) ∧
    (∀ i, (x.columns i).law.denominator≤(2:ℤ)^x.encode.length) := by
  let L := x.encode.length
  have he : L=2*(encodeList (fun _ : Unit => []) x.raw.1).length+1+
      (encodeList (ed erB) x.raw.2).length := encodePair_length _ _ _
  have hn := EncodedList.length_le (fun _ : Unit => []) x.raw.1
  have hm := EncodedList.length_le (ed erB) x.raw.2
  simp only [Input.raw,List.length_ofFn,List.length_replicate] at hn hm he
  have hcol (i : Fin x.m) : (ed erB (columnRaw (x.columns i))).length≤L := by
    have h := EncodedList.member_length (ed erB) x.raw.2 (columnRaw (x.columns i))
      (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simp only [Input.raw] at h
    omega
  have hc (i : Fin x.m) : (ed erB (columnRaw (x.columns i))).length=
      2*(2*(Signed.encode (x.columns i).law.denominator).length+1+
        (encodeList Signed.encode (List.ofFn (x.columns i).law.numerator)).length)+1+
      (encodeList erB ((x.columns i).states.toList.map ListOperation.setView)).length := by
    simp only [columnRaw,ed,el,IntegerLaw.ListPivot.el,encodePair_length]
  refine ⟨by change x.n≤L; omega,by change x.m≤L; omega,?_,?_⟩
  · intro i
    have h := EncodedList.length_le Signed.encode (List.ofFn (x.columns i).law.numerator)
    simp only [List.length_ofFn] at h
    have hh := hcol i
    rw [hc i] at hh
    change (x.columns i).length≤L
    omega
  · intro i
    have hh := hcol i
    rw [hc i] at hh
    have hl : (Signed.encode (x.columns i).law.denominator).length≤L := by omega
    exact (le_abs_self _).trans ((Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) hl))

theorem entry_bound (x : Input) : ∀ i, ∀ a : Fin (x.columns i).length, ∀ h,
    (x.columns i).states[a.val] h≤2^x.encode.length := by
  intro i a h
  have he := encodePair_length (encodeList (fun _ : Unit => [])) (encodeList (ed erB)) x.raw
  have hcol := EncodedList.member_length (ed erB) x.raw.2 (columnRaw (x.columns i))
    (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hs := encodePair_length el (encodeList erB) (columnRaw (x.columns i))
  have hrow := EncodedList.member_length erB ((x.columns i).states.toList.map ListOperation.setView)
    (ListOperation.setView (x.columns i).states[a.val]) (by
      apply List.mem_map.mpr
      exact ⟨(x.columns i).states[a.val], by simp, rfl⟩)
  have hv := EncodedList.member_length Nat.bits (ListOperation.setView (x.columns i).states[a.val])
    ((x.columns i).states[a.val] h) (List.mem_ofFn.mpr ⟨h,rfl⟩)
  have hl : ((x.columns i).states[a.val] h).bits.length≤x.encode.length := by
    change x.encode.length=_ at he
    change (ed erB (columnRaw (x.columns i))).length=
      2*(el ((x.columns i).law.denominator,List.ofFn (x.columns i).law.numerator)).length+1+
        (encodeList erB ((x.columns i).states.toList.map ListOperation.setView)).length at hs
    change ((x.columns i).states[a.val] h).bits.length≤(erB (ListOperation.setView (x.columns i).states[a.val])).length at hv
    omega
  exact (NatBinary.le_two_pow_length _).trans (Nat.pow_le_pow_right (by decide) hl)

theorem state_size (x : Input) (t : ℕ) (ht : t≤x.m) :
    (State.encode (x.state t)).length≤ sizePolynomial.eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hm,hN,hD⟩ := input_bounds x
  have htL : t≤L := ht.trans hm
  have hc : (Context.encode ⟨x,t⟩).length≤3*L+2 := by
    have hbits : t.bits.length≤t+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
    change (encodePair Input.encode Nat.bits (x,t)).length≤_
    rw [encodePair_length]
    change 2*L+1+t.bits.length≤_
    omega
  have hsupport : (x.state t).law.length≤ supportBound L := by
    apply (run_length x.columns t).trans
    unfold supportBound
    gcongr
  have hheight : SparseCounts.stepHeight x.n x.m L L L*t≤heightBound L := by
    unfold heightBound SparseCounts.stepHeight
    dsimp only
    gcongr
  have hden : (x.state t).law.law.denominator≤(2:ℤ)^(heightBound L) :=
    (denominator_height x.columns L L L hN hD (entry_bound x) t).trans (pow_le_pow_right₀ (by norm_num) hheight)
  have hr (S : Fin x.n → ℕ) (hS : ∀ i,S i≤2^L) : (erB (ListOperation.setView S)).length≤L*(2*(L+1)+1) := by
    have h := EncodedList.length_bound Nat.bits (ListOperation.setView S) (L+1) (by
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact NatBinary.length_le_height (hS i))
    simp only [ListOperation.setView,List.length_ofFn] at h
    exact h.trans (Nat.mul_le_mul_right _ hn)
  have hs (a : Fin (run x.columns t).length) :
      (et (ListOperation.view (run x.columns t).states[a.val])).length≤graphSize L := by
    have hg := run_bound x.columns (2^L) (entry_bound x) t a
    have h := EncodedList.length_bound erB (ListOperation.view (run x.columns t).states[a.val]) (L*(2*(L+1)+1)) (by
      intro row hrow
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
      exact hr _ (hg i))
    simp only [ListOperation.view,List.length_ofFn] at h
    apply h.trans
    unfold graphSize
    gcongr
  have hb := SparseIntegerLaw.encode_length_bound (fun G : SparseCounts.Table x.n x.m => et (ListOperation.view G))
    (run x.columns t) (supportBound L) (heightBound L) (graphSize L) hsupport hden (fun i => hs _)
  have he : State.encode (x.state t)=encodePair Context.encode
      (SparseIntegerLaw.BinarySparse.encode (fun G : SparseCounts.Table x.n x.m => et (ListOperation.view G)))
        (⟨x,t⟩,run x.columns t) := by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.state,view,
      SparseIntegerLaw.BinarySparse.encode,SparseIntegerLaw.BinarySparse.raw,ed,encodePair,RoundingProgram.encodeList_map]
  rw [sizePolynomial_eval,he,encodePair_length]
  unfold sizeBound
  dsimp only at ⊢
  simp only [L] at hc hb ⊢
  omega

end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridRoundingProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram SparseCounts.Program

noncomputable def columnsProgram : PolyProgram QInput.encode (encodeList SparseGridRounding.Program.Input.encode) QInput.columns :=
  (snd (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun x => by
    change qt (List.ofFn (fun i => List.ofFn (x.column i).q))=
      encodeList SparseGridRounding.Program.Input.encode (List.ofFn x.column)
    rw [show List.ofFn (fun i => List.ofFn (x.column i).q)=
      (List.ofFn x.column).map (fun c => List.ofFn c.q) by rw [List.map_ofFn]; rfl]
    exact RoundingProgram.encodeList_map qr (fun c : SparseGridRounding.Program.Input => List.ofFn c.q) _)

end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierPreparationProgram
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
abbrev Input.raw (x : Input) := supplierView x.S
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalSortProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RationalSortProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly

 theorem insertData_sorted (xs : List ℚ) (hx : xs.SortedLT) (a : ℚ) : (insertData (xs,a)).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  rw [insertData,List.pairwise_append,List.pairwise_cons]
  refine ⟨hx.pairwise.filter _,⟨?_,hx.pairwise.filter _⟩,?_⟩
  · intro b hb
    exact of_decide_eq_true (List.mem_filter.mp hb).2
  · intro b hb c hc
    have hb' : b<a := of_decide_eq_true (List.mem_filter.mp hb).2
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hb'
    · exact hb'.trans (of_decide_eq_true (List.mem_filter.mp hc).2)
 theorem insertData_mem (xs : List ℚ) (a q : ℚ) : q∈insertData (xs,a) ↔ q=a ∨ q∈xs := by
  simp only [insertData,List.mem_append,List.mem_filter,List.mem_cons,decide_eq_true_eq]
  constructor
  · tauto
  · rintro (rfl | hq)
    · tauto
    · rcases lt_trichotomy q a with h | h | h <;> tauto
 theorem insertData_sort (Q : Finset ℚ) (a : ℚ) : insertData (Q.sort,a) = (insert a Q).sort := by
  apply List.SortedLT.eq_of_mem_iff
  · exact insertData_sorted Q.sort Q.sortedLT_sort a
  · exact (insert a Q).sortedLT_sort
  · intro q
    simp only [insertData_mem,mem_sort,mem_insert]
 theorem fold_sort (xs : List ℚ) (Q : Finset ℚ) :
     xs.foldl (fun s a => insertData (s,a)) Q.sort=(xs.toFinset ∪ Q).sort := by
  induction xs generalizing Q with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,insertData_sort,ih]
    congr 1
    ext q
    simp only [List.toFinset_cons,mem_union,mem_insert]
    tauto
 theorem sort_eq (xs : List ℚ) : sort xs=xs.toFinset.sort := by
  have h := fold_sort xs ∅
  simpa only [sort,Finset.sort_empty,union_empty] using h
end MetricKMedian.RationalSortProgram
end

end OAI
end


