-- Prove2me | Definitions.Def_OAIQ053K057
-- name    : OAIQ053K057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:12:10.416058+00:00
-- url     : https://prove2.me/theorems/b81d6d5f-2871-44e1-8280-b27561bcdd75
-- title:
--   Definitions bundle OAIQ053K057 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 5 definitions and 27 theorems. The definitions and types are `OAI.MetricKMedian.InputParser.foldProgram`, `OAI.MetricKMedian.LPBinary.Repair.nearestRowsProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.dimensionsProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.featuresProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.Input.raw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_NumericParserProgram`, `KMedian_Binary_SequentialParserProgram`, `KMedian_Geometry_GraphListOperations`, `KMedian_Geometry_GraphRunHeight`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Probability_BernoulliRunHeight`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_BatchActionArrays`, `KMedian_Process_BatchGraphData`, `KMedian_Process_BatchOrdinalArrays`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_PhysicalBatchList`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_TaperAllProgram`, `KMedian_Process_TaperListProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K048`, `OAIQ053K049`, `OAIQ053K050` and `OAIQ053K051` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K064`, `OAIQ053K065` and `OAIQ053K066`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K048
import Definitions.Def_OAIQ053K049
import Definitions.Def_OAIQ053K050
import Definitions.Def_OAIQ053K051

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
 theorem natRead_rest_length (xs : List Bool) : (natRead xs).2.length≤xs.length := by
  simp only [natRead,List.length_drop]; omega
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_SequentialParserProgram
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
noncomputable def foldProgram : PolyProgram enc enc
    (fun x : List Unit × State (α:=α) => x.1.foldl (fun b a => parseStep read (b,a)) x.2) :=
  (parseStep_poly read ⟨P⟩).program.listFold () (parseBound read P) (by
    intro as b pre suf he
    have hh := parseFold_size read P hrest pre b
    let L := (enc (as,b)).length
    have hb : (enc b).length≤L := by
      dsimp only [L]
      change (enc b).length≤(encodePair enc enc (as,b)).length
      rw [encodePair_length]; dsimp only; omega
    have hp : pre.length≤L := by
      have ha := EncodedList.length_le (enc : Unit → List Bool) as
      have hl : pre.length≤as.length := by rw [he,List.length_append]; omega
      change as.length≤(enc as).length at ha
      dsimp only [L]
      change pre.length≤(encodePair enc enc (as,b)).length
      rw [encodePair_length]; dsimp only; omega
    have hx : (enc b.1).length≤L := by
      change (encodePair enc enc b).length≤L at hb
      rw [encodePair_length] at hb; omega
    have hq := polynomial_eval_mono P.sizeBound hx
    have hr : (enc (pre.foldl (fun b a => parseStep read (b,a)) b).1).length≤(enc b.1).length := by
      change (encodeList encodeBool _).length≤(encodeList encodeBool _).length
      rw [BooleanLists.length,BooleanLists.length]; omega
    change (encodePair enc enc _).length≤_
    rw [encodePair_length]
    change (encodePair enc enc b).length≤L at hb
    rw [encodePair_length] at hb
    simp only [parseBound,eval_add,eval_X,eval_mul,eval_ofNat,eval_one]
    change _≤L+L*(2*P.sizeBound.eval L+1)
    have hm := Nat.mul_le_mul hp (show 2*P.sizeBound.eval (enc b.1).length+1≤2*P.sizeBound.eval L+1 by omega)
    have hh2 := hh.2
    omega)
end Generic
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.SparseEnumeratedGraph.mem_lift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

 theorem edges_view {n m : ℕ} (G : Graph n m) :
    edges (List.replicate n (),view G)=List.ofFn (edgeCode G) := by
  simp only [edges,indices,List.length_replicate,RoundingList.range_finRange,view,
    List.flatMap_def,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map]
  simp only [List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    decide_eq_true_eq]
  rw [RoundingList.ofFn_product]
  rfl

 theorem featureList_view {n m : ℕ} (G : Graph n m) :
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

end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphRunHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseEnumeratedGraph.mem_lift _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseGraph
open Binary
variable {n m : ℕ}

theorem denominator_height (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) (N L : ℕ)
    (hN : ∀ i, (ν i).length≤N) (hL : ∀ i, (ν i).law.denominator≤(2:ℤ)^L) (t : ℕ) :
    (run ν t).law.denominator≤(2:ℤ)^(stepHeight n m N L*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      let μ := run ν t
      let ρ := μ.prod (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩)
      have hc := ρ.compressAuto_denominator features 0
        (fun i a => (features_height ρ.states[i.val] a).1)
        (fun i a => (features_height ρ.states[i.val] a).2)
      simp only [zero_mul,add_zero] at hc
      have hrD : ρ.law.denominator=μ.law.denominator*(ν ⟨t,ht⟩).law.denominator := rfl
      have hrN : ρ.length ≤ (n*m+(n*m)*(n*m)+1)*N :=
        Nat.mul_le_mul (run_length ν t) (hN _)
      change (ρ.compressAuto features).law.denominator≤_
      apply hc.trans
      rw [hrD]
      calc
        _ ≤ ((2:ℤ)^(stepHeight n m N L*t)*(2:ℤ)^L)*
            (2:ℤ)^((2*(n*m+(n*m)*(n*m)+1)*(n*m+(n*m)*(n*m)+1))*
              ((n*m+(n*m)*(n*m)+1)*N+1)*((n*m+(n*m)*(n*m)+1)*N)) := by
          gcongr
          · exact (ν ⟨t,ht⟩).law.denominator_pos.le
          · exact hL _
          · norm_num
        _ = _ := by rw [← pow_add,← pow_add]; congr 1; simp only [stepHeight]; ring
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))
end MetricKMedian.SparseGraph
end

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
noncomputable def nearestRowsProgram : PolyProgram (encodePair ers er) ers (fun x : Rows × Row => nearestRows x.1 x.2) :=
  ((exchange ers er).comp (Nearest.fillingProgram.listMapWith [] [])).congr _ (fun _ => rfl)
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliListOperations
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

theorem units_eq (d : ℕ) (q : Row) : units d q=List.replicate ((q.length+1)^d) () := by
  rw [← units_length d q]
  exact List.eq_replicate_length.mpr (fun b hb => Subsingleton.elim _ _)

 theorem tests_true_iff {n degree : ℕ} (q : Fin n → Bool) (j : Fin ((n+1)^degree)) :
    (tests degree (List.ofFn q) j.val).all id=true ↔ ∀ i∈used (finFunctionFinEquiv.symm j), q i=true := by
  simp only [tests,List.all_map,List.all_eq_true,Function.comp_def,id_eq,List.mem_range,List.length_ofFn]
  constructor
  · intro h i hi
    obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hi).2
    apply (get_true_iff q _).mp (h a.val a.isLt) i
    exact ha
  · intro h a ha
    apply (get_true_iff q _).mpr
    intro i hi
    apply h i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨a,ha⟩,hi⟩⟩

 theorem featureList_ofFn {n degree : ℕ} (q : Fin n → Bool) :
    featureList degree (List.ofFn q)=List.ofFn (features (d:=degree) q) := by
  apply List.ext_getElem
  · simp [featureList]
  · intro i hi hi'
    have hi'' : i<(n+1)^degree := by simpa [featureList] using hi
    simp only [featureList,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    unfold value features monomial
    rw [flag_product]
    congr 1
    exact propext (tests_true_iff q ⟨i,hi''⟩)

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRunHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparseBernoulli
open Binary
variable {n d : ℕ}

theorem denominator_height (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (L : ℕ) (hL : ∀ i, HasHeight (p i) L) (t : ℕ) :
    (run (d:=d) p hp t).law.denominator ≤ (2:ℤ)^(stepHeight n d L*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      have h := SparseIntegerLaw.step_denominator_height (run (d:=d) p hp t) (features (d:=d))
        (fun _ => p ⟨t,ht⟩) (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)
        ((n+1)^d+1) L 0 (run_length p hp t) (fun _ => hL _) (fun _ _ _ => features_height _ _)
      apply h.trans
      calc
        _ ≤ (2:ℤ)^(stepHeight n d L*t)*(2:ℤ)^(stepHeight n d L) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ = _ := by rw [← pow_add,Nat.mul_succ]
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))

end MetricKMedian.SparseBernoulli
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram

noncomputable def dimensionsProgram (d : ℕ) : PolyProgram Context.encode IntegerLaw.BinaryCompression.es
    (fun c => List.replicate ((c.input.n+1)^d) ()) := by
  let raw : PolyProgram (encodePair qr Nat.bits) IntegerLaw.BinaryCompression.es
      (fun x : List ℚ × ℕ => ListOperation.units d (x.1.map (fun _ => false))) := by
    apply Binary.Automatic.Poly.program
    exact Binary.Automatic.Poly.comp (ListOperation.units_poly d) (by
      apply Binary.Automatic.Poly.list_map <;> fun_prop)
  exact raw.recode Context.raw (fun _ => rfl) (fun c => by
    simp only [ListOperation.units_eq,List.length_map,List.length_ofFn])
noncomputable def featuresProgram (d : ℕ) : PolyProgram (encodePair Context.encode er) IntegerLaw.BinaryCompression.eqr
    (fun x => ListOperation.featureList d x.2) :=
  (snd Context.encode er).comp (ListOperation.featureList_poly d).program

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchList
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparsePhysicalBatch.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table er et indices)

 theorem conflictFree_view {n : ℕ} (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) (e : Fin n) :
    conflictFree (List.ofFn (fun a => SparseGraph.ListOperation.setView (C a)),List.ofFn ω) e.val=true ↔
      ∀ f∈C e, ω f=false := by
  simp only [conflictFree,indices,List.length_ofFn,RoundingList.range_finRange,List.map_map,
    Function.comp_def,List.all_map,List.all_eq_true,List.mem_finRange,forall_const,
    SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,id_eq,Bool.or_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not]
  constructor
  · intro h f hf
    exact (h f).resolve_left (not_not.mpr hf)
  · intro h f
    by_cases hf : f∈C e
    · exact Or.inr (h f hf)
    · exact Or.inl hf

 theorem select_view {n : ℕ} (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (ω : Fin n → Bool) (bal : Bool) :
    select bal (((SparseGraph.ListOperation.setView Z,List.ofFn (fun a => SparseGraph.ListOperation.setView (C a))),
      (p,List.ofFn q)),List.ofFn ω)=SparseGraph.ListOperation.setView
      (if bal then balanced Z C ω else unbalanced Z ω) := by
  apply List.ext_getElem
  · simp only [select,indices,List.length_ofFn,List.length_map,List.length_range,
      SparseGraph.ListOperation.setView]
  · intro i hi hi'
    have hin : i<n := by simpa only [SparseGraph.ListOperation.setView,List.length_ofFn] using hi'
    simp only [select,indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left hin,Option.getD_some]
    apply Bool.eq_iff_iff.mpr
    cases bal
    · simp only [Bool.false_eq_true,ite_false,unbalanced,Finset.mem_filter,Finset.mem_univ,true_and,
        Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not,decide_eq_true_eq]
    · simp only [ite_true,balanced,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,
        Bool.and_eq_true,decide_eq_true_eq]
      rw [show conflictFree (List.ofFn (fun a => List.ofFn (fun h => decide (h∈C a))),List.ofFn ω) i=true ↔
        ∀ f∈C ⟨i,hin⟩, ω f=false from conflictFree_view C ω ⟨i,hin⟩]
end MetricKMedian.SparsePhysicalBatch.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchActionArrays
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.ActionArrays
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch Finset
open SparseGraph.ListOperation (Row Table setView indices)

 theorem overlap_view {n : ℕ} (A B : Finset (Fin n)) :
    overlap (setView A) (setView B)=true ↔ (A∩B).Nonempty := by
  simp only [overlap,indices,setView,List.length_ofFn,RoundingList.range_finRange,List.map_map,
    Function.comp_def,List.any_map,List.any_eq_true,List.mem_finRange,true_and,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,id_eq,Bool.and_eq_true,
    decide_eq_true_eq,Finset.Nonempty,mem_inter]

end MetricKMedian.RationalBatchData.ActionArrays

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchGraphData
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.RationalBatchData.GraphData
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch Finset
open SparseGraph.ListOperation (Row Table setView indices view)

 theorem amount_view {n : ℕ} (m : Fin n → ℚ) : amount (List.ofFn m)=RationalBatchData.amount m := by
  simp only [amount,List.map_ofFn,List.sum_ofFn,Function.comp_def,RationalBatchData.amount]
end MetricKMedian.RationalBatchData.GraphData
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalCodes
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

 theorem parent_code (e : HeavyAction D H) :
    ActionList.parent n (code r D H e)=(r.symm (heavyParent D H e)).val := by
  cases e with
  | inl e => simp only [ActionList.parent,code,Fin.isLt,ite_true,heavyParent]
  | inr e =>
    have hn : 0<n := Nat.zero_lt_of_lt (r.symm e.val.1).isLt
    have hi := (r.symm e.val.2).isLt
    have hc : ¬n+(r.symm e.val.1).val*n+(r.symm e.val.2).val<n := by omega
    change ActionList.parent n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.1).val
    rw [ActionList.parent,ite_eq_right hc,Nat.add_assoc,Nat.add_sub_cancel_left,Nat.mul_comm _ n,
      Nat.mul_add_div hn,Nat.div_eq_of_lt hi,Nat.add_zero]
 theorem child_code (e : {p : I × I // p.1∈H ∧ p.2∈D.erase p.1}) :
    ActionList.child n (code r D H (.inr e))=(r.symm e.val.2).val := by
  simp only [ActionList.child,code]
  rw [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (r.symm e.val.2).isLt]
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalArrays
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

 omit [Fintype I] in
 theorem bias_code (m : I → ℚ) (p φ : ℚ) (e : HeavyAction D H) :
    ActionArrays.bias (((p,φ),List.ofFn (fun i => m (r i))),n) (code r D H e)=
      RationalBatchData.bias m p φ (heavyParent D H e) := by
  simp only [ActionArrays.bias,parent_code,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,OrderIso.apply_symm_apply,RationalBatchData.bias]

end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparsePhysicalBatch.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse SparseIntegerLaw.DependentProgram
open SparseGraph.ListOperation (Row Table et)

def Input.raw (x : Input) : ListOperation.Raw :=
  ((SparseGraph.ListOperation.setView x.Z,List.ofFn fun e => SparseGraph.ListOperation.setView (x.C e)),
    (x.p,List.ofFn x.q))
end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperListProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset

 theorem upper_list {n : ℕ} (d : Fin n → ℚ) : upper (List.ofFn d)=Taper.upper d := by
  simp only [upper,Taper.upper,List.map_ofFn,List.sum_ofFn,one_div,Function.comp_def]
 theorem mem_breaks {n : ℕ} (P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈breaks (P,List.ofFn d) ↔ q∈Taper.breakpoints P d := by
  simp only [breaks,upper_list,List.mem_cons,List.mem_append,List.mem_map,List.mem_ofFn,
    Taper.breakpoints,mem_insert,mem_union,mem_image,mem_univ,true_and]
  aesop
 theorem aSum_list {n : ℕ} (P t : ℚ) (d : Fin n → ℚ) :
    aSum ((P,List.ofFn d),t)=Taper.A P d t := by
  simp only [aSum,List.map_ofFn,List.sum_ofFn,Taper.A,Function.comp_def]
 theorem bSum_list {n : ℕ} (P t : ℚ) (d : Fin n → ℚ) :
    bSum ((P,List.ofFn d),t)=Taper.B P d t := by
  simp only [bSum,List.map_ofFn,List.sum_ofFn,Taper.B,Function.comp_def]
 theorem mem_candidates {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈candidateList ((g,P),List.ofFn d) ↔ q∈Taper.candidates g P d := by
  simp only [candidateList,List.mem_append,List.mem_flatMap,List.mem_map,mem_breaks,
    aSum_list,bSum_list,Taper.candidates,mem_union,mem_image,mem_product,Prod.exists]
  aesop
 theorem mass_list {n : ℕ} (g P r : ℚ) (d : Fin n → ℚ) :
    mass (((g,P),List.ofFn d),r)=rationalMass g P d r := by
  simp only [mass,List.map_ofFn,List.sum_ofFn,rationalMass,Function.comp_def]
 theorem mem_roots {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈roots ((g,P),List.ofFn d) ↔ q∈rootCandidates g P d := by
  simp only [roots,List.mem_filter,mem_candidates,Bool.and_eq_true,decide_eq_true_eq,mass_list,
    rootCandidates,mem_filter]
 theorem radius_list {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) :
    radius ((g,P),List.ofFn d)=inverseRadius g P d := by
  unfold inverseRadius
  split_ifs with h
  · apply LPBinary.foldl_max_eq
    · exact (mem_filter.mp (max'_mem (rootCandidates g P d) h)).2.1.le
    · exact (mem_roots _ _ _ _).mpr (max'_mem _ h)
    · intro q hq
      exact le_max' _ _ ((mem_roots _ _ _ _).mp hq)
  · have he : roots ((g,P),List.ofFn d)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      exact h ⟨q,(mem_roots _ _ _ _).mp hq⟩
    simp only [radius,he,List.foldl_nil]
end MetricKMedian.Taper.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperAllProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset

 theorem colocated_list {n : ℕ} (g : ℚ) (d : Fin n → ℚ) :
    colocated (g,List.ofFn d)=rationalColocatedMass g d := by
  simp only [colocated,List.map_ofFn,List.sum_ofFn,rationalColocatedMass,Function.comp_def]
 theorem extras_list {n : ℕ} (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    extras ((List.ofFn d,List.ofFn fun i => decide (i∈own)),Δ)=
      (((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val := by
  have hf : (RoundingList.indices (List.ofFn d)).filter
      (fun i => decide ((List.ofFn d)[i]?.getD 0=0) && !((List.ofFn fun k => decide (k∈own))[i]?.getD false))=
      ((zeroSources d\own).sort).map Fin.val := by
    simp only [RoundingList.indices,List.length_ofFn,RoundingList.range_finRange,List.filter_map,Function.comp_def,
      List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
    rw [show (fun i : Fin n => decide (d i=0) && !decide (i∈own))=
      (fun i : Fin n => decide (i∈zeroSources d\own)) by
      funext i; simp only [zeroSources,mem_sdiff,mem_filter,mem_univ,true_and,Bool.decide_and,decide_not]]
    rw [EncodingLists.filter_range]
    simp only [filter_univ_mem]
  simp only [extras,hf,EncodingLists.bool_card,List.map_take]
 theorem zeroRow_list {n : ℕ} (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    zeroRow ((List.ofFn d,List.ofFn fun i => decide (i∈own)),Δ)=List.ofFn (zeroMarginal d own Δ) := by
  apply List.ext_getElem
  · simp only [zeroRow,RoundingList.indices,List.length_map,List.length_range,List.length_ofFn]
  · intro k hk hk'
    have hkn : k<n := by simpa only [List.length_ofFn] using hk'
    let i : Fin n := ⟨k,hkn⟩
    simp only [zeroRow,RoundingList.indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hkn,Option.getD_some,extras_list]
    have he : natMember ((((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val,i.val)=true ↔
        i∈(((zeroSources d\own).sort).take (Δ-own.card)).toFinset := by
      rw [natMember_true,List.mem_toFinset]
      simp only [List.mem_map,Fin.val_inj]
      simp only [exists_eq_right]
    change (if decide (i∈own) || natMember ((((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val,i.val) then (1:ℚ) else 0)=zeroMarginal d own Δ i
    simp only [Bool.or_eq_true,decide_eq_true_eq,he,zeroMarginal,zeroSelection,extend,mem_union]
 theorem sourceRow_list {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    sourceRow ((((g,P),List.ofFn d),List.ofFn fun i => decide (i∈own)),Δ)=List.ofFn (sourceMarginals g P d own Δ) := by
  simp only [sourceRow,colocated_list,sourceMarginals]
  split_ifs
  · exact zeroRow_list d own Δ
  · simp only [List.map_ofFn,radius_list,Function.comp_def]
end MetricKMedian.Taper.ListOperation
end

end OAI
end


