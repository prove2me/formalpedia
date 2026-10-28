-- Prove2me | Definitions.Def_OAIQ035K053
-- name    : OAIQ035K053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:12:40.175751+00:00
-- url     : https://prove2.me/theorems/e4f7cafe-2c55-4466-ae32-7d0985501fe1
-- title:
--   Definitions bundle OAIQ035K053 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 31 definitions and 14 theorems. The definitions and types are `OAI.MetricKMedian.InputParser.parse`, `OAI.MetricKMedian.LPBinary.Program.chooseProgram`, `OAI.MetricKMedian.LPBinary.Program.componentProgram`, `OAI.MetricKMedian.LPBinary.Program.dualAffineProgram`, `OAI.MetricKMedian.LPBinary.Program.dualBestProgram`, `OAI.MetricKMedian.LPBinary.Program.dualValueProgram`, `OAI.MetricKMedian.LPBinary.Program.gradientProgram`, `OAI.MetricKMedian.LPBinary.Program.levelProgram`, `OAI.MetricKMedian.LPBinary.Program.maximumProgram`, `OAI.MetricKMedian.LPBinary.Program.nextProgram`, `OAI.MetricKMedian.LPBinary.Program.objectiveProgram`, `OAI.MetricKMedian.LPBinary.Program.optimizeProgram`, `OAI.MetricKMedian.LPBinary.Program.projectProgram`, `OAI.MetricKMedian.LPBinary.Program.statesProgram`, `OAI.MetricKMedian.LPBinary.Program.thresholdProgram`, `OAI.MetricKMedian.LPBinary.Program.thresholdsProgram`, `OAI.MetricKMedian.LPBinary.Program.updateProgram`, `OAI.MetricKMedian.LPBinary.Program.valueProgram`, `OAI.MetricKMedian.LPBinary.Repair.assignmentProgram`, `OAI.MetricKMedian.LPBinary.Repair.assignmentsProgram`, `OAI.MetricKMedian.LPBinary.Repair.dominatedProgram`, `OAI.MetricKMedian.LPBinary.Repair.dotProgram`, `OAI.MetricKMedian.LPBinary.Repair.valueProgram`, `OAI.MetricKMedian.LPBinary.Scale.guessesProgram`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.result`, `OAI.MetricKMedian.SparseBundleEncoding.law`, `OAI.MetricKMedian.SparseBundles.Program.QInput.input`, `OAI.MetricKMedian.SparseCounts.Program.Input.state`, `OAI.MetricKMedian.SparseCounts.Program.State.step`, `OAI.MetricKMedian.SparseRescaledInner.encodedLaw`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.graph`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_SequentialParserProgram`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_DualListCompiler`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_FractionalSelectProgram`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPBinaryTrajectory`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Optimization_TruncatedListCompiler`, `KMedian_Process_CountRunProgram`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_ScaleListProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Sparse_SparseBundleEncoding`, `KMedian_Sparse_SparseCardinalFixed`, `KMedian_Sparse_SparseTargetSubset`.
--
--   **Imports.** It imports the bundles `OAIQ035K046`, `OAIQ035K047`, `OAIQ035K048` and `OAIQ035K049` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K057`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K046
import Definitions.Def_OAIQ035K047
import Definitions.Def_OAIQ035K048
import Definitions.Def_OAIQ035K049

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_SequentialParserProgram
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
def parse (x : List Unit × List Bool) : List α × List Bool :=
  let s := x.1.foldl (fun b a => parseStep read (b,a)) (x.2,[])
  (s.2.reverse,s.1)
 omit [Coding α] [Inhabited α] in
 theorem parse_fold_encoded (put : α → List Bool) (hr : ∀ a xs, read (put a++xs)=(a,xs))
    (as : List α) (xs : List Bool) (acc : List α) :
    (List.replicate as.length ()).foldl (fun b a => parseStep read (b,a)) ((as.map put).flatten++xs,acc)=
      (xs,as.reverse++acc) := by
  induction as generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons,List.replicate_succ,List.map_cons,List.flatten_cons,List.append_assoc,
      List.foldl_cons,parseStep,hr]
    change (List.replicate as.length ()).foldl (fun b a => parseStep read (b,a)) ((as.map put).flatten++xs,a::acc)=_
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
 omit [Coding α] [Inhabited α] in
 theorem parse_encoded (put : α → List Bool) (hr : ∀ a xs, read (put a++xs)=(a,xs))
    (as : List α) (xs : List Bool) :
    parse read (List.replicate as.length (),(as.map put).flatten++xs)=(as,xs) := by
  unfold parse
  rw [parse_fold_encoded read put hr]
  simp
end Generic
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SimplexListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

namespace Program
open Binary Binary.PolyProgram
noncomputable def thresholdProgram : PolyProgram ethreshold Ratio.encode (fun x : (Row × ℚ) × ℚ => threshold x.1.1 x.1.2 x.2) := by
  let dat := fst (encodePair er Ratio.encode) Ratio.encode
  let xs := dat.comp (fst er Ratio.encode)
  let k := dat.comp (snd er Ratio.encode)
  let a := snd (encodePair er Ratio.encode) Ratio.encode
  let us := (a.fanout xs).comp upperProgram
  let sum := us.comp ratSum
  let card := (us.comp (listLength Ratio.encode 0)).comp ratOfNat
  exact (((sum.fanout k).comp ratSub).fanout card).comp ratDiv
noncomputable def thresholdsProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => thresholds x.1 x.2) :=
  (((identity (encodePair er Ratio.encode)).fanout (fst er Ratio.encode)).comp
    (thresholdProgram.listMapWith 0 0)).congr _ (fun _ => rfl)
noncomputable def levelProgram : PolyProgram (encodePair er Ratio.encode) Ratio.encode (fun x : Row × ℚ => level x.1 x.2) :=
  ((thresholdsProgram.fanout (thresholdsProgram.comp (listHead Ratio.encode 0))).comp maxFold).congr _ (fun _ => rfl)
noncomputable def projectProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => project x.1 x.2) := by
  let sub := ((exchange Ratio.encode Ratio.encode).comp ratSub).comp positivePart
  exact ((levelProgram.fanout (fst er Ratio.encode)).comp (sub.listMapWith 0 0)).congr _ (fun _ => rfl)
end Program
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_DualListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function

noncomputable def maximumProgram : PolyProgram er Ratio.encode maximum :=
  (((identity er).fanout (listHead Ratio.encode 0)).comp maxFold).congr _ (fun _ => rfl)

noncomputable def dualAffineProgram : PolyProgram edual Ratio.encode (fun x : (Row × Row) × ℚ => Dual.affine x.1.1 x.1.2 x.2) := by
  let t := snd epoint Ratio.encode
  let zip := (fst epoint Ratio.encode).comp (listZip Ratio.encode Ratio.encode 0 0)
  let ec := encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)
  let q := snd Ratio.encode (encodePair Ratio.encode Ratio.encode)
  let d := q.comp (fst Ratio.encode Ratio.encode)
  let y := q.comp (snd Ratio.encode Ratio.encode)
  let s := ((fst Ratio.encode (encodePair Ratio.encode Ratio.encode)).fanout d).comp ratSub
  let weighted := (y.fanout (s.comp positivePart)).comp ratMul
  let sum := (((t.fanout zip).comp (weighted.listMapWith (0,0) 0)).comp ratSum)
  exact ((t.fanout sum).comp ratSub).congr _ (fun _ => rfl)

noncomputable def dualValueProgram : PolyProgram edual Ratio.encode (fun x : (Row × Row) × ℚ => Dual.value x.1.1 x.1.2 x.2) := by
  let dat := fst epoint Ratio.encode
  let ts := (((dat.comp (fst er er)).fanout (snd epoint Ratio.encode)).comp candidatesProgram)
  exact (((dat.fanout ts).comp (dualAffineProgram.listMapWith 0 0)).comp maximumProgram).congr _ (fun _ => rfl)

noncomputable def dualBestProgram : PolyProgram edual Ratio.encode (fun x : (Row × Row) × ℚ => Dual.best x.1.1 x.1.2 x.2) := by
  let dat := fst epoint Ratio.encode
  let ts := (((dat.comp (fst er er)).fanout (snd epoint Ratio.encode)).comp candidatesProgram)
  let context := dat.fanout dualValueProgram
  let c := fst edual Ratio.encode
  let dy := c.comp (fst epoint Ratio.encode)
  let v := c.comp (snd epoint Ratio.encode)
  let a := snd edual Ratio.encode
  let test := (((dy.fanout a).comp dualAffineProgram).fanout v).comp ratEQ
  exact (((context.fanout ts).comp (test.listFilterWith 0 (([],[]),0))).comp maximumProgram).congr _ (fun _ => rfl)

end MetricKMedian.LPBinary.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function

noncomputable def objectiveProgram : PolyProgram etrunc Ratio.encode (fun x : (Rows × Row) × ℚ => Truncated.objective x.1.1 x.1.2 x.2) := by
  let dat := fst (encodePair ers er) Ratio.encode
  let ys := dat.comp (snd ers er)
  let H := snd (encodePair ers er) Ratio.encode
  let matrix := ((dat.comp (fst ers er)).fanout H).comp truncateMatrixProgram
  let ec := encodePair er Ratio.encode
  let c := fst ec er
  let y := c.comp (fst er Ratio.encode)
  let h := c.comp (snd er Ratio.encode)
  let row := snd ec er
  let value := ((row.fanout y).fanout h).comp dualValueProgram
  exact ((((ys.fanout H).fanout matrix).comp (value.listMapWith [] 0)).comp ratSum).congr _ (fun _ => rfl)

noncomputable def componentProgram : PolyProgram (encodePair etrunc Nat.bits) Ratio.encode
    (fun x : ((Rows × Row) × ℚ) × ℕ => Truncated.component x.1.1.1 x.1.1.2 x.1.2 x.2) := by
  let t := fst etrunc Nat.bits
  let dat := t.comp (fst (encodePair ers er) Ratio.encode)
  let ys := dat.comp (snd ers er)
  let H := t.comp (snd (encodePair ers er) Ratio.encode)
  let i := snd etrunc Nat.bits
  let matrix := ((dat.comp (fst ers er)).fanout H).comp truncateMatrixProgram
  let ec := encodePair (encodePair er Ratio.encode) Nat.bits
  let c := fst ec er
  let yh := c.comp (fst (encodePair er Ratio.encode) Nat.bits)
  let y := yh.comp (fst er Ratio.encode)
  let h := yh.comp (snd er Ratio.encode)
  let idx := c.comp (snd (encodePair er Ratio.encode) Nat.bits)
  let row := snd ec er
  let best := ((row.fanout y).fanout h).comp dualBestProgram
  let distance := (row.fanout idx).comp (listGetD Ratio.encode 0)
  let coord := (((best.fanout distance).comp ratSub).comp positivePart).comp ratNeg
  exact (((((ys.fanout H).fanout i).fanout matrix).comp (coord.listMapWith [] 0)).comp ratSum).congr _ (fun _ => rfl)

noncomputable def gradientProgram : PolyProgram etrunc er (fun x : (Rows × Row) × ℚ => Truncated.gradient x.1.1 x.1.2 x.2) := by
  let ys := (fst (encodePair ers er) Ratio.encode).comp (snd ers er)
  let ids := ys.comp (listIndices Ratio.encode 0)
  exact (((identity etrunc).fanout ids).comp (componentProgram.listMapWith 0 0)).congr _ (fun _ => rfl)

noncomputable def nextProgram : PolyProgram enext er
    (fun x : ((Rows × Row) × ℚ) × (ℚ × ℚ) => Truncated.next x.1.1.1 x.1.1.2 x.1.2 x.2.1 x.2.2) := by
  let t := fst etrunc (encodePair Ratio.encode Ratio.encode)
  let kr := snd etrunc (encodePair Ratio.encode Ratio.encode)
  let ys := (t.comp (fst (encodePair ers er) Ratio.encode)).comp (snd ers er)
  let grad := t.comp gradientProgram
  let zip := (ys.fanout grad).comp (listZip Ratio.encode Ratio.encode 0 0)
  let rate := kr.comp (snd Ratio.encode Ratio.encode)
  let coords := snd Ratio.encode (encodePair Ratio.encode Ratio.encode)
  let y := coords.comp (fst Ratio.encode Ratio.encode)
  let g := coords.comp (snd Ratio.encode Ratio.encode)
  let rg := ((fst Ratio.encode (encodePair Ratio.encode Ratio.encode)).fanout g).comp ratMul
  let coord := (y.fanout rg).comp ratSub
  let update := (rate.fanout zip).comp (coord.listMapWith (0,0) 0)
  exact ((update.fanout (kr.comp (fst Ratio.encode Ratio.encode))).comp projectProgram).congr _ (fun _ => rfl)
end MetricKMedian.LPBinary.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function

namespace Program
noncomputable def updateProgram : PolyProgram es es update := by
  let c := fst ec er
  let ds := c.comp (fst ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
  let hkr := c.comp (snd ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
  let h := hkr.comp (fst Ratio.encode (encodePair Ratio.encode Ratio.encode))
  let kr := hkr.comp (snd Ratio.encode (encodePair Ratio.encode Ratio.encode))
  let args := (((ds.fanout (snd ec er)).fanout h).fanout kr)
  exact (c.fanout (args.comp nextProgram)).congr _ (fun _ => rfl)
end Program

theorem update_iterate (r : ℕ) (I : Input) (t : ℕ) :
    update^[t] (start r I)=(rawContext r I.raw,I.iterate r t) := by
  induction t with
  | zero => exact start_eq r I
  | succ t ih => rw [Function.iterate_succ_apply',ih,update_eq]
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryTrajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Polynomial Function

 theorem state_size (r : ℕ) (hr : 0 < r) (I : Input) (t : ℕ) (ht : t ≤ rawSteps r I.raw) :
    (es (update^[t] (start r I))).length ≤ (statePolynomial r).eval I.encode.length := by
  rw [update_iterate]
  have hc : (ec (rawContext r I.raw)).length ≤ (Program.startProgram r).sizeBound.eval I.encode.length := by
    have hh := (Program.startProgram r).length_bound I
    change (encodePair ec er (rawContext r I.raw,rawInitial I.raw)).length ≤ (Program.startProgram r).sizeBound.eval I.encode.length at hh
    rw [encodePair_length] at hh
    dsimp only at hh
    omega
  have hy := iterate_size I r hr t (by rwa [rawSteps_eq] at ht)
  change (encodePair ec er (rawContext r I.raw,I.iterate r t)).length ≤ _
  rw [encodePair_length]
  dsimp only
  simp only [statePolynomial,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,heightPolynomial_eval]
  omega

theorem states_eq (r : ℕ) (I : Input) :
    states r I=List.ofFn (fun t : Fin (rawSteps r I.raw) => (rawContext r I.raw,I.iterate r t.val)) := by
  rw [states,Iteration.iterates_eq,range_ofFn,List.map_ofFn]
  congr 1
  funext t
  exact update_iterate r I t.val

namespace Program
noncomputable def statesProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode (encodeList es) (states r) :=
  (updateProgram.iteratesFrom (startProgram r) (stepsProgram r) (([],(0,(0,0))),[])
    (stepsPolynomial r) (statePolynomial r)
    (fun I => by rw [stepsPolynomial_eval,rawSteps_eq]; exact steps_bound I r)
    (state_size r hr)).congr _ (fun _ => rfl)
noncomputable def valueProgram : PolyProgram es Ratio.encode value := by
  let c := fst ec er
  let ds := c.comp (fst ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
  let H := (c.comp (snd ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))).comp (fst Ratio.encode (encodePair Ratio.encode Ratio.encode))
  exact (((ds.fanout (snd ec er)).fanout H).comp objectiveProgram).congr _ (fun _ => rfl)
noncomputable def chooseProgram : PolyProgram (encodeList es) es choose := by
  let a0 : State := (([],(0,(0,0))),[])
  let vals := valueProgram.listMap a0
  let mn := vals.comp minimumProgram
  let val := (snd Ratio.encode es).comp valueProgram
  let pred := ((fst Ratio.encode es).fanout val).comp ratEQ
  let filt := ((mn.fanout (identity (encodeList es))).comp (pred.listFilterWith a0 0))
  exact (filt.comp (listHead es a0)).congr _ (fun ss => by
    change (ss.filter (fun a => decide (minimum (ss.map value)=value a))).head?.getD a0=choose ss
    unfold choose selectMinimum
    apply congrArg (fun xs : List State => xs.head?.getD a0)
    exact List.filter_congr (fun a _ => decide_eq_decide.mpr eq_comm))

noncomputable def optimizeProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode er (result r) :=
  (((statesProgram r hr).comp chooseProgram).comp (snd ec er)).congr _ (fun _ => rfl)
end Program

 theorem result_eq (r : ℕ) (hr : 0 < r) (I : Input) :
    result r I=List.ofFn (ProjectedSubgradient.point (TruncatedLP.optimize I.distance r I.k (TruncatedLP.penalty r I.k) hr I.kpos (TruncatedLP.penalty_pos r I.k hr))) := by
  let T := TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)
  have hT : 0 < T := TruncatedLP.steps_pos _ _ _ hr I.kpos (TruncatedLP.penalty_pos r I.k hr)
  let : NeZero T := ⟨hT.ne'⟩
  unfold result choose
  have hs := states_eq r I
  rw [rawSteps_eq] at hs
  rw [hs,selectMinimum_ofFn]
  simp only [value_eq]
  unfold TruncatedLP.optimize
  simp only [Input.iterate,Input.vector]
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationListProgram
attribute [-instance] _root_.OAI.MetricKMedian.TruncatedLP.instDecidableValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair

theorem raw_eq (r : ℕ) (hr : 0 < r) (I : Input) (hd : ∀ j i, 0 ≤ I.distance j i) :
    raw r I=encodeData (TruncatedLP.approximation I.distance r I.k hr I.kpos hd) := by
  let H := TruncatedLP.penalty r I.k
  let y := ProjectedSubgradient.point (TruncatedLP.optimize I.distance r I.k H hr I.kpos (TruncatedLP.penalty_pos r I.k hr))
  have hy : ProjectedSubgradient.feasible (I.k:ℚ) y := (TruncatedLP.optimize_spec I.distance r I.k H hr I.kpos
    (TruncatedLP.penalty_pos r I.k hr) hd (ProjectedSubgradient.point (ProjectedSubgradient.initial (I.k:ℚ)))
    (ProjectedSubgradient.initial_feasible _ (by positivity))).1
  have hm : 1 ≤ ∑ i, y i := by rw [hy.2]; exact_mod_cast I.kpos
  unfold raw finish
  rw [result_eq r hr]
  change (opening (List.ofFn y) (TruncatedLP.loss r I.k),
    assignments I.rows (nearestRows (Truncated.matrix I.rows H) (List.ofFn y)))=_
  rw [opening_ofFn]
  have hn : nearestRows (Truncated.matrix I.rows H) (List.ofFn y)=
      List.ofFn (fun j => List.ofFn (ProjectedSubgradient.point (Preparation.computedNearest y (TruncatedLP.truncated I.distance H j) hy.1 hm))) := by
    simp only [Input.rows,Truncated.matrix_ofFn,nearestRows,List.map_ofFn,Function.comp_def,Nearest.filling_ofFn _ _ hy.1 hm]
  rw [hn]
  unfold Input.rows
  rw [assignments_ofFn]
  simp only [encodeData,TruncatedLP.approximation,Vector.getElem_ofFn,ProjectedSubgradient.point_ofFn]
  rfl

noncomputable def assignmentProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => assignment x.1 x.2) := by
  let coord := (exchange Ratio.encode Ratio.encode).comp ratDiv
  let norm := ((ratSum.fanout (identity er)).comp (coord.listMapWith 0 0))
  exact (weightsProgram.comp norm).congr _ (fun _ => rfl)
noncomputable def assignmentsProgram : PolyProgram (encodePair ers ers) ers (fun x : Rows × Rows => assignments x.1 x.2) :=
  ((listZip er er [] []).comp (assignmentProgram.listMap ([],[]))).congr _ (fun _ => rfl)
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalListChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Binary Binary.PolyProgram Function Finset

noncomputable def dominatedProgram : PolyProgram (encodePair er er) encodeBool (fun x : Row × Row => dominated x.1 x.2) := by
  let lo := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 0).fanout (fst Ratio.encode Ratio.encode)).comp ratLE
  let test := (lo.fanout ratLE).comp boolAnd
  exact ((listZip Ratio.encode Ratio.encode 0 0).comp (test.listAll (0,0))).congr _ (fun _ => by simp only [Function.comp_def,dominated,Bool.decide_and])
noncomputable def dotProgram : PolyProgram (encodePair er er) Ratio.encode (fun x : Row × Row => dot x.1 x.2) :=
  ((listZipWith Ratio.encode Ratio.encode 0 0 ratMul).comp ratSum).congr _ (fun _ => rfl)
noncomputable def valueProgram : PolyProgram (encodePair eo ers) Ratio.encode (fun x : Output × Rows => value x.1 x.2) := by
  let xs := (fst eo ers).comp (snd er ers)
  let ds := snd eo ers
  exact (((xs.fanout ds).comp (listZipWith er er [] [] dotProgram)).comp ratSum).congr _ (fun _ => rfl)
end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_ScaleListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

noncomputable def guessesProgram : PolyProgram ers er guesses := by
  let e := encodePair er Ratio.encode
  let q := snd er Ratio.encode
  let ps := fst er Ratio.encode
  let times := ratMul.listMapWith 0 0
  let pos := ((constant e Ratio.encode 0).fanout q).comp ratLT
  let body := ite pos (constant e er []) ((q.fanout ps).comp times)
  let powers := (listLength er []).comp Dyadic.program
  exact ((powers.fanout (listFlatten Ratio.encode 0)).comp (body.listFlatMapWith 0 0)).congr _ (fun _ => by
    simp only [Function.comp_apply,guesses,decide_eq_true_eq])

end Scale
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalSelectProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

theorem candidate_eq (r : ℕ) (hr : 0 < r) (I : Input) (hd : ∀ j i, 0 ≤ I.distance j i) (B : ℚ) :
    candidate r I B=Repair.encodeData (TruncatedLP.scaledCandidate I.distance r I.k hr I.kpos hd B) := by
  unfold candidate TruncatedLP.scaledCandidate
  by_cases hB : 0 < B
  · rw [ite_eq_left hB,dite_eq_left hB]
    exact Repair.raw_eq r hr (I.scale B) (fun j i => div_nonneg (hd j i) hB.le)
  · rw [ite_eq_right hB,dite_eq_right hB]
    have hz : ProjectedSubgradient.point (Vector.replicate I.n (0:ℚ)) = (fun _ => 0) := by
      funext i
      exact Vector.getElem_replicate _
    simp only [Repair.encodeData,Input.zeroOutput,Vector.getElem_replicate,hz,List.ofFn_const]

theorem feasible_mem (r : ℕ) (hr : 0 < r) (I : Input) (hd : ∀ j i, 0 ≤ I.distance j i) (B : ℚ) :
    B ∈ feasible r I ↔ B ∈ TruncatedLP.feasibleScales I.distance r I.k hr I.kpos hd := by
  simp only [feasible,List.mem_filter,Input.rows,guesses_mem,candidate_eq r hr I hd,
    Repair.valid_encodeData,decide_eq_true_eq,TruncatedLP.feasibleScales,mem_filter]

theorem selected_eq (r : ℕ) (hr : 0 < r) (I : Input) (hd : ∀ j i, 0 ≤ I.distance j i) :
    selected r I=Repair.encodeData (TruncatedLP.selectFractional I.distance r I.k hr I.kpos hd) := by
  have hm (B : ℚ) : Repair.value (candidate r I B) I.rows=(TruncatedLP.scaledCandidate I.distance r I.k hr I.kpos hd B).value I.distance := by
    rw [candidate_eq r hr I hd,Input.rows,Repair.value_encodeData]
  unfold selected selectedScale
  simp only [hm]
  rw [argmin_eq _ _ _ (feasible_mem r hr I hd),candidate_eq r hr I hd]
  rfl

end Scale
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountStepProgram
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
def State.step (x : State) : State :=
  State.increment (if x.ctx.t<x.ctx.input.m then
    Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m))
      (fun _ => features) x.product else x)

end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountRunProgram
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

def Input.state (x : Input) (t : ℕ) : State := ⟨⟨x,t⟩,run x.columns t⟩

theorem state_next (x : Input) (t : ℕ) : State.step (x.state t)=x.state (t+1) := by
  have he (ht : t < x.m) : update ⟨x,t⟩=(fun G S => next G S ⟨t,ht⟩) := by
    funext G S i
    by_cases h : i=⟨t,ht⟩
    · subst i; simp only [update,next,Function.update_self,ite_true]
    · have hv : i.val≠t := fun hh => h (Fin.ext hh)
      simp only [update,next,Function.update_of_ne h,ite_eq_right hv]
  unfold State.step Input.state
  by_cases ht : t < x.m
  · rw [ite_eq_left ht]
    change (⟨⟨x,t+1⟩,((run x.columns t).prod (column ⟨x,t⟩) (update ⟨x,t⟩)).compressAuto features⟩ : State)=_
    rw [run,dite_eq_left ht]
    simp only [column,dite_eq_left ht,he ht,SparseCounts.step,SparseIntegerLaw.prodCompress]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

theorem state_iterate (x : Input) (t : ℕ) : (State.step)^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalFixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open RationalWeightedStep

theorem run_positive {n : ℕ} (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (a : Fin (run β hβ p t).length) :
    0 < (run β hβ p t).law.rational.weight a := by
  cases t with
  | zero => change 0 < ((1:ℤ):ℚ)/1; norm_num
  | succ t =>
    exact ((run β hβ p t).branch (probability β) (probability_unit β hβ)
      (endpoint β)).compressAuto_positive features a

end MetricKMedian.SparseWeightedPartial

end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram SparseCounts.Program
def QInput.input (x : QInput) : Input := ⟨x.n,x.m,(fun j => SparseGridRounding.law (fun i => x.q i j))⟩
end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_LastFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def result (x : Input false) : RoundingProgram.State false :=
  ⟨x.n,x.β,x.positive,SparseWeightedRounding.round x.β (x.positive rfl) x.p⟩
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTargetSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

theorem positive (D : Finset (Fin n)) (q : ℚ) (a : Fin (law D q).length) :
    0 < (law D q).law.rational.weight a := by
  exact ((SparseWeightedPartial.run (fun _ => 1) (fun _ => by norm_num) (initial D q) n).branch
    RationalLastFraction.probability RationalLastFraction.probability_unit
    RationalLastFraction.endpoint).compressAuto_positive SparseWeightedPartial.features a

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)
def Input.graph (x : Input) : SparseGraph.Program.Input :=
  ⟨x.n,x.m,fun e => SparseTargetSubset.law (x.D e) (x.q e)⟩
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBundleEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBundleEncoding
open Finset
variable {n m : ℕ}

noncomputable def law (q : Fin n → Fin m → ℚ) : FiniteLaw (Fin m → Finset (Fin n)) :=
  (SparseBundles.law q).realIndex.map
    (fun a => encode q (SparseBundles.law q).states[a.val])

end MetricKMedian.SparseBundleEncoding

namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

noncomputable def encodedLaw (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) : FiniteLaw (Fin t → Finset (Fin n)) :=
  SparseBundleEncoding.law (piece P y p K)

end MetricKMedian.SparseRescaledInner
end

end OAI
end


