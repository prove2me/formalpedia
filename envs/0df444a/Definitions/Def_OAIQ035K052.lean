-- Prove2me | Definitions.Def_OAIQ035K052
-- name    : OAIQ035K052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:09:44.558052+00:00
-- url     : https://prove2.me/theorems/9d1969cc-c204-4517-92e6-68de15b42563
-- title:
--   Definitions bundle OAIQ035K052 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 29 definitions and 22 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.ListOperation.bodyProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.coefficientsProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.downProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.kernelProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.liftProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.reduceProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.residualProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.upProgram`, `OAI.MetricKMedian.InputParser.foldProgram`, `OAI.MetricKMedian.InputParser.natRead`, `OAI.MetricKMedian.InputParser.parseBound`, `OAI.MetricKMedian.InputParser.ratRead`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.largeProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.activeDataProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.activeProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.activeRowsProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.kernelInputProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.leastProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.pivotProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.updateProgram`, `OAI.MetricKMedian.LPBinary.Nearest.amountProgram`, `OAI.MetricKMedian.LPBinary.Nearest.fillingProgram`, `OAI.MetricKMedian.LPBinary.Nearest.priorProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.Input.state`, `OAI.MetricKMedian.SparseBernoulli.Program.State.increment`, `OAI.MetricKMedian.SparseBernoulli.Program.State.step`, `OAI.MetricKMedian.SparseBernoulli.Program.incrementProgram`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.activeProgram`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.trimDataProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_NumericParserProgram`, `KMedian_Binary_SequentialParserProgram`, `KMedian_Compression_AffineListCompiler`, `KMedian_Compression_CompressionBounds`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_GaussianBinaryProgram`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Compression_GaussianListMachine`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Rounding_SignedListOperations`, `KMedian_Sparse_SparseListTrim`.
--
--   **Imports.** It imports the bundles `OAIQ035K046`, `OAIQ035K047` and `OAIQ035K048` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K055`, `OAIQ035K056` and `OAIQ035K057`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K046
import Definitions.Def_OAIQ035K047
import Definitions.Def_OAIQ035K048

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_NumericParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
@[fun_prop] theorem take_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨listTake enc default⟩
@[fun_prop] theorem drop_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨listDrop enc default⟩
@[fun_prop] theorem value_poly : Poly Word.value := ⟨BooleanLists.valueProgram⟩
@[fun_prop] theorem signed_poly : Poly (fun x : Bool × ℕ => Signed.value x.1 x.2) := ⟨intFromParts⟩
@[fun_prop] theorem mkRat_poly : Poly (fun x : ℤ × ℕ => mkRat x.1 x.2) := ⟨mkRational⟩
@[fun_prop] theorem width_poly : Poly width := by unfold width; apply list_findIdx <;> fun_prop
def natRead (xs : List Bool) : ℕ × List Bool :=
  (Word.value ((xs.drop (width xs+1)).take (width xs)),xs.drop (width xs+1+width xs))
@[fun_prop] theorem natRead_poly : Poly natRead := by
  have hd : Poly (fun xs : List Bool => xs.drop (width xs+1)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1)) (by fun_prop)
  have ht : Poly (fun xs : List Bool => (xs.drop (width xs+1)).take (width xs)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.take x.2) take_poly (pair hd width_poly)
  exact pair (Poly.comp value_poly ht) (Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1+width xs)) (by fun_prop))
def ratRead (xs : List Bool) : ℚ × List Bool :=
  let a := natRead xs.tail
  let b := natRead a.2
  (mkRat (Signed.value (xs.head?.getD false) a.1) b.1,b.2)
@[fun_prop] theorem ratRead_poly : Poly ratRead := by unfold ratRead; fun_prop
end MetricKMedian.InputParser
end

end OAI
end

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
 omit [Inhabited α] in
 theorem parseStep_poly (h : Poly read) : Poly (parseStep read) := by
  unfold parseStep
  have hh : Poly (fun x : State (α:=α) × Unit => read x.1.1) := Poly.comp h (by fun_prop)
  have ha : Poly (fun x : State (α:=α) × Unit => (read x.1.1).1 :: x.1.2) :=
    Poly.comp (f:=fun y : α × List α => y.1::y.2) list_cons (g:=fun x : State (α:=α) × Unit => ((read x.1.1).1,x.1.2)) (by fun_prop)
  exact pair (by fun_prop) ha
variable (P : PolyProgram enc enc read) (hrest : ∀ xs, (read xs).2.length≤xs.length)
noncomputable def parseBound : Polynomial ℕ := X+X*(2*P.sizeBound+1)
 omit [Inhabited α] in
 include hrest in
 theorem parseFold_size (as : List Unit) (b : State (α:=α)) :
    let out := as.foldl (fun b a => parseStep read (b,a)) b
    out.1.length≤b.1.length ∧
    (enc out.2).length≤(enc b.2).length+as.length*(2*P.sizeBound.eval (enc b.1).length+1) := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,List.length_nil,zero_mul,add_zero]; exact ⟨le_rfl,le_rfl⟩
  | cons a as ih =>
    have hh := ih (parseStep read (b,a))
    have hr := hrest b.1
    have hs := P.length_bound b.1
    have he : (enc ((read b.1).1)).length ≤ P.sizeBound.eval (enc b.1).length := by
      change (encodePair enc enc (read b.1)).length≤_ at hs
      rw [encodePair_length] at hs
      omega
    have hp : P.sizeBound.eval (enc (read b.1).2).length≤P.sizeBound.eval (enc b.1).length := by
      apply polynomial_eval_mono
      change (encodeList encodeBool (read b.1).2).length≤(encodeList encodeBool b.1).length
      rw [BooleanLists.length,BooleanLists.length]
      omega
    dsimp only [parseStep] at hh
    simp only [List.foldl_cons,List.length_cons]
    refine ⟨hh.1.trans hr,?_⟩
    have hc : (enc ((read b.1).1::b.2)).length=2*(enc (read b.1).1).length+1+(enc b.2).length := EncodedList.cons_length _ _ _
    rw [hc] at hh
    exact hh.2.trans (by nlinarith)
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def coefficientsProgram : PolyProgram ef er (fun x : ℕ × Row => coefficients x.2 x.1) := by
  let p := fst Nat.bits er
  let row := snd Nat.bits er
  let inp := row.fanout p
  let denom := inp.comp (listGetD Ratio.encode 0)
  let rem := inp.comp (listEraseIdx Ratio.encode 0)
  let divide : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.2/x.1) :=
    ((exchange Ratio.encode Ratio.encode).comp ratDiv).congr _ (fun _ => rfl)
  exact ((denom.fanout rem).comp (divide.listMapWith 0 0)).congr _ (fun _ => rfl)

noncomputable def reduceProgram : PolyProgram (encodePair (encodePair er Nat.bits) er) er
    (fun x : (Row × ℕ) × Row => reduce x.1.1 x.1.2 x.2) := by
  let ec := encodePair er Nat.bits
  let cp := fst ec er
  let c := cp.comp (fst er Nat.bits)
  let p := cp.comp (snd er Nat.bits)
  let row := snd ec er
  let inp := row.fanout p
  let rem := inp.comp (listEraseIdx Ratio.encode 0)
  let val := inp.comp (listGetD Ratio.encode 0)
  let zp := (rem.fanout c).comp (listZip Ratio.encode Ratio.encode 0 0)
  let term : PolyProgram (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)) Ratio.encode
      (fun x : ℚ × (ℚ × ℚ) => x.2.1-x.2.2*x.1) := by
    let pair := snd Ratio.encode (encodePair Ratio.encode Ratio.encode)
    let a := pair.comp (fst Ratio.encode Ratio.encode)
    let b := pair.comp (snd Ratio.encode Ratio.encode)
    let d := fst Ratio.encode (encodePair Ratio.encode Ratio.encode)
    exact ((a.fanout ((b.fanout d).comp ratMul)).comp ratSub).congr _ (fun _ => rfl)
  exact ((val.fanout zp).comp (term.listMapWith (0,0) 0)).congr _ (fun _ => rfl)

noncomputable def residualProgram : PolyProgram (encodePair ef ers) ers
    (fun x : (ℕ × Row) × Rows => residual x.1.2 x.1.1 x.2) := by
  let frame := fst ef ers
  let p := frame.comp (fst Nat.bits er)
  let c := frame.comp coefficientsProgram
  let rows := snd ef ers
  let start := (c.fanout p).fanout rows
  exact (start.comp (reduceProgram.listMapWith [] [])).congr _ (fun _ => rfl)

noncomputable def liftProgram : PolyProgram (encodePair ef er) er
    (fun x : (ℕ × Row) × Row => lift x.1.2 x.1.1 x.2) := by
  let frame := fst ef er
  let p := frame.comp (fst Nat.bits er)
  let c := frame.comp coefficientsProgram
  let z := snd ef er
  let terms := (c.fanout z).comp (listZipWith Ratio.encode Ratio.encode 0 0 ratMul)
  let value := (terms.comp ratSum).comp ratNeg
  exact (((z.fanout p).fanout value).comp (listInsertAt Ratio.encode 0)).congr _ (fun _ => rfl)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def downProgram : PolyProgram ed (encodeLoop eState er) down := by
  let dat := fst edata efs
  let slots := dat.comp (fst eslots ers)
  let rows := dat.comp (snd eslots ers)
  let frames := snd edata efs
  let row := rows.comp (listHead er [])
  let p := row.comp pivotProgram
  let frame := p.fanout row
  let tl := rows.comp (listTail er [])
  let recRows := (frame.fanout tl).comp residualProgram
  let recSlots := slots.comp (listTail eu ())
  let recFrames := (frame.fanout frames).comp (listCons ef)
  let recurse := (((recSlots.fanout recRows).fanout recFrames).comp (injectLeft eUp ed)).comp (injectRight eState er)
  let skip := (((slots.fanout tl).fanout frames).comp (injectLeft eUp ed)).comp (injectRight eState er)
  let test := (p.fanout (row.comp (listLength Ratio.encode 0))).comp natLT
  let pivotCase := ite test skip recurse
  let zeroCase := (((constant ed er []).fanout frames).comp (injectRight eUp ed)).comp (injectRight eState er)
  let noCols := ite (slots.comp (listIsEmpty eu)) pivotCase zeroCase
  let baseCase := (((slots.comp basisProgram).fanout frames).comp (injectRight eUp ed)).comp (injectRight eState er)
  exact (ite (rows.comp (listIsEmpty er)) noCols baseCase).congr _ (fun x => by
    simp only [down,Function.comp_def,decide_eq_true_eq])

noncomputable def upProgram : PolyProgram eUp (encodeLoop eState er) up := by
  let z := fst er efs
  let frames := snd er efs
  let frame := frames.comp (listHead ef (0,[]))
  let new := (frame.fanout z).comp liftProgram
  let tl := frames.comp (listTail ef (0,[]))
  let recur := ((new.fanout tl).comp (injectRight eUp ed)).comp (injectRight eState er)
  let done := z.comp (injectLeft eState er)
  exact (ite (frames.comp (listIsEmpty ef)) recur done).congr _ (fun _ => rfl)

noncomputable def bodyProgram : PolyProgram eState (encodeLoop eState er) body :=
  sumElim ed eUp downProgram upProgram (([],[]),[]) ([],[])
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianBinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Polynomial

noncomputable def kernelProgram : PolyProgram Input.encode er Input.result :=
  loopFrom startProgram bodyProgram Input.result (2*X+2) statePolynomial (fun I => by
    obtain ⟨t,ht,hrun⟩ := full_run I.encode.length I.encode.length
      (residualHeight I.encode.length I.encode.length I.encode.length)
      (returnHeight I.encode.length I.encode.length I.encode.length)
      I.rows I.cols I.data I.underdetermined (input_audit I)
    refine ⟨t,?_,?_⟩
    · have hr := (input_bounds I).1
      simp only [eval_add,eval_mul,eval_ofNat,eval_X]
      omega
    · simpa only [statePolynomial_eval,Input.result] using hrun)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def activeProgram : PolyProgram ed ees active := by
  let num := (snd Nat.bits (encodePair Signed.encode er)).comp (fst Signed.encode er)
  let test := ((num.fanout (constant ee Signed.encode 0)).comp intEQ).comp boolNot
  exact (entriesProgram.comp (test.listFilter (0,(0,[])))).congr _ (fun x => by
    simp only [Function.comp_apply,active]
    congr 1
    funext e
    simp)

noncomputable def activeRowsProgram : PolyProgram ed em activeRows := by
  let ones := activeProgram.comp ((constant ee Signed.encode 1).listMap (0,(0,[])))
  let ids := (fst es (encodePair er em)).comp (listIndices Gaussian.ListOperation.eu ())
  let a := fst Nat.bits ee
  let row := (snd Nat.bits ee).comp ((snd Nat.bits (encodePair Signed.encode er)).comp (snd Signed.encode er))
  let coord := (row.fanout a).comp (listGetD Signed.encode 0)
  let col := (exchange ees Nat.bits).comp (coord.listMapWith (0,(0,[])) 0)
  let cols := (activeProgram.fanout ids).comp (col.listMapWith 0 [])
  exact ((ones.fanout cols).comp (listCons er)).congr _ (fun _ => rfl)

noncomputable def activeDataProgram : PolyProgram ed Gaussian.IntegerProgram.ed activeData :=
  (((activeProgram.comp ((constant ee Gaussian.ListOperation.eu ()).listMap (0,(0,[])))).fanout activeRowsProgram)).congr _ (fun _ => rfl)

noncomputable def kernelInputProgram : PolyProgram Input.encode Gaussian.IntegerProgram.Input.encode Input.kernel :=
  activeDataProgram.recode Input.raw (fun _ => rfl) (fun I => by rw [activeData_raw])

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
noncomputable def leastProgram : PolyProgram ees Ratio.encode least :=
  ((((positiveProgram.listFilter (0,0)).comp (ratioProgram.listMap (0,0))).comp LPBinary.Program.minimumProgram)).congr _ (fun _ => rfl)
noncomputable def pivotProgram : PolyProgram ees Nat.bits pivot := by
  let m := fst Ratio.encode ee
  let e := snd Ratio.encode ee
  let eq := ((e.comp ratioProgram).fanout m).comp ratEQ
  let test := ((e.comp positiveProgram).fanout eq).comp boolAnd
  let tests := (leastProgram.fanout (identity ees)).comp (test.listMapWith (0,0) false)
  exact (tests.comp (listFindIdx (identity encodeBool) false)).congr _ (fun es => by
    simp only [Function.comp_def, List.findIdx_map, id_eq, pivot, Bool.decide_and])

noncomputable def updateProgram : PolyProgram (encodePair el er) el (fun x : LawData × Row => update x.1 x.2) := by
  let μ := fst el er
  let num := μ.comp (snd Signed.encode er)
  let z := snd el er
  let es := (num.fanout z).comp (listZip Signed.encode Signed.encode 0 0)
  let p := es.comp pivotProgram
  let b := (es.fanout p).comp (listGetD ee (0,0))
  let g := fst ee ee
  let e := snd ee ee
  let m1 := ((e.comp (fst Signed.encode Signed.encode)).fanout (g.comp (snd Signed.encode Signed.encode))).comp intMul
  let m2 := ((g.comp (fst Signed.encode Signed.encode)).fanout (e.comp (snd Signed.encode Signed.encode))).comp intMul
  let coord := (m1.fanout m2).comp intSub
  let nums := (b.fanout es).comp (coord.listMapWith (0,0) 0)
  let den := ((μ.comp (fst Signed.encode er)).fanout (b.comp (snd Signed.encode Signed.encode))).comp intMul
  exact (den.fanout nums).congr _ (fun _ => rfl)

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionListStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset

noncomputable def largeProgram : PolyProgram Input.encode encodeBool (fun I => decide I.large) := by
  let nums := lawProgram.comp (snd Signed.encode er)
  let nonz := (((identity Signed.encode).fanout (constant Signed.encode Signed.encode 0)).comp intEQ).comp boolNot
  let size := (nums.comp (nonz.listFilter 0)).comp (listLength Signed.encode 0)
  let dim := ((dimProgram.comp (listLength Gaussian.ListOperation.eu ())).fanout (constant Input.encode Nat.bits 1)).comp natAdd
  exact ((dim.fanout size).comp natLT).congr _ (fun I => by
    simp only [Function.comp_apply,Input.large,Input.lawData,List.length_replicate]
    congr 1
    congr 1
    change ((List.ofFn I.μ.numerator).filter (fun z => !decide (z=0))).length=I.μ.support.card
    have he : (List.ofFn I.μ.numerator).filter (fun z => !decide (z=0))=
        List.ofFn (fun j : Fin I.μ.support.card => I.μ.numerator ((I.μ.support.orderIsoOfFin rfl) j).val) := by
      simp only [← decide_not]
      rw [List.ofFn_eq_map,List.filter_map]
      exact EncodingLists.map_filter_enum _ (fun i => I.μ.numerator i≠0)
    rw [he,List.length_ofFn])

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset Polynomial

theorem iterate_denominator {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j|≤(2:ℤ)^L) (hμ : μ.denominator≤(2:ℤ)^L) (t : ℕ) :
    ((lawStep v)^[t] μ).denominator ≤ (2:ℤ)^(L+((2*(d+1)*(d+1+L))*(n+1))*t) := by
  induction t with
  | zero => simpa using hμ
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      apply (lawStep_denominator _ v L hv).trans
      apply (mul_le_mul_of_nonneg_right ih (by positivity)).trans
      rw [← pow_add]
      have he : L+((2*(d+1)*(d+1+L))*(n+1))*t+((2*(d+1)*(d+1+L))*(n+1))=
          L+((2*(d+1)*(d+1+L))*(n+1))*(t+1) := by ring
      rw [he]

theorem state_size (I : Input) (t : ℕ) (ht : t≤I.n) :
    (Input.encode (Input.step^[t] I)).length≤ statePolynomial.eval I.encode.length := by
  let L := I.encode.length
  let ν := (lawStep I.v)^[t] I.μ
  obtain ⟨hn,hd,hμ,hv⟩ := input_bounds I
  have hν : ν.denominator≤(2:ℤ)^(height L) := by
    apply (iterate_denominator I.μ I.v L hv hμ t).trans
    apply pow_le_pow_right₀ (by norm_num)
    dsimp only [height]
    gcongr
    exact ht.trans hn
  have hden : (Signed.encode ν.denominator).length≤height L+4 :=
    Signed.length_height (by rwa [abs_of_pos ν.denominator_pos])
  have hnum : (er (List.ofFn ν.numerator)).length ≤ L*(2*(height L+4)+1) := by
    apply (EncodedList.length_bound Signed.encode (List.ofFn ν.numerator) (height L+4) ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*(height L+4)+1) hn
    · intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      apply Signed.length_height
      rw [abs_of_nonneg (ν.numerator_nonneg i)]
      exact (ν.numerator_le i).trans hν
  have hfeat : (em I.features).length≤L := by
    simp only [L,Input.raw,encodePair_length]
    omega
  rw [input_iterate,Input.encode_length,statePolynomial_eval]
  exact size_arithmetic L I.d (Signed.encode ν.denominator).length
    (er (List.ofFn ν.numerator)).length (em I.features).length (height L) hd hden hnum hfeat

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseListTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}

noncomputable def activeProgram (ea : α → List Bool) (a0 : α) :
    PolyProgram (ed ea) (encodeList (encodePair Signed.encode ea)) activeEntries := by
  let l := fst el (encodeList ea)
  let nums := l.comp (snd Signed.encode er)
  let s := snd el (encodeList ea)
  let test := ((((fst Signed.encode ea).fanout (constant (encodePair Signed.encode ea) Signed.encode 0)).comp intEQ).comp boolNot)
  exact (((nums.fanout s).comp (listZip Signed.encode ea 0 a0)).comp (test.listFilter (0,a0))).congr _ (fun x => by
    simp only [Function.comp_def,activeEntries,decide_not])

noncomputable def trimDataProgram (ea : α → List Bool) (a0 : α) :
    PolyProgram (ed ea) (ed ea) trimData := by
  let zs := activeProgram ea a0
  let nums := zs.comp ((fst Signed.encode ea).listMap (0,a0))
  let states := zs.comp ((snd Signed.encode ea).listMap (0,a0))
  let den := (fst el (encodeList ea)).comp (fst Signed.encode er)
  exact ((den.fanout nums).fanout states).congr _ (fun _ => rfl)

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset

attribute [fun_prop] square_poly

theorem square_list {n : ℕ} (p : Vector ℚ n) :
    square p.toList=List.ofFn (fun z : Fin (n*n) => ((finProdFinEquiv.symm z).1.val,(finProdFinEquiv.symm z).2.val)) := by
  simp only [square,indices,Vector.length_toList,range_finRange,List.flatMap_def,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map]
  conv => lhs; arg 1; arg 1; intro i; rw [← List.ofFn_eq_map]
  exact ofFn_product _

namespace Signed

theorem valid_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (z : Fin (n*n)) :
    valid (List.ofFn β) p.toList ((finProdFinEquiv.symm z).1.val,(finProdFinEquiv.symm z).2.val)=
      decide (z∈RationalSignedStep.pairs β p) := by
  simp only [valid,frac,get_point,Gaussian.ListOperation.get_ofFn,← Bool.decide_and]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,RationalSignedStep.pairs,mem_filter,mem_univ,true_and,RationalWeightedStep.fractional,Fin.val_ne_iff]
  tauto

theorem active_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    active (List.ofFn β) p.toList=decide (RationalSignedStep.Active β p) := by
  unfold active index
  rw [square_list]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.findIdx_lt_length,List.mem_ofFn]
  constructor
  · rintro ⟨a,⟨z,rfl⟩,hz⟩
    exact ⟨z,by simpa only [valid_list,decide_eq_true_eq] using hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨_,⟨z,rfl⟩,by simpa only [valid_list,decide_eq_true_eq] using hz⟩

theorem index_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (h : RationalSignedStep.Active β p) :
    index (List.ofFn β) p.toList=((RationalSignedStep.pairs β p).min' h).val := by
  unfold index
  rw [square_list]
  let z := (RationalSignedStep.pairs β p).min' h
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using z.isLt)).mpr
  constructor
  · simp only [List.getElem_ofFn,valid_list,decide_eq_true_eq]
    exact min'_mem _ h
  · intro j hj
    simp only [List.getElem_ofFn,valid_list,decide_eq_false_iff_not]
    intro hm
    exact (not_le_of_gt hj) ((RationalSignedStep.pairs β p).min'_le _ hm)

theorem pair_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (h : RationalSignedStep.Active β p) :
    pair (List.ofFn β) p.toList=((RationalSignedStep.pair β p h).val.1.val,(RationalSignedStep.pair β p h).val.2.val) := by
  simp only [pair,index_list β p h,square_list,Gaussian.ListOperation.get_ofFn,RationalSignedStep.pair]

theorem probability_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    probability (List.ofFn β) p.toList=RationalSignedStep.probability β p := by
  unfold probability RationalSignedStep.probability
  rw [active_list]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp only [ratio,pair_list β p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
  · rfl

theorem endpoint_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) :
    endpoint (List.ofFn β) p.toList (decide (b≠0))=(RationalSignedStep.endpoint β p b).toList := by
  unfold endpoint RationalSignedStep.endpoint
  rw [active_list]
  simp only [decide_eq_true_eq]
  by_cases h : RationalSignedStep.Active β p
  · simp only [ite_eq_left h,dite_eq_left h,ratio,pair_list β p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
    by_cases hb : b=0 <;> simp [hb,move_list]
  · simp only [ite_eq_right h,dite_eq_right h]

end Signed
end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram

def State.increment (x : State) : State := ⟨⟨x.ctx.input,x.ctx.t+1⟩,x.law⟩
def State.step (d : ℕ) (x : State) : State :=
  State.increment (if x.ctx.t<x.ctx.input.n then
    Bundle.compress (fun c : Context => (c.input.n+1)^d) (fun _ => features (d:=d))
      (Bundle.branch probability probability_unit endpoint x)
    else x)

noncomputable def incrementProgram : PolyProgram State.encode State.encode State.increment := by
  let old := fst Context.encode (SparseIntegerLaw.BinarySparse.ed er)
  let inp := old.comp ((fst qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let t := old.comp ((snd qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let inc := (t.fanout (constant _ Nat.bits 1)).comp natAdd
  let law := snd Context.encode (SparseIntegerLaw.BinarySparse.ed er)
  exact ((inp.fanout inc).fanout law).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram
open SparseIntegerLaw.BinarySparse (el ed)

def Input.state (x : Input) (d t : ℕ) : State := ⟨⟨x,t⟩,run (d:=d) x.p x.feasible t⟩

 theorem state_next (x : Input) (d t : ℕ) : State.step d (x.state d t)=x.state d (t+1) := by
  have hp (ht : t<x.n) : probability ⟨x,t⟩=(fun _ => x.p ⟨t,ht⟩) := by
    funext q; simp only [probability,dite_eq_left ht]
  have he (ht : t<x.n) : endpoint ⟨x,t⟩=(fun q b => SparseBernoulli.endpoint q ⟨t,ht⟩ b) := by
    funext q b i
    simp only [endpoint,SparseBernoulli.endpoint,Fin.ext_iff]
  unfold State.step Input.state
  by_cases ht : t<x.n
  · rw [ite_eq_left ht]
    change (⟨⟨x,t+1⟩, ((run (d:=d) x.p x.feasible t).branch
      (probability ⟨x,t⟩) (probability_unit ⟨x,t⟩) (endpoint ⟨x,t⟩)).compressAuto features⟩ : State)=_
    rw [run,dite_eq_left ht]
    apply congrArg (fun μ => (⟨⟨x,t+1⟩,μ⟩ : State))
    simp only [SparseIntegerLaw.step,hp ht,he ht]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)

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
    simp only [column,dite_eq_left ht,he ht,SparseGraph.step,SparseIntegerLaw.prodCompress]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

theorem state_iterate (x : Input) (t : ℕ) : (State.step)^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest
noncomputable def priorProgram : PolyProgram (encodePair ees ee) Ratio.encode (fun x : List Entry × Entry => prior x.1 x.2) := by
  let pred := (exchange ee ee).comp beforeProgram
  let filtered := (exchange ees ee).comp (pred.listFilterWith (0,(0,0)) (0,(0,0)))
  let cap := (snd Nat.bits (encodePair Ratio.encode Ratio.encode)).comp (fst Ratio.encode Ratio.encode)
  exact ((filtered.comp (cap.listMap (0,(0,0)))).comp ratSum).congr _ (fun _ => rfl)
noncomputable def amountProgram : PolyProgram (encodePair ees ee) Ratio.encode (fun x : List Entry × Entry => amount x.1 x.2) := by
  let cap := ((snd ees ee).comp (snd Nat.bits (encodePair Ratio.encode Ratio.encode))).comp (fst Ratio.encode Ratio.encode)
  let remain := ((constant (encodePair ees ee) Ratio.encode 1).fanout priorProgram).comp ratSub
  exact ((cap.fanout (remain.comp Program.positivePart)).comp Program.ratMin).congr _ (fun _ => rfl)
noncomputable def fillingProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => filling x.1 x.2) :=
  ((entriesProgram.fanout entriesProgram).comp (amountProgram.listMapWith (0,(0,0)) 0)).congr _ (fun _ => rfl)
end Nearest
end MetricKMedian.LPBinary
end

end OAI
end


