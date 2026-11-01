-- Prove2me | Definitions.Def_OAIQ053K051
-- name    : OAIQ053K051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:09:09.424675+00:00
-- url     : https://prove2.me/theorems/6fe93382-bac8-48ab-b63e-28a8e6b7025d
-- title:
--   Definitions bundle OAIQ053K051 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 32 definitions and 17 theorems. The definitions and types are `OAI.MetricKMedian.InputParser.parse`, `OAI.MetricKMedian.IntegerLaw.ListOperation.activeDataProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.activeProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.activeRowsProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.kernelInputProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.leastProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.pivotProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.updateProgram`, `OAI.MetricKMedian.LPBinary.Input.scaleProgram`, `OAI.MetricKMedian.LPBinary.Input.zeroOutputProgram`, `OAI.MetricKMedian.LPBinary.Program.chooseProgram`, `OAI.MetricKMedian.LPBinary.Program.componentProgram`, `OAI.MetricKMedian.LPBinary.Program.dualAffineProgram`, `OAI.MetricKMedian.LPBinary.Program.dualBestProgram`, `OAI.MetricKMedian.LPBinary.Program.dualValueProgram`, `OAI.MetricKMedian.LPBinary.Program.gradientProgram`, `OAI.MetricKMedian.LPBinary.Program.levelProgram`, `OAI.MetricKMedian.LPBinary.Program.maximumProgram`, `OAI.MetricKMedian.LPBinary.Program.nextProgram`, `OAI.MetricKMedian.LPBinary.Program.objectiveProgram`, `OAI.MetricKMedian.LPBinary.Program.optimizeProgram`, `OAI.MetricKMedian.LPBinary.Program.projectProgram`, `OAI.MetricKMedian.LPBinary.Program.startProgram`, `OAI.MetricKMedian.LPBinary.Program.statesProgram`, `OAI.MetricKMedian.LPBinary.Program.stepsProgram`, `OAI.MetricKMedian.LPBinary.Program.thresholdProgram`, `OAI.MetricKMedian.LPBinary.Program.thresholdsProgram`, `OAI.MetricKMedian.LPBinary.Program.updateProgram`, `OAI.MetricKMedian.LPBinary.Program.valueProgram`, `OAI.MetricKMedian.LPBinary.statePolynomial`, `OAI.MetricKMedian.SparseCounts.Program.Input.state`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.μ`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_SequentialParserProgram`, `KMedian_Compression_AffineListCompiler`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_DualListCompiler`, `KMedian_Optimization_FractionalSelectProgram`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPBinaryTrajectory`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Optimization_TruncatedListCompiler`, `KMedian_Process_CountRunProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Programs_ScaleListProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseProduct`.
--
--   **Imports.** It imports the bundles `OAIQ053K044`, `OAIQ053K045`, `OAIQ053K046` and `OAIQ053K047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K056`, `OAIQ053K057`, `OAIQ053K058`, `OAIQ053K060`, `OAIQ053K061` and `OAIQ053K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K044
import Definitions.Def_OAIQ053K045
import Definitions.Def_OAIQ053K046
import Definitions.Def_OAIQ053K047

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
 omit [Inhabited α] in
 theorem parseStep_poly (h : Poly read) : Poly (parseStep read) := by
  unfold parseStep
  have hh : Poly (fun x : State (α:=α) × Unit => read x.1.1) := Poly.comp h (by fun_prop)
  have ha : Poly (fun x : State (α:=α) × Unit => (read x.1.1).1 :: x.1.2) :=
    Poly.comp (f:=fun y : α × List α => y.1::y.2) list_cons (g:=fun x : State (α:=α) × Unit => ((read x.1.1).1,x.1.2)) (by fun_prop)
  exact pair (by fun_prop) ha
variable (P : PolyProgram enc enc read) (hrest : ∀ xs, (read xs).2.length≤xs.length)
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListCompiler
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.scaledFeatures_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input

 theorem bounds (I : Input) : I.n ≤ I.encode.length ∧ I.m ≤ I.encode.length ∧ I.k ≤ I.encode.length ∧
    ∀ j i, HasHeight (I.distance j i) I.encode.length := by
  let L := I.encode.length
  have henc : L=2*(ers I.rows).length+1+I.k.bits.length := by
    simp only [L,raw,encodePair_length]
  have hm := EncodedList.length_le er I.rows
  change I.rows.length ≤ (ers I.rows).length at hm
  simp only [rows,List.length_ofFn] at hm
  change I.m ≤ (ers I.rows).length at hm
  have hrow (j : Fin I.m) : (er (List.ofFn (I.distance j))).length  ≤  (ers I.rows).length :=
    EncodedList.member_length er I.rows _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  have hn := EncodedList.length_le Ratio.encode (List.ofFn (I.distance ⟨0,I.mpos⟩))
  change (List.ofFn (I.distance ⟨0,I.mpos⟩)).length ≤ (er (List.ofFn (I.distance ⟨0,I.mpos⟩))).length at hn
  simp only [List.length_ofFn] at hn
  have hnL : I.n ≤ L := by have hh := hrow ⟨0,I.mpos⟩; omega
  refine ⟨hnL,by omega,I.kle.trans hnL,?_⟩
  intro j i
  have hh := EncodedList.member_length Ratio.encode (List.ofFn (I.distance j)) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  change (Ratio.encode (I.distance j i)).length ≤ (er (List.ofFn (I.distance j))).length at hh
  have hrow := hrow j
  exact (Ratio.height_length _).mono (by omega)

end Input

 theorem penalty_bound (I : Input) (r : ℕ) : TruncatedLP.penalty r I.k  ≤  4*r*(I.encode.length+1) := by
  unfold TruncatedLP.penalty
  gcongr
  exact I.bounds.2.2.1
 theorem grad_bound (I : Input) (r : ℕ) :
    TruncatedLP.gradSize (n:=I.n) (m:=I.m) (TruncatedLP.penalty r I.k)  ≤  gradientBound r I.encode.length := by
  unfold TruncatedLP.gradSize gradientBound
  gcongr
  · exact I.bounds.1
  · exact I.bounds.2.1
  · exact penalty_bound I r
 theorem steps_bound (I : Input) (r : ℕ) :
    TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)  ≤  stepsBound r I.encode.length := by
  unfold TruncatedLP.steps stepsBound
  gcongr
  · exact grad_bound I r
  · exact I.bounds.2.2.1

 theorem iterate_height (I : Input) (r : ℕ) (hr : 0 < r) (t : ℕ)
    (ht : t ≤ TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)) (i : Fin I.n) :
    HasHeight (ProjectedSubgradient.point (I.vector r t) i) (heightBound r I.encode.length) := by
  let L := I.encode.length
  let q := fun p : Fin I.m × Fin I.n => I.distance p.1 p.2
  let R := RationalScaling.denominator q
  have hR : 0 < R := RationalScaling.denominator_pos q
  have hd : ∀ j i, RationalGrid.At R (I.distance j i) := by
    intro j i
    refine ⟨RationalScaling.numerator q (j,i),?_⟩
    rw [RationalScaling.numerator_cast,mul_div_cancel_right₀]
    exact_mod_cast hR.ne'
  have hRbound : R ≤ (2:ℤ)^(L*(L*L)) := by
    have hh := RationalScaling.denominator_bound q L (fun p => (I.bounds.2.2.2 p.1 p.2).2)
    simp only [Fintype.card_prod,Fintype.card_fin] at hh
    apply hh.trans
    apply pow_le_pow_right₀ (by norm_num)
    gcongr
    · exact I.bounds.2.1
    · exact I.bounds.1
  have hbn : TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*(I.n:ℤ) ≤ baseBound r L := by
    unfold TruncatedLP.rateDen
    have hg := grad_bound I r
    have hn := I.bounds.1
    dsimp only [baseBound]
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left (2*r) hg) hn
  have hnat : (baseBound r L:ℤ) ≤ (2:ℤ)^(baseBound r L) := by exact_mod_cast (Nat.lt_two_pow_self (n:=baseBound r L)).le
  have hbase : TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*R*(I.n:ℤ) ≤ (2:ℤ)^(exponentBound r L) := by
    calc
      _ = (TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*(I.n:ℤ))*R := by ring
      _  ≤  (2:ℤ)^(baseBound r L)*(2:ℤ)^(L*(L*L)) := mul_le_mul (hbn.trans hnat) hRbound hR.le (by positivity)
      _ = (2:ℤ)^(baseBound r L+L*(L*L)) := (pow_add ..).symm
      _  ≤  _ := pow_le_pow_right₀ (by norm_num) (by unfold exponentBound; omega)
  have hk : (I.k:ℤ) ≤ (2:ℤ)^(exponentBound r L) := by
    have hkL : (I.k:ℤ) ≤ L := by exact_mod_cast I.bounds.2.2.1
    have hL : (L:ℤ) ≤ (2:ℤ)^L := by exact_mod_cast (Nat.lt_two_pow_self (n:=L)).le
    exact (hkL.trans hL).trans (pow_le_pow_right₀ (by norm_num) (by unfold exponentBound; omega))
  have hh := TruncatedLP.trajectory_height I.distance r I.k (TruncatedLP.penalty r I.k) hr I.kpos
    (TruncatedLP.penalty_pos r I.k hr) R hR hd (exponentBound r L) hbase hk t i
  apply hh.mono
  unfold heightBound
  exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (ht.trans (steps_bound I r)))

 theorem iterate_size (I : Input) (r : ℕ) (hr : 0 < r) (t : ℕ)
    (ht : t ≤ TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)) :
    (er (I.iterate r t)).length  ≤  I.encode.length*(2*(3*heightBound r I.encode.length+10)+1) := by
  have hh := EncodedList.length_bound Ratio.encode (I.iterate r t) (3*heightBound r I.encode.length+10) (by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact Ratio.length_height (iterate_height I r hr t ht i))
  simp only [Input.iterate,List.length_ofFn] at hh
  exact hh.trans (Nat.mul_le_mul_right _ I.bounds.1)

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexListProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_DualListCompiler
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedListCompiler
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function

namespace Program
noncomputable def startProgram (r : ℕ) : PolyProgram Input.encode es (start r) :=
  (inputRaw.comp ((rawContextProgram r).fanout rawInitialProgram)).congr _ (fun _ => rfl)
noncomputable def stepsProgram (r : ℕ) : PolyProgram Input.encode Nat.bits (fun I => rawSteps r I.raw) :=
  (inputRaw.comp (rawStepsProgram r)).congr _ (fun _ => rfl)
noncomputable def updateProgram : PolyProgram es es update := by
  let c := fst ec er
  let ds := c.comp (fst ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
  let hkr := c.comp (snd ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
  let h := hkr.comp (fst Ratio.encode (encodePair Ratio.encode Ratio.encode))
  let kr := hkr.comp (snd Ratio.encode (encodePair Ratio.encode Ratio.encode))
  let args := (((ds.fanout (snd ec er)).fanout h).fanout kr)
  exact (c.fanout (args.comp nextProgram)).congr _ (fun _ => rfl)
end Program

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryTrajectory
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Polynomial Function

noncomputable def statePolynomial (r : ℕ) : Polynomial ℕ :=
  2*(Program.startProgram r).sizeBound+1+X*(2*(3*heightPolynomial r+10)+1)

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

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximationListProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.TruncatedLP.instDecidableValid
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

end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_ScaleListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Input

noncomputable def scaleProgram : PolyProgram (encodePair Input.encode Ratio.encode) Input.encode (fun x : Input × ℚ => x.1.scale x.2) := by
  let coord := (exchange Ratio.encode Ratio.encode).comp ratDiv
  let matrix := (coord.listMapWith 0 0).listMapWith [] []
  let I := fst Input.encode Ratio.encode
  let B := snd Input.encode Ratio.encode
  let ds := I.comp (Program.inputRaw.comp (fst ers Nat.bits))
  let k := I.comp (Program.inputRaw.comp (snd ers Nat.bits))
  let raw := ((B.fanout ds).comp matrix).fanout k
  exact raw.recode id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_apply,id_eq]
    change ei ((x.1.rows.map (fun ds => ds.map (fun d => d/x.2))),x.1.k)=ei ((x.1.scale x.2).raw)
    rw [Input.raw,scale_rows]
    rfl)
end Input
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalSelectProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Input
noncomputable def zeroOutputProgram : PolyProgram Input.encode Repair.eo Input.zeroOutput := by
  let rows := Program.inputRaw.comp (fst ers Nat.bits)
  let rowZero := (constant Ratio.encode Ratio.encode 0).listMap 0
  let mat := rows.comp (rowZero.listMap [])
  let row := (rows.comp (listHead er [])).comp rowZero
  exact (row.fanout mat).congr _ (fun I => by
    change (((I.rows.head?.getD []).map (fun _ => (0:ℚ))),I.rows.map (fun ds => ds.map (fun _ => (0:ℚ))))=I.zeroOutput
    have hi : I.rows.head?.getD []=List.ofFn (I.distance ⟨0,I.mpos⟩) := by
      dsimp only [Input.rows]
      rw [List.head?_eq_getElem?]
      simp only [List.getElem?_ofFn, I.mpos, dite_eq_left, Option.getD_some]
    rw [hi]
    simp only [Input.rows,List.map_ofFn,Function.comp_def,Input.zeroOutput,List.ofFn_const])
end Input
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

theorem prodCompress_spec {d : ℕ} (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (v : γ → Fin d → ℚ) :
    let ρ := μ.prodCompress ν f v
    ρ.length ≤ d+1 ∧
    (∀ a : Fin ρ.length, ∃ b : Fin μ.length, ∃ c : Fin ν.length,
      ρ.states[a.val]=f μ.states[b.val] ν.states[c.val]) ∧
    ∀ j, ρ.moment (fun t => v t j)=μ.moment (fun a => ν.moment (fun b => v (f a b) j)) := by
  have h := (μ.prod ν f).compressAuto_correct v
  refine ⟨h.1,?_,fun j => (h.2.2 j).trans (prod_moment μ ν f _)⟩
  intro a
  obtain ⟨b,hb⟩ := h.2.1 a
  refine ⟨((finProdFinEquiv (m := μ.length) (n := ν.length)).symm b).1,((finProdFinEquiv (m := μ.length) (n := ν.length)).symm b).2,?_⟩
  exact hb.trans (by
    simp only [prod,Vector.getElem_ofFn]
    congr 3)

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_PivotListProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Process_CountRunProgram
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
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

theorem run_length (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) (t : ℕ) :
    (run ν t).length ≤ n*m+(n*m)*(n*m)+1 := by
  induction t with
  | zero => change 1 ≤ _; omega
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · exact ((run ν t).prodCompress_spec (ν ⟨t,ht⟩)
        (fun G S => next G S ⟨t,ht⟩) features).1
    · exact ih

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)

def Input.μ (x : Input) := SparseSignedRounding.round (SparseSignedPreparation.signed x.D x.c) x.p x.feasible

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end


