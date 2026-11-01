-- Prove2me | Definitions.Def_OAIQ053K044
-- name    : OAIQ053K044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:05:01.733198+00:00
-- url     : https://prove2.me/theorems/10fe5f48-a5f7-4351-9477-29da7e6ad315
-- title:
--   Definitions bundle OAIQ053K044 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 70 declarations of OpenAI's Lean: 22 definitions and 48 theorems. The definitions and types are `OAI.MetricKMedian.Binary.IntegerList.prodProgram`, `OAI.MetricKMedian.Binary.PolyProgram.listAll`, `OAI.MetricKMedian.Binary.PolyProgram.listAny`, `OAI.MetricKMedian.Binary.PolyProgram.listFlatMapWith`, `OAI.MetricKMedian.Binary.PolyProgram.listFlatten`, `OAI.MetricKMedian.Binary.PolyProgram.listTake`, `OAI.MetricKMedian.Binary.PolyProgram.natSize`, `OAI.MetricKMedian.Binary.PolyProgram.ratFoldAdd`, `OAI.MetricKMedian.Binary.PolyProgram.ratFoldMul`, `OAI.MetricKMedian.Binary.PolyProgram.ratProd`, `OAI.MetricKMedian.Binary.PolyProgram.ratSum`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.el`, `OAI.MetricKMedian.PCP.Compiler.finiteCoding`, `OAI.MetricKMedian.RoundingList.Signed.active`, `OAI.MetricKMedian.RoundingList.Signed.endpoint`, `OAI.MetricKMedian.RoundingList.Signed.index`, `OAI.MetricKMedian.RoundingList.Signed.pair`, `OAI.MetricKMedian.RoundingList.Signed.probability`, `OAI.MetricKMedian.RoundingList.Signed.ratio`, `OAI.MetricKMedian.RoundingList.Signed.valid`, `OAI.MetricKMedian.RoundingList.dimensions`, `OAI.MetricKMedian.RoundingList.square`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_BinaryAutoExtras`, `KMedian_Binary_BinaryAutoFiniteLists`, `KMedian_Binary_BinaryAutomatic`, `KMedian_Binary_BinaryFloor`, `KMedian_Binary_BinaryListExtras`, `KMedian_Binary_BinaryListIndex`, `KMedian_Binary_BinaryListMap`, `KMedian_Binary_BinaryNatSum`, `KMedian_Binary_BinaryRationalFold`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_IntegerListProgram`, `KMedian_Machines_FiniteCompiler`, `KMedian_Machines_ListAllProgram`, `KMedian_Process_RoundingListOperations`, `KMedian_Process_RoundingUniformStep`, `KMedian_Rounding_SignedListOperations`, `KMedian_Sparse_SparseProductProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K038` and `OAIQ053K039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K048`, `OAIQ053K049`, `OAIQ053K050`, `OAIQ053K051`, `OAIQ053K052` and `OAIQ053K053`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K038
import Definitions.Def_OAIQ053K039

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

noncomputable def listAll {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.all p) := by
  let step := (P.second encodeBool).comp boolAnd
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool true)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.true_and] using ListAlgorithms.all p as true)

noncomputable def listAny {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.any p) := by
  let step := (P.second encodeBool).comp boolOr
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool false)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.false_or] using ListAlgorithms.any p as false)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def natSize : PolyProgram Nat.bits Nat.bits Nat.size :=
  (natAsList.comp (listLength encodeBool false)).congr _ (fun n => Nat.size_eq_bits_len n)
noncomputable def listFlatten (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList (encodeList ea)) (encodeList ea) List.flatten := by
  let P := (listAppend ea a0).listFoldLinear [] 1 (by
    intro bs as
    simp only [EncodedList.append,List.length_append]
    omega)
  exact (((identity (encodeList (encodeList ea))).fanout (constant (encodeList (encodeList ea)) (encodeList ea) [])).comp P).congr _ (fun xs => by
    change xs.foldl (fun b a => b++a) []=xs.flatten
    have he (xs : List (List α)) (acc : List α) : xs.foldl (fun b a => b++a) acc=acc++xs.flatten := by
      induction xs generalizing acc with
      | nil => simp
      | cons y ys hi => simpa only [List.foldl_cons,List.flatten_cons,List.append_assoc] using hi (acc++y)
    simpa using he xs [])
noncomputable def listFlatMapWith {f : γ × α → List β} (P : PolyProgram (encodePair ec ea) (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.flatMap (fun a => f (x.1,a))) :=
  ((P.listMapWith a0 []).comp (listFlatten eb b0)).congr _ (fun x => by rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listTake : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2) :=
  ((listSplitAt ea a0).comp (fst (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryAutomatic
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open PolyProgram Function

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
@[fun_prop] theorem rat_le_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp rat_le (pair hf hg)
@[fun_prop] theorem rat_eq_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp rat_eq (pair hf hg)
@[fun_prop] theorem nat_lt_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp nat_lt (pair hf hg)
@[fun_prop] theorem nat_le_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp nat_le (pair hf hg)
@[fun_prop] theorem nat_eq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp nat_eq (pair hf hg)
@[fun_prop] theorem ite_prop {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Poly (fun x => decide (p x))) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  exact ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => by simp only [decide_eq_true_eq])⟩

@[fun_prop] theorem list_flatMap [Inhabited β] [Inhabited γ] {f : α → β → List γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).flatMap (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFlatMapWith default default)⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryRationalFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace PolyProgram
noncomputable def ratFoldAdd : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode)
    Ratio.encode (fun x : List ℚ × ℚ => x.1.foldl (·+·) x.2) :=
  ratAdd.listFold 0 (3*X+10) (fun as b pre suf he => by
    have hh := Ratio.length_height (HasHeight.foldAdd pre b (Ratio.encode b).length (Ratio.height_length b))
    have hp : (encodeList Ratio.encode pre).length ≤ (encodeList Ratio.encode as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [encodePair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
noncomputable def ratFoldMul : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode)
    Ratio.encode (fun x : List ℚ × ℚ => x.1.foldl (·*·) x.2) :=
  ratMul.listFold 0 (3*X+10) (fun as b pre suf he => by
    have hh := Ratio.length_height (HasHeight.foldMul pre b (Ratio.encode b).length (Ratio.height_length b))
    have hp : (encodeList Ratio.encode pre).length ≤ (encodeList Ratio.encode as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [encodePair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
noncomputable def ratSum : PolyProgram (encodeList Ratio.encode) Ratio.encode List.sum := by
  refine (((identity (encodeList Ratio.encode)).fanout (constant (encodeList Ratio.encode) Ratio.encode 0)).comp ratFoldAdd).congr _ ?_
  intro as
  simp only [Function.comp_apply,id_eq]
  simpa only [zero_add] using ListAlgorithms.foldAdd as 0
noncomputable def ratProd : PolyProgram (encodeList Ratio.encode) Ratio.encode List.prod := by
  refine (((identity (encodeList Ratio.encode)).fanout (constant (encodeList Ratio.encode) Ratio.encode 1)).comp ratFoldMul).congr _ ?_
  intro as
  simp only [Function.comp_apply,id_eq]
  simpa only [one_mul] using ListAlgorithms.foldMul as 1
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryAutoExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary.Automatic.Poly
open PolyProgram
variable {α β γ : Type} [Coding α] [Coding γ]

@[fun_prop] theorem nat_div : Poly (fun x : ℕ × ℕ => x.1/x.2) := ⟨natDiv⟩
@[fun_prop] theorem nat_mod : Poly (fun x : ℕ × ℕ => x.1%x.2) := ⟨natMod⟩
@[fun_prop] theorem nat_pow (n : ℕ) : Poly (fun x : ℕ => x^n) := by
  induction n with
  | zero => simpa only [pow_zero] using const (α:=ℕ) 1
  | succ n ih =>
    simpa only [pow_succ,id_eq] using comp nat_mul (pair ih identity)

 theorem fixed_map (bs : List β) (f : α → β → γ)
    (hf : ∀ b∈bs, Poly (fun x => f x b)) : Poly (fun x => bs.map (f x)) := by
  induction bs with
  | nil => exact const []
  | cons b bs ih =>
    exact comp list_cons (pair (hf b (by simp)) (ih (fun c hc => hf c (by simp [hc]))))

@[fun_prop] theorem rat_prod : Poly (List.prod : List ℚ → ℚ) := ⟨ratProd⟩
@[fun_prop] theorem rat_sum : Poly (List.sum : List ℚ → ℚ) := ⟨ratSum⟩
@[fun_prop] theorem bool_all : Poly (fun xs : List Bool => xs.all id) := ⟨listAll (PolyProgram.identity _) false⟩

end MetricKMedian.Binary.Automatic.Poly
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryAutoFiniteLists
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Binary.Automatic.Poly
open PolyProgram
@[fun_prop] theorem bool_any : Poly (fun xs : List Bool => xs.any id) := ⟨listAny (PolyProgram.identity _) false⟩
@[fun_prop] theorem list_take {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨listTake enc default⟩
@[fun_prop] theorem list_drop {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨listDrop enc default⟩

@[fun_prop] theorem natMember_poly : Poly natMember := by
  unfold natMember
  apply comp bool_any
  apply list_map <;> fun_prop
@[simp] theorem natMember_true (xs : List ℕ) (i : ℕ) : natMember (xs,i)=true ↔ i∈xs := by
  simp only [natMember,List.any_map,List.any_eq_true,id_eq,Function.comp_def,decide_eq_true_eq]
  simp only [exists_eq_right]
end MetricKMedian.Binary.Automatic.Poly

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryFloor
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary.Automatic.Poly
@[fun_prop] theorem int_natAbs : Poly Int.natAbs := by
  exact ⟨(PolyProgram.snd encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem rat_num : Poly Rat.num := by
  exact ⟨(PolyProgram.fst Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem rat_den : Poly Rat.den := by
  exact ⟨(PolyProgram.snd Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem rat_floor : Poly (fun q : ℚ => ⌊q⌋₊) := by
  have division : Poly (fun values : ℕ × ℕ => values.1 / values.2) :=
    ⟨PolyProgram.natDiv⟩
  have floorProgram : Poly (fun rational : ℚ =>
      if decide (rational < 0) then 0 else rational.num.natAbs / rational.den) :=
    ite (rat_lt_comp identity (const 0)) (const 0)
      (comp division (pair (comp int_natAbs rat_num) rat_den))
  simpa only [decide_eq_true_eq,← natFloor_eq] using floorProgram
end MetricKMedian.Binary.Automatic.Poly
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryNatSum
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Binary.Automatic.Poly
@[fun_prop] theorem nat_list_sum : Poly (List.sum : List ℕ → ℕ) := by
  have hm : Poly (fun xs : List ℕ => xs.map (fun n : ℕ => (n:ℚ))) := by
    apply list_map <;> fun_prop
  have h : Poly (fun xs : List ℕ => ⌊(xs.map (fun n : ℕ => (n:ℚ))).sum⌋₊) :=
    comp rat_floor (comp rat_sum hm)
  have he : (fun xs : List ℕ => ⌊(xs.map (fun n : ℕ => (n:ℚ))).sum⌋₊)=List.sum := by
    funext xs
    change ⌊(xs.map (Nat.cast : ℕ → ℚ)).sum⌋₊ = xs.sum
    rw [← Nat.cast_list_sum]
    exact Nat.floor_natCast xs.sum
  rw [he] at h
  exact h
@[fun_prop] theorem nat_min : Poly (fun x : ℕ × ℕ => min x.1 x.2) := by
  have h : Poly (fun x : ℕ × ℕ => if decide (x.1≤x.2) then x.1 else x.2) := by fun_prop
  have he : (fun x : ℕ × ℕ => if decide (x.1≤x.2) then x.1 else x.2)=(fun x => min x.1 x.2) := by
    funext x
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (le_of_not_ge h)).symm
  rw [he] at h
  exact h
end MetricKMedian.Binary.Automatic.Poly
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open PolyProgram Function
namespace IntegerList
noncomputable def prodProgram : PolyProgram er Signed.encode List.prod :=
  (((ratOfInt.listMap 0).comp ratProd).comp ratNum).congr _ (fun xs => by
    simp only [Function.comp_apply,← Int.cast_list_prod,Rat.num_intCast])

end IntegerList
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionListStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
abbrev el := ListPivot.el

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteCompiler

namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

@[instance_reducible]
noncomputable def finiteCoding (A : Type) [Fintype A] : Coding A :=
  ⟨fun a => Nat.bits (Fintype.equivFin A a).val⟩
lemma poly_congr {A B : Type} [Coding A] [Coding B] {f g : A → B}
    (h : Poly f) (he : ∀ a, f a=g a) : Poly g := ⟨h.program.congr g he⟩
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_ListAllProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPListAllProgram
namespace MetricKMedian.Binary.Automatic.Poly
open scoped Classical

lemma list_all {X A : Type} [Coding X] [Coding A] [Inhabited X] [Inhabited A]
    {f : X→A→Bool} {xs : X→List A} (hf : Poly (fun z : X×A=>f z.1 z.2))
    (hx : Poly xs) : Poly (fun x=>(xs x).all (f x)) := by
  have hh := list_empty.comp (list_filter (f:=fun x a=>!f x a) (bool_not.comp hf) hx)
  apply MetricKMedian.PCP.Compiler.poly_congr hh
  intro x
  rw [Bool.eq_iff_iff]
  simp only [List.isEmpty_iff,List.filter_eq_nil_iff,Bool.not_eq_true_eq_eq_false,
    Bool.not_eq_false,List.all_eq_true]
end MetricKMedian.Binary.Automatic.Poly

end Inline_PCPListAllProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset

@[fun_prop] theorem frac_poly : Poly frac := by unfold frac; fun_prop
@[fun_prop] theorem indices_poly : Poly indices := list_indices
@[fun_prop] theorem fractional_poly : Poly fractional := by
  unfold fractional
  apply list_filter <;> fun_prop
@[fun_prop] theorem first_poly : Poly first := by
  unfold first
  apply list_findIdx <;> fun_prop
@[fun_prop] theorem second_poly : Poly second := by
  unfold second
  apply list_findIdx
  · simp only [ne_eq,decide_not]
    fun_prop
  · fun_prop
@[fun_prop] theorem active_poly : Poly active := by unfold active; fun_prop
@[fun_prop] theorem ratio_poly : Poly (fun x : Row × Row => ratio x.1 x.2) := by unfold ratio; fun_prop
@[fun_prop] theorem up_poly : Poly (fun x : Row × (ℕ × (ℕ × ℚ)) => up x.1 x.2.1 x.2.2.1 x.2.2.2) := by unfold up; fun_prop
@[fun_prop] theorem down_poly : Poly (fun x : Row × (ℕ × (ℕ × ℚ)) => down x.1 x.2.1 x.2.2.1 x.2.2.2) := by unfold down; fun_prop
@[fun_prop] theorem move_poly : Poly (fun x : Row × (ℕ × (ℕ × (ℚ × ℚ))) => move x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold move
  apply list_map
  · fun_prop
  · fun_prop
@[fun_prop] theorem probability_poly : Poly (fun x : Row × Row => probability x.1 x.2) := by unfold probability; fun_prop
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (fun x : Row × Row => endpoint x.1 x.2 b) := by
  unfold endpoint
  cases b <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> fun_prop

end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset

def square (p : Row) : List (ℕ × ℕ) := (indices p).flatMap (fun i => (indices p).map (fun j => (i,j)))

theorem square_poly : Poly square := by
  unfold square
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop
attribute [fun_prop] square_poly

namespace Signed

def valid (β p : Row) (ij : ℕ × ℕ) : Bool :=
  frac (p[ij.1]?.getD 0) && frac (p[ij.2]?.getD 0) &&
    decide (ij.1≠ij.2) && decide (0<β[ij.1]?.getD 0*β[ij.2]?.getD 0)
def index (β p : Row) : ℕ := (square p).findIdx (valid β p)
def pair (β p : Row) : ℕ × ℕ := (square p)[index β p]?.getD (0,0)
def active (β p : Row) : Bool := decide (index β p<(square p).length)
def ratio (β p : Row) : ℚ := β[(pair β p).1]?.getD 0/β[(pair β p).2]?.getD 0

def probability (β p : Row) : ℚ :=
  if active β p then
    down p (pair β p).1 (pair β p).2 (ratio β p) /
      (up p (pair β p).1 (pair β p).2 (ratio β p)+down p (pair β p).1 (pair β p).2 (ratio β p))
  else 0

def endpoint (β p : Row) (b : Bool) : Row :=
  if active β p then move p (pair β p).1 (pair β p).2 (ratio β p)
    (if b then -down p (pair β p).1 (pair β p).2 (ratio β p) else up p (pair β p).1 (pair β p).2 (ratio β p))
  else p

@[fun_prop] theorem valid_poly : Poly (fun x : (Row × Row) × (ℕ × ℕ) => valid x.1.1 x.1.2 x.2) := by
  unfold valid
  simp only [ne_eq,decide_not]
  fun_prop
@[fun_prop] theorem index_poly : Poly (fun x : Row × Row => index x.1 x.2) := by
  unfold index
  apply list_findIdx <;> fun_prop
@[fun_prop] theorem pair_poly : Poly (fun x : Row × Row => pair x.1 x.2) := by unfold pair; fun_prop
@[fun_prop] theorem active_poly : Poly (fun x : Row × Row => active x.1 x.2) := by unfold active; fun_prop
@[fun_prop] theorem ratio_poly : Poly (fun x : Row × Row => ratio x.1 x.2) := by unfold ratio; fun_prop
@[fun_prop] theorem probability_poly : Poly (fun x : Row × Row => probability x.1 x.2) := by unfold probability; fun_prop
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (fun x : Row × Row => endpoint x.1 x.2 b) := by
  unfold endpoint
  cases b <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> fun_prop

end Signed
end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly

def dimensions (p : Row) : List Unit := (indices p).map (fun _ => ()) ++ (square p).map (fun _ => ())

end MetricKMedian.RoundingList

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseProductProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Binary.Automatic.Poly
@[fun_prop] theorem int_mul : Poly (fun x : ℤ × ℤ => x.1*x.2) := ⟨PolyProgram.intMul⟩
end MetricKMedian.Binary.Automatic.Poly

end

end OAI
end


