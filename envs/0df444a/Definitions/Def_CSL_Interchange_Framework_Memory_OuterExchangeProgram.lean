-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Memory_OuterExchangeProgram
-- name    : CSL_Interchange_Framework_Memory_OuterExchangeProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:37:09.821492+00:00
-- url     : https://prove2.me/theorems/2e4d3b84-2b88-46b0-b142-94c95073654f
-- title:
--   Coded sorting library: Interchange / Framework / Memory / OuterExchangeProgram
-- statement:
--   Module `CodedSorting.Interchange.Framework.Memory.OuterExchangeProgram` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Actual shared scans surrounding the encoded network execution.
--   The field is a vector of residues; subtraction is coordinatewise and never
--   integer subtraction with carries across its packed representation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Memory.OuterExchangeProgram

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Fields_ScalarLayoutBridge
import Definitions.Def_CSL_Shared_Memory_BlockDigitMove

/-! Actual shared scans surrounding the encoded network execution.
The field is a vector of residues; subtraction is coordinatewise and never
integer subtraction with carries across its packed representation. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CSL.OuterExchangeProgram
open Address RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge CodedSimulation
open CommonAddressLayout SingleCoordinate ScanProgram CoordinateScans
noncomputable section

local instance : LinearOrder Index := RecursiveExchange.indexOrder
local instance : LE Index := RecursiveExchange.indexOrder.toLE
local instance : LT Index := RecursiveExchange.indexOrder.toLT
local instance : WellFoundedLT Index :=
  @Finite.to_wellFoundedLT Index inferInstance RecursiveExchange.indexOrder.toPreorder

abbrev Addr (f P G S : ℕ) :=
  LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f

def digitShape (f P G S : ℕ) :=
  CommonAddressLayout.shape (Equiv.refl (Fin P)) (digitVector f)
    (Equiv.refl (Fin G)) (Equiv.refl (Fin S))

def scalarVolume (f P G S : ℕ) (i : Index) :
    (ChildPrefix P (radix^f) i*(radix^f*ChildGap G (radix^f) i i))*
      (radix^f*ChildSuffix S (radix^f) i) = longVolume f P G S :=
  (CommonAddressLayout.childVolume i i).trans (CoordinateLayoutBridge.volume_eq f P G S)

def addOne (f P G S : ℕ) (i : Index) : List (Pass (longVolume f P G S)) :=
  BlockDigitMove.castProgram (scalarVolume f P G S i)
    (ScalarCoordinateProgram.before (P := ChildPrefix P (radix^f) i)
      (Q := radix^f) (G := ChildGap G (radix^f) i i) (S := ChildSuffix S (radix^f) i))

def reflectOne (f P G S : ℕ) (hS : 0 < S) (i : Index) :
    List (Pass (longVolume f P G S)) :=
  BlockDigitMove.castProgram (scalarVolume f P G S i)
    (ScalarCoordinateProgram.after (P := ChildPrefix P (radix^f) i)
      (Q := radix^f) (G := ChildGap G (radix^f) i i)
      (mul_pos (pow_pos (NeZero.pos (radix^f)) _) hS))

def subtractOne (f P G S : ℕ) (i : Index) : List (Pass (longVolume f P G S)) :=
  BlockDigitMove.inverseProgram (addOne f P G S i)

theorem digitShape_before (f P G S : ℕ) (i : Index) (a : Addr f P G S) :
    digitShape f P G S (beforeScan i i a) =
      beforeScan i i (digitShape f P G S a) := by
  rcases a with ⟨p,h,g,d,s⟩
  simp only [digitShape,CommonAddressLayout.shape,beforeScan,modifySelected,
    Equiv.coe_fn_mk,Equiv.refl_apply,digitVector,Equiv.arrowCongr_apply,
    lowerAdd,lowerReflect,Function.update_eq_self]
  congr 1 <;> funext j <;> by_cases hj : j=i <;>
    simp [Function.update,hj,Equiv.arrowCongr_apply,Function.comp_def]
  try exact map_add (ZMod.finEquiv (radix^f)).symm _ _

theorem digitShape_after (f P G S : ℕ) (i : Index) (a : Addr f P G S) :
    digitShape f P G S (afterScan i i a) =
      afterScan i i (digitShape f P G S a) := by
  rcases a with ⟨p,h,g,d,s⟩
  simp only [digitShape,CommonAddressLayout.shape,afterScan,modifySelected,
    Equiv.coe_fn_mk,Equiv.refl_apply,digitVector,Equiv.arrowCongr_apply,
    lowerAdd,lowerReflect,Function.update_eq_self]
  congr 1 <;> funext j <;> by_cases hj : j=i <;>
    simp [Function.update,hj,Equiv.arrowCongr_apply,Function.comp_def]
  try exact map_sub (ZMod.finEquiv (radix^f)).symm _ _

theorem common_scalar (f P G S : ℕ) (i : Index) (a : Addr f P G S) :
    commonLayout f P G S a = finCongr (scalarVolume f P G S i)
      (CommonAddressLayout.childLayout i i (repack i i (digitShape f P G S a))) := by
  apply Fin.ext
  rw [commonLayout_apply,finCongr_apply_coe,finCongr_apply_coe,
    CommonAddressLayout.childLayout_repack_val]
  rfl

theorem addOne_destination (f P G S : ℕ) (i : Index) (a : Addr f P G S) :
    destination (addOne f P G S i) (commonLayout f P G S a) =
      commonLayout f P G S (beforeScan i i a) := by
  rw [common_scalar f P G S i a,addOne,BlockDigitMove.castProgram_destination]
  have he := ScalarCoordinateProgram.before_encoded
    (childShape i i (repack i i (digitShape f P G S a)))
  rw [common_scalar f P G S i (beforeScan i i a),digitShape_before]
  apply congrArg (finCongr (scalarVolume f P G S i))
  rw [show beforeScan i i (digitShape f P G S a) =
    modifySelected i i lowerAddPerm (digitShape f P G S a) from rfl]
  change destination ScalarCoordinateProgram.before _ = _
  rw [show CommonAddressLayout.childLayout i i
      (repack i i (modifySelected i i lowerAddPerm (digitShape f P G S a))) =
      lowLayout (childShape i i (repack i i
        (modifySelected i i lowerAddPerm (digitShape f P G S a)))) from rfl,
    selected_encoded]
  exact he

theorem reflectOne_destination (f P G S : ℕ) (hS : 0 < S) (i : Index)
    (a : Addr f P G S) :
    destination (reflectOne f P G S hS i) (commonLayout f P G S a) =
      commonLayout f P G S (afterScan i i a) := by
  rw [common_scalar f P G S i a,reflectOne,BlockDigitMove.castProgram_destination]
  have he := ScalarCoordinateProgram.after_encoded
    (mul_pos (pow_pos (NeZero.pos (radix^f)) _) hS)
    (childShape i i (repack i i (digitShape f P G S a)))
  rw [common_scalar f P G S i (afterScan i i a),digitShape_after]
  apply congrArg (finCongr (scalarVolume f P G S i))
  rw [show afterScan i i (digitShape f P G S a) =
    modifySelected i i lowerReflectPerm (digitShape f P G S a) from rfl]
  change destination (ScalarCoordinateProgram.after _) _ = _
  rw [show CommonAddressLayout.childLayout i i
      (repack i i (modifySelected i i lowerReflectPerm (digitShape f P G S a))) =
      lowLayout (childShape i i (repack i i
        (modifySelected i i lowerReflectPerm (digitShape f P G S a)))) from rfl,
    selected_encoded]
  exact he

/-- One selected coordinate of the low vector; all high coordinates and
all spectator fields stay at their existing physical positions. -/
def lowStep {I R P G S : Type*} [DecidableEq I] (op : R → R → R)
    (i : I) (a : FullAddress P (I → R) G S) : FullAddress P (I → R) G S :=
  ⟨a.prefixCoord,a.high,a.gap,Function.update a.low i (op (a.high i) (a.low i)),a.suffix⟩

theorem subtractOne_destination (f P G S : ℕ) (i : Index) (a : Addr f P G S) :
    destination (subtractOne f P G S i) (commonLayout f P G S a) =
      commonLayout f P G S (lowStep (fun h d => d-h) i a) := by
  rw [subtractOne,BlockDigitMove.inverseProgram_destination]
  apply (destination (addOne f P G S i)).injective
  rw [Equiv.apply_symm_apply,addOne_destination]
  congr 1
  cases a
  simp only [beforeScan,modifySelected,lowStep,lowerAdd]
  congr 1 <;> funext j <;> by_cases hj : j=i <;> simp [Function.update,hj]

theorem reflectOne_lowStep (f P G S : ℕ) (hS : 0 < S) (i : Index) (a : Addr f P G S) :
    destination (reflectOne f P G S hS i) (commonLayout f P G S a) =
      commonLayout f P G S (lowStep (fun h d => h-d) i a) := by
  rw [reflectOne_destination]
  congr 1
  cases a
  simp only [afterScan,modifySelected,lowStep,lowerReflect]
  congr 1 <;> funext j <;> by_cases hj : j=i <;> simp [Function.update,hj]

@[simp] theorem subtractOne_constant (f P G S : ℕ) (i : Index) :
    totalConstant (subtractOne f P G S i)=10 := by
  rw [subtractOne,BlockDigitMove.inverseProgram_constant,addOne,
    BlockDigitMove.castProgram_constant,ScalarCoordinateProgram.before_constant]

@[simp] theorem reflectOne_constant (f P G S : ℕ) (hS : 0 < S) (i : Index) :
    totalConstant (reflectOne f P G S hS i)=20 := by
  rw [reflectOne,BlockDigitMove.castProgram_constant,ScalarCoordinateProgram.after_constant]


section Aggregate
variable {I R P G S : Type*} [DecidableEq I]

def lowSteps (op : R → R → R) : List I → FullAddress P (I → R) G S → FullAddress P (I → R) G S
  | [],a => a
  | i::is,a => lowSteps op is (lowStep op i a)

theorem lowSteps_eq (op : R → R → R) (is : List I) (hn : is.Nodup)
    (a : FullAddress P (I → R) G S) :
    lowSteps op is a = ⟨a.prefixCoord,a.high,a.gap,
      (fun j => if j ∈ is then op (a.high j) (a.low j) else a.low j),a.suffix⟩ := by
  induction is generalizing a with
  | nil => cases a; simp [lowSteps]
  | cons i is ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
    rw [lowSteps,ih hn]
    simp only [lowStep]
    congr 1
    funext j
    by_cases hj : j=i
    · subst j; simp [hi]
    · simp [Function.update_of_ne hj,hj]

variable {V : ℕ}
theorem flatMap_destination (op : R → R → R)
    (code : FullAddress P (I → R) G S ≃ Fin V) (ps : I → List (Pass V))
    (hp : ∀ i a,destination (ps i) (code a)=code (lowStep op i a))
    (is : List I) (a : FullAddress P (I → R) G S) :
    destination (is.flatMap ps) (code a)=code (lowSteps op is a) := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih =>
    rw [List.flatMap_cons,BlockDigitMove.destination_append,Equiv.trans_apply,hp,ih]
    rfl

theorem flatMap_constant (ps : I → List (Pass V)) (C : ℕ)
    (hc : ∀ i,totalConstant (ps i)=C) (is : List I) :
    totalConstant (is.flatMap ps)=is.length*C := by
  induction is with
  | nil => simp [totalConstant]
  | cons i is ih =>
    simp only [List.flatMap_cons,totalConstant,List.map_append,List.sum_append]
    change totalConstant (ps i)+totalConstant (is.flatMap ps)=_
    rw [hc,ih,List.length_cons]
    ring
end Aggregate

def coordinates : List Index := Finset.univ.toList

@[simp] theorem mem_coordinates (i : Index) : i ∈ coordinates := by simp [coordinates]
@[simp] theorem coordinates_length : coordinates.length=Parameters.m := by
  simpa only [coordinates,Finset.length_toList,Finset.card_univ] using
    StageLabels.actual_matrix_card

def beforeProgram (f P G S : ℕ) : List (Pass (longVolume f P G S)) :=
  coordinates.flatMap (subtractOne f P G S)

def afterProgram (f P G S : ℕ) (hS : 0 < S) : List (Pass (longVolume f P G S)) :=
  coordinates.flatMap (reflectOne f P G S hS)

/-- Actual disk scans replace D by D-H in the fixed whole-vector layout. -/
theorem before_destination (f P G S : ℕ) (a : Addr f P G S) :
    destination (beforeProgram f P G S) (commonLayout f P G S a) =
      commonLayout f P G S (mapPairEquiv lowerSubtractEquiv a) := by
  rw [beforeProgram,flatMap_destination (fun h d => d-h)
    (commonLayout f P G S) (subtractOne f P G S) (subtractOne_destination f P G S)]
  have hn : coordinates.Nodup := Finset.nodup_toList _
  rw [lowSteps_eq _ _ hn]
  congr 1
  cases a
  simp [mapPairEquiv,mapPair,lowerSubtractEquiv,lowerSubtract]
  rfl

/-- Actual disk scans replace D by H-D, with no change to H or spectators. -/
theorem after_destination (f P G S : ℕ) (hS : 0 < S) (a : Addr f P G S) :
    destination (afterProgram f P G S hS) (commonLayout f P G S a) =
      commonLayout f P G S (mapPairEquiv lowerReflectEquiv a) := by
  rw [afterProgram,flatMap_destination (fun h d => h-d)
    (commonLayout f P G S) (reflectOne f P G S hS) (reflectOne_lowStep f P G S hS)]
  have hn : coordinates.Nodup := Finset.nodup_toList _
  rw [lowSteps_eq _ _ hn]
  congr 1
  cases a
  simp [mapPairEquiv,mapPair,lowerReflectEquiv,lowerReflect]
  rfl

@[simp] theorem before_constant (f P G S : ℕ) :
    totalConstant (beforeProgram f P G S)=10*Parameters.m := by
  rw [beforeProgram,flatMap_constant _ 10 (subtractOne_constant f P G S),coordinates_length]
  ring

@[simp] theorem after_constant (f P G S : ℕ) (hS : 0 < S) :
    totalConstant (afterProgram f P G S hS)=20*Parameters.m := by
  rw [afterProgram,flatMap_constant _ 20 (reflectOne_constant f P G S hS),coordinates_length]
  ring

theorem before_execution {Value : Type*} [Inhabited Value] (f P G S B : ℕ) (hB : 0 < B)
    (F : Fin (longVolume f P G S) → Value) :
    ∃ cost,Execution B hB (beforeProgram f P G S) F cost ∧
      cost≤(10*Parameters.m)*(longVolume f P G S/B+1) := by
  simpa only [before_constant] using program_correct (beforeProgram f P G S) F B hB

theorem after_execution {Value : Type*} [Inhabited Value] (f P G S B : ℕ)
    (hB : 0 < B) (hS : 0 < S) (F : Fin (longVolume f P G S) → Value) :
    ∃ cost,Execution B hB (afterProgram f P G S hS) F cost ∧
      cost≤(20*Parameters.m)*(longVolume f P G S/B+1) := by
  simpa only [after_constant] using program_correct (afterProgram f P G S hS) F B hB

end
end CSL.OuterExchangeProgram


