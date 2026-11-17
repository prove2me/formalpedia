-- Prove2me | Definitions.Def_WitnessEncryption_Runtime_BinaryArithmetic
-- name    : WitnessEncryption_Runtime_BinaryArithmetic
-- status  : Definition
-- author  : @vigyan
-- created : 2026-11-16T11:24:42.7703+00:00
-- url     : https://prove2.me/theorems/bd421cbc-472b-4fde-aa46-1d542c02d980
-- title:
--   Certified bit-list arithmetic and unary-exponent powering
-- statement:
--   For a finite bit list $b=(b_0,\ldots,b_{n-1})$, let its little-endian value be
--
--   $$\llbracket b\rrbracket=\sum_{i=0}^{n-1}2^i\,\mathbf 1_{b_i=\mathrm{true}}.$$
--
--   This module provides list-based carry addition, binary addition and multiplication, and powering by a unary natural exponent. The algorithms operate on bit lists without requiring a normalized representation. Their concrete realizers carry polynomial resource certificates: for each such realizer $R$ of a function $f$, there are fixed $d,C_T,C_V\in\mathbb N$ such that every encoded input $x$ satisfies
--
--   $$R.\operatorname{time}(x)\le C_T(\operatorname{vol}(x)+2)^d,\qquad \operatorname{vol}(f(x))\le C_V(\operatorname{vol}(x)+2)^d.$$
--
--   Addition and multiplication are measured in the encoded sizes of their bit-list inputs. In the powering routine the exponent $k$ is physically unary, with $\operatorname{vol}(k)=2k+1$; its certificate is polynomial in the encoded pair consisting of that exponent and the base bit list. The numeric interpretation of bit lists is a mathematical specification, rather than a claimed efficient conversion to unary integers. These routines supply the arithmetic and resource interfaces used by the rank reduction's feature and field programs.
-- source:
--   Runtime formalization supporting Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, Section 6.5 and Theorem 6.1; supplied paper https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf . Selected original declarations from WitnessEncryption/Runtime/NatPrimitives.lean, Binary/Value.lean, Binary/Arithmetic.lean, Binary/Adder.lean, Binary/Multiplier.lean and Prime/UnaryPower.lean, with unchanged declaration bodies; export SHA256 3d78e085ce4a612f55d91e0fe3c2f0a274a1f0e837f4f48323bf0005c60d9975.

import Definitions.Def_WitnessEncryption_Runtime_UnaryRange

set_option autoImplicit false

section
-- Source: WitnessEncryption.Runtime.NatPrimitives

namespace WitnessEncryption.Runtime.NatPrimitives
open OAI.ThreeMachine.StackCompiler



theorem pred_certified : Certified Realizer.pred := by
  refine ⟨1, ?_, ?_⟩
  · change Poly volume (fun n : ℕ => volume n+2) 1
    exact Poly.base volume
  · apply Poly.of_le (g := volume) _ (Poly.size volume)
    intro n
    simp only [volume_nat, Nat.pred_eq_sub_one]
    omega

theorem positive_certified : Certified Realizer.positive := by
  refine ⟨1, ?_, ?_⟩
  · apply Poly.of_le (g := fun n : ℕ => 10000*(volume n+2))
    · intro n
      have hh := Realizer.time_test_le (fun k : ℕ => decide (0 < k))
        (by intro k; cases k <;> rfl) n
      exact hh.trans (by omega)
    · simpa only [pow_one] using Poly.powerBase (volume : ℕ → ℕ) 10000 1
  · exact (Poly.of_le (fun n => volume_bool (decide (0 < n)))
      (OAI.ThreeMachine.StackCompiler.Poly.const volume 3)).lift (by omega)

theorem isZero_certified : Certified Realizer.isZero := by
  unfold Realizer.isZero
  apply Certified.congr
  exact positive_certified.comp (Certified.of_finite Realizer.not)

theorem add_certified : Certified Realizer.add := by
  refine ⟨2, ?_, ?_⟩
  · apply Poly.of_le (g := fun x : ℕ × ℕ => 10000000*(volume x+2)^2)
    · intro x
      exact (Realizer.time_add_le x.1 x.2).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by rw [volume_prod, volume_nat, volume_nat]; omega) 2))
    · exact Poly.powerBase (volume : ℕ × ℕ → ℕ) 10000000 2
  · apply Poly.lift (d := 1) _ (by omega)
    apply Poly.of_le (g := volume) _ (Poly.size volume)
    intro x
    change volume (x.1+x.2) ≤ volume x
    rw [volume_nat, volume_prod, volume_nat, volume_nat]
    omega

theorem le_certified : Certified Realizer.le := by
  refine ⟨2, ?_, ?_⟩
  · apply Poly.of_le (g := fun x : ℕ × ℕ => 1000000000*(volume x+2)^2)
    · intro x
      exact (Realizer.time_le_le x.1 x.2).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by rw [volume_prod, volume_nat, volume_nat]; omega) 2))
    · exact Poly.powerBase (volume : ℕ × ℕ → ℕ) 1000000000 2
  · exact (Poly.of_le (fun x : ℕ × ℕ => volume_bool (decide (x.1 ≤ x.2)))
      (OAI.ThreeMachine.StackCompiler.Poly.const volume 3)).lift (by omega)

end WitnessEncryption.Runtime.NatPrimitives


end

section
-- Source: WitnessEncryption.Runtime.Binary.Value

namespace WitnessEncryption.Runtime.Binary

/-- Denotation only: executable arithmetic traverses the bit lists themselves. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * value bs

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (b : Bool) (bs : List Bool) :
    value (b :: bs) = (if b then 1 else 0) + 2 * value bs := rfl



@[simp] theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h, value_cons, ih]
    cases b <;> simp [Nat.bit, Nat.add_comm]









end WitnessEncryption.Runtime.Binary

end

section
-- Source: WitnessEncryption.Runtime.Binary.Arithmetic

namespace WitnessEncryption.Runtime.Binary

def bitValue (b : Bool) : ℕ := if b then 1 else 0
@[simp] theorem bitValue_false : bitValue false = 0 := rfl


@[simp] theorem value_cons_bit (b : Bool) (bs : List Bool) :
    value (b::bs) = bitValue b + 2*value bs := rfl

def sumBit (a b c : Bool) : Bool := (a.xor b).xor c
def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem fullAdder_correct (a b c : Bool) :
    bitValue (sumBit a b c) + 2 * bitValue (carryBit a b c) =
      bitValue a + bitValue b + bitValue c := by
  cases a <;> cases b <;> cases c <;> decide

def carryAdd (c : Bool) : List Bool → List Bool
  | [] => if c then [true] else []
  | b :: bs => sumBit false b c :: carryAdd (carryBit false b c) bs

def addCarry (c : Bool) : List Bool → List Bool → List Bool
  | [], ys => carryAdd c ys
  | a :: xs, [] => sumBit a false c :: addCarry (carryBit a false c) xs []
  | a :: xs, b :: ys => sumBit a b c :: addCarry (carryBit a b c) xs ys

def add (xs ys : List Bool) : List Bool := addCarry false xs ys

theorem value_carryAdd (c : Bool) (ys : List Bool) :
    value (carryAdd c ys) = value ys + bitValue c := by
  induction ys generalizing c with
  | nil => cases c <;> simp [carryAdd, bitValue]
  | cons b bs ih =>
      simp only [carryAdd, value_cons_bit, ih]
      have h := fullAdder_correct false b c
      simp only [bitValue_false, zero_add] at h
      omega

theorem value_addCarry (c : Bool) (xs ys : List Bool) :
    value (addCarry c xs ys) = value xs + value ys + bitValue c := by
  induction xs generalizing c ys with
  | nil => simp [addCarry, value_carryAdd]
  | cons a xs ih =>
      cases ys with
      | nil =>
          simp only [addCarry, value_cons_bit, ih, value_nil]
          have h := fullAdder_correct a false c
          simp only [bitValue_false, add_zero] at h
          omega
      | cons b ys =>
          simp only [addCarry, value_cons_bit, ih]
          have h := fullAdder_correct a b c
          omega

@[simp]
theorem value_add (xs ys : List Bool) :
    value (add xs ys) = value xs + value ys := by
  simp [add, value_addCarry]

theorem length_carryAdd (c : Bool) (ys : List Bool) :
    (carryAdd c ys).length ≤ ys.length + 1 := by
  induction ys generalizing c with
  | nil => cases c <;> simp [carryAdd]
  | cons b bs ih =>
      simp only [carryAdd, List.length_cons]
      have h := ih (carryBit false b c)
      omega

theorem length_addCarry (c : Bool) (xs ys : List Bool) :
    (addCarry c xs ys).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing c ys with
  | nil => simpa [addCarry] using length_carryAdd c ys
  | cons a xs ih =>
      cases ys with
      | nil =>
          simp only [addCarry, List.length_cons, List.length_nil, Nat.max_zero]
          have h := ih (carryBit a false c) []
          simp only [List.length_nil, Nat.max_zero] at h
          omega
      | cons b ys =>
          simp only [addCarry, List.length_cons]
          have h := ih (carryBit a b c) ys
          omega

theorem length_add (xs ys : List Bool) :
    (add xs ys).length ≤ max xs.length ys.length + 1 :=
  length_addCarry false xs ys

/-- Shift-and-add multiplication; no natural-number arithmetic is executed
by this data routine. Leading zero bits are allowed in its output. -/
def mul : List Bool → List Bool → List Bool
  | [], _ => []
  | b :: bs, ys =>
      let shifted := false :: mul bs ys
      if b then add ys shifted else shifted



/-- A deliberately loose output-width bound that needs no normalization. -/
theorem length_mul (xs ys : List Bool) :
    (mul xs ys).length ≤ 2 * xs.length + ys.length := by
  induction xs with
  | nil => simp [mul]
  | cons b bs ih =>
      cases b with
      | false => simp only [mul, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      | true =>
          simp only [mul, ↓reduceIte]
          have h := length_add ys (false :: mul bs ys)
          simp only [List.length_cons] at h ⊢
          omega

end WitnessEncryption.Runtime.Binary

end

section
-- Source: WitnessEncryption.Runtime.Binary.Adder

namespace WitnessEncryption.Runtime.Binary
open OAI.ThreeMachine.StackCompiler
open WitnessEncryption.Runtime.ListPrimitives

local notation "Bits" => List Bool

def xorR : Realizer (fun x : Bool × Bool => x.1.xor x.2) :=
  (Realizer.not.choose Realizer.id).congr
    (fun x => by rcases x with ⟨a,b⟩; cases a <;> cases b <;> rfl)

def sumR : Realizer (fun x : Bool × (Bool × Bool) => sumBit x.1 x.2.1 x.2.2) :=
  ((((Realizer.fst.pair (Realizer.snd.comp Realizer.fst)).comp xorR).pair
    (Realizer.snd.comp Realizer.snd)).comp xorR).congr (fun _ => rfl)

def carryR : Realizer (fun x : Bool × (Bool × Bool) => carryBit x.1 x.2.1 x.2.2) :=
  (Realizer.or.choose Realizer.and).congr
    (fun x => by rcases x with ⟨a,b,c⟩; cases a <;> cases b <;> cases c <;> rfl)

def fullR : Realizer (fun x : Bool × (Bool × Bool) =>
    (sumBit x.1 x.2.1 x.2.2, carryBit x.1 x.2.1 x.2.2)) := sumR.pair carryR

def carryStep (x : Bool × (Bool × Bits)) : Bool × Bits :=
  (carryBit false x.1 x.2.1, sumBit false x.1 x.2.1 :: x.2.2)

def carryEnd (x : Bool × Bits) : Bits :=
  x.2.reverse ++ if x.1 then [true] else []

theorem carry_fold_correct (xs : Bits) (c : Bool) (rev : Bits) :
    carryEnd (xs.foldl (fun s a => carryStep (a,s)) (c,rev)) =
      rev.reverse ++ carryAdd c xs := by
  induction xs generalizing c rev with
  | nil => rfl
  | cons b xs ih =>
    change carryEnd (xs.foldl (fun s a => carryStep (a,s))
      (carryBit false b c, sumBit false b c :: rev)) = _
    rw [ih]
    simp [carryAdd, List.reverse_cons, List.append_assoc]

theorem carry_fold_length (xs : Bits) (state : Bool × Bits) :
    (xs.foldl (fun s a => carryStep (a,s)) state).2.length = state.2.length+xs.length := by
  induction xs generalizing state with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons, ih]
    simp only [carryStep, List.length_cons]
    omega

def carryArgsR : Realizer (fun x : Bool × (Bool × Bits) => (false,(x.1,x.2.1))) :=
  (Realizer.constant false).pair (Realizer.fst.pair (Realizer.snd.comp Realizer.fst))

def carryFullR : Realizer (fun x : Bool × (Bool × Bits) =>
    (sumBit false x.1 x.2.1, carryBit false x.1 x.2.1)) := carryArgsR.comp fullR

def carryStepR : Realizer carryStep :=
  (carryFullR.comp Realizer.snd).pair
    (((carryFullR.comp Realizer.fst).pair (Realizer.snd.comp Realizer.snd)).comp Realizer.cons)

theorem carryStep_certified : Certified carryStepR := by
  have hargs : Certified carryArgsR :=
    (Certified.constant false).pair (Certified.fst.pair (Certified.snd.comp Certified.fst))
  have hf : Certified carryFullR := hargs.comp (Certified.of_finite fullR)
  exact (hf.comp Certified.snd).pair
    (((hf.comp Certified.fst).pair (Certified.snd.comp Certified.snd)).comp cons_certified)

def carryEndR : Realizer carryEnd :=
  (((Realizer.snd.comp reverseR).pair
    ((Realizer.fst.pair (Realizer.constant ())).comp
      ((Realizer.constant [true]).choose (Realizer.constant ([] : Bits))))).comp appendR).congr
    (fun _ => rfl)

theorem carryEnd_certified : Certified carryEndR :=
  (((Certified.snd.comp reverse_certified).pair
    ((Certified.fst.pair (Certified.constant ())).comp
      ((Certified.constant [true]).choose (Certified.constant ([] : Bits))))).comp append_certified).congr
    (fun _ => rfl)

theorem carryFold_certified : Certified carryStepR.fold := by
  apply Certified.fold carryStep_certified
  refine ⟨10,1,?_⟩
  intro x j hj
  let s := (x.1.take j).foldl (fun s a => carryStep (a,s)) x.2
  have hs : s.2.length = x.2.2.length+(x.1.take j).length := carry_fold_length _ _
  have hv := volume_list_le s.2 3 (fun b _ => volume_bool b)
  have hb := volume_bool s.1
  have hx := length_le_volume x.1
  have hy := length_le_volume x.2.2
  have hj' := List.length_take_le' j x.1
  change volume s ≤ 10*(volume x+2)^1
  simp only [pow_one, volume_prod] at *
  omega

def carryAddR : Realizer (fun x : Bool × Bits => carryAdd x.1 x.2) :=
  ((((Realizer.snd.pair (Realizer.fst.pair Realizer.nil)).comp carryStepR.fold).comp carryEndR)).congr
    (fun x => by simpa only [Function.comp_apply, List.reverse_nil, List.nil_append]
      using carry_fold_correct x.2 x.1 [])

theorem carryAdd_certified : Certified carryAddR :=
  ((((Certified.snd.pair (Certified.fst.pair nil_certified)).comp carryFold_certified).comp carryEnd_certified)).congr
    (fun x => by simpa only [Function.comp_apply, List.reverse_nil, List.nil_append]
      using carry_fold_correct x.2 x.1 [])

def addStep (x : Bool × (Bits × (Bool × Bits))) : Bits × (Bool × Bits) :=
  let b := x.2.1.headD false
  (x.2.1.tail, (carryBit x.1 b x.2.2.1, sumBit x.1 b x.2.2.1 :: x.2.2.2))

def addEnd (x : Bits × (Bool × Bits)) : Bits :=
  x.2.2.reverse ++ carryAdd x.2.1 x.1

theorem add_fold_correct (xs ys : Bits) (c : Bool) (rev : Bits) :
    addEnd (xs.foldl (fun s a => addStep (a,s)) (ys,(c,rev))) =
      rev.reverse ++ addCarry c xs ys := by
  induction xs generalizing ys c rev with
  | nil => rfl
  | cons a xs ih =>
    cases ys with
    | nil =>
      change addEnd (xs.foldl (fun s a => addStep (a,s))
        ([], (carryBit a false c, sumBit a false c :: rev))) = _
      rw [ih]
      simp [addCarry, List.reverse_cons, List.append_assoc]
    | cons b ys =>
      change addEnd (xs.foldl (fun s a => addStep (a,s))
        (ys, (carryBit a b c, sumBit a b c :: rev))) = _
      rw [ih]
      simp [addCarry, List.reverse_cons, List.append_assoc]

theorem add_fold_width (xs : Bits) (state : Bits × (Bool × Bits)) :
    (xs.foldl (fun s a => addStep (a,s)) state).1.length ≤ state.1.length ∧
    (xs.foldl (fun s a => addStep (a,s)) state).2.2.length = state.2.2.length+xs.length := by
  induction xs generalizing state with
  | nil => simp
  | cons a xs ih =>
    have hh := ih (addStep (a,state))
    constructor
    · exact hh.1.trans (by simp only [addStep, List.length_tail]; omega)
    · simpa only [List.foldl_cons, addStep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh.2

def headBoolR : Realizer (fun xs : Bits => xs.headD false) :=
  ((headR.pair (Realizer.constant false)).comp getDR).congr
    (fun xs => by cases xs <;> rfl)

theorem headBool_certified : Certified headBoolR :=
  ((head_certified.pair (Certified.constant false)).comp getD_certified).congr
    (fun xs => by cases xs <;> rfl)

def addArgsR : Realizer (fun x : Bool × (Bits × (Bool × Bits)) =>
    (x.1,(x.2.1.headD false,x.2.2.1))) :=
  Realizer.fst.pair ((((Realizer.snd.comp Realizer.fst).comp headBoolR).pair
    (Realizer.snd.comp (Realizer.snd.comp Realizer.fst))))

def addFullR : Realizer (fun x : Bool × (Bits × (Bool × Bits)) =>
    (sumBit x.1 (x.2.1.headD false) x.2.2.1,
      carryBit x.1 (x.2.1.headD false) x.2.2.1)) := addArgsR.comp fullR

def addStepR : Realizer addStep :=
  ((Realizer.snd.comp Realizer.fst).comp tailR).pair
    ((addFullR.comp Realizer.snd).pair
      (((addFullR.comp Realizer.fst).pair (Realizer.snd.comp (Realizer.snd.comp Realizer.snd))).comp Realizer.cons))

theorem addStep_certified : Certified addStepR := by
  have hargs : Certified addArgsR :=
    Certified.fst.pair (((Certified.snd.comp Certified.fst).comp headBool_certified).pair
      (Certified.snd.comp (Certified.snd.comp Certified.fst)))
  have hf : Certified addFullR := hargs.comp (Certified.of_finite fullR)
  exact ((Certified.snd.comp Certified.fst).comp tail_certified).pair
    ((hf.comp Certified.snd).pair
      (((hf.comp Certified.fst).pair (Certified.snd.comp (Certified.snd.comp Certified.snd))).comp cons_certified))

def addEndR : Realizer addEnd :=
  ((((Realizer.snd.comp Realizer.snd).comp reverseR).pair
    (((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp carryAddR)).comp appendR)

theorem addEnd_certified : Certified addEndR :=
  ((((Certified.snd.comp Certified.snd).comp reverse_certified).pair
    (((Certified.snd.comp Certified.fst).pair Certified.fst).comp carryAdd_certified)).comp append_certified)

theorem addFold_certified : Certified addStepR.fold := by
  apply Certified.fold addStep_certified
  refine ⟨20,1,?_⟩
  intro x j hj
  let s := (x.1.take j).foldl (fun s a => addStep (a,s)) x.2
  have hs := add_fold_width (x.1.take j) x.2
  have hy := volume_list_le s.1 3 (fun b _ => volume_bool b)
  have ho := volume_list_le s.2.2 3 (fun b _ => volume_bool b)
  have hc := volume_bool s.2.1
  have hx := length_le_volume x.1
  have hxy := length_le_volume x.2.1
  have hxo := length_le_volume x.2.2.2
  have hj' := List.length_take_le' j x.1
  change volume s ≤ 20*(volume x+2)^1
  change s.1.length ≤ x.2.1.length ∧ s.2.2.length = x.2.2.2.length+(x.1.take j).length at hs
  simp only [pow_one, volume_prod] at *
  omega

def addR : Realizer (fun x : Bits × Bits => add x.1 x.2) :=
  ((((Realizer.fst.pair (Realizer.snd.pair ((Realizer.constant false).pair Realizer.nil))).comp
    addStepR.fold).comp addEndR)).congr
      (fun x => by simpa only [Function.comp_apply, List.reverse_nil, List.nil_append, add]
        using add_fold_correct x.1 x.2 false [])

theorem add_certified : Certified addR :=
  ((((Certified.fst.pair (Certified.snd.pair ((Certified.constant false).pair nil_certified))).comp
    addFold_certified).comp addEnd_certified)).congr
      (fun x => by simpa only [Function.comp_apply, List.reverse_nil, List.nil_append, add]
        using add_fold_correct x.1 x.2 false [])

end WitnessEncryption.Runtime.Binary

end

section
-- Source: WitnessEncryption.Runtime.Binary.Multiplier

namespace WitnessEncryption.Runtime.Binary
open OAI.ThreeMachine.StackCompiler
open WitnessEncryption.Runtime.ListPrimitives
local notation "Bits" => List Bool

def mulStep (x : Bool × (Bits × Bits)) : Bits × Bits :=
  let shifted := false :: x.2.2
  (x.2.1, if x.1 then add x.2.1 shifted else shifted)



theorem mul_fold_correct (xs ys : Bits) :
    xs.reverse.foldl (fun s a => mulStep (a,s)) (ys,[]) = (ys,mul xs ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    rfl

theorem mul_fold_width (xs : Bits) (state : Bits × Bits) :
    (xs.foldl (fun s a => mulStep (a,s)) state).1 = state.1 ∧
    (xs.foldl (fun s a => mulStep (a,s)) state).2.length ≤
      state.2.length+xs.length*(state.1.length+2) := by
  induction xs generalizing state with
  | nil => simp
  | cons a xs ih =>
    have hh := ih (mulStep (a,state))
    have hw : (mulStep (a,state)).2.length ≤ state.2.length+state.1.length+2 := by
      cases a with
      | false => simp [mulStep]; omega
      | true =>
        have h := length_add state.1 (false::state.2)
        simp only [List.length_cons] at h
        simp only [mulStep, ↓reduceIte]
        omega
    refine ⟨hh.1, ?_⟩
    change (xs.foldl (fun s a => mulStep (a,s)) (mulStep (a,state))).2.length ≤ _
    have hi := hh.2
    change _ ≤ (mulStep (a,state)).2.length+xs.length*(state.1.length+2) at hi
    simp only [List.length_cons, Nat.succ_mul]
    omega

def mulShiftR : Realizer (fun x : Bool × (Bits × Bits) => false :: x.2.2) :=
  ((Realizer.constant false).pair (Realizer.snd.comp Realizer.snd)).comp Realizer.cons

def mulTermR : Realizer (fun x : Bool × (Bits × Bits) => add x.2.1 (false :: x.2.2)) :=
  (((Realizer.snd.comp Realizer.fst).pair mulShiftR).comp addR)

def mulStepR : Realizer mulStep :=
  (Realizer.snd.comp Realizer.fst).pair
    ((Realizer.fst.pair Realizer.id).comp (mulTermR.choose mulShiftR))

theorem mulStep_certified : Certified mulStepR := by
  have hs : Certified mulShiftR :=
    ((Certified.constant false).pair (Certified.snd.comp Certified.snd)).comp cons_certified
  have ht : Certified mulTermR :=
    (((Certified.snd.comp Certified.fst).pair hs).comp add_certified)
  exact (Certified.snd.comp Certified.fst).pair
    ((Certified.fst.pair Certified.identity).comp (ht.choose hs))

theorem mulFold_certified : Certified mulStepR.fold := by
  apply Certified.fold mulStep_certified
  refine ⟨20,2,?_⟩
  intro x j hj
  let s := (x.1.take j).foldl (fun s a => mulStep (a,s)) x.2
  have hs := mul_fold_width (x.1.take j) x.2
  change s.1 = x.2.1 ∧ s.2.length ≤ x.2.2.length+(x.1.take j).length*(x.2.1.length+2) at hs
  have hv := volume_list_le s.2 3 (fun b _ => volume_bool b)
  have hx := length_le_volume x.1
  have hy := length_le_volume x.2.1
  have ha := length_le_volume x.2.2
  have hp := List.length_take_le' j x.1
  have hprod : (x.1.take j).length*(x.2.1.length+2) ≤ (volume x+2)^2 := by
    rw [pow_two]
    apply Nat.mul_le_mul
    · simp only [volume_prod]; omega
    · simp only [volume_prod]; omega
  change volume s ≤ 20*(volume x+2)^2
  rw [volume_prod, hs.1]
  have hbase : 1 ≤ volume x+2 := by omega
  have hsq : volume x+2 ≤ (volume x+2)^2 := le_self_pow (by omega) (by decide)
  simp only [volume_prod] at *
  nlinarith

def mulR : Realizer (fun x : Bits × Bits => mul x.1 x.2) :=
  (((((Realizer.fst.comp reverseR).pair (Realizer.snd.pair Realizer.nil)).comp
    mulStepR.fold).comp Realizer.snd)).congr
      (fun x => congrArg Prod.snd (mul_fold_correct x.1 x.2))

theorem mul_certified : Certified mulR :=
  (((((Certified.fst.comp reverse_certified).pair (Certified.snd.pair nil_certified)).comp
    mulFold_certified).comp Certified.snd)).congr
      (fun x => congrArg Prod.snd (mul_fold_correct x.1 x.2))

end WitnessEncryption.Runtime.Binary

end

section
-- Source: WitnessEncryption.Runtime.Prime.UnaryPower

namespace WitnessEncryption.Runtime.Prime
open OAI.ThreeMachine.StackCompiler
namespace UnaryPowerProof
abbrev Bits := List Bool
abbrev State := Bits × Bits

def step (p : Unit × State) : State := (p.2.1,Binary.mul p.2.1 p.2.2)

theorem fold_base (us : List Unit) (s : State) :
    (us.foldl (fun s u => step (u,s)) s).1 = s.1 := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih => exact ih (step (u,s))



theorem fold_width (us : List Unit) (s : State) :
    (us.foldl (fun s u => step (u,s)) s).2.length ≤
      s.2.length+2*us.length*s.1.length := by
  induction us generalizing s with
  | nil => simp
  | cons u us ih =>
      have hh := ih (step (u,s))
      have hw := Binary.length_mul s.1 s.2
      change (us.foldl (fun s u => step (u,s)) (step (u,s))).2.length ≤ _
      change _ ≤ (Binary.mul s.1 s.2).length+2*us.length*s.1.length at hh
      simp only [List.length_cons]
      nlinarith

def stepR : Realizer step :=
  (Realizer.snd.comp Realizer.fst).pair
    (((Realizer.snd.comp Realizer.fst).pair (Realizer.snd.comp Realizer.snd)).comp Binary.mulR)

theorem stepR_certified : Certified stepR :=
  (Certified.snd.comp Certified.fst).pair
    (((Certified.snd.comp Certified.fst).pair (Certified.snd.comp Certified.snd)).comp
      Binary.mul_certified)

theorem fold_step_certified : Certified stepR.fold := by
  apply Certified.fold stepR_certified
  refine ⟨40,2,?_⟩
  intro x j hj
  let s := (x.1.take j).foldl (fun s u => step (u,s)) x.2
  have hb := fold_base (x.1.take j) x.2
  have hw := fold_width (x.1.take j) x.2
  change s.1 = x.2.1 at hb
  change s.2.length ≤ x.2.2.length+2*(x.1.take j).length*x.2.1.length at hw
  have hv := volume_list_le s.2 3 (fun b _ => volume_bool b)
  have hx := length_le_volume x.1
  have hbase := length_le_volume x.2.1
  have hacc := length_le_volume x.2.2
  have hp := List.length_take_le' j x.1
  have hprod : (x.1.take j).length*x.2.1.length ≤ (volume x+2)^2 := by
    rw [pow_two]
    apply Nat.mul_le_mul
    · simp only [volume_prod]; omega
    · simp only [volume_prod]; omega
  change volume s ≤ 40*(volume x+2)^2
  rw [volume_prod,hb]
  have hsq : volume x+2 ≤ (volume x+2)^2 := le_self_pow (by omega) (by decide)
  simp only [volume_prod] at *
  nlinarith







def prepareR : Realizer (fun p : ℕ × Bits => (List.replicate p.1 (),(p.2,[true]))) :=
  (Realizer.fst.comp unitsR).pair (Realizer.snd.pair (Realizer.constant [true]))

theorem prepareR_certified : Certified prepareR :=
  (Certified.fst.comp unitsR_certified).pair (Certified.snd.pair (Certified.constant [true]))

end UnaryPowerProof

/-- Binary base raised by a unary-small exponent. The fixed base is the first multiplier operand. -/
def unaryPower (k : ℕ) (bs : List Bool) : List Bool :=
  ((List.replicate k ()).foldl (fun s u => UnaryPowerProof.step (u,s)) (bs,[true])).2





def unaryPowerR : Realizer (fun p : ℕ × List Bool => unaryPower p.1 p.2) :=
  ((UnaryPowerProof.prepareR.comp UnaryPowerProof.stepR.fold).comp Realizer.snd).congr (fun _ => rfl)

/-- Polynomial in unary exponent Coding volume and input-bit volume, not logarithm of the exponent. -/
theorem unaryPower_certified : Certified unaryPowerR := by
  unfold unaryPowerR
  apply Certified.congr
  exact (UnaryPowerProof.prepareR_certified.comp UnaryPowerProof.fold_step_certified).comp Certified.snd

end WitnessEncryption.Runtime.Prime

end


