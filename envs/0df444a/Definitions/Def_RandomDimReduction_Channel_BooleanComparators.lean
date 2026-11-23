-- Prove2me | Definitions.Def_RandomDimReduction_Channel_BooleanComparators
-- name    : RandomDimReduction_Channel_BooleanComparators
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:33:44.238053+00:00
-- url     : https://prove2.me/theorems/bbbf29c1-4302-4393-8662-02511b8ee1f7
-- title:
--   Binary words and bounded-size Boolean comparison circuits
-- statement:
--   This module encodes a length-$q$ Boolean word as the natural number $\sum_{i<q} b_i2^i$ and defines a most-significant-bit-first strict comparator. It proves the range bound $0\le \operatorname{binaryValue}(x)<2^q$, compatibility with `Nat.testBit`, correctness of comparison, and a Boolean-program implementation of size $11q+3$.
--
--   These routines provide the binary arithmetic interface used in the efficient dimension-reduction circuit construction. **Formalization Note.** This is the recovered, sorry-free `Solutions.BooleanComparators` module of submission `7d8da302-ad2d-4946-b139-915784e2b187`; the combined comparator-and-addition source passed remote Lean checking before publication.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994, Theorem 1.1 p.2 and Section 5.2 pp.15–19; supporting classical circuit infrastructure recovered from failed prove2.me submission 7d8da302-ad2d-4946-b139-915784e2b187, module Solutions.BooleanComparators.

-- Recovered from failed submission 7d8da302-ad2d-4946-b139-915784e2b187,
-- module Solutions.BooleanComparators.
import Definitions.Def_RandomDimReduction_Channel_BooleanPrograms
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false
set_option linter.defProp false

section p2mFlat_Solutions_BooleanComparators

set_option autoImplicit false
noncomputable section
open QAlgorithms
namespace RandomDimReduction.Channel.BooleanPrograms
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [-simp] bool_false bool_true

def binaryValue : {q : ℕ} → (Fin q → Bool) → ℕ
  | 0,_ => 0
  | q+1,x => (if x (Fin.last q) then 2^q else 0)+binaryValue (fun i => x i.castSucc)

def binaryLess : {q : ℕ} → (Fin q → Bool) → (Fin q → Bool) → Bool
  | 0,_,_ => false
  | q+1,x,y => ((!x (Fin.last q)) && y (Fin.last q)) ||
      ((!(Bool.xor (x (Fin.last q)) (y (Fin.last q)))) &&
        binaryLess (fun i => x i.castSucc) (fun i => y i.castSucc))

lemma binaryValue_lt {q : ℕ} (x : Fin q → Bool) : binaryValue x < 2^q := by
  induction q with
  | zero => simp [binaryValue]
  | succ q ih =>
    have hb := ih (fun i => x i.castSucc)
    simp only [binaryValue,pow_succ]
    cases x (Fin.last q) <;> dsimp <;> omega

lemma binaryLess_correct {q : ℕ} (x y : Fin q → Bool) :
    binaryLess x y=true ↔ binaryValue x < binaryValue y := by
  induction q with
  | zero => simp [binaryLess,binaryValue]
  | succ q ih =>
    have hx := binaryValue_lt (fun i => x i.castSucc)
    have hy := binaryValue_lt (fun i => y i.castSucc)
    have hh := ih (fun i => x i.castSucc) (fun i => y i.castSucc)
    change (((!x (Fin.last q)) && y (Fin.last q)) ||
      ((!(Bool.xor (x (Fin.last q)) (y (Fin.last q)))) &&
        binaryLess (fun i => x i.castSucc) (fun i => y i.castSucc)))=true ↔
      (if x (Fin.last q) then 2^q else 0)+binaryValue (fun i => x i.castSucc) <
        (if y (Fin.last q) then 2^q else 0)+binaryValue (fun i => y i.castSucc)
    cases ha : x (Fin.last q) <;> cases hb : y (Fin.last q) <;>
      simp [ha,hb,hh] <;> omega

lemma hp_binaryLess {ι : Type} (i₀ : ι) {q : ℕ} (a b : Fin q → ι) :
    HasProgram (fun x (_ : Unit) => binaryLess (fun j => x (a j)) (fun j => x (b j))) (11*q+3) := by
  induction q with
  | zero => simpa [binaryLess] using hp_const i₀ false
  | succ q ih =>
    have hlo := ih (fun i => a i.castSucc) (fun i => b i.castSucc)
    have hna := hp_neg (hp_wire (fun _ : Unit => a (Fin.last q)))
    have hhi := hp_mul hna (hp_wire (fun _ : Unit => b (Fin.last q)))
    have heq := hp_neg (hp_xor_wires (a (Fin.last q)) (b (Fin.last q)))
    have hsame := hp_mul heq hlo
    have hor := hp_scalar_op hhi hsame .or
    apply hp_mono (a:=((0+1)+0+1)+((4+1)+(11*q+3)+1)+1) _ (by omega)
    convert hor using 1
    funext x u
    rfl

lemma binaryValue_testBit {q : ℕ} (x : Fin q → Bool) (i : Fin q) :
    Nat.testBit (binaryValue x) i.val=x i := by
  induction q with
  | zero => exact i.elim0
  | succ q ih =>
    by_cases hi : i.val=q
    · have he : i=Fin.last q := Fin.ext hi
      subst i
      change Nat.testBit ((if x (Fin.last q) then 2^q else 0)+binaryValue (fun j => x j.castSucc)) q=x (Fin.last q)
      have hb := Nat.testBit_eq_false_of_lt (binaryValue_lt (fun j => x j.castSucc))
      cases hx : x (Fin.last q) <;> simp [hx,Nat.testBit_two_pow_add_eq,hb]
    · have hiq : i.val < q := by have := i.isLt;omega
      let j : Fin q := ⟨i.val,hiq⟩
      have he : j.castSucc=i := Fin.ext rfl
      have hh := ih (fun k => x k.castSucc) j
      simp only [he] at hh
      change Nat.testBit ((if x (Fin.last q) then 2^q else 0)+binaryValue (fun j => x j.castSucc)) i.val=x i
      cases hx : x (Fin.last q)
      · simpa only [if_neg Bool.false_ne_true,Nat.zero_add] using hh
      · simpa [Nat.testBit_two_pow_add_gt hiq] using hh

lemma binaryValue_natBits {q a : ℕ} (ha : a < 2^q) :
    binaryValue (fun i : Fin q => Nat.testBit a i.val)=a := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < q
  · exact binaryValue_testBit _ ⟨j,hj⟩
  · have hp : 2^q ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt ((binaryValue_lt _).trans_le hp),Nat.testBit_eq_false_of_lt (ha.trans_le hp)]

lemma binaryLess_natBits {q a b : ℕ} (ha : a < 2^q) (hb : b < 2^q) :
    binaryLess (fun i : Fin q => Nat.testBit a i.val) (fun i : Fin q => Nat.testBit b i.val)=true ↔ a < b := by
  rw [binaryLess_correct,binaryValue_natBits ha,binaryValue_natBits hb]

end RandomDimReduction.Channel.BooleanPrograms
end
end p2mFlat_Solutions_BooleanComparators


