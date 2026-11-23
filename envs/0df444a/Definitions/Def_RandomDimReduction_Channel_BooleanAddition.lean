-- Prove2me | Definitions.Def_RandomDimReduction_Channel_BooleanAddition
-- name    : RandomDimReduction_Channel_BooleanAddition
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:35:24.844439+00:00
-- url     : https://prove2.me/theorems/5f216bd8-ff8e-4a03-9a41-06756eedf7f0
-- title:
--   Ripple-carry Boolean addition with circuit size bounds
-- statement:
--   This module defines full-adder sum and carry bits and a ripple-carry addition algorithm on length-$q$ Boolean words. It proves the exact identity
--   $$
--   \operatorname{binaryValue}(\operatorname{addWord}(a,b,c))
--    +2^q\operatorname{bitValue}(\operatorname{carryOut}(a,b,c))
--    =\operatorname{binaryValue}(a)+\operatorname{binaryValue}(b)+\operatorname{bitValue}(c),
--   $$
--   and hence addition modulo $2^q$. It also constructs Boolean programs for addition with the explicit bound $2q^2+6q$, together with composition rules for previously programmed inputs.
--
--   This is classical circuit infrastructure for the efficient dimension-reduction proof. **Formalization Note.** This is the recovered, sorry-free `Solutions.BooleanAddition` module of submission `7d8da302-ad2d-4946-b139-915784e2b187`; the combined comparator-and-addition source passed remote Lean checking before publication.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994, Theorem 1.1 p.2 and Section 5.2 pp.15–19; supporting classical circuit infrastructure recovered from failed prove2.me submission 7d8da302-ad2d-4946-b139-915784e2b187, module Solutions.BooleanAddition.

-- Recovered from failed submission 7d8da302-ad2d-4946-b139-915784e2b187,
-- module Solutions.BooleanAddition.
import Definitions.Def_RandomDimReduction_Channel_BooleanComparators
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

section p2mFlat_Solutions_BooleanAddition

set_option autoImplicit false
noncomputable section
open QAlgorithms
namespace RandomDimReduction.Channel.BooleanPrograms
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [-simp] bool_false bool_true

def fullCarry (a b c : Bool) : Bool := (a&&b)||((a||b)&&c)
def fullSum (a b c : Bool) : Bool := Bool.xor (Bool.xor a b) c
def bitValue (b : Bool) : ℕ := if b then 1 else 0

lemma fullAdder_correct (a b c : Bool) :
    bitValue (fullSum a b c)+2*bitValue (fullCarry a b c)=bitValue a+bitValue b+bitValue c := by
  cases a <;> cases b <;> cases c <;> decide

def carryOut : {q : ℕ} → (Fin q → Bool) → (Fin q → Bool) → Bool → Bool
  | 0,_,_,c => c
  | q+1,a,b,c => fullCarry (a (Fin.last q)) (b (Fin.last q))
      (carryOut (fun j => a j.castSucc) (fun j => b j.castSucc) c)

def addWord : {q : ℕ} → (Fin q → Bool) → (Fin q → Bool) → Bool → Fin q → Bool
  | 0,_,_,_ => Fin.elim0
  | q+1,a,b,c => Fin.snoc
      (addWord (fun j => a j.castSucc) (fun j => b j.castSucc) c)
      (fullSum (a (Fin.last q)) (b (Fin.last q))
        (carryOut (fun j => a j.castSucc) (fun j => b j.castSucc) c))

lemma addWord_correct {q : ℕ} (a b : Fin q → Bool) (c : Bool) :
    binaryValue (addWord a b c)+2^q*bitValue (carryOut a b c)=
      binaryValue a+binaryValue b+bitValue c := by
  induction q with
  | zero => simp [binaryValue,carryOut]
  | succ q ih =>
    have hlo := ih (fun j => a j.castSucc) (fun j => b j.castSucc)
    have hhi := fullAdder_correct (a (Fin.last q)) (b (Fin.last q))
      (carryOut (fun j => a j.castSucc) (fun j => b j.castSucc) c)
    have hb (z : Bool) : (if z then 2^q else 0)=2^q*bitValue z := by cases z <;> simp [bitValue]
    simp only [binaryValue,addWord,Fin.snoc_last,Fin.snoc_castSucc,carryOut,hb,pow_succ]
    have hw := congrArg (fun z : ℕ => 2^q*z) hhi
    nlinarith only [hlo,hw]

lemma hp_fullCarry {ι : Type} {f g h : (ι → Bool) → Unit → Bool} {a b c : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) (hh : HasProgram h c) :
    HasProgram (fun x (_ : Unit) => fullCarry (f x ()) (g x ()) (h x ())) (2*a+2*b+c+4) := by
  have hab := hp_mul hf hg
  have hor := hp_scalar_op hf hg .or
  have htail := hp_mul hor hh
  have H := hp_scalar_op hab htail .or
  convert H using 1 <;> first | rfl | omega

lemma hp_fullSum {ι : Type} {f g h : (ι → Bool) → Unit → Bool} {a b c : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) (hh : HasProgram h c) :
    HasProgram (fun x (_ : Unit) => fullSum (f x ()) (g x ()) (h x ())) (a+b+c+8) := by
  have H := hp_add (hp_add hf hg) hh
  convert H using 1
  · rfl
  · omega

lemma hp_carryOut {ι : Type} {q : ℕ} (a b : Fin q → ι) (c : ι) :
    HasProgram (fun x (_ : Unit) => carryOut (fun j => x (a j)) (fun j => x (b j)) (x c)) (4*q) := by
  induction q with
  | zero => exact hp_wire (fun _ => c)
  | succ q ih =>
    have hlo := ih (fun j => a j.castSucc) (fun j => b j.castSucc)
    have H := hp_fullCarry (hp_wire (fun _ : Unit => a (Fin.last q)))
      (hp_wire (fun _ : Unit => b (Fin.last q))) hlo
    convert H using 1 <;> first | rfl | omega

lemma hp_addWord {ι : Type} {q : ℕ} (a b : Fin q → ι) (c : ι) :
    HasProgram (fun x => addWord (fun j => x (a j)) (fun j => x (b j)) (x c)) (2*q^2+6*q) := by
  induction q with
  | zero =>
    convert hp_wire (fun j : Fin 0 => j.elim0) using 1 <;> simp
  | succ q ih =>
    have hlo := ih (fun j => a j.castSucc) (fun j => b j.castSucc)
    have hc := hp_carryOut (fun j => a j.castSucc) (fun j => b j.castSucc) c
    have hhi := hp_fullSum (hp_wire (fun _ : Unit => a (Fin.last q)))
      (hp_wire (fun _ : Unit => b (Fin.last q))) hc
    have H := hp_map (hp_pair hlo hhi) (fun j : Fin (q+1) =>
      if h : j.val < q then Sum.inl (⟨j.val,h⟩ : Fin q) else Sum.inr ())
    convert H using 1
    · funext x j
      dsimp only [Function.comp_apply]
      by_cases hj : j.val < q
      · let k : Fin q := ⟨j.val,hj⟩
        have he : j=k.castSucc := Fin.ext rfl
        simp only [he,addWord,Fin.snoc_castSucc,Fin.val_castSucc,dif_pos k.isLt,Sum.elim_inl,Function.comp_apply]
      · have he : j=Fin.last q := by
          apply Fin.ext
          change j.val=q
          have := j.isLt
          omega
        simp only [he,addWord,Fin.snoc_last,Fin.val_last,dif_neg (Nat.lt_irrefl q),Sum.elim_inr,Function.comp_apply]
    · ring

lemma addWord_mod {q : ℕ} (a b : Fin q → Bool) (c : Bool) :
    binaryValue (addWord a b c)=(binaryValue a+binaryValue b+bitValue c) % 2^q := by
  calc
    _ = (binaryValue (addWord a b c)+2^q*bitValue (carryOut a b c)) % 2^q := by
      simp [Nat.add_mod,Nat.mod_eq_of_lt (binaryValue_lt (addWord a b c))]
    _ = _ := congrArg (fun z : ℕ => z % 2^q) (addWord_correct a b c)

lemma hp_addWord_functions {ι : Type} {q : ℕ}
    {f g : (ι → Bool) → Fin q → Bool} {h : (ι → Bool) → Unit → Bool} {a b c : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) (hh : HasProgram h c) :
    HasProgram (fun x => addWord (f x) (g x) (h x ())) (a+b+c+2*q^2+6*q) := by
  have H := hp_comp (hp_pair hf (hp_pair hg hh))
    (hp_addWord (fun j : Fin q => Sum.inl j)
      (fun j : Fin q => Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr ())))
  convert H using 1 <;> first | rfl | omega

end RandomDimReduction.Channel.BooleanPrograms
end
end p2mFlat_Solutions_BooleanAddition


