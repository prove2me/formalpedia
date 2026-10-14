-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part11
-- name    : OAI_QuantumFactoring_Part11
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:26:16.908729+00:00
-- url     : https://prove2.me/theorems/fd67b3ef-fd57-441e-b42a-ed653864428b
-- title:
--   Exact quantum factoring, part 11 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 11 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `NaturalExpressionCircuit`, `ExpressionTemplateCircuit`, `ExpressionPredicates`, `ContinuedFractionPairs`, `ContinuedFractionCircuit`, `BinLabelCircuit`, `LabelRecoveryCircuit`, `SamplerLabels`, `PhysicalTrialLaw`, `OrderCandidateLaw`, `ListTransition`, `OrderTransition`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/NaturalExpressionCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ExpressionTemplateCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ExpressionPredicates.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ContinuedFractionPairs.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ContinuedFractionCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BinLabelCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/LabelRecoveryCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/SamplerLabels.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalTrialLaw.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OrderCandidateLaw.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ListTransition.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OrderTransition.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 11 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: NaturalExpressionCircuit.lean, ExpressionTemplateCircuit.lean, ExpressionPredicates.lean, ContinuedFractionPairs.lean, ContinuedFractionCircuit.lean, BinLabelCircuit.lean, LabelRecoveryCircuit.lean, SamplerLabels.lean, PhysicalTrialLaw.lean, OrderCandidateLaw.lean, ListTransition.lean, OrderTransition.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part10

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NaturalExpressionCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace BitArithmetic

def natSubOn {k w : ℕ} (a b : BooleanNetwork k w) : BooleanNetwork k w :=
  wordMux (wordLe b a) ((a.pair b).comp (sub w)) (wordConstant (BitVec.ofNat w 0))

lemma natSubOn_value {k w : ℕ} (a b : BooleanNetwork k w) (x : Basis k) :
    (bitsValue ((natSubOn a b).eval x)).toNat=
      (bitsValue (a.eval x)).toNat-(bitsValue (b.eval x)).toNat := by
  rw [natSubOn,wordMux_eval,wordLe_eval]
  by_cases h : (bitsValue (b.eval x)).toNat ≤ (bitsValue (a.eval x)).toNat
  · rw [ite_eq_left (by simpa using h),eval_comp,eval_pair,sub_word,BitVec.toNat_sub]
    have hb := (bitsValue (b.eval x)).isLt
    have ha := (bitsValue (a.eval x)).isLt
    have he : 2^w-(bitsValue (b.eval x)).toNat+(bitsValue (a.eval x)).toNat=
        2^w+((bitsValue (a.eval x)).toNat-(bitsValue (b.eval x)).toNat) := by omega
    rw [he,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using h),wordConstant_eval]
    simp only [BitVec.toNat_ofNat,Nat.zero_mod]
    omega

lemma natSubOn_count {k w : ℕ} (a b : BooleanNetwork k w) :
    (natSubOn a b).net.count ≤ 2*a.net.count+2*b.net.count+214*w+15 := by
  have hc := wordLe_count b a
  have hs := sub_count w
  simp only [natSubOn,wordMux_count,count_comp,count_pair,wordConstant_count]
  omega

end BitArithmetic
namespace NatExpr
variable {v : Type*} {k w : ℕ}

def compile (vars : v → BooleanNetwork k w) : NatExpr v → BooleanNetwork k w
  | .var i => vars i
  | .const c => wordConstant (BitVec.ofNat w c)
  | .add a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.add w)
  | .mul a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.mul w)
  | .sub a b => natSubOn (compile vars a) (compile vars b)
  | .div a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.div w)
  | .mod a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.mod w)
  | .iteLe a b c d => wordMux (wordLe (compile vars a) (compile vars b))
      (compile vars c) (compile vars d)

lemma compile_value (vars : v → BooleanNetwork k w) (x : Basis k)
    (e : NatExpr v) (he : Fits (2^w) (fun i => (bitsValue ((vars i).eval x)).toNat) e) :
    (bitsValue ((e.compile vars).eval x)).toNat=
      e.eval (fun i => (bitsValue ((vars i).eval x)).toNat) := by
  induction e with
  | var i => rfl
  | const c =>
    rw [compile,wordConstant_eval,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt he.1
  | add a b ia ib =>
    rw [compile,eval_comp,eval_pair,add_word,BitVec.toNat_add,ia he.2.1,ib he.2.2]
    exact Nat.mod_eq_of_lt he.1
  | mul a b ia ib =>
    rw [compile,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,ia he.2.1,ib he.2.2]
    exact Nat.mod_eq_of_lt he.1
  | sub a b ia ib =>
    rw [compile,natSubOn_value,ia he.2.1,ib he.2.2]
    rfl
  | div a b ia ib =>
    rw [compile,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,ia he.2.1,ib he.2.2]
    rfl
  | mod a b ia ib =>
    rw [compile,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,ia he.2.1,ib he.2.2]
    rfl
  | iteLe a b c d ia ib ic id =>
    rw [compile,wordMux_eval,wordLe_eval,ia he.2.1,ib he.2.2.1]
    simp only [eval,decide_eq_true_eq]
    split_ifs
    · exact ic he.2.2.2.1
    · exact id he.2.2.2.2

/-- Syntactic duplication cost; independent of the numerical constants. -/
def cost : NatExpr v → ℕ
  | .var _ | .const _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => 2*(cost a+cost b)+1
  | .iteLe a b c d => 2*(cost a+cost b+cost c+cost d)+1

def operationBound (w : ℕ) : ℕ := 300*w*w+1000*w+200

lemma compile_count (vars : v → BooleanNetwork k w) {c : ℕ} (hc : ∀ i, (vars i).net.count ≤ c)
    (e : NatExpr v) : (e.compile vars).net.count ≤ e.cost*(operationBound w+c) := by
  induction e with
  | var i =>
    simp only [compile,cost,one_mul]
    exact (hc i).trans (Nat.le_add_left _ _)
  | const d => simp only [compile,cost,one_mul,wordConstant_count,operationBound]; omega
  | add a b ia ib =>
    have hh := add_count w
    simp only [compile,count_comp,count_pair,cost]
    dsimp [operationBound] at *
    nlinarith
  | mul a b ia ib =>
    have hh := mul_count w
    simp only [compile,count_comp,count_pair,cost]
    dsimp [operationBound] at *
    nlinarith
  | sub a b ia ib =>
    have hh := natSubOn_count (a.compile vars) (b.compile vars)
    change (natSubOn (a.compile vars) (b.compile vars)).net.count ≤ _
    simp only [cost]
    dsimp [operationBound] at *
    nlinarith
  | div a b ia ib =>
    have hh := div_count w
    simp only [compile,count_comp,count_pair,cost]
    dsimp [operationBound] at *
    nlinarith
  | mod a b ia ib =>
    have hh := mod_count w
    simp only [compile,count_comp,count_pair,cost]
    dsimp [operationBound] at *
    nlinarith
  | iteLe a b d e ia ib id ie =>
    have hh := wordLe_count (a.compile vars) (b.compile vars)
    simp only [compile,wordMux_count,cost]
    dsimp [operationBound] at *
    nlinarith

end NatExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionTemplateCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

def maxConst : NatExpr v → ℕ
  | .var _ => 0
  | .const c => c
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => max a.maxConst b.maxConst
  | .iteLe a b c d => max (max a.maxConst b.maxConst) (max c.maxConst d.maxConst)

lemma constOK_of_maxConst_lt (e : NatExpr v) {B : ℕ} (h : e.maxConst < B) : e.constOK B := by
  induction e with
  | var i => trivial
  | const c => exact h
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    exact ⟨ia (lt_of_le_of_lt (le_max_left _ _) h),ib (lt_of_le_of_lt (le_max_right _ _) h)⟩
  | iteLe a b c d ia ib ic id =>
    have h₁ : max a.maxConst b.maxConst < B := lt_of_le_of_lt (le_max_left _ _) h
    have h₂ : max c.maxConst d.maxConst < B := lt_of_le_of_lt (le_max_right _ _) h
    exact ⟨ia (lt_of_le_of_lt (le_max_left _ _) h₁),ib (lt_of_le_of_lt (le_max_right _ _) h₁),
      ic (lt_of_le_of_lt (le_max_left _ _) h₂),id (lt_of_le_of_lt (le_max_right _ _) h₂)⟩

def templateWidth (e : NatExpr v) (b : ℕ) : ℕ := (b+e.maxConst.size+1)*e.size
lemma le_templateWidth (e : NatExpr v) (b : ℕ) : b ≤ e.templateWidth b := by
  have h := Nat.le_mul_of_pos_right (b+e.maxConst.size+1) e.size_pos
  dsimp [templateWidth]
  omega

def template {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) :
    BooleanNetwork k (e.templateWidth b) :=
  e.compile (fun i => (vars i).comp (resizeWord b (e.templateWidth b)))

lemma template_value {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) (x : Basis k) :
    (bitsValue ((e.template vars).eval x)).toNat =
      e.eval (fun i => (bitsValue ((vars i).eval x)).toNat) := by
  have hv : (fun i => (bitsValue (((vars i).comp (resizeWord b (e.templateWidth b))).eval x)).toNat)=
      (fun i => (bitsValue ((vars i).eval x)).toNat) := by
    funext i
    rw [eval_comp,resizeWord_toNat (le_templateWidth e b)]
  unfold template
  rw [compile_value,hv]
  rw [hv]
  apply fits_bits (by omega : 1 ≤ b+e.maxConst.size+1)
  · intro i
    exact (bitsValue ((vars i).eval x)).isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  · apply e.constOK_of_maxConst_lt
    exact (Nat.lt_size_self e.maxConst).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega))

lemma template_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.template vars).net.count ≤
      e.cost*(operationBound (e.templateWidth b)+c+e.templateWidth b) := by
  unfold template
  have hh := e.compile_count (fun i => (vars i).comp (resizeWord b (e.templateWidth b)))
    (c:=c+e.templateWidth b) (by
      intro i
      rw [count_comp]
      exact Nat.add_le_add (hc i) (resizeWord_count _ _))
  simpa only [Nat.add_assoc] using hh

end NatExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionPredicates.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

def testEq (a b : NatExpr v) (yes no : NatExpr v) : NatExpr v :=
  .iteLe a b (.iteLe b a yes no) no
lemma eval_testEq (x : v → ℕ) (a b yes no : NatExpr v) :
    (testEq a b yes no).eval x=if a.eval x=b.eval x then yes.eval x else no.eval x := by
  simp only [testEq,eval]
  split_ifs <;> omega

/-- A total exact predicate compiler. All intermediate words are widened from
an explicit expression-derived bound, including on rejected inputs. -/
def isOne {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) : BooleanNetwork k 1 :=
  equalOn (e.template vars) (wordConstant (BitVec.ofNat (e.templateWidth b) 1))
lemma isOne_eval {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) (x : Basis k) :
    (e.isOne vars).eval x 0=true ↔ e.eval (fun i => (bitsValue ((vars i).eval x)).toNat)=1 := by
  rw [isOne,equalOn_value,template_value,wordConstant_eval,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  apply Nat.one_lt_two_pow
  have hh := Nat.mul_pos (show 0<b+e.maxConst.size+1 by omega) e.size_pos
  exact hh.ne'
lemma isOne_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.isOne vars).net.count ≤
      e.cost*(operationBound (e.templateWidth b)+c+e.templateWidth b)+
        100*(e.templateWidth b)+21 := by
  have he := e.template_count vars hc
  have hh := equalOn_count (e.template vars) (wordConstant (n:=k) (BitVec.ofNat (e.templateWidth b) 1))
  simp only [wordConstant_count] at hh
  exact hh.trans (by omega)
end NatExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ContinuedFractionPairs.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

/-- Reduced nonnegative numerator/positive denominator representation; the zero
case is essential because the total rational inverse sends zero to zero. -/
def convergentPair (a b : ℕ) : ℕ → ℕ×ℕ
  | 0 => (a/b,1)
  | k+1 =>
    let p := convergentPair b (a%b) k
    if p.1=0 then (a/b,1) else ((a/b)*p.1+p.2,p.1)

lemma convergentPair_reduced (a b k : ℕ) :
    0<(convergentPair a b k).2 ∧
      Nat.Coprime (convergentPair a b k).1 (convergentPair a b k).2 := by
  induction k generalizing a b with
  | zero => simp [convergentPair]
  | succ k ih =>
    have hh := ih b (a%b)
    simp only [convergentPair]
    split_ifs with h
    · simp
    · constructor
      · exact Nat.pos_of_ne_zero h
      · simpa [Nat.coprime_add_mul_left_left] using hh.2.symm

lemma convergentPair_ratio (a b k : ℕ) :
    ((convergentPair a b k).1:ℚ)/(convergentPair a b k).2=euclidConvergent a b k := by
  induction k generalizing a b with
  | zero => simp [convergentPair,euclidConvergent]
  | succ k ih =>
    have hh := ih b (a%b)
    by_cases h : (convergentPair b (a%b) k).1=0
    · have he : euclidConvergent b (a%b) k=0 := by rw [← hh,h]; simp
      simp [convergentPair,h,euclidConvergent,he]
    · have hp : ((convergentPair b (a%b) k).1:ℚ) ≠ 0 := by exact_mod_cast h
      simp only [convergentPair,ite_eq_right h,Nat.cast_add,Nat.cast_mul,euclidConvergent]
      rw [← hh,inv_div,add_div,mul_div_cancel_right₀ _ hp]

lemma convergentPair_label (a b k : ℕ) :
    rationalLabel (euclidConvergent a b k)=
      ((convergentPair a b k).2,(convergentPair a b k).1) := by
  rw [← convergentPair_ratio]
  exact rationalLabel_reduced (convergentPair_reduced a b k).1 (convergentPair_reduced a b k).2

/-- Linear bit growth, rather than syntactic nested rational inverses. -/
lemma convergentPair_bound {s a b : ℕ} (ha : a<2^s) (hb : b<2^s) (k : ℕ) :
    (convergentPair a b k).1<2^(s*(k+1)+1) ∧
      (convergentPair a b k).2<2^(s*(k+1)+1) := by
  induction k generalizing a b with
  | zero =>
    have hp : 2^s ≤ 2^(s*1+1) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hone : 1<2^(s*1+1) := Nat.one_lt_two_pow (by omega)
    exact ⟨(Nat.div_le_self a b).trans_lt (ha.trans_le hp),hone⟩
  | succ k ih =>
    have hm : a%b<2^s := (Nat.mod_le a b).trans_lt ha
    obtain ⟨hn,hd⟩ := ih hb hm
    have hdiv : a/b<2^s := (Nat.div_le_self a b).trans_lt ha
    have hpow : 2^(s*(k+1)+1) ≤ 2^(s*(k+1+1)+1) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    have ha' : a/b<2^(s*(k+1+1)+1) := hdiv.trans_le
      (Nat.pow_le_pow_right (by omega) (by nlinarith))
    have hone : 1<2^(s*(k+1+1)+1) := Nat.one_lt_two_pow (by omega)
    simp only [convergentPair]
    split_ifs
    · exact ⟨ha',hone⟩
    · refine ⟨?_,hn.trans_le hpow⟩
      have hs : a/b+1 ≤ 2^s := hdiv
      have h₁ : (a/b)*(convergentPair b (a%b) k).1+(convergentPair b (a%b) k).2 <
          (a/b+1)*2^(s*(k+1)+1) := by
        have hx := Nat.mul_le_mul_left (a/b) hn.le
        nlinarith
      have h₂ := Nat.mul_le_mul_right (2^(s*(k+1)+1)) hs
      apply h₁.trans_le
      apply h₂.trans_eq
      rw [← pow_add]
      congr 1
      ring

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ContinuedFractionCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open OrderTrial

abbrev cfWidth (s k : ℕ) := s*(k+1)+1

def cfHead (w : ℕ) : BooleanNetwork (w+(w+w)) w := select (Fin.castAdd (w+w))
def cfTail (w : ℕ) : BooleanNetwork (w+(w+w)) (w+w) := select (Fin.natAdd w)
def cfP (w : ℕ) : BooleanNetwork (w+(w+w)) w := (cfTail w).comp (rootModulus w)
def cfQ (w : ℕ) : BooleanNetwork (w+(w+w)) w := (cfTail w).comp (rootGuess w)
def cfProduct (w : ℕ) : BooleanNetwork (w+(w+w)) w :=
  (((cfHead w).pair (cfP w)).comp (mul w)).pair (cfQ w) |>.comp (add w)
def cfCombine (w : ℕ) : BooleanNetwork (w+(w+w)) (w+w) :=
  let z := equalOn (cfP w) (wordConstant (BitVec.ofNat w 0))
  (wordMux z (cfHead w) (cfProduct w)).pair
    (wordMux z (wordConstant (BitVec.ofNat w 1)) (cfP w))

def convergentNet (w : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => (div w).pair (wordConstant (BitVec.ofNat w 1))
  | k+1 =>
    ((div w).pair ((rootGuess w).pair (mod w))).comp
      ((cfHead w).pair ((cfTail w).comp (convergentNet w k))) |>.comp (cfCombine w)

lemma cfHead_eval (w : ℕ) (h p q : Basis w) :
    (cfHead w).eval (Fin.append h (Fin.append p q))=h := by
  funext i
  exact Fin.append_left h (Fin.append p q) i
lemma cfTail_eval (w : ℕ) (h : Basis w) (pq : Basis (w+w)) :
    (cfTail w).eval (Fin.append h pq)=pq := by
  funext i
  exact Fin.append_right h pq i
lemma cfP_eval (w : ℕ) (h p q : Basis w) :
    (cfP w).eval (Fin.append h (Fin.append p q))=p := by
  rw [cfP,eval_comp,cfTail_eval,rootModulus_eval]
lemma cfQ_eval (w : ℕ) (h p q : Basis w) :
    (cfQ w).eval (Fin.append h (Fin.append p q))=q := by
  rw [cfQ,eval_comp,cfTail_eval,rootGuess_eval]

lemma cfProduct_value (w : ℕ) (h p q : Basis w) :
    (bitsValue ((cfProduct w).eval (Fin.append h (Fin.append p q)))).toNat=
      ((bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat)%2^w := by
  simp only [cfProduct,eval_comp,eval_pair,add_word,mul_word,cfHead_eval,cfP_eval,cfQ_eval,
    BitVec.toNat_add,BitVec.toNat_mul,Nat.mod_add_mod]

lemma cfCombine_value {w : ℕ} (hw : 0<w) (h p q : Basis w)
    (hn : (bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat<2^w) :
    ∃ u v : Basis w,
      (cfCombine w).eval (Fin.append h (Fin.append p q))=Fin.append u v ∧
      (bitsValue u).toNat=(if (bitsValue p).toNat=0 then (bitsValue h).toNat
        else (bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat) ∧
      (bitsValue v).toNat=(if (bitsValue p).toNat=0 then 1 else (bitsValue p).toNat) := by
  have hc : (equalOn (cfP w) (wordConstant (BitVec.ofNat w 0))).eval
      (Fin.append h (Fin.append p q)) 0=true ↔ (bitsValue p).toNat=0 := by
    rw [equalOn_value,cfP_eval,wordConstant_eval]
    simp
  by_cases hp : (bitsValue p).toNat=0
  · refine ⟨h,(wordConstant (n:=w+(w+w)) (BitVec.ofNat w 1)).eval
      (Fin.append h (Fin.append p q)),?_,by simp [hp],?_⟩
    · rw [cfCombine,eval_pair,wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hp),ite_eq_left (hc.mpr hp),cfHead_eval]
    · simp [wordConstant_eval,hp,Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]
  · refine ⟨(cfProduct w).eval (Fin.append h (Fin.append p q)),p,?_,?_,by simp [hp]⟩
    · rw [cfCombine,eval_pair,wordMux_eval,wordMux_eval,
        ite_eq_right (fun hh => hp (hc.mp hh)),ite_eq_right (fun hh => hp (hc.mp hh)),cfP_eval]
    · rw [ite_eq_right hp,cfProduct_value,Nat.mod_eq_of_lt hn]

/-- One recursive circuit is used once per Euclidean level; no exponential
syntax duplication of earlier convergents. -/
lemma convergentNet_value {s w : ℕ} (k : ℕ) (hw : cfWidth s k ≤ w)
    (a b : Basis w) (ha : (bitsValue a).toNat<2^s) (hb : (bitsValue b).toNat<2^s) :
    ∃ p q : Basis w,
      (convergentNet w k).eval (Fin.append a b)=Fin.append p q ∧
      ((bitsValue p).toNat,(bitsValue q).toNat)=convergentPair (bitsValue a).toNat (bitsValue b).toNat k := by
  induction k generalizing a b with
  | zero =>
    refine ⟨(div w).eval (Fin.append a b),(wordConstant (n:=w+w) (BitVec.ofNat w 1)).eval
      (Fin.append a b),eval_pair _ _ _,?_⟩
    simp only [div_word,BitVec.toNat_udiv,wordConstant_eval,BitVec.toNat_ofNat,convergentPair]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by dsimp [cfWidth] at hw; omega))]
  | succ k ih =>
    let r := (mod w).eval (Fin.append a b)
    let d := (div w).eval (Fin.append a b)
    have hr : (bitsValue r).toNat=(bitsValue a).toNat%(bitsValue b).toNat := by
      
      change (bitsValue ((mod w).eval (Fin.append a b))).toNat=_
      rw [mod_word,BitVec.toNat_umod]
    have hd : (bitsValue d).toNat=(bitsValue a).toNat/(bitsValue b).toNat := by
      
      change (bitsValue ((div w).eval (Fin.append a b))).toNat=_
      rw [div_word,BitVec.toNat_udiv]
    have hwk : cfWidth s k ≤ w := by dsimp [cfWidth] at *; nlinarith
    have hrb : (bitsValue r).toNat<2^s := by rw [hr]; exact (Nat.mod_le _ _).trans_lt ha
    obtain ⟨p,q,hpq,he⟩ := ih hwk b r hb hrb
    have hep := congrArg Prod.fst he
    have heq := congrArg Prod.snd he
    simp only [hr] at hep heq
    have hn : (bitsValue d).toNat*(bitsValue p).toNat+(bitsValue q).toNat<2^w := by
      rw [hd,hep,heq]
      by_cases hp : (convergentPair (bitsValue b).toNat ((bitsValue a).toNat%(bitsValue b).toNat) k).1=0
      · rw [hp,mul_zero,zero_add]
        have hh := (convergentPair_bound hb ((Nat.mod_le (bitsValue a).toNat (bitsValue b).toNat).trans_lt ha) k).2
        exact hh.trans_le (Nat.pow_le_pow_right (by omega) hwk)
      · have hh := (convergentPair_bound ha hb (k+1)).1
        simp only [convergentPair,ite_eq_right hp] at hh
        exact hh.trans_le (Nat.pow_le_pow_right (by omega) hw)
    obtain ⟨u,v,huv,hun,hvn⟩ := cfCombine_value (by dsimp [cfWidth] at hw; omega) d p q hn
    refine ⟨u,v,?_,?_⟩
    · simp only [convergentNet,eval_comp,eval_pair,rootGuess_eval,cfTail_eval]
      change (cfCombine w).eval (Fin.append ((cfHead w).eval (Fin.append d (Fin.append b r)))
        ((convergentNet w k).eval (Fin.append b r)))=Fin.append u v
      rw [cfHead_eval,hpq,huv]
    · simp only [hun,hvn,hd,hep,heq,convergentPair]
      split_ifs <;> rfl

lemma cfProduct_count (w : ℕ) : (cfProduct w).net.count ≤ 90*w*w+100*w+12 := by
  simp only [cfProduct,count_comp,count_pair,cfHead,cfP,cfQ,cfTail,rootModulus,rootGuess,
    count_select,zero_add,add_zero]
  have := mul_count w
  have := add_count w
  omega

lemma cfCombine_count (w : ℕ) : (cfCombine w).net.count ≤ 90*w*w+400*w+100 := by
  have hc := equalOn_count (cfP w) (wordConstant (n:=w+(w+w)) (BitVec.ofNat w 0))
  simp only [cfP,cfTail,rootModulus,count_comp,count_select,wordConstant_count,zero_add] at hc
  have hp := cfProduct_count w
  simp only [cfCombine,count_pair,wordMux_count,cfHead,cfP,cfTail,rootModulus,
    count_comp,count_select,wordConstant_count]
  omega

lemma convergentNet_count (w k : ℕ) :
    (convergentNet w k).net.count ≤ (k+1)*(600*w*w+600*w+120) := by
  induction k with
  | zero =>
    simp only [convergentNet,count_pair,wordConstant_count]
    have := div_count w
    nlinarith
  | succ k ih =>
    simp only [convergentNet,count_comp,count_pair,cfHead,cfTail,rootGuess,count_select]
    have := div_count w
    have := mod_count w
    have := cfCombine_count w
    nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BinLabelCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- Input order Q,B,k,d,j; coprimality is already guaranteed by the convergent
recurrence and does not require a second gcd computation. -/
def binCheckExpr : NatExpr (Fin 5) :=
  let Q := NatExpr.var 0
  let B := NatExpr.var 1
  let k := NatExpr.var 2
  let d := NatExpr.var 3
  let j := NatExpr.var 4
  let bin := NatExpr.div (.add (.mul (.mul (.const 2) j) Q) d) (.mul (.const 2) d)
  .iteLe (.const 1) d
    (.iteLe (.add d (.const 1)) B
      (.iteLe (.add j (.const 1)) d
        (.testEq bin k (.const 1) (.const 0)) (.const 0)) (.const 0)) (.const 0)

lemma binCheckExpr_eval (x : Fin 5 → ℕ) :
    binCheckExpr.eval x=1 ↔ 0<x 3 ∧ x 3<x 1 ∧ x 4<x 3 ∧ bin (x 0) (x 3) (x 4)=x 2 := by
  unfold bin
  by_cases hd : 1≤x 3 <;> by_cases hB : x 3+1≤x 1 <;>
    by_cases hj : x 4+1≤x 3 <;>
    by_cases he : (2*x 4*x 0+x 3)/(2*x 3)=x 2 <;>
    simp [binCheckExpr,NatExpr.eval_testEq,NatExpr.eval,hd,hB,hj,he] <;> omega

def checkedConvergent {n w : ℕ} (i : ℕ) (Q B k : BooleanNetwork n w) : BooleanNetwork n (w+w) :=
  let conv := (k.pair Q).comp (convergentNet w i)
  let d := conv.comp (rootGuess w)
  let j := conv.comp (rootModulus w)
  let pass := binCheckExpr.isOne ![Q,B,k,d,j]
  (wordMux pass d (wordConstant (BitVec.ofNat w 0))).pair
    (wordMux pass j (wordConstant (BitVec.ofNat w 0)))

def checkedPair (Q B k i : ℕ) : ℕ×ℕ :=
  let p := convergentPair k Q i
  if IsBinLabel Q B k (p.2,p.1) then (p.2,p.1) else (0,0)

lemma checkedConvergent_value {n s w : ℕ} (i : ℕ) (hw : cfWidth s i ≤ w)
    (Q B k : BooleanNetwork n w) (x : Basis n)
    (hQ : (bitsValue (Q.eval x)).toNat<2^s) (hk : (bitsValue (k.eval x)).toNat<2^s) :
    ∃ d j : Basis w,
      (checkedConvergent i Q B k).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=checkedPair
        (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat i := by
  obtain ⟨p,q,hpq,he⟩ := convergentNet_value i hw (k.eval x) (Q.eval x) hk hQ
  let cv := (k.pair Q).comp (convergentNet w i)
  have hv : cv.eval x=Fin.append p q := by rw [eval_comp,eval_pair,hpq]
  let den := cv.comp (rootGuess w)
  let num := cv.comp (rootModulus w)
  have hd : den.eval x=q := by rw [eval_comp,hv,rootGuess_eval]
  have hj : num.eval x=p := by rw [eval_comp,hv,rootModulus_eval]
  let pass := binCheckExpr.isOne ![Q,B,k,den,num]
  have hc : pass.eval x 0=true ↔ IsBinLabel (bitsValue (Q.eval x)).toNat
      (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat
      ((bitsValue q).toNat,(bitsValue p).toNat) := by
    rw [NatExpr.isOne_eval,binCheckExpr_eval]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Matrix.cons_val_succ,hd,hj]
    have hr := convergentPair_reduced (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i
    have hpv : (bitsValue p).toNat = (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).1 := congrArg Prod.fst he
    have hqv : (bitsValue q).toNat = (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).2 := congrArg Prod.snd he
    change 0<(bitsValue q).toNat ∧ (bitsValue q).toNat<(bitsValue (B.eval x)).toNat ∧
      (bitsValue p).toNat<(bitsValue q).toNat ∧
      bin (bitsValue (Q.eval x)).toNat (bitsValue q).toNat (bitsValue p).toNat=(bitsValue (k.eval x)).toNat ↔ _
    have hcop : Nat.Coprime (bitsValue p).toNat (bitsValue q).toNat := by
      rw [hpv,hqv]
      exact hr.2
    exact ⟨fun ⟨a,b,c,e⟩ => ⟨a,b,c,hcop,e⟩,fun ⟨a,b,c,_,e⟩ => ⟨a,b,c,e⟩⟩
  have he' : ((bitsValue q).toNat,(bitsValue p).toNat)=
      ((convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).2,
        (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).1) :=
    congrArg Prod.swap he
  let zero := (wordConstant (n:=n) (BitVec.ofNat w 0)).eval x
  have hz : (bitsValue zero).toNat=0 := by simp [zero,wordConstant_eval]
  by_cases hh : IsBinLabel (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat
      (bitsValue (k.eval x)).toNat ((bitsValue q).toNat,(bitsValue p).toNat)
  · refine ⟨q,p,?_,?_⟩
    · rw [checkedConvergent,eval_pair]
      change Fin.append ((wordMux pass den _).eval x) ((wordMux pass num _).eval x)=_
      rw [wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hh),ite_eq_left (hc.mpr hh),hd,hj]
    · rw [checkedPair,← he',ite_eq_left hh]
  · refine ⟨zero,zero,?_,?_⟩
    · rw [checkedConvergent,eval_pair]
      change Fin.append ((wordMux pass den _).eval x) ((wordMux pass num _).eval x)=_
      rw [wordMux_eval,wordMux_eval,ite_eq_right (fun h => hh (hc.mp h)),ite_eq_right (fun h => hh (hc.mp h))]
    · rw [checkedPair,← he',ite_eq_right hh,hz]

lemma checkedPair_nonzero_iff {Q B k i : ℕ} :
    (checkedPair Q B k i).1≠0 ↔
      IsBinLabel Q B k ((convergentPair k Q i).2,(convergentPair k Q i).1) := by
  dsimp only [checkedPair]
  split_ifs with h
  · exact ⟨fun _ => h,fun _ => Nat.ne_of_gt h.1⟩
  · simp [h]
lemma checkedPair_sound {Q B k i : ℕ} (h : (checkedPair Q B k i).1≠0) :
    IsBinLabel Q B k (checkedPair Q B k i) := by
  have hh := checkedPair_nonzero_iff.mp h
  simp [checkedPair,hh]

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/LabelRecoveryCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- A bounded scan; either the sole valid label, or the distinguished zero pair. -/
def scanPairs (Q B k : ℕ) : ℕ → ℕ×ℕ
  | 0 => (0,0)
  | i+1 => let a := checkedPair Q B k i
           if a.1≠0 then a else scanPairs Q B k i

lemma scanPairs_success {Q B k K : ℕ} :
    (scanPairs Q B k K).1≠0 ↔ ∃ i<K, (checkedPair Q B k i).1≠0 := by
  induction K with
  | zero => simp [scanPairs]
  | succ K ih =>
    simp only [scanPairs]
    split_ifs with h
    · exact ⟨fun _ => ⟨K,by omega,h⟩,fun _ => h⟩
    · rw [ih]
      constructor
      · rintro ⟨i,hi,hx⟩; exact ⟨i,by omega,hx⟩
      · rintro ⟨i,hi,hx⟩
        refine ⟨i,?_,hx⟩
        by_contra hh
        have he : i=K := by omega
        exact h (he ▸ hx)

lemma scanPairs_sound {Q B k K : ℕ} (h : (scanPairs Q B k K).1≠0) :
    IsBinLabel Q B k (scanPairs Q B k K) := by
  induction K with
  | zero => simp [scanPairs] at h
  | succ K ih =>
    simp only [scanPairs] at h ⊢
    split_ifs at h ⊢ with hh
    · exact checkedPair_sound hh
    · exact ih h

lemma scanPairs_complete {s Q B k : ℕ} {l : ℕ×ℕ} (hQ : B^2≤Q) (hsize : Q<2^s)
    (hl : IsBinLabel Q B k l) : scanPairs Q B k (2*s+1)=l := by
  obtain ⟨_,i,hi,he⟩ := mem_recoveredLabels.mp (recoveredLabels_complete hQ hsize hl)
  rw [convergentPair_label] at he
  have hh : (checkedPair Q B k i).1≠0 := checkedPair_nonzero_iff.mpr (he ▸ hl)
  have hs := scanPairs_success.mpr (⟨i,by omega,hh⟩ : ∃ i<2*s+1, (checkedPair Q B k i).1≠0)
  exact (scanPairs_sound hs).unique hQ hl

/-- Choose the left nonzero-denominator pair, otherwise the right. The costly
candidate and recursive scan are paired ONCE before this inexpensive mux. -/
def pairChoice (w : ℕ) : BooleanNetwork ((w+w)+(w+w)) (w+w) :=
  let left := rootModulus (w+w)
  let right := rootGuess (w+w)
  let den := left.comp (rootModulus w)
  let zero := equalOn den (wordConstant (BitVec.ofNat w 0))
  wordMux zero right left

lemma pairChoice_eval {w : ℕ} (a b c d : Basis w) :
    (pairChoice w).eval (Fin.append (Fin.append a b) (Fin.append c d))=
      if (bitsValue a).toNat=0 then Fin.append c d else Fin.append a b := by
  rw [pairChoice,wordMux_eval]
  simp only [rootModulus_eval,rootGuess_eval]
  have he := equalOn_value
    ((rootModulus (w+w)).comp (rootModulus w))
    (wordConstant (n:=(w+w)+(w+w)) (BitVec.ofNat w 0))
    (Fin.append (Fin.append a b) (Fin.append c d))
  simp only [eval_comp,rootModulus_eval,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod] at he
  simp only [he]

lemma pairChoice_count (w : ℕ) : (pairChoice w).net.count ≤ 120*w+31 := by
  have hc := equalOn_count ((rootModulus (w+w)).comp (rootModulus w))
    (wordConstant (n:=(w+w)+(w+w)) (BitVec.ofNat w 0))
  simp only [rootModulus,count_select,count_comp,wordConstant_count,zero_add] at hc
  simp only [pairChoice,wordMux_count,rootGuess,rootModulus,count_select]
  omega

def recoveryNet {n w : ℕ} (Q B k : BooleanNetwork n w) : ℕ → BooleanNetwork n (w+w)
  | 0 => (wordConstant (BitVec.ofNat w 0)).pair (wordConstant (BitVec.ofNat w 0))
  | i+1 => ((checkedConvergent i Q B k).pair (recoveryNet Q B k i)).comp (pairChoice w)

lemma recoveryNet_value {n s w : ℕ} (Q B k : BooleanNetwork n w) (K : ℕ)
    (hw : cfWidth s K≤w) (x : Basis n)
    (hQ : (bitsValue (Q.eval x)).toNat<2^s) (hk : (bitsValue (k.eval x)).toNat<2^s) :
    ∃ d j : Basis w, (recoveryNet Q B k K).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=scanPairs
        (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat K := by
  induction K with
  | zero =>
    let z := (wordConstant (n:=n) (BitVec.ofNat w 0)).eval x
    refine ⟨z,z,?_,?_⟩
    · exact eval_pair _ _ x
    · simp [z,scanPairs,wordConstant_eval]
  | succ K ih =>
    have hwK : cfWidth s K≤w := by unfold cfWidth at *; nlinarith
    obtain ⟨c,d,hcd,hcdv⟩ := ih hwK
    obtain ⟨a,b,hab,habv⟩ := checkedConvergent_value K hwK Q B k x hQ hk
    have hs : (recoveryNet Q B k (K+1)).eval x=
        if (bitsValue a).toNat=0 then Fin.append c d else Fin.append a b := by
      rw [recoveryNet,eval_comp,eval_pair,hab,hcd,pairChoice_eval]
    have hv : (bitsValue a).toNat=(checkedPair (bitsValue (Q.eval x)).toNat
        (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat K).1 := congrArg Prod.fst habv
    by_cases ha : (bitsValue a).toNat=0
    · refine ⟨c,d,by rw [hs,ite_eq_left ha],?_⟩
      rw [scanPairs,ite_eq_right (by simpa [← hv] using ha),hcdv]
    · refine ⟨a,b,by rw [hs,ite_eq_right ha],?_⟩
      rw [scanPairs,ite_eq_left (by simpa [← hv] using ha)]
      exact habv

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SamplerLabels.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork

def sampleY {w b : ℕ} (x : Basis (OrderSample.width w b)) : Basis b :=
  fun i => x (((Fin.natAdd (w+w) (Triangular.dataWire i)).castAdd w).castAdd (OrderSample.scratch w b))
def sampleU {w b : ℕ} (x : Basis (OrderSample.width w b)) : Basis w :=
  fun i => x ((Fin.natAdd (OrderSample.inputWidth w b) i).castAdd (OrderSample.scratch w b))

lemma sampleY_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    sampleY (OrderSample.word a m y u)=y := by
  funext i
  change (OrderSample.word a m y u) _=y i
  exact (packed_input (OrderSample.inputWord a m y) u (Fin.natAdd (w+w) (Triangular.dataWire i))).trans
    (by simp only [OrderSample.inputWord,Fin.append_right,Triangular.encode_bit])
lemma sampleU_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    sampleU (OrderSample.word a m y u)=u := by
  funext i
  exact packed_target _ _ i

/-- Selected phase block, with every workspace bit accounted for. The input
copies are compared to their retained read-only values. -/
def SampleSelected {w b : ℕ} (a m : Basis w) (x : Basis (OrderSample.width w b)) : Prop :=
  x=OrderSample.word a m (sampleY x) (sampleU x)

lemma sampleSelected_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    SampleSelected a m (OrderSample.word a m y u) := by
  rw [SampleSelected,sampleY_word,sampleU_word]

lemma sampleY_number_injective (b : ℕ) : Function.Injective (@Triangular.outputNumber b) := by
  intro x y h
  apply (bitsEquiv b).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue x).toNat=(bitsValue y).toNat
  simpa only [bitsValue_toNat,Triangular.outputNumber] using h

lemma natBasis_outputNumber (b k : ℕ) : Triangular.outputNumber (natBasis b k)=k%2^b := by
  rw [Triangular.outputNumber,← bitsValue_toNat,natBasis_value]

lemma scanPairs_eq_iff {s Q B k : ℕ} (hQ : B^2≤Q) (hsize : Q<2^s)
    {d j : ℕ} (hd : 0<d) (hdB : d<B) (hj : j<d) (hcop : Nat.Coprime j d) :
    scanPairs Q B k (2*s+1)=(d,j) ↔ bin Q d j=k := by
  constructor
  · intro h
    have hh : (scanPairs Q B k (2*s+1)).1≠0 := by rw [h]; omega
    have hs := scanPairs_sound hh
    rw [h] at hs
    exact hs.2.2.2.2
  · intro h
    exact scanPairs_complete hQ hsize ⟨hd,hdB,hj,hcop,h⟩

lemma selected_recovered_label {w b s B d j : ℕ} (a m : Basis w)
    (hB : B^2≤2^b) (hs : 2^b<2^s) (hd : 0<d) (hdB : d<B)
    (hj : j<d) (hcop : Nat.Coprime j d) :
    (fun x : Basis (OrderSample.width w b) => SampleSelected a m x ∧
      scanPairs (2^b) B (Triangular.outputNumber (sampleY x)) (2*s+1)=(d,j))=
    (fun x => x∈Set.range (OrderSample.word a m (natBasis b (bin (2^b) d j)))) := by
  funext x
  apply propext
  rw [scanPairs_eq_iff hB hs hd hdB hj hcop]
  have hdQ : d≤2^b := by
    have hbpos : 1≤B := by omega
    have hsq : B≤B*B := by simpa using Nat.mul_le_mul_left B hbpos
    nlinarith
  have hk : bin (2^b) d j<2^b := bin_lt hd hdQ hj
  constructor
  · rintro ⟨hx,hy⟩
    refine ⟨sampleU x,?_⟩
    have he : natBasis b (bin (2^b) d j)=sampleY x := by
      apply sampleY_number_injective b
      rw [natBasis_outputNumber,Nat.mod_eq_of_lt hk,hy]
    rw [he]
    exact hx.symm
  · rintro ⟨u,rfl⟩
    refine ⟨sampleSelected_word a m u _,?_⟩
    rw [sampleY_word,natBasis_outputNumber,Nat.mod_eq_of_lt hk]

/-- Recovery and selected-block checking are now linked to the ACTUAL physical
bin mass, without enumerating bins or residues in the circuit. -/
theorem sampler_recovered_label_mass {w b s B : ℕ} (a m : Basis w)
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hB : B^2≤2^(b+2)) (hs : 2^(b+2)<2^s) (hdB : orderOf u<B)
    (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    Exactness.outcomeMass (fun x : Basis (OrderSample.width w (b+2)) => SampleSelected a m x ∧
      scanPairs (2^(b+2)) B (Triangular.outputNumber (sampleY x)) (2*s+1)=(orderOf u,j))
      (samplerState (s:=b) a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(b+2)) (orderOf u) j t.val := by
  have hd : 0<orderOf u := orderOf_pos u
  rw [selected_recovered_label a m hB hs hd hdB hj hcop]
  apply sampler_selected_bin_mass a m _ hm u ha j
  have hdQ : orderOf u≤2^(b+2) := by
    have hbpos : 1≤B := by omega
    have hsq : B≤B*B := by simpa using Nat.mul_le_mul_left B hbpos
    nlinarith
  rw [natBasis_outputNumber,Nat.mod_eq_of_lt (bin_lt hd hdQ hj)]

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalTrialLaw.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness

noncomputable def recovered {w s : ℕ} (a m : Basis w) (n d j : ℕ)
    (x : Basis (OrderSample.width w (s+2))) : Prop :=
  SampleSelected a m x ∧
    scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY x)) (2*(s+3)+1)=(d,j)

noncomputable def modeFirst {w : ℕ} (s n : ℕ) (a m : Basis w) (d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat<2 ∧ recovered a m n d j x.2.1 ∧ firstPass n d j x.2.2
noncomputable def modeSecond {w : ℕ} (s n d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat=2 ∧ secondPass n d j x.2.2
noncomputable def modeThird {w : ℕ} (s n d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat=3 ∧ thirdPass n d j x.2.2

noncomputable def labelEvent {w : ℕ} (s n : ℕ) (a m : Basis w) (d j : ℕ) (x : Raw w s n) : Prop :=
  modeFirst s n a m d j x ∨ modeSecond s n d j x ∨ modeThird s n d j x

lemma phaseScale_bounds {n s : ℕ} (_hn : 1≤n) (hs : 2^(s+2)=(2^n)^16) :
    (2^n)^2≤2^(s+2) ∧ 2^(s+2)<2^(s+3) := by
  constructor
  · rw [hs]
    exact Nat.pow_le_pow_right (by positivity) (by decide)
  · exact Nat.pow_lt_pow_right (by decide) (by omega)

lemma first_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    outcomeMass (modeFirst s n a m (orderOf u) j) (rawState s n a m)=
      firstModeMass n ((2^n)^16) (2^n) (orderOf u) j := by
  have hd : 0<orderOf u := orderOf_pos u
  have hsamp := sampler_recovered_label_mass (b:=s) (s:=s+3) a m hm u ha
    (phaseScale_bounds hn hs).1 (phaseScale_bounds hn hs).2 hdB j hj hcop
  have hsmass : outcomeMass (recovered (s:=s) a m n (orderOf u) j) (samplerState (s:=s) a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(s+2)) (orderOf u) j t.val := hsamp
  unfold modeFirst rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat<2)
      (fun x => recovered a m n (orderOf u) j x.1 ∧ firstPass n (orderOf u) j x.2),
    fair_threshold_mass (by decide : 2≤2^2),
    independent_mass (samplerState (s:=s) a m) (guessState n) (recovered a m n (orderOf u) j) (firstPass n (orderOf u) j),
    firstPass_mass hn hd hdB j]
  rw [hsmass,Fin.sum_univ_eq_sum_range,hs]
  unfold firstModeMass firstRetention
  norm_num
  ring

lemma second_mass {w n s : ℕ} (hn : 1≤n) (a m : Basis w)
    {d : ℕ} (hd : 0<d) (hdB : d<2^n) (j : ℕ) (hj : j<d) :
    outcomeMass (modeSecond (w:=w) s n d j) (rawState s n a m)=
      secondModeMass n ((2^n)^16) (2^n) d j := by
  unfold modeSecond rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat=2) (fun x => secondPass n d j x.2),
    fair_value_mass (by decide : 2<2^2),
    independent_mass_right (samplerState (s:=s) a m) (guessState n) (secondPass n d j)
      (basis_preparation_normalized (OrderSample.completeSampler w s) _),
    secondPass_mass hn hd hdB j hj]
  unfold secondModeMass
  rw [Finset.mul_sum]
  simp only [discrepancyRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_sub,
    residueProbabilityRat_cast (by positivity : 0<(2^n)^16),Nat.cast_pow,Nat.cast_ofNat]
  norm_num

lemma third_mass {w n s : ℕ} (hn : 1≤n) (a m : Basis w)
    {d : ℕ} (hd : 0<d) (hdB : d<2^n) (j : ℕ) (hj : j<d) :
    outcomeMass (modeThird (w:=w) s n d j) (rawState s n a m)=
      thirdModeMass n ((2^n)^16) (2^n) d j := by
  unfold modeThird rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat=3) (fun x => thirdPass n d j x.2),
    fair_value_mass (by decide : 3<2^2),
    independent_mass_right (samplerState (s:=s) a m) (guessState n) (thirdPass n d j)
      (basis_preparation_normalized (OrderSample.completeSampler w s) _),
    thirdPass_mass hn hd hdB j hj]
  simp only [thirdModeMass,remainderRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    Nat.cast_pow,Nat.cast_ofNat]
  norm_num
  ring

/-- True-order cancellation for the ACTUAL physical finite-gate experiment,
with all unselected sampler amplitudes, guesses, and retention coins retained. -/
theorem labelEvent_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    outcomeMass (labelEvent s n a m (orderOf u) j) (rawState s n a m)=
      (prescribedMass (orderOf u):ℝ) := by
  have hd : 0<orderOf u := orderOf_pos u
  unfold labelEvent
  rw [outcomeMass_disjoint_or _ _ _ (by
    intro x h
    rcases h with ⟨h0,h1|h2⟩
    · have h0 := h0.1; have h1 := h1.1; omega
    · have h0 := h0.1; have h2 := h2.1; omega),
    outcomeMass_disjoint_or _ _ _ (by
      intro x h
      have h1 := h.1.1; have h2 := h.2.1; omega),
    first_mass hn hs a m hm u ha hdB j hj hcop,
    second_mass hn a m hd hdB j hj,third_mass hn a m hd hdB j hj,← add_assoc]
  exact three_mode_mass (by positivity) hd hcop

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderCandidateLaw.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma outcomeMass_finite_union {α β : Type*} [Fintype α] [DecidableEq β]
    (ψ : α→ℂ) (S : Finset β) (E : β→α→Prop)
    (h : ∀ x j k, j∈S → k∈S → E j x → E k x → j=k) :
    outcomeMass (fun x => ∃ j∈S, E j x) ψ=∑ j∈S, outcomeMass (E j) ψ := by
  classical
  unfold outcomeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∃ j∈S, E j x
  · obtain ⟨j,hj,he⟩ := hx
    rw [ite_eq_left ⟨j,hj,he⟩,Finset.sum_eq_single j]
    · rw [ite_eq_left he]
    · intro k hk hkj
      exact ite_eq_right (fun hek => hkj (h x k j hk hj hek he))
    · exact fun hj' => False.elim (hj' hj)
  · rw [ite_eq_right hx]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun he => hx ⟨j,hj,he⟩)

namespace OrderTrial

def ValidLabel (n a m d j : ℕ) : Prop :=
  0<d ∧ d<2^n ∧ j<d ∧ Nat.Coprime j d ∧ a^d%m=1

noncomputable def labelPair {w : ℕ} (s n : ℕ) (x : Raw w s n) : ℕ×ℕ :=
  if (bitsValue x.1).toNat<2 then
    scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY x.2.1)) (2*(s+3)+1)
  else ((bitsValue x.2.2.1).toNat,(bitsValue x.2.2.2.1).toNat)

lemma labelEvent_pair {w s n d j : ℕ} (a m : Basis w) (x : Raw w s n)
    (h : labelEvent s n a m d j x) : labelPair s n x=(d,j) := by
  rcases h with h|h|h
  · rw [labelPair,ite_eq_left h.1]
    exact h.2.1.2
  · have hm := h.1
    rw [labelPair,ite_eq_right (by omega)]
    exact Prod.ext h.2.1 h.2.2.1
  · have hm := h.1
    rw [labelPair,ite_eq_right (by omega)]
    exact Prod.ext h.2.1 h.2.2.1

lemma labelEvent_unique {w s n d j d' j' : ℕ} (a m : Basis w) (x : Raw w s n)
    (h : labelEvent s n a m d j x) (h' : labelEvent s n a m d' j' x) :
    d=d' ∧ j=j' := by
  have he := (labelEvent_pair a m x h).symm.trans (labelEvent_pair a m x h')
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- Arithmetic validation is performed in every mode, before any returned
candidate is used. The plain scan/guess never serves as an order certificate. -/
noncomputable def trialResult {w : ℕ} (s n : ℕ) (a m : Basis w) (x : Raw w s n) : Option ℕ := by
  classical
  let dj := labelPair s n x
  exact if ValidLabel n (bitsValue a).toNat (bitsValue m).toNat dj.1 dj.2 ∧
      labelEvent s n a m dj.1 dj.2 x then some dj.1 else none

lemma trialResult_some {w s n d : ℕ} (a m : Basis w) (x : Raw w s n) :
    trialResult s n a m x=some d ↔ ∃ j,
      ValidLabel n (bitsValue a).toNat (bitsValue m).toNat d j ∧ labelEvent s n a m d j x := by
  classical
  unfold trialResult
  dsimp only
  split_ifs with h
  · constructor
    · intro hd
      have he := Option.some.inj hd
      exact ⟨(labelPair s n x).2,he ▸ h⟩
    · rintro ⟨j,hv,hl⟩
      rw [labelEvent_pair a m x hl]
  · constructor
    · intro hh; cases hh
    · rintro ⟨j,hv,hl⟩
      have he := labelEvent_pair a m x hl
      exact False.elim (h (by simpa only [he] using And.intro hv hl))

lemma validLabel_order_dvd {n a m d j : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (h : ValidLabel n a m d j) : orderOf u∣d := by
  let : NeZero m := ⟨by omega⟩
  apply orderOf_dvd_of_pow_eq_one
  apply Units.ext
  apply ZMod.val_injective
  rw [← nat_pow_eq_unit u ha d,h.2.2.2.2]
  exact (ZMod.val_one'' (by omega : m≠1)).symm

lemma true_validLabel {n a m : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (hdB : orderOf u<2^n)
    (j : ℕ) (hj : j<orderOf u) (hc : Nat.Coprime j (orderOf u)) :
    ValidLabel n a m (orderOf u) j := by
  let : NeZero m := ⟨by omega⟩
  refine ⟨orderOf_pos u,hdB,hj,hc,?_⟩
  rw [nat_pow_eq_unit u ha,pow_orderOf_eq_one,Units.val_one,ZMod.val_one'' (by omega : m≠1)]

lemma trialResult_multiple {w s n d : ℕ} (a m : Basis w) (hm : 2≤(bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (x : Raw w s n) (h : trialResult s n a m x=some d) :
    0<d ∧ d<2^n ∧ orderOf u∣d := by
  obtain ⟨j,hv,_⟩ := (trialResult_some a m x).mp h
  exact ⟨hv.1,hv.2.1,validLabel_order_dvd hm u ha hv⟩

/-- The physical, validated order trial has the manuscript's exact true-order
mass phi(r)*lambda(r). False candidates remain in the recorded history. -/
theorem trialResult_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) :
    outcomeMass (fun x => trialResult s n a m x=some (orderOf u)) (rawState s n a m)=
      (Nat.totient (orderOf u):ℝ)*(prescribedMass (orderOf u):ℝ) := by
  classical
  let S := (Finset.range (orderOf u)).filter (fun j => Nat.Coprime j (orderOf u))
  have he : (fun x : Raw w s n => trialResult s n a m x=some (orderOf u))=
      (fun x => ∃ j∈S, labelEvent s n a m (orderOf u) j x) := by
    funext x
    apply propext
    rw [trialResult_some]
    constructor
    · rintro ⟨j,hv,hl⟩
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv.2.2.1,hv.2.2.2.1⟩,hl⟩
    · rintro ⟨j,hj,hl⟩
      have hj' := Finset.mem_filter.mp hj
      exact ⟨j,true_validLabel hm u ha hdB j (Finset.mem_range.mp hj'.1) hj'.2,hl⟩
  rw [he,outcomeMass_finite_union _ S _ (by
    intro x j k _ _ hj hk
    exact (labelEvent_unique a m x hj hk).2)]
  have hr : ∀ j∈S, outcomeMass (labelEvent s n a m (orderOf u) j) (rawState s n a m)=
      (prescribedMass (orderOf u):ℝ) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact labelEvent_mass hn hs a m hm u ha hdB j (Finset.mem_range.mp hj'.1) hj'.2
  rw [Finset.sum_congr rfl hr,Finset.sum_const,nsmul_eq_mul]
  congr 1
  norm_cast
  simp [S,Nat.totient,Nat.coprime_comm]

lemma actual_trial_lower {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) :
    1/(2048*(n+1):ℝ)≤outcomeMass (fun x => trialResult s n a m x=some (orderOf u)) (rawState s n a m) := by
  rw [trialResult_mass hn hs a m hm u ha hdB]
  have hd := orderOf_pos u
  have he : (1/(2048*(orderOf u:ℝ)))≤(prescribedMass (orderOf u):ℝ) := by
    have ht := (Rat.cast_le (K:=ℝ)).mpr (prescribedMass_lower hd)
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast] using ht
  have ht := totient_ratio_lower hd hdB
  have hmul := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (Nat.totient (orderOf u)))
  have hdiv := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤1/2048)
  calc
    _ = (1/2048:ℝ)*(1/(n+1)) := by simp only [div_eq_mul_inv,mul_inv_rev,one_mul]; ring
    _ ≤ (1/2048:ℝ)*((Nat.totient (orderOf u):ℝ)/orderOf u) := hdiv
    _ = (Nat.totient (orderOf u):ℝ)*(1/(2048*(orderOf u:ℝ))) := by simp only [div_eq_mul_inv,mul_inv_rev,one_mul]; ring
    _ ≤ _ := hmul

end OrderTrial
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ListTransition.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


/-! The actual uniform-list transition in Section 5: its event, exact closed
probability, and unchanged repetition guarantee. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

noncomputable def FavorableBits {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (p₀ : Component m) (b : ℕ) (x : Basis b) : Prop :=
  ∃ a : (ZMod m)ˣ, (a : ZMod m).val=(bitsValue x).toNat ∧ FavorableUnit hm hb p₀ a

lemma favorableBits_mass {m n b : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) (hmb : m ≤ 2^b) :
    outcomeMass (FavorableBits hm hb p₀ b) (fairState b)=
      (favorableCount m n : ℝ)/(2:ℝ)^b := by
  classical
  let : NeZero m := ⟨hm⟩
  let S : Finset (ZMod m)ˣ := Finset.univ.filter (FavorableUnit hm hb p₀)
  have he : (FavorableBits hm hb p₀ b)=
      (fun x => ∃ a∈S, (bitsValue x).toNat=(a : ZMod m).val) := by
    funext x
    apply propext
    simp only [FavorableBits,S,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun ⟨a,ha,hf⟩ => ⟨a,hf,ha.symm⟩,fun ⟨a,hf,ha⟩ => ⟨a,ha.symm,hf⟩⟩
  rw [he,outcomeMass_finite_union _ S _ (by
    intro x a c _ _ ha hc
    apply Units.ext
    exact ZMod.val_injective m (ha.symm.trans hc))]
  have hs : ∀ a∈S, outcomeMass (fun x : Basis b => (bitsValue x).toNat=(a : ZMod m).val)
      (fairState b)=1/(2:ℝ)^b := fun a _ =>
    fair_value_mass ((ZMod.val_lt (a : ZMod m)).trans_le hmb)
  rw [Finset.sum_congr rfl hs,Finset.sum_const,nsmul_eq_mul]
  have hc : S.card=favorableCount m n := by
    rw [favorableCount_eq_card hm hb hodd p₀,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hc,mul_one_div]

lemma coveringPower_le_twice {m : ℕ} (hm : 1 ≤ m) : 2^(Nat.clog 2 m) ≤ 2*m := by
  by_cases he : m=1
  · simp [he]
  · have hm' : 1 < m := by omega
    have hc := Nat.clog_pos (by decide : 1 < 2) hm'
    have hh := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hm'
    simp only [Nat.pred_eq_sub_one] at hh
    calc
      _ = 2^(Nat.clog 2 m-1)*2 := by rw [← pow_succ]; congr 1; omega
      _  ≤  2*m := by omega

lemma favorableBits_lower {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    1/(4*((n:ℝ)+1)) ≤  (favorableCount m n : ℝ)/(2:ℝ)^(Nat.clog 2 m) := by
  have hphi := totient_ratio_lower (by omega : 0 < m) hb
  have hhalf := totient_le_twice_favorableCount (by omega : m ≠ 0) hb hodd p₀ p₁ hne
  have hc := coveringPower_le_twice (by omega : 1 ≤ m)
  have hmR : (0:ℝ) < m := by positivity
  have hpR : (0:ℝ) < (2:ℝ)^(Nat.clog 2 m) := by positivity
  have hnR : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hphiR : (m:ℝ)/(n+1) ≤ m.totient := by
    have hh := (le_div_iff₀ hmR).mp hphi
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hh
  have hhalfR : (m.totient:ℝ) ≤ 2*favorableCount m n := by exact_mod_cast hhalf
  have hcR : (2:ℝ)^(Nat.clog 2 m) ≤ 2*m := by exact_mod_cast hc
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*(n+1)) hpR).mpr
  have hh := (div_le_iff₀ hnR).mp hphiR
  nlinarith

noncomputable def GoodList {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (p₀ : Component m) (K : ℕ) (x : Fin K→Basis (Nat.clog 2 m)) : Prop :=
  ∃ i, FavorableBits hm hb p₀ (Nat.clog 2 m) (x i)

/-- Source formula (5.4), over the literal independent fair-bit preparation. -/
theorem list_good_mass {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) (K : ℕ) :
    outcomeMass (GoodList hm hb p₀ K) (tensorState (fairState (Nat.clog 2 m)) K)=
      1-(1-(favorableCount m n : ℝ)/(2:ℝ)^(Nat.clog 2 m))^K := by
  unfold GoodList
  rw [tensor_some_mass (fairState (Nat.clog 2 m)) K (FavorableBits hm hb p₀ (Nat.clog 2 m)) (fairState_normalized _),
    favorableBits_mass hm hb hodd p₀ (Nat.le_pow_clog (by decide) _)]

theorem list_good_lower {m n : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    1-1/(2:ℝ)^(2*n) ≤ outcomeMass (GoodList (by omega : m ≠ 0) hb p₀ (n^5))
      (tensorState (fairState (Nat.clog 2 m)) (n^5)) := by
  rw [list_good_mass _ hb hodd p₀]
  have hl := favorableBits_lower hm hb hodd p₀ p₁ hne
  have hu := (mass_bounds (fairState (Nat.clog 2 m))
    (FavorableBits (by omega : m ≠ 0) hb p₀ (Nat.clog 2 m)) (fairState_normalized _)).2
  rw [favorableBits_mass _ hb hodd p₀ (Nat.le_pow_clog (by decide) _)] at hu
  apply repeated_success_lower hn _ hu
  calc
    _  ≤  1/(4*((n:ℝ)+1)) := by apply one_div_le_one_div_of_le (by positivity); nlinarith
    _  ≤  _ := hl

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderTransition.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness RepeatedTrials

def minOption : Option ℕ→Option ℕ→Option ℕ
  | none,b => b
  | some a,none => some a
  | some a,some b => some (min a b)

def minimumCandidate : List (Option ℕ)→Option ℕ
  | [] => none
  | a::as => minOption a (minimumCandidate as)

lemma minOption_some_mem {a b : Option ℕ} {d : ℕ} (h : minOption a b=some d) :
    a=some d ∨ b=some d := by
  cases a with
  | none => exact Or.inr h
  | some a =>
    cases b with
    | none => exact Or.inl h
    | some b =>
      have he : min a b=d := Option.some.inj h
      by_cases hab : a≤b
      · exact Or.inl (congrArg some ((min_eq_left hab).symm.trans he))
      · exact Or.inr (congrArg some ((min_eq_right (by omega)).symm.trans he))

lemma minimumCandidate_mem {as : List (Option ℕ)} {d : ℕ} (h : minimumCandidate as=some d) :
    some d∈as := by
  induction as with
  | nil => cases h
  | cons a as ih =>
    rcases minOption_some_mem h with hd|hd
    · exact List.mem_cons.mpr (Or.inl hd.symm)
    · exact List.mem_cons.mpr (Or.inr (ih hd))

lemma minimumCandidate_lower {as : List (Option ℕ)} {d r : ℕ}
    (h : ∀ a, some a∈as → r≤a) (hd : minimumCandidate as=some d) : r≤d :=
  h d (minimumCandidate_mem hd)

lemma minOption_eq_low {a b : Option ℕ} {r : ℕ}
    (ha : ∀ d, a=some d → r≤d) (hb : ∀ d, b=some d → r≤d) :
    minOption a b=some r ↔ a=some r ∨ b=some r := by
  constructor
  · exact minOption_some_mem
  · rintro (he|he)
    · subst a
      cases b with
      | none => rfl
      | some d => simp only [minOption,min_eq_left (hb d rfl)]
    · subst b
      cases a with
      | none => rfl
      | some d => simp only [minOption,min_eq_right (ha d rfl)]

lemma minimumCandidate_eq_low {as : List (Option ℕ)} {r : ℕ}
    (h : ∀ a, some a∈as → r≤a) : minimumCandidate as=some r ↔ some r∈as := by
  induction as with
  | nil => simp [minimumCandidate]
  | cons a as ih =>
    have ht : ∀ b, some b∈as → r≤b := fun b hb => h b (List.mem_cons_of_mem a hb)
    rw [minimumCandidate,minOption_eq_low (by
      intro d hd
      exact h d (List.mem_cons.mpr (Or.inl hd.symm))) (fun d hd => minimumCandidate_lower ht hd),ih ht]
    simp only [List.mem_cons,eq_comm]

/-- The source order transition ignores empty trials and returns the least
nonempty candidate, with zero for the entirely empty list. -/
noncomputable def orderResult {w : ℕ} (s n : ℕ) (a m : Basis w) (K : ℕ)
    (x : Fin K→Raw w s n) : ℕ :=
  (minimumCandidate (List.ofFn (fun i => trialResult s n a m (x i)))).getD 0

lemma orderResult_eq_order {w s n K : ℕ} (a m : Basis w) (hm : 2≤(bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (x : Fin K→Raw w s n) :
    orderResult s n a m K x=orderOf u ↔ ∃ i, trialResult s n a m (x i)=some (orderOf u) := by
  have hlow : ∀ d, some d∈List.ofFn (fun i => trialResult s n a m (x i)) → orderOf u≤d := by
    intro d hd
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hd
    have hh := trialResult_multiple a m hm u ha (x i) hi
    exact Nat.le_of_dvd hh.1 hh.2.2
  have he := minimumCandidate_eq_low hlow
  have hr : 0<orderOf u := orderOf_pos u
  have hd : ∀ c : Option ℕ, c.getD 0=orderOf u ↔ c=some (orderOf u) := by
    intro c
    cases c <;> simp [Ne.symm hr.ne']
  rw [orderResult,hd,he]
  simp only [List.mem_ofFn]

/-- Physical repeated law (before the deterministic minimum oracle). -/
theorem orderResult_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (K : ℕ) :
    outcomeMass (fun x => orderResult s n a m K x=orderOf u) (tensorState (rawState s n a m) K)=
      1-(1-(Nat.totient (orderOf u):ℝ)*(prescribedMass (orderOf u):ℝ))^K := by
  have he : (fun x : Fin K→Raw w s n => orderResult s n a m K x=orderOf u)=
      (fun x => ∃ i, trialResult s n a m (x i)=some (orderOf u)) := by
    funext x
    exact propext (orderResult_eq_order a m hm u ha x)
  rw [he,tensor_some_mass (rawState s n a m) K (fun x => trialResult s n a m x=some (orderOf u)) (raw_normalized s n a m),trialResult_mass hn hs a m hm u ha hdB]

/-- Original cutoff, original K=n^5, no extra oracle or changed asymptotics. -/
theorem orderResult_lower {w n s : ℕ} (hn : 128≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) :
    1-1/(2:ℝ)^(2*n)≤outcomeMass (fun x => orderResult s n a m (n^5) x=orderOf u)
      (tensorState (rawState s n a m) (n^5)) := by
  have hn' : 1≤n := by omega
  rw [orderResult_mass hn' hs a m hm u ha hdB]
  have hl := actual_trial_lower hn' hs a m hm u ha hdB
  have hu := (mass_bounds (rawState s n a m) (fun x => trialResult s n a m x=some (orderOf u))
    (raw_normalized s n a m)).2
  rw [trialResult_mass hn' hs a m hm u ha hdB] at hl hu
  exact repeated_success_lower hn hl hu

end ExactQuantumFactoring.OrderTrial


end

end OAI


