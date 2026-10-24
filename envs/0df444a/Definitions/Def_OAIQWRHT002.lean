-- Prove2me | Definitions.Def_OAIQWRHT002
-- name    : OAIQWRHT002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T22:19:23.479362+00:00
-- url     : https://prove2.me/theorems/f98f1689-7961-4eed-a1d3-3664f1e46adb
-- title:
--   OpenAI rational hitting lists split: definitions bundle OAIQWRHT002
-- statement:
--   One of the five definitions bundles (`OAIQWRHT000` to `OAIQWRHT004`) of the split of OpenAI's proof that one deterministic Turing machine writes, in polynomial time, a polynomial-size list of rational matrix tuples hitting every admissible nonzero noncommutative rational formula of size at most $s$ (`OAI.RationalHitting.main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/RationalHitting` (OpenAI, *Polynomial Hitting Lists for Noncommutative Rational Formulas*, OpenAI Math Release, September 24, 2026, result family 116, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. Among them are the cyclotomic grid construction of the list (`Generator.list`, `ExecutableGenerator.list`), the pencil certificates, the binary arithmetic procedures, the stack language with its time bounds, and the compiler to `Turing.TM0` machines. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`Formula`, `Evaluates`, `Admissible`, `Nonzero`, `Output`, `encodeOutput`, `Machine`, `run`, `OutputsWithin`, `Hits`, `MainStatement` and the rest) are not repeated: the bundles import them from the published bundle `Def_RationalHitting`. It also imports the bundles `OAIQWRHT000`, `OAIQWRHT001` of this split.
--
--   Modules (some only in part): `BinaryBinomial`, `BinaryDivision`, `BinaryFactorial`, `BinaryGcd`, `BinaryMultiply`, `BinarySubtract`, `BinomialBounds`, `DenseDeterminant`, `DenseRecords`, `Feasibility`, `FiniteCompiler`, `LiftComputation`, `ListProcedures`, `MatrixComputation`, `OutputComputation`, `ProcedureControl`, `ProcedurePairs`, `Procedures`, `RationalArithmetic`, `RationalBinary`, `SignedArithmetic`, `SignedBinary`, `StackLanguage`, `Tabulation`, `TaylorComputation`, `UnaryArithmetic`.
--
--   The theorems the definitions do not need are proved in the three solutions of this split. One proves the published intermediate statement `OAI.RationalHitting.Generator.list_hits` (the paper's Proposition 5.1), one proves `OAI.RationalHitting.ExecutableGenerator.implementation` (Proposition 5.3) using it, and the third proves `OAI.RationalHitting.main` from both. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Polynomial Hitting Lists for Noncommutative Rational Formulas, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 116; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/RationalHitting at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWRHT000
import Definitions.Def_OAIQWRHT001

section
-- module Solutions.OAIQW_RationalHitting.StackLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite structured binary-stack language. Every primitive is a push,
pop, or transfer. -/
namespace RationalHitting.StackLanguage
open Turing
open RationalHitting.TMTime
variable {K : Type} [DecidableEq K]

def instruction : List (Program K) → Stmt K
  | [] => .halt
  | .skip :: ps => jump ps
  | .push k b :: ps => .push k (fun _ => b) (jump ps)
  | .drop k :: ps => .pop k (fun _ _ => none) (jump ps)
  | .transfer a b :: ps => .peek a (fun _ x => x)
      (.branch (fun x => x.isSome)
        (.pop a (fun v _ => v) (.push b (fun v => v.getD false) (jump ps))) (jump ps))
  | .seq p q :: ps => jump (p::q::ps)
  | .branch k p q r :: ps => .peek k (fun _ x => x)
      (.branch (fun x => x.isNone) (jump (p::ps))
        (.branch (fun x => x.getD false) (jump (r::ps)) (jump (q::ps))))
  | .loop k p :: ps => .peek k (fun _ x => x)
      (.branch (fun x => x.isNone) (jump ps) (jump (p::.loop k p::ps)))

def machine (p : Program K) : Labels K → Stmt K
  | none => jump [p]
  | some ps => instruction ps


def support (p : Program K) : Finset (Labels K) := insert none ((locations p []).image some)

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.FiniteCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage.Compiler
open Turing RationalHitting.TMTime
open scoped BigOperators
variable {K : Type} [DecidableEq K]

noncomputable def stackConstant (p : Program K) : ℕ :=
  1 + ∑ l ∈ support p, (StackToOne.stackWeight (machine p l)+1)

abbrev TapeLabels (K : Type) := TM2to1.Λ' K (fun _ => Bool) (Labels K) (Option Bool)
noncomputable def tapeSupport (p : Program K) : Finset (TapeLabels K) :=
  TM2to1.trSupp (machine p) (support p)

end RationalHitting.StackLanguage.Compiler

/-! Raw unary input adapter for the finite block-coded stack compiler.
The alphabet is exactly Fin 4. No list-processing oracle is an instruction. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma normalizeWord_length (l : List Bool) : (normalizeWord l).length = (wordValue l).size := by
  rw [normalizeWord_eq_bits,Nat.size_eq_bits_len]

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinarySubtract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

lemma wordValue_bit (x : Bool) (a : List Bool) : wordValue (x::a) = bitNat x+2*wordValue a := rfl

lemma digit_subtract (x y c : Bool) :
    bitNat x + 2*bitNat (borrowBit x y c) =
      bitNat (differenceBit x y c)+bitNat y+bitNat c := by
  cases x <;> cases y <;> cases c <;> decide

/-- Fixed-width subtraction, returning the overflow borrow. Registers may have
leading zeros. Width is exactly the larger input word length. -/
def subtractWord : List Bool → List Bool → Bool → List Bool × Bool
  | [],[],c => ([],c)
  | x::a,b,c =>
    let u := subtractWord a b.tail (borrowBit x (b.headD false) c)
    (differenceBit x (b.headD false) c :: u.1,u.2)
  | [],y::b,c =>
    let u := subtractWord [] b (borrowBit false y c)
    (differenceBit false y c :: u.1,u.2)

lemma subtractWord_length (a b : List Bool) (c : Bool) :
    (subtractWord a b c).1.length = max a.length b.length := by
  fun_induction subtractWord a b c with
  | case1 c => simp []
  | case2 x a b c u ih =>
    cases b <;> simp_all [u,Nat.succ_max_succ]
  | case3 y b c u ih => simp_all [u]

lemma subtractWord_value (a b : List Bool) (c : Bool) :
    wordValue a + 2^(max a.length b.length)*bitNat (subtractWord a b c).2 =
      wordValue (subtractWord a b c).1 + wordValue b + bitNat c := by
  fun_induction subtractWord a b c with
  | case1 c => simp [wordValue]
  | case2 x a b c u ih =>
    have hd := digit_subtract x (b.headD false) c
    cases b <;>
      simp only [u,List.tail_nil,List.tail_cons,List.headD_nil,List.headD_cons,
        List.length_nil,List.length_cons,Nat.max_zero,Nat.succ_max_succ,
        pow_succ,wordValue_bit,wordValue_nil,bitNat_false] at * <;>
      linear_combination 2*ih+hd
  | case3 y b c u ih =>
    have hd := digit_subtract false y c
    simp only [u,List.length_nil,List.length_cons,Nat.zero_max,
      pow_succ,wordValue_bit,wordValue_nil,bitNat_false] at *
    linear_combination 2*ih+hd

lemma subtractWord_borrow (a b : List Bool) :
    (subtractWord a b false).2 = true ↔ wordValue a < wordValue b := by
  have hv := subtractWord_value a b false
  have hx := wordValue_lt (subtractWord a b false).1
  rw [subtractWord_length] at hx
  have ha := (wordValue_lt a).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left a.length b.length))
  have hb := (wordValue_lt b).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_right a.length b.length))
  cases he : (subtractWord a b false).2 <;> simp [he,bitNat] at hv ⊢ <;> omega

lemma subtractWord_nonnegative {a b : List Bool} (h : wordValue b ≤ wordValue a) :
    (subtractWord a b false).2 = false ∧
      wordValue (subtractWord a b false).1 = wordValue a-wordValue b := by
  have hn : (subtractWord a b false).2 = false := by
    cases he : (subtractWord a b false).2
    · rfl
    · have := (subtractWord_borrow a b).mp he; omega
  have hv := subtractWord_value a b false
  simp [hn,bitNat] at hv
  exact ⟨hn,by omega⟩

variable {K : Type} [DecidableEq K]

lemma eval_readBit (k : K) (f : Bool → Program K) (s v : Store K) (t : ℕ)
    (h : Eval (f ((s k).headD false)) s v t) : Eval (readBit k f) s v (1+t) := by
  cases he : s k with
  | nil => exact Eval.branchNone he (by simpa [he] using h)
  | cons b l =>
    cases b with
    | false => exact Eval.branchFalse he (by simpa [he] using h)
    | true => exact Eval.branchTrue he (by simpa [he] using h)

lemma eval_subtractDigit (s : Store (Fin 5)) (c : Bool) (hc : s 3 = [c]) :
    Eval subtractDigit s
      (update (update (update (update s 0 (s 0).tail) 1 (s 1).tail)
        3 [borrowBit ((s 0).headD false) ((s 1).headD false) c])
        2 (differenceBit ((s 0).headD false) ((s 1).headD false) c :: s 2)) 12 := by
  unfold subtractDigit
  apply eval_readBit (t := 11)
  apply eval_readBit (t := 10)
  apply eval_readBit (t := 9)
  let s₁ := update s 0 (s 0).tail
  let s₂ := update s₁ 1 (s 1).tail
  let s₃ := update s₂ 3 []
  have h1 := Eval.drop (0 : Fin 5) s
  have h2 := Eval.drop (1 : Fin 5) s₁
  have h3 : Eval (Program.drop 3) s₂ s₃ 1 := by simpa [s₃,s₂,s₁,hc] using Eval.drop (3 : Fin 5) s₂
  have h4 := Eval.push (3 : Fin 5) (borrowBit ((s 0).headD false) ((s 1).headD false) c) s₃
  have h4' : Eval (Program.push 3 (borrowBit ((s 0).headD false) ((s 1).headD false) c)) s₃
    (update s₃ 3 [borrowBit ((s 0).headD false) ((s 1).headD false) c]) 1 := by simpa [s₃] using h4
  have h5 := Eval.push (2 : Fin 5) (differenceBit ((s 0).headD false) ((s 1).headD false) c)
    (update s₃ 3 [borrowBit ((s 0).headD false) ((s 1).headD false) c])
  simpa [s₃,s₂,s₁,hc] using Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4' h5)))

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

def subStep (s : Store (Fin 5)) (c : Bool) : Store (Fin 5) :=
  update (update (update (update s 0 (s 0).tail) 1 (s 1).tail)
    3 [borrowBit ((s 0).headD false) ((s 1).headD false) c])
    2 (differenceBit ((s 0).headD false) ((s 1).headD false) c :: s 2)

def subFinish (s : Store (Fin 5)) (c : Bool) : Store (Fin 5) :=
  let r := subtractWord (s 0) (s 1) c
  update (update (update (update (update s 0 []) 1 []) 2 (r.1.reverse++s 2))
    3 [r.2]) 4 []

lemma eval_subtractLoop (s : Store (Fin 5)) (c : Bool) (hc : s 3 = [c]) (hf : s 4 = [true]) :
    ∃ t ≤ 15*((s 0).length+(s 1).length)+7,
      Eval subtractLoop s (subFinish s c) t := by
  generalize ha : s 0 = a, hb : s 1 = b
  induction a generalizing b c s with
  | nil =>
    induction b generalizing c s with
    | nil =>
      have hclear : Eval (clear 4) s (update s 4 []) 3 := by simpa [hf] using eval_clear (4 : Fin 5) s
      have hbody : Eval subtractBody s (update s 4 []) 5 :=
        Eval.branchNone ha (Eval.branchNone hb hclear)
      have h := Eval.whileCons (k := (4 : Fin 5)) (by simp [hf]) hbody (Eval.whileNil (k := (4 : Fin 5)) (p := subtractBody) (by simp))
      have heq : subFinish s c = update s 4 [] := by
        ext k; fin_cases k <;> simp [subFinish,ha,hb,subtractWord,hc]
      exact ⟨7,by simp,by simpa [subtractLoop,heq] using h⟩
    | cons y b ih =>
      let u := subStep s c
      have hcd : u 3 = [borrowBit false y c] := by simp [u,subStep,ha,hb]
      have hflag : u 4 = [true] := by simp [u,subStep,hf]
      obtain ⟨t,ht,hr⟩ := ih u (borrowBit false y c) hcd hflag
        (by simp [u,subStep,ha]) (by simp [u,subStep,hb])
      have hd : Eval subtractDigit s u 12 := eval_subtractDigit s c hc
      have hbdy : Eval subtractBody s u 14 := by
        cases y with
        | false => exact Eval.branchNone ha (Eval.branchFalse hb hd)
        | true => exact Eval.branchNone ha (Eval.branchTrue hb hd)
      have heq : subFinish u (borrowBit false y c) = subFinish s c := by
        ext k; fin_cases k <;>
          simp [subFinish,u,subStep,ha,hb,subtractWord,List.reverse_cons,List.append_assoc]
      rw [heq] at hr
      refine ⟨15+t,?_,Eval.whileCons (by simp [hf]) hbdy hr⟩
      simp [List.length_cons] at *
      omega
  | cons x a ih =>
    let u := subStep s c
    have hcd : u 3 = [borrowBit x (b.headD false) c] := by simp [u,subStep,ha,hb]
    have hflag : u 4 = [true] := by simp [u,subStep,hf]
    obtain ⟨t,ht,hr⟩ := ih u (borrowBit x (b.headD false) c) hcd hflag
      b.tail (by simp [u,subStep,ha]) (by simp [u,subStep,hb])
    have hd : Eval subtractDigit s u 12 := eval_subtractDigit s c hc
    have hbdy : Eval subtractBody s u 13 := by
      cases x with
      | false => exact Eval.branchFalse ha hd
      | true => exact Eval.branchTrue ha hd
    have heq : subFinish u (borrowBit x (b.headD false) c) = subFinish s c := by
      ext k; fin_cases k <;>
        simp [subFinish,u,subStep,ha,hb,subtractWord,List.reverse_cons,List.append_assoc]
    rw [heq] at hr
    refine ⟨14+t,?_,Eval.whileCons (by simp [hf]) hbdy hr⟩
    have hlen : b.tail.length ≤ b.length := by cases b <;> simp
    simp only [List.length_cons]
    omega

lemma eval_subtract (s : Store (Fin 5)) :
    ∃ t ≤ 17*((s 0).length+(s 1).length)+2*(s 2).length+2*(s 3).length+2*(s 4).length+19,
      Eval subtract s
        (update (update (update (update (update s 0 (subtractWord (s 0) (s 1) false).1) 1 []) 2 [])
          3 [(subtractWord (s 0) (s 1) false).2]) 4 []) t := by
  let s₁ := update s 2 []
  let s₂ := update s₁ 3 []
  let s₃ := update s₂ 4 []
  let s₄ := update s₃ 3 [false]
  let s₅ := update s₄ 4 [true]
  obtain ⟨t,ht,hl⟩ := eval_subtractLoop s₅ false (by simp [s₅,s₄]) (by simp [s₅])
  have hr := eval_reverse (a := (2 : Fin 5)) (b := 0) (by decide) (subFinish s₅ false)
  have hp3 : Eval (Program.push 3 false) s₃ s₄ 1 := by simpa [s₄,s₃,s₂] using Eval.push (3 : Fin 5) false s₃
  have hp4 : Eval (Program.push 4 true) s₄ s₅ 1 := by simpa [s₅,s₄,s₃] using Eval.push (4 : Fin 5) true s₄
  have h := Eval.seq (eval_clear (2 : Fin 5) s) (Eval.seq (eval_clear (3 : Fin 5) s₁)
    (Eval.seq (eval_clear (4 : Fin 5) s₂) (Eval.seq hp3 (Eval.seq hp4 (Eval.seq hl hr)))))
  have heq : update (update (subFinish s₅ false) 2 []) 0
      (((subFinish s₅ false) 2).reverse++(subFinish s₅ false) 0) =
        update (update (update (update (update s 0 (subtractWord (s 0) (s 1) false).1) 1 []) 2 [])
          3 [(subtractWord (s 0) (s 1) false).2]) 4 [] := by
    ext k; fin_cases k <;> simp [subFinish,s₅,s₄,s₃,s₂,s₁]
  rw [heq] at h
  refine ⟨_,?_,h⟩
  have hlength := subtractWord_length (s 0) (s 1) false
  simp [s₅,s₄,s₃,s₂,s₁,subFinish] at *
  omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage

def reduceWord (a b : List Bool) : List Bool × Bool :=
  let r := subtractWord a b false
  if r.2 then (normalizeWord a,false) else (normalizeWord r.1,true)

lemma normalize_length_of_lt (a : List Bool) (B : ℕ) (h : wordValue a < 2^B) :
    (normalizeWord a).length ≤ B := by
  rw [normalizeWord_length,Nat.size_le]
  exact h

lemma reduceWord_spec (a b : List Bool) (_hb : 0<wordValue b)
    (ha : wordValue a < 2*wordValue b) :
    wordValue (reduceWord a b).1 < wordValue b ∧
    wordValue (reduceWord a b).1+bitNat (reduceWord a b).2*wordValue b = wordValue a ∧
    (reduceWord a b).1.length ≤ b.length := by
  by_cases hl : wordValue a < wordValue b
  · have hc := (subtractWord_borrow a b).mpr hl
    simp only [reduceWord,hc,ite_true,normalizeWord_value,bitNat_false,zero_mul,add_zero,true_and]
    exact ⟨hl,normalize_length_of_lt a b.length (hl.trans (wordValue_lt b))⟩
  · obtain ⟨hc,hv⟩ := subtractWord_nonnegative (Nat.le_of_not_gt hl)
    have hs : wordValue (subtractWord a b false).1 < wordValue b := by omega
    simp only [reduceWord,hc,Bool.false_eq_true,ite_false,normalizeWord_value]
    refine ⟨hs,?_,normalize_length_of_lt _ _ (hs.trans (wordValue_lt b))⟩
    simp only [bitNat,ite_true,one_mul]
    omega

/-- Long division, scanning the original numerator most-significant-bit first.
The quotient and remainder registers remain ordinary little-endian words. -/
def divideDigits (b : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | [],r,q => (r,q)
  | x::l,r,q =>
    let v := reduceWord (x::r) b
    divideDigits b l v.1 (v.2::q)

lemma divideDigits_spec (b l r q : List Bool) (hb : 0<wordValue b) (hr : wordValue r<wordValue b) :
    wordValue (divideDigits b l r q).1 < wordValue b ∧
    wordValue (divideDigits b l r q).2*wordValue b+wordValue (divideDigits b l r q).1 =
      (wordValue q*wordValue b+wordValue r)*2^l.length+wordValue l.reverse ∧
    (divideDigits b l r q).2.length = q.length+l.length ∧
    (divideDigits b l r q).1.length ≤ max r.length b.length := by
  induction l generalizing r q with
  | nil => simp [divideDigits,hr]
  | cons x l ih =>
    have hx := bitNat_le_one x
    have hc : wordValue (x::r) < 2*wordValue b := by rw [wordValue_bit]; omega
    obtain ⟨hv,he,hlen⟩ := reduceWord_spec (x::r) b hb hc
    obtain ⟨hv',he',hq',hl'⟩ := ih (reduceWord (x::r) b).1 ((reduceWord (x::r) b).2::q) hv
    refine ⟨hv',?_,?_,?_⟩
    · rw [wordValue_bit] at he he'
      simp only [divideDigits,List.length_cons]
      rw [he',List.reverse_cons,wordValue_append,wordValue_bit,wordValue_nil,mul_zero,add_zero,List.length_reverse]
      simp only [pow_succ]
      linear_combination (2^l.length)*he
    · simpa [divideDigits,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq'
    · exact hl'.trans (max_le (hlen.trans (Nat.le_max_right _ _)) (Nat.le_max_right _ _))

lemma divideDigits_quotient_remainder (a b : List Bool) (hb : 0<wordValue b) :
    wordValue (divideDigits b a.reverse [] []).1 = wordValue a % wordValue b ∧
    wordValue (divideDigits b a.reverse [] []).2 = wordValue a / wordValue b := by
  obtain ⟨hr,he,_,_⟩ := divideDigits_spec b a.reverse [] [] hb (by simpa [wordValue] using hb)
  simp [wordValue] at he
  have hm := congrArg (fun k => k % wordValue b) he
  simp [Nat.add_mod,Nat.mod_eq_of_lt hr] at hm
  refine ⟨hm,?_⟩
  symm
  exact Nat.div_eq_of_lt_le (by omega) (by linarith only [he,hr])

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Uniform register allocation: renaming injectively never changes time and
preserves every register outside its finite image. -/
theorem Eval.rename {p : Program K} {s v : Store K} {t : ℕ} (h : Eval p s v t)
    (f : K → L) (hf : Injective f) (S : Store L) :
    Eval (p.rename f) (extend f s S) (extend f v S) t := by
  classical
  induction h with
  | skip s => exact Eval.skip _
  | push k b s =>
    simpa [Program.rename,extend_update_store f hf,hf.extend_apply] using
      Eval.push (f k) b (extend f s S)
  | drop k s =>
    simpa [Program.rename,extend_update_store f hf,hf.extend_apply] using
      Eval.drop (f k) (extend f s S)
  | transfer a b s =>
    simpa [Program.rename,extend_transfer_store f hf] using Eval.transfer (f a) (f b) (extend f s S)
  | seq h1 h2 ih1 ih2 => exact Eval.seq ih1 ih2
  | branchNone he hh ih => exact Eval.branchNone (by simpa only [hf.extend_apply] using he) ih
  | branchFalse he hh ih => exact Eval.branchFalse (by simpa only [hf.extend_apply] using he) ih
  | branchTrue he hh ih => exact Eval.branchTrue (by simpa only [hf.extend_apply] using he) ih
  | whileNil he => exact Eval.whileNil (by simpa only [hf.extend_apply] using he)
  | whileCons he h1 h2 ih1 ih2 => exact Eval.whileCons (by simpa only [hf.extend_apply] using he) ih1 ih2

lemma eval_rename_from (f : K → L) (hf : Injective f) (S : Store L)
    {p : Program K} {v : Store K} {t : ℕ} (h : Eval p (fun k => S (f k)) v t) :
    Eval (p.rename f) S (extend f v S) t := by
  simpa only [extend_pull_store f hf S] using h.rename f hf S

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryGcd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

lemma eval_subtract10 (s : Store (Fin 10)) :
    ∃ t ≤ 17*((s 0).length+(s 1).length)+2*(s 2).length+2*(s 3).length+2*(s 4).length+19,
      Eval subtract10 s
        (update (update (update (update (update s 0 (subtractWord (s 0) (s 1) false).1) 1 []) 2 [])
          3 [(subtractWord (s 0) (s 1) false).2]) 4 []) t := by
  obtain ⟨t,ht,he⟩ := eval_subtract (fun k : Fin 5 => s (subEmbed k))
  have hh := eval_rename_from subEmbed subEmbed.injective s he
  refine ⟨t,ht,?_⟩
  have h0 : subEmbed 0 = 0 := by decide
  have h1 : subEmbed 1 = 1 := by decide
  have h2 : subEmbed 2 = 2 := by decide
  have h3 : subEmbed 3 = 3 := by decide
  have h4 : subEmbed 4 = 4 := by decide
  simpa only [subtract10,h0,h1,h2,h3,h4,extend_update_store subEmbed subEmbed.injective,
    extend_pull_store subEmbed subEmbed.injective] using hh

lemma eval_reducePick (s : Store (Fin 10)) (c : Bool) (hc : s 3 = [c]) (h9 : s 9 = []) :
    ∃ t ≤ 7*(s 8).length+2*(s 0).length+10,
      Eval reducePick s
        (update (update s 0 (if c then s 8 else s 0)) 7 ((!c)::s 7)) t := by
  cases c with
  | false =>
    refine ⟨2,by omega,?_⟩
    simpa [reducePick] using (Eval.branchFalse (p := Program.skip)
      (r := Program.seq (copy 8 0 9) (.push 7 false)) hc (Eval.push (7 : Fin 10) true s))
  | true =>
    let u := update (update s 0 (s 8)) 9 []
    have hc' := eval_copy (a := (8 : Fin 10)) (b := 0) (tmp := 9) (by decide) (by decide) (by decide) s
    have hp : Eval (Program.push 7 false) u (update u 7 (false::s 7)) 1 := by
      simpa [u] using Eval.push (7 : Fin 10) false u
    have hh := Eval.branchTrue (p := Program.skip) (q := Program.push 7 true) hc (Eval.seq hc' hp)
    have heq : update u 7 (false::s 7) = update (update s 0 (s 8)) 7 (false::s 7) := by
      funext k; by_cases hk0 : k=0 <;> by_cases hk7 : k=7 <;> by_cases hk9 : k=9 <;> simp_all [u]
    rw [heq] at hh
    refine ⟨7*(s 8).length+2*(s 0).length+10,le_refl _,?_⟩
    convert hh using 1 <;> simp [reducePick,h9,Nat.add_comm] ; omega

def divScratch (s : Store (Fin 10)) : Prop :=
  s 1 = [] ∧ s 2 = [] ∧ s 3 = [] ∧ s 4 = [] ∧ s 8 = [] ∧ s 9 = []

lemma eval_reduceOnce (s : Store (Fin 10)) (hs : divScratch s) :
    ∃ t ≤ 100*((s 0).length+(s 5).length+1),
      Eval reduceOnce s (update (update s 0 (reduceWord (s 0) (s 5)).1)
        7 ((reduceWord (s 0) (s 5)).2::s 7)) t := by
  obtain ⟨h1,h2,h3,h4,h8,h9⟩ := hs
  let s₁ := update (update s 8 (s 0)) 9 []
  let s₂ := update (update s₁ 1 (s 5)) 9 []
  have hc0 : Eval (copy 0 8 9) s s₁ (7*(s 0).length+7) := by
    simpa [s₁,h8,h9] using eval_copy (a := (0 : Fin 10)) (b := 8) (tmp := 9) (by decide) (by decide) (by decide) s
  have hc5 : Eval (copy 5 1 9) s₁ s₂ (7*(s 5).length+7) := by
    simpa [s₂,s₁,h1] using eval_copy (a := (5 : Fin 10)) (b := 1) (tmp := 9) (by decide) (by decide) (by decide) s₁
  obtain ⟨t,ht,hd⟩ := eval_subtract10 s₂
  let r := subtractWord (s 0) (s 5) false
  let s₃ := update (update (update (update (update s₂ 0 r.1) 1 []) 2 []) 3 [r.2]) 4 []
  have hd' : Eval subtract10 s₂ s₃ t := by simpa [s₃,r,s₂,s₁] using hd
  obtain ⟨u,hu,hp⟩ := eval_reducePick s₃ r.2 (by simp [s₃]) (by simp [s₃,s₂])
  let s₄ := update (update s₃ 0 (if r.2 then s 0 else r.1)) 7 ((!r.2)::s 7)
  have hp' : Eval reducePick s₃ s₄ u := by simpa [s₄,s₃,s₂,s₁] using hp
  obtain ⟨v,hv,hn⟩ := eval_normalize (a := (0 : Fin 10)) (tmp := 2) (flag := 4)
    (by decide) (by decide) (by decide) s₄
  let s₅ := update (update (update s₄ 0 (normalizeWord (s₄ 0))) 2 []) 4 []
  have hn' : Eval (normalize 0 2 4) s₄ s₅ v := hn
  let s₆ := update s₅ 3 []
  have hclear3 : Eval (clear 3) s₅ s₆ 3 := by simpa [s₆,s₅,s₄,s₃] using eval_clear (3 : Fin 10) s₅
  have hclear8 : Eval (clear 8) s₆ (update s₆ 8 []) (2*(s 0).length+1) := by
    simpa [s₆,s₅,s₄,s₃,s₂,s₁] using eval_clear (8 : Fin 10) s₆
  have heval := Eval.seq hc0 (Eval.seq hc5 (Eval.seq hd' (Eval.seq hp' (Eval.seq hn' (Eval.seq hclear3 hclear8)))))
  have heq : update s₆ 8 [] = update (update s 0 (reduceWord (s 0) (s 5)).1)
      7 ((reduceWord (s 0) (s 5)).2::s 7) := by
    funext k
    cases hr : r.2 <;> dsimp [r] at hr <;> fin_cases k <;>
      simp [s₆,s₅,s₄,s₃,s₂,s₁,reduceWord,r,hr,h1,h2,h3,h4,h8,h9]
  rw [heq] at heval
  refine ⟨_,?_,heval⟩
  have hlen : r.1.length = max (s 0).length (s 5).length := subtractWord_length ..
  have hchosen : (if r.2 then s 0 else r.1).length ≤ (s 0).length+(s 5).length := by
    cases r.2 <;> simp [hlen]
  simp [s₂,s₁,h2,h3,h4] at ht
  simp [s₃,s₂,s₁] at hu
  simp [s₄,s₃] at hv
  omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

lemma eval_divBody (s : Store (Fin 10)) (hs : divScratch s) (x : Bool) (l : List Bool)
    (h6 : s 6=x::l) :
    ∃ t ≤ 110*((s 0).length+(s 5).length+2),
      Eval divBody s (update (update (update s 6 l) 0 (reduceWord (x::s 0) (s 5)).1)
        7 ((reduceWord (x::s 0) (s 5)).2::s 7)) t := by
  let s₁ := update s 6 l
  let s₂ := update s₁ 0 (x::s 0)
  have hd : Eval (Program.drop 6) s s₁ 1 := by simpa [s₁,h6] using Eval.drop (6 : Fin 10) s
  have hp : Eval (Program.push 0 x) s₁ s₂ 1 := by simpa [s₂,s₁] using Eval.push (0 : Fin 10) x s₁
  have hs₂ : divScratch s₂ := by simpa [divScratch,s₂,s₁] using hs
  obtain ⟨t,ht,he⟩ := eval_reduceOnce s₂ hs₂
  have hh := eval_readBit 6 (fun x => Program.seq (.drop 6) (.seq (.push 0 x) reduceOnce)) s _ _
    (by simpa [h6] using Eval.seq hd (Eval.seq hp he))
  refine ⟨1+(2+(2+t)),?_,?_⟩
  · simp [s₂,s₁] at ht
    omega
  · simpa [divBody,s₂,s₁,update_idem] using hh

lemma eval_divLoop (s : Store (Fin 10)) (hs : divScratch s)
    (hb : 0<wordValue (s 5)) (hr : wordValue (s 0)<wordValue (s 5))
    (B : ℕ) (hB : (s 0).length ≤ B) (hbB : (s 5).length ≤ B) :
    ∃ t ≤ (s 6).length*(250*(B+1))+1,
      Eval divLoop s
        (update (update (update s 6 []) 0 (divideDigits (s 5) (s 6) (s 0) (s 7)).1)
          7 (divideDigits (s 5) (s 6) (s 0) (s 7)).2) t := by
  generalize h6 : s 6 = l
  induction l generalizing s with
  | nil =>
    have heq : update (update (update s 6 []) 0 (s 0)) 7 (s 7) = s := by
      funext k; by_cases hk6 : k=6 <;> by_cases hk0 : k=0 <;> by_cases hk7 : k=7 <;> simp_all
    refine ⟨1,by simp,?_⟩
    simpa only [divideDigits,heq,divLoop] using (Eval.whileNil (p := divBody) h6)
  | cons x l ih =>
    let r := reduceWord (x::s 0) (s 5)
    let u := update (update (update s 6 l) 0 r.1) 7 (r.2::s 7)
    have hc : wordValue (x::s 0) < 2*wordValue (s 5) := by
      have hx := bitNat_le_one x
      rw [wordValue_bit]; omega
    obtain ⟨hr',_,hlen⟩ := reduceWord_spec (x::s 0) (s 5) hb hc
    obtain ⟨t,ht,he⟩ := eval_divBody s hs x l h6
    have hs' : divScratch u := by simpa [divScratch,u] using hs
    obtain ⟨v,hv,hloop⟩ := ih u hs' (by simpa [u] using hb) (by simpa [u,r] using hr')
      (by simpa [u,r] using hlen.trans hbB) (by simpa [u] using hbB) (by simp [u])
    have h := Eval.whileCons (by simp [h6]) he hloop
    have heq : update (update (update u 6 []) 0 (divideDigits (u 5) l (u 0) (u 7)).1)
        7 (divideDigits (u 5) l (u 0) (u 7)).2 =
        update (update (update s 6 []) 0 (divideDigits (s 5) (x::l) (s 0) (s 7)).1)
        7 (divideDigits (s 5) (x::l) (s 0) (s 7)).2 := by
      funext k; by_cases hk6 : k=6 <;> by_cases hk0 : k=0 <;> by_cases hk7 : k=7 <;>
        simp_all [u,r,divideDigits]
    rw [heq] at h
    refine ⟨1+t+v,?_,h⟩
    simp only [List.length_cons]
    have hstep : 1+t ≤ 250*(B+1) := by omega
    linarith

lemma eval_divide (s : Store (Fin 10)) (hs : divScratch s) (h6 : s 6=[]) (h7 : s 7=[])
    (hb : 0<wordValue (s 5)) :
    ∃ t ≤ 300*((s 0).length+1)*((s 5).length+1)+30,
      Eval divide s (update (update s 0 (wordValue (s 0)%wordValue (s 5)).bits)
        7 (wordValue (s 0)/wordValue (s 5)).bits) t := by
  let u := update (update s 0 []) 6 (s 0).reverse
  have hre : Eval (reverse 0 6) s u (2*(s 0).length+1) := by
    simpa [u,h6] using eval_reverse (a := (0 : Fin 10)) (b := 6) (by decide) s
  have hu : divScratch u := by simpa [divScratch,u] using hs
  obtain ⟨t,ht,he⟩ := eval_divLoop u hu (by simpa [u] using hb)
    (by simpa [u,wordValue] using hb) (s 5).length (by simp [u]) (by simp [u])
  let r := divideDigits (s 5) (s 0).reverse [] []
  let v := update (update (update u 6 []) 0 r.1) 7 r.2
  have he' : Eval divLoop u v t := by simpa [v,r,u,h7] using he
  obtain ⟨w,hw,hn⟩ := eval_normalize (a := (7 : Fin 10)) (tmp := 2) (flag := 4)
    (by decide) (by decide) (by decide) v
  have h := Eval.seq hre (Eval.seq he' hn)
  obtain ⟨hr,hq⟩ := divideDigits_quotient_remainder (s 0) (s 5) hb
  have hrnorm : normalizeWord r.1 = r.1 := by
    -- Each nonempty digit loop ends in a normalized one-step remainder.
    have aux (b l a q : List Bool) (ha : normalizeWord a=a) :
        normalizeWord (divideDigits b l a q).1=(divideDigits b l a q).1 := by
      induction l generalizing a q with
      | nil => exact ha
      | cons x l ih =>
        apply ih
        cases hh : (subtractWord (x::a) b false).2 <;>
          simp [reduceWord,hh,normalizeWord_eq_bits]
    exact aux _ _ _ _ (by rfl)
  have hrbits : r.1=(wordValue (s 0)%wordValue (s 5)).bits := by
    rw [←hrnorm,normalizeWord_eq_bits]
    exact congrArg Nat.bits hr
  have h2 := hs.2.1
  have h4 := hs.2.2.2.1
  have heq : update (update (update v 7 (normalizeWord (v 7))) 2 []) 4 [] =
      update (update s 0 (wordValue (s 0)%wordValue (s 5)).bits)
        7 (wordValue (s 0)/wordValue (s 5)).bits := by
    funext k; by_cases hk0 : k=0 <;> by_cases hk7 : k=7 <;> by_cases hk2 : k=2 <;>
      by_cases hk4 : k=4 <;> by_cases hk6 : k=6 <;>
      simp_all [v,u,hrbits,normalizeWord_eq_bits,r]
  rw [heq] at h
  refine ⟨_,?_,h⟩
  obtain ⟨_,_,hlen,_⟩ := divideDigits_spec (s 5) (s 0).reverse [] [] hb (by simpa [wordValue] using hb)
  simp [v,u,h2,h4] at hw
  simp [u] at ht
  simp at hlen
  change r.2.length = (s 0).length at hlen
  rw [hlen] at hw
  nlinarith

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryFactorial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

def gcdBody : Program (Fin 10) := .seq divide (.seq (copy 5 6 9)
  (.seq (copy 0 5 9) (.seq (copy 6 0 9) (.seq (clear 6) (clear 7)))))
def gcdLoop : Program (Fin 10) := .loop 5 gcdBody

def gcdScratch (s : Store (Fin 10)) : Prop := divScratch s ∧ s 6=[] ∧ s 7=[]

lemma eval_gcdBody (s : Store (Fin 10)) (hs : gcdScratch s) (hb : 0<wordValue (s 5))
    (B : ℕ) (h0 : (s 0).length ≤ B) (h5 : (s 5).length ≤ B) :
    ∃ t ≤ 500*(B+1)^2,
      Eval gcdBody s (update (update s 0 (s 5)) 5 (wordValue (s 0)%wordValue (s 5)).bits) t := by
  obtain ⟨hd,h6,h7⟩ := hs
  obtain ⟨t,ht,he⟩ := eval_divide s hd h6 h7 hb
  let r := (wordValue (s 0)%wordValue (s 5)).bits
  let q := (wordValue (s 0)/wordValue (s 5)).bits
  let u := update (update s 0 r) 7 q
  let v := update (update u 6 (s 5)) 9 []
  let w := update (update v 5 r) 9 []
  let z := update (update w 0 (s 5)) 9 []
  have h9 := hd.2.2.2.2.2
  have hc1 : Eval (copy 5 6 9) u v (7*(s 5).length+7) := by
    simpa [v,u,h6,h9] using eval_copy (a := (5 : Fin 10)) (b := 6) (tmp := 9)
      (by decide) (by decide) (by decide) u
  have hc2 : Eval (copy 0 5 9) v w (7*r.length+2*(s 5).length+7) := by
    simpa [w,v,u] using eval_copy (a := (0 : Fin 10)) (b := 5) (tmp := 9)
      (by decide) (by decide) (by decide) v
  have hc3 : Eval (copy 6 0 9) w z (7*(s 5).length+2*r.length+7) := by
    simpa [z,w,v,u] using eval_copy (a := (6 : Fin 10)) (b := 0) (tmp := 9)
      (by decide) (by decide) (by decide) w
  have hclear6 : Eval (clear 6) z (update z 6 []) (2*(s 5).length+1) := by
    simpa [z,w,v,u] using eval_clear (6 : Fin 10) z
  have hclear7 : Eval (clear 7) (update z 6 []) (update (update z 6 []) 7 []) (2*q.length+1) := by
    simpa [z,w,v,u] using eval_clear (7 : Fin 10) (update z 6 [])
  have h := Eval.seq he (Eval.seq hc1 (Eval.seq hc2 (Eval.seq hc3 (Eval.seq hclear6 hclear7))))
  have heq : update (update z 6 []) 7 [] = update (update s 0 (s 5)) 5 r := by
    funext k; fin_cases k <;> simp [z,w,v,u,h6,h7,h9]
  rw [heq] at h
  refine ⟨_,?_,h⟩
  have hrlen : r.length ≤ (s 5).length := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.mod_lt _ hb).trans (wordValue_lt _)
  have hqlen : q.length ≤ (s 0).length := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.div_le_self _ _).trans_lt (wordValue_lt _)
  have hmul := Nat.mul_le_mul (Nat.add_le_add_right h0 1) (Nat.add_le_add_right h5 1)
  nlinarith

lemma eval_gcdLoop_ordered (f : ℕ) (s : Store (Fin 10)) (hs : gcdScratch s)
    (hcan0 : (wordValue (s 0)).bits=s 0) (hcan5 : (wordValue (s 5)).bits=s 5)
    (hab : wordValue (s 5)≤wordValue (s 0))
    (hf : wordValue (s 0)*wordValue (s 5)<2^f)
    (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ f*(500*(B+1)^2+1)+1,
      Eval gcdLoop s (update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []) t := by
  induction f generalizing s with
  | zero =>
    have hz : wordValue (s 5)=0 := by simp only [pow_zero] at hf; nlinarith
    have he5 : s 5=[] := by rw [←hcan5,hz]; rfl
    have heq : update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []=s := by
      simp [hz,hcan0,←he5]
    refine ⟨1,by simp,?_⟩
    rw [heq]
    exact Eval.whileNil he5
  | succ f ih =>
    by_cases hz : wordValue (s 5)=0
    · have he5 : s 5=[] := by rw [←hcan5,hz]; rfl
      have heq : update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []=s := by
        simp [hz,hcan0,←he5]
      refine ⟨1,by omega,?_⟩
      rw [heq]
      exact Eval.whileNil he5
    · have hb : 0<wordValue (s 5) := Nat.pos_of_ne_zero hz
      let u := update (update s 0 (s 5)) 5 (wordValue (s 0)%wordValue (s 5)).bits
      obtain ⟨t,ht,he⟩ := eval_gcdBody s hs hb B h0 h5
      have hu : gcdScratch u := by simpa [gcdScratch,divScratch,u] using hs
      have hu0 : (wordValue (u 0)).bits=u 0 := by simpa [u] using hcan5
      have hu5 : (wordValue (u 5)).bits=u 5 := by simp [u]
      have hule : wordValue (u 5)≤wordValue (u 0) := by simpa [u] using Nat.le_of_lt (Nat.mod_lt (wordValue (s 0)) hb)
      have huf : wordValue (u 0)*wordValue (u 5)<2^f := by
        have hh := gcd_product_halving hb hab
        simp only [pow_succ] at hf
        simp [u]
        linarith
      have hulen : (u 5).length≤B := by
        simp only [u,update_self]
        apply le_trans _ h5
        rw [Nat.size_eq_bits_len,Nat.size_le]
        exact (Nat.mod_lt _ hb).trans (wordValue_lt _)
      obtain ⟨v,hv,hl⟩ := ih u hu hu0 hu5 hule huf (by simpa [u] using h5) hulen
      have hnz : s 5≠[] := by intro hh; simp [hh] at hb
      have h := Eval.whileCons hnz he hl
      have hg : Nat.gcd (wordValue (s 5)) (wordValue (s 0)%wordValue (s 5)) =
          Nat.gcd (wordValue (s 0)) (wordValue (s 5)) := by
        calc _ = Nat.gcd (wordValue (s 0)%wordValue (s 5)) (wordValue (s 5)) := Nat.gcd_comm ..
             _ = Nat.gcd (wordValue (s 5)) (wordValue (s 0)) := (Nat.gcd_rec _ _).symm
             _ = _ := Nat.gcd_comm ..
      have heq : update (update u 0 (Nat.gcd (wordValue (u 0)) (wordValue (u 5))).bits) 5 [] =
          update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 [] := by
        simp [u,hg,update_idem,update_comm (show (0 : Fin 10) ≠ 5 by decide)]
      rw [heq] at h
      exact ⟨1+t+v,by linarith,h⟩


/-- No value-sized fuel: the compiler executes an ordinary while loop, and
Euclid's product-halving supplies a bound linear in the input bit lengths. -/
lemma eval_gcdLoop (s : Store (Fin 10)) (hs : gcdScratch s)
    (hcan0 : (wordValue (s 0)).bits=s 0) (hcan5 : (wordValue (s 5)).bits=s 5)
    (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ (2*B+1)*(500*(B+1)^2+1)+1,
      Eval gcdLoop s (update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []) t := by
  by_cases hz : wordValue (s 5)=0
  · have he5 : s 5=[] := by rw [←hcan5,hz]; rfl
    have heq : update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []=s := by
      simp [hz,hcan0,←he5]
    refine ⟨1,by omega,?_⟩
    rw [heq]
    exact Eval.whileNil he5
  · have hb : 0<wordValue (s 5) := Nat.pos_of_ne_zero hz
    let u := update (update s 0 (s 5)) 5 (wordValue (s 0)%wordValue (s 5)).bits
    obtain ⟨t,ht,he⟩ := eval_gcdBody s hs hb B h0 h5
    have hu : gcdScratch u := by simpa [gcdScratch,divScratch,u] using hs
    have hu0 : (wordValue (u 0)).bits=u 0 := by simpa [u] using hcan5
    have hu5 : (wordValue (u 5)).bits=u 5 := by simp [u]
    have hule : wordValue (u 5)≤wordValue (u 0) := by simpa [u] using Nat.le_of_lt (Nat.mod_lt (wordValue (s 0)) hb)
    have hu0len : (u 0).length≤B := by simpa [u] using h5
    have hu5len : (u 5).length≤B := by
      simp only [u,update_self]
      apply le_trans _ h5
      rw [Nat.size_eq_bits_len,Nat.size_le]
      exact (Nat.mod_lt _ hb).trans (wordValue_lt _)
    have hf : wordValue (u 0)*wordValue (u 5)<2^(2*B) := by
      have hlt0 := (wordValue_lt (u 0)).trans_le (Nat.pow_le_pow_right (by decide) hu0len)
      have hlt5 := (wordValue_lt (u 5)).trans_le (Nat.pow_le_pow_right (by decide) hu5len)
      rw [two_mul,pow_add]
      exact mul_lt_mul'' hlt0 hlt5 (Nat.zero_le _) (Nat.zero_le _)
    obtain ⟨v,hv,hl⟩ := eval_gcdLoop_ordered (2*B) u hu hu0 hu5 hule hf B hu0len hu5len
    have hnz : s 5≠[] := by intro hh; simp [hh] at hb
    have h := Eval.whileCons hnz he hl
    have hg : Nat.gcd (wordValue (s 5)) (wordValue (s 0)%wordValue (s 5)) =
        Nat.gcd (wordValue (s 0)) (wordValue (s 5)) := by
      calc _ = Nat.gcd (wordValue (s 0)%wordValue (s 5)) (wordValue (s 5)) := Nat.gcd_comm ..
           _ = Nat.gcd (wordValue (s 5)) (wordValue (s 0)) := (Nat.gcd_rec _ _).symm
           _ = _ := Nat.gcd_comm ..
    have heq : update (update u 0 (Nat.gcd (wordValue (u 0)) (wordValue (u 5))).bits) 5 [] =
        update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 [] := by
      simp [u,hg,update_idem,update_comm (show (0 : Fin 10) ≠ 5 by decide)]
    rw [heq] at h
    exact ⟨1+t+v,by linarith,h⟩

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

lemma eval_quotient (s : Store (Fin 10)) (hs : gcdScratch s)
    (hb : 0<wordValue (s 5)) (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ 400*(B+1)^2,
      Eval quotient s (update s 0 (wordValue (s 0)/wordValue (s 5)).bits) t := by
  obtain ⟨hd,h6,h7⟩ := hs
  obtain ⟨t,ht,he⟩ := eval_divide s hd h6 h7 hb
  let q := (wordValue (s 0)/wordValue (s 5)).bits
  let r := (wordValue (s 0)%wordValue (s 5)).bits
  let u := update (update s 0 r) 7 q
  let v := update (update u 0 q) 9 []
  have h9 := hd.2.2.2.2.2
  have hc : Eval (copy 7 0 9) u v (7*q.length+2*r.length+7) := by
    simpa [q,r,u,v,h9] using eval_copy (a := (7 : Fin 10)) (b := 0) (tmp := 9)
      (by decide) (by decide) (by decide) u
  have hz : Eval (clear 7) v (update s 0 q) (2*q.length+1) := by
    have hh := eval_clear (7 : Fin 10) v
    have heq : update v 7 []=update s 0 q := by
      funext k; fin_cases k <;> simp [v,u,h7,h9]
    rw [heq] at hh
    simpa [v,u] using hh
  have hbq : q.length≤B := by
    apply le_trans _ h0
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.div_le_self _ _).trans_lt (wordValue_lt _)
  have hbr : r.length≤B := by
    apply le_trans _ h5
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.mod_lt _ hb).trans (wordValue_lt _)
  refine ⟨_,?_,Eval.seq he (Eval.seq hc hz)⟩
  have hp := Nat.mul_le_mul h0 h5
  nlinarith

def fractionScratch (s : Store (Fin 12)) : Prop :=
  ∀ k : Fin 10, k≠0 → k≠5 → s (fractionArith k)=[]

lemma fractionScratch_gcd (s : Store (Fin 12)) (hs : fractionScratch s) :
    gcdScratch (fun k => s (fractionArith k)) := by
  unfold gcdScratch divScratch
  exact ⟨⟨hs 1 (by decide) (by decide),hs 2 (by decide) (by decide),
    hs 3 (by decide) (by decide),hs 4 (by decide) (by decide),
    hs 8 (by decide) (by decide),hs 9 (by decide) (by decide)⟩,
    hs 6 (by decide) (by decide),hs 7 (by decide) (by decide)⟩

lemma eval_fractionGcd (s : Store (Fin 12)) (hs : fractionScratch s)
    (hcan0 : (wordValue (s 0)).bits=s 0) (hcan5 : (wordValue (s 5)).bits=s 5)
    (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ (2*B+1)*(500*(B+1)^2+1)+1,
      Eval (gcdLoop.rename fractionArith) s
        (update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []) t := by
  obtain ⟨t,ht,he⟩ := eval_gcdLoop (fun k => s (fractionArith k))
    (fractionScratch_gcd s hs) hcan0 hcan5 B h0 h5
  have hh := eval_rename_from fractionArith fractionArith.injective s he
  simp only [extend_update_store fractionArith fractionArith.injective,
    extend_pull_store fractionArith fractionArith.injective] at hh
  exact ⟨t,ht,hh⟩

lemma eval_fractionQuotient (s : Store (Fin 12)) (hs : fractionScratch s)
    (hb : 0<wordValue (s 5)) (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ 400*(B+1)^2,
      Eval (quotient.rename fractionArith) s
        (update s 0 (wordValue (s 0)/wordValue (s 5)).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_quotient (fun k => s (fractionArith k))
    (fractionScratch_gcd s hs) hb B h0 h5
  have hh := eval_rename_from fractionArith fractionArith.injective s he
  simp only [extend_update_store fractionArith fractionArith.injective,
    extend_pull_store fractionArith fractionArith.injective] at hh
  exact ⟨t,ht,hh⟩

lemma fractionScratch_update (s : Store (Fin 12)) (hs : fractionScratch s)
    (i : Fin 12) (hi : i = 0 ∨ i = 5 ∨ 10 ≤ i.val) (w : List Bool) :
    fractionScratch (update s i w) := by
  intro k h0 h5
  have hki : fractionArith k≠i := by
    rcases hi with rfl|rfl|hi
    · intro h; have hh := congrArg Fin.val h; apply h0; apply Fin.ext; exact hh
    · intro h; have hh := congrArg Fin.val h; apply h5; apply Fin.ext; exact hh
    · intro h; have hh := congrArg Fin.val h; simp only [fractionArith_val] at hh; omega
  simp [hki,hs k h0 h5]

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryBinomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

lemma eval_multiplyClean (s : Store (Fin 8)) (hf : ∀ k : Fin 8, 2≤k.val → s k=[])
    (B : ℕ) (ha : (s 0).length≤B) (hb : (s 1).length≤B) :
    ∃ t≤200*(B+1)^4, Eval multiplyClean s
      (update (update s 0 (wordValue (s 0)*wordValue (s 1)).bits) 1 []) t := by
  obtain ⟨t,ht,hm⟩ := eval_multiply s (hf 2 (by decide)) (fun k hk => hf k (by omega))
  let A := wordValue (s 0)
  let D := wordValue (s 1)
  let u := update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 []) 2 (A*D).bits
  let v := update u 0 []
  let z := update v 0 (A*D).bits
  have h1 : Eval (clear 0) u v (2*((s 1).length+(s 0).length)+1) := by
    simpa [u,v] using eval_clear (0 : Fin 8) u
  have h2 : Eval (copy 2 0 7) v z (7*(A*D).bits.length+7) := by
    have hh := eval_copy (a:=(2 : Fin 8)) (b:=0) (tmp:=7) (by decide) (by decide) (by decide) v
    have he : update (update v 0 (v 2)) 7 []=z := by
      funext k; fin_cases k <;> simp [u,v,z,hf 7 (by decide)]
    rw [he] at hh
    simpa [u,v,hf 7 (by decide)] using hh
  have h3 := eval_clear (2 : Fin 8) z
  have he : update z 2 []=update (update s 0 (A*D).bits) 1 [] := by
    funext k; fin_cases k <;> simp [z,v,u,hf 2 (by decide)]
  rw [he] at h3
  have hm' : Eval multiply s u t := hm
  have h := Eval.seq hm' (Eval.seq h1 (Eval.seq h2 h3))
  refine ⟨_,?_,h⟩
  have hp : (A*D).bits.length≤2*B := (product_bits_length (s 0) (s 1)).trans (by omega)
  simp [z,v,u] at *
  have h₀ : (s 0).length+(s 1).length≤2*B := by omega
  have h₁ : (s 1).length*((s 0).length+(s 1).length)≤2*B^2 := by nlinarith
  have h₂ : ((s 0).length+(s 1).length)*(7*((s 1).length*((s 0).length+(s 1).length))+34)≤
      2*B*(14*B^2+34) := Nat.mul_le_mul h₀ (by omega)
  have h₃ := Nat.mul_le_mul hb (Nat.add_le_add_right h₂ 23)
  linarith only [ht,hp,h₀,h₁,h₃,Nat.zero_le (B^2),Nat.zero_le (B^3)]

lemma eval_factorMul (s : Store (Fin 10)) (hf : ∀ k : Fin 10, 2≤k.val → k.val<8 → s k=[])
    (B : ℕ) (ha : (s 0).length≤B) (hb : (s 1).length≤B) :
    ∃ t≤200*(B+1)^4, Eval (multiplyClean.rename factorMul) s
      (update (update s 0 (wordValue (s 0)*wordValue (s 1)).bits) 1 []) t := by
  obtain ⟨t,ht,he⟩ := eval_multiplyClean (fun k => s (factorMul k))
    (fun k hk => hf (factorMul k) hk (by exact k.isLt)) B ha hb
  have hh := eval_rename_from factorMul factorMul.injective s he
  have hx : extend factorMul (update (update (fun k => s (factorMul k)) 0
      (wordValue (s 0)*wordValue (s 1)).bits) 1 []) s =
      update (update s 0 (wordValue (s 0)*wordValue (s 1)).bits) 1 [] := by
    simp only [extend_update_store _ factorMul.injective,extend_pull_store _ factorMul.injective]
    rfl
  change Eval (multiplyClean.rename factorMul) s
    (extend factorMul (update (update (fun k => s (factorMul k)) 0
      (wordValue (s 0)*wordValue (s 1)).bits) 1 []) s) t at hh
  rw [hx] at hh
  exact ⟨t,ht,hh⟩

lemma eval_factorialBody (s : Store (Fin 10)) (hf : factorialScratch s)
    (B : ℕ) (h0 : (s 0).length≤B) (h8 : (s 8).length≤B) :
    ∃ t≤300*(B+1)^4, Eval factorialBody s
      (update (update (update s 0 (wordValue (s 0)*wordValue (s 8)).bits)
        8 (incrementWord (s 8))) 9 (s 9).tail) t := by
  let u := update s 1 (s 8)
  let v := update s 0 (wordValue (s 0)*wordValue (s 8)).bits
  let z := update v 8 (incrementWord (s 8))
  have h1 : Eval (copy 8 1 7) s u (7*(s 8).length+7) := by
    have hh := eval_copy (a:=(8 : Fin 10)) (b:=1) (tmp:=7) (by decide) (by decide) (by decide) s
    have he : update (update s 1 (s 8)) 7 []=u := by
      funext k; fin_cases k <;> simp [u,hf 7 (by decide) (by decide)]
    rw [he] at hh
    simpa [hf 1 (by decide) (by decide),hf 7 (by decide) (by decide)] using hh
  obtain ⟨t,ht,hh⟩ := eval_factorMul u (by
    intro k hk hk'; have h := hf k (by omega) hk'; simp [u,show k≠1 by omega,h])
    B (by simpa [u] using h0) (by simpa [u] using h8)
  have he : update (update u 0 (wordValue (u 0)*wordValue (u 1)).bits) 1 []=v := by
    funext k; fin_cases k <;> simp [v,u,hf 1 (by decide) (by decide)]
  rw [he] at hh
  obtain ⟨t',ht',hi⟩ := eval_increment (a:=(8 : Fin 10)) (tmp:=5) (flag:=6)
    (by decide) (by decide) (by decide) v
  have he' : update (update (update v 8 (incrementWord (v 8))) 5 []) 6 []=z := by
    funext k; fin_cases k <;> simp [z,v,hf 5 (by decide) (by decide),hf 6 (by decide) (by decide)]
  rw [he'] at hi
  have hd : Eval (Program.drop 9) z (update z 9 (s 9).tail) 1 := by
    simpa [z,v] using Eval.drop (9 : Fin 10) z
  have hs := Eval.seq h1 (Eval.seq hh (Eval.seq hi hd))
  refine ⟨_,?_,hs⟩
  simp [v,hf 5 (by decide) (by decide),hf 6 (by decide) (by decide)] at ht'
  nlinarith only [ht,ht',h8,Nat.zero_le (B^2),Nat.zero_le (B^3)]

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

@[simp] lemma factorial_wordValue_bits (n : ℕ) : wordValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    cases b <;> simp [wordValue,ih,Nat.bit] ; omega

/-- Rising products, with a unary iteration budget obtained from the input.
No scalar factorial operation occurs in this fixed finite program. -/
lemma eval_factorialLoop (n L : ℕ) (s : Store (Fin 10))
    (hf : factorialScratch s) (hcan : (wordValue (s 0)).bits=s 0)
    (hn : (s 9).length=n)
    (hp : (s 0).length+n*((s 8).length+n)≤L)
    (hi : (s 8).length+n≤L) :
    ∃ t≤n*(300*(L+1)^4+1)+1, ∃ v,
      Eval factorialLoop s v t ∧
      v 0 = (wordValue (s 0)*(wordValue (s 8)).ascFactorial n).bits ∧
      wordValue (v 8)=wordValue (s 8)+n ∧ v 9=[] ∧ factorialScratch v ∧
      (v 8).length≤(s 8).length+n := by
  induction n generalizing s with
  | zero =>
    have hz : s 9=[] := List.length_eq_zero_iff.mp hn
    exact ⟨1,by simp,s,Eval.whileNil hz,by simpa using hcan.symm,by simp,hz,hf,by simp⟩
  | succ n ih =>
    let u := update (update (update s 0 (wordValue (s 0)*wordValue (s 8)).bits)
      8 (incrementWord (s 8))) 9 (s 9).tail
    obtain ⟨t,ht,he⟩ := eval_factorialBody s hf L (by omega) (by omega)
    have hu : factorialScratch u := by
      intro k hk hk'; simpa [u,show k≠0 by omega,show k≠8 by omega,show k≠9 by omega]
        using hf k hk hk'
    have hc : (wordValue (u 0)).bits=u 0 := by simp [u]
    have hcnt : (u 9).length=n := by simp [u,List.length_tail,hn]
    have hlen0 : (u 0).length≤(s 0).length+(s 8).length := by
      simpa [u] using product_bits_length (s 0) (s 8)
    have hlen8 : (u 8).length≤(s 8).length+1 := by
      simpa [u] using incrementWord_length (s 8)
    have hpot : (u 0).length+n*((u 8).length+n)≤L := by nlinarith
    have hidx : (u 8).length+n≤L := by omega
    obtain ⟨w,hw,v,hv,hv0,hv8,hv9,hvf,hvl⟩ := ih u hu hc hcnt hpot hidx
    have hstep : Eval factorialBody s u t := he
    have hne : s 9≠[] := by intro h; simp [h] at hn
    refine ⟨1+t+w,by linarith,v,Eval.whileCons hne hstep hv,?_,?_,hv9,hvf,?_⟩
    · have hasc := Nat.ascFactorial_mul_ascFactorial (wordValue (s 8)) 1 n
      have hid : wordValue (s 8)*(wordValue (s 8)+1).ascFactorial n =
          (wordValue (s 8)).ascFactorial (n+1) := by
        simpa [Nat.ascFactorial_succ,Nat.add_comm] using hasc
      simpa [u,Nat.mul_assoc,hid] using hv0
    · simpa [u,Nat.add_assoc,Nat.add_comm] using hv8
    · omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

lemma factorial_bits_length (n : ℕ) : n.factorial.bits.length≤1+n*(n+1) := by
  have hbits (k : ℕ) : k.bits.length≤k := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    induction k with
    | zero => decide
    | succ k ih => simp only [pow_succ]; linarith
  induction n with
  | zero => decide
  | succ n ih =>
    have hm := product_bits_length (n+1).bits n.factorial.bits
    simp only [factorial_wordValue_bits,←Nat.factorial_succ] at hm
    have hn := hbits (n+1)
    linarith

lemma eval_factorialCore (s : Store (Fin 10))
    (hs : ∀ k : Fin 10, k.val<9 → s k=[]) :
    ∃ t≤(s 9).length*(300*(1+(s 9).length*(1+(s 9).length)+1)^4+1)+2*(s 9).length+10,
    Eval factorialCore s (update (update s 0 (s 9).length.factorial.bits) 9 []) t := by
  let u := update s 0 [true]
  let v := update u 8 [true]
  have h1 : Eval (Program.push 0 true) s u 1 := by simpa [u,hs 0 (by decide)] using Eval.push (0 : Fin 10) true s
  have h2 : Eval (Program.push 8 true) u v 1 := by simpa [v,u,hs 8 (by decide)] using Eval.push (8 : Fin 10) true u
  have hf : factorialScratch v := by
    intro k hk hk'; simp [v,u,show k≠0 by omega,show k≠8 by omega,hs k (by omega)]
  obtain ⟨t,ht,z,hz,hz0,hz8,hz9,hzf,hzl⟩ := eval_factorialLoop (s 9).length
    (1+(s 9).length*(1+(s 9).length)) v hf (by simp [v,u,wordValue])
    (by simp [v,u]) (by simp [v,u]) (by simp [v,u];nlinarith)
  have hz0' : z 0=(s 9).length.factorial.bits := by
    simpa [v,u,wordValue,Nat.one_ascFactorial] using hz0
  have h3 := eval_clear (8 : Fin 10) z
  have heq : update z 8 []=update (update s 0 (s 9).length.factorial.bits) 9 [] := by
    funext k; fin_cases k <;> simp [hz0',hz9,hzf 1 (by decide) (by decide),hzf 2 (by decide) (by decide),
      hzf 3 (by decide) (by decide),hzf 4 (by decide) (by decide),hzf 5 (by decide) (by decide),
      hzf 6 (by decide) (by decide),hzf 7 (by decide) (by decide),hs 1 (by decide),hs 2 (by decide),
      hs 3 (by decide),hs 4 (by decide),hs 5 (by decide),hs 6 (by decide),hs 7 (by decide),hs 8 (by decide)]
  rw [heq] at h3
  have hh := Eval.seq h1 (Eval.seq h2 (Eval.seq hz h3))
  refine ⟨_,?_,hh⟩
  simp [v,u] at ht hzl
  omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

/-- Variable-length subtraction of unary loop counters. The leftover flag is
nonempty exactly when the second counter exceeded the first. -/
theorem eval_unaryDiff {a b flag : K} (hab : a≠b) (haf : a≠flag) (hbf : b≠flag)
    (s : Store K) :
    Eval (unaryDiff a b flag) s
      (update (update (update s a ((s a).drop (s b).length)) b [])
        flag (List.replicate ((s b).length-(s a).length) true++s flag))
      (5*(s b).length+1) := by
  generalize he : s b=w
  induction w generalizing s with
  | nil =>
    have heq : update (update (update s a (s a)) b []) flag (s flag)=s := by
      simp [←he]
    simp only [List.length_nil,List.drop_zero,Nat.zero_sub,List.replicate_zero,List.nil_append,
      Nat.mul_zero,Nat.zero_add,heq]
    exact Eval.whileNil he
  | cons x w ih =>
    cases ha : s a with
    | nil =>
      let u := update (update s b w) flag (true::s flag)
      have h1 : Eval (Program.drop b) s (update s b w) 1 := by
        simpa [he] using Eval.drop b s
      have h2 : Eval (Program.push flag true) (update s b w) u 1 := by
        simpa [u,Ne.symm hbf] using Eval.push flag true (update s b w)
      have hb : Eval (unaryDiffBody a b flag) s u 4 := Eval.branchNone ha (Eval.seq h1 h2)
      have hu : u b=w := by simp [u,hbf]
      have hl := ih u hu
      have hh := Eval.whileCons (by simp [he]) hb hl
      have heq : update (update (update u a ((u a).drop w.length)) b [])
          flag (List.replicate (w.length-(u a).length) true++u flag) =
          update (update (update s a ((s a).drop (x::w).length)) b [])
          flag (List.replicate ((x::w).length-(s a).length) true++s flag) := by
        funext k; by_cases hk : k=a <;> by_cases hk' : k=b <;> by_cases hk'' : k=flag <;>
          simp_all [u,List.replicate_add,List.append_assoc]
      rw [heq] at hh
      convert hh using 1 <;> simp [unaryDiff,ha] ; ring
    | cons y v =>
      let u := update (update s a v) b w
      have h1 : Eval (Program.drop a) s (update s a v) 1 := by simpa [ha] using Eval.drop a s
      have h2 : Eval (Program.drop b) (update s a v) u 1 := by
        simpa [u,Ne.symm hab,he] using Eval.drop b (update s a v)
      have hb : Eval (unaryDiffBody a b flag) s u 4 := by
        cases y
        · exact Eval.branchFalse ha (Eval.seq h1 h2)
        · exact Eval.branchTrue ha (Eval.seq h1 h2)
      have hu : u b=w := by simp [u]
      have hl := ih u hu
      have hh := Eval.whileCons (by simp [he]) hb hl
      have heq : update (update (update u a ((u a).drop w.length)) b [])
          flag (List.replicate (w.length-(u a).length) true++u flag) =
          update (update (update s a ((s a).drop (x::w).length)) b [])
          flag (List.replicate ((x::w).length-(s a).length) true++s flag) := by
        funext k; by_cases hk : k=a <;> by_cases hk' : k=b <;> by_cases hk'' : k=flag <;>
          simp_all [u]
      rw [heq] at hh
      convert hh using 1 <;> simp [unaryDiff,ha] ; ring

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage.Binomial
open Function

lemma eval_factorBlock (a b : Fin 18) (ha : 10≤a.val) (hb : 10≤b.val)
    (ha17 : a≠17) (hb17 : b≠17) (s : Store (Fin 18)) (hs : lowEmpty s) (h17 : s 17=[]) :
    ∃ t≤factorCost (s a).length (s b).length,
      Eval (factorBlock a b) s (update s b (s a).length.factorial.bits) t := by
  have ha9 : a≠9 := by omega
  have hb0 : b≠0 := by omega
  let n := (s a).length
  let f := n.factorial.bits
  let u := update s 9 (s a)
  let v := update s 0 f
  let w := update v b f
  have e1 : Eval (copy a 9 17) s u (7*n+7) := by
    have hh := eval_copy (a:=a) (b:=9) (tmp:=17) ha9 ha17 (by decide) s
    have hx : update (update s 9 (s a)) 17 []=u := by
      funext k; by_cases h9 : k=9 <;> by_cases h17k : k=17 <;> simp_all [u]
    rw [hx] at hh
    simpa [n,hs 9 (by decide),h17] using hh
  obtain ⟨t,ht,he⟩ := eval_factorialCore (fun k => u (arith k)) (by
    intro k hk
    have ha9 : arith k≠9 := by intro hh; have hv:=congrArg (fun k : Fin 18 => k.val) hh; change k.val=9 at hv; omega
    simpa [u,ha9] using hs (arith k) (by change k.val<10;omega))
  have he' := eval_rename_from arith arith.injective u he
  have hx : extend arith (update (update (fun k => u (arith k)) 0
      (u (arith 9)).length.factorial.bits) 9 []) u = v := by
    simp only [extend_update_store _ arith.injective,extend_pull_store _ arith.injective]
    change update (update u 0 (u 9).length.factorial.bits) 9 []=v
    funext k; by_cases h0 : k=0 <;> by_cases h9 : k=9 <;> simp_all [u,v,f,n,hs 9 (by decide)]
  rw [hx] at he'
  have e2 : Eval (factorialCore.rename arith) u v t := he'
  have e3 : Eval (copy 0 b 17) v w (7*f.length+2*(s b).length+7) := by
    have hh := eval_copy (a:=(0 : Fin 18)) (b:=b) (tmp:=17) (Ne.symm hb0) (by decide) hb17 v
    have hx : update (update v b (v 0)) 17 []=w := by
      funext k; by_cases h0 : k=0 <;> by_cases hbk : k=b <;>
        by_cases h17k : k=17 <;> simp_all [v,w]
    rw [hx] at hh
    simpa [v,h17,hb0] using hh
  have e4 := eval_clear (0 : Fin 18) w
  have hx' : update w 0 []=update s b f := by
    funext k; by_cases h0 : k=0 <;> by_cases hbk : k=b <;> simp_all [w,v,hs 0 (by decide)]
  rw [hx'] at e4
  have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
  refine ⟨_,?_,hh⟩
  change t≤factorialCost n at ht
  have hfl : f.length ≤ 1+n*(n+1) := factorial_bits_length n
  simp only [w,update_of_ne (Ne.symm hb0),v,update_self]
  change _≤factorCost n (s b).length
  unfold factorCost
  omega

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

def input (n k : ℕ) : Store (Fin 18) :=
  update (update (fun _ => []) 14 (List.replicate n true)) 15 (List.replicate k true)
def prepared (n k : ℕ) : Store (Fin 18) :=
  update (update (input n k) 12 (List.replicate (n-k) true)) 13 (List.replicate (k-n) true)

lemma eval_prepare (n k : ℕ) : Eval prepare (input n k) (prepared n k) (7*n+12*k+17) := by
  let s := input n k
  let u := update s 12 (List.replicate n true)
  let v := update u 16 (List.replicate k true)
  have h1 := eval_copy (a:=(14 : Fin 18)) (b:=12) (tmp:=17) (by decide) (by decide) (by decide) s
  have he1 : update (update s 12 (s 14)) 17 []=u := by
    funext j; fin_cases j <;> simp [s,u,input]
  rw [he1] at h1
  have e1 : Eval (copy 14 12 17) s u (7*n+7) := by simpa [s,input] using h1
  have h2 := eval_copy (a:=(15 : Fin 18)) (b:=16) (tmp:=17) (by decide) (by decide) (by decide) u
  have he2 : update (update u 16 (u 15)) 17 []=v := by
    funext j; fin_cases j <;> simp [v,u,s,input]
  rw [he2] at h2
  have e2 : Eval (copy 15 16 17) u v (7*k+7) := by simpa [u,s,input] using h2
  have h3 := eval_unaryDiff (a:=(12 : Fin 18)) (b:=16) (flag:=13) (by decide) (by decide) (by decide) v
  have he3 : update (update (update v 12 ((v 12).drop (v 16).length)) 16 []) 13
      (List.replicate ((v 16).length-(v 12).length) true++v 13)=prepared n k := by
    funext j; fin_cases j <;> simp [prepared,v,u,s,input]
  rw [he3] at h3
  have e3 : Eval (unaryDiff 12 16 13) v (prepared n k) (5*k+1) := by simpa [v,u,s,input] using h3
  convert Eval.seq e1 (Eval.seq e2 e3) using 1 <;> first |rfl |omega

lemma lowEmpty_input (n k : ℕ) : lowEmpty (input n k) := by
  intro j hj
  simp [input,show j≠14 by omega,show j≠15 by omega]
lemma lowEmpty_update (s : Store (Fin 18)) (hs : lowEmpty s) (j : Fin 18) (hj : 10≤j.val) (w : List Bool) :
    lowEmpty (update s j w) := by
  intro i hi
  simpa [show i≠j by intro he;subst j;omega] using hs i hi
lemma lowEmpty_prepared (n k : ℕ) : lowEmpty (prepared n k) :=
  lowEmpty_update _ (lowEmpty_update _ (lowEmpty_input n k) 12 (by decide) _) 13 (by decide) _

end RationalHitting.StackLanguage.Binomial

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage.Binomial
open Function

def factored (n k : ℕ) : Store (Fin 18) :=
  update (update (update (prepared n k) 10 n.factorial.bits) 11 k.factorial.bits) 16 (n-k).factorial.bits

lemma eval_allFactors (n k : ℕ) :
    ∃ t≤factorCost n 0+factorCost k 0+factorCost (n-k) 0+2,
      Eval allFactors (prepared n k) (factored n k) t := by
  let u := update (prepared n k) 10 n.factorial.bits
  let v := update u 11 k.factorial.bits
  obtain ⟨t1,ht1,h1⟩ := eval_factorBlock 14 10 (by decide) (by decide) (by decide) (by decide)
    (prepared n k) (lowEmpty_prepared n k) (by simp [prepared,input])
  have e1 : Eval (factorBlock 14 10) (prepared n k) u t1 := by simpa [u,prepared,input] using h1
  have hu : lowEmpty u := lowEmpty_update _ (lowEmpty_prepared n k) 10 (by decide) _
  obtain ⟨t2,ht2,h2⟩ := eval_factorBlock 15 11 (by decide) (by decide) (by decide) (by decide)
    u hu (by simp [u,prepared,input])
  have e2 : Eval (factorBlock 15 11) u v t2 := by simpa [v,u,prepared,input] using h2
  have hv : lowEmpty v := lowEmpty_update _ hu 11 (by decide) _
  obtain ⟨t3,ht3,h3⟩ := eval_factorBlock 12 16 (by decide) (by decide) (by decide) (by decide)
    v hv (by simp [v,u,prepared,input])
  have e3 : Eval (factorBlock 12 16) v (factored n k) t3 := by simpa [factored,v,u,prepared,input] using h3
  refine ⟨_,?_,Eval.seq e1 (Eval.seq e2 e3)⟩
  simp [v,u,prepared,input] at ht1 ht2 ht3
  omega

lemma eval_cleanMul (s : Store (Fin 18))
    (hs : ∀ j : Fin 18, 2≤j.val → j.val<8 → s j=[])
    (B : ℕ) (h0 : (s 0).length≤B) (h1 : (s 1).length≤B) :
    ∃ t≤200*(B+1)^4, Eval cleanMul s
      (update (update s 0 (wordValue (s 0)*wordValue (s 1)).bits) 1 []) t := by
  obtain ⟨t,ht,he⟩ := eval_factorMul (fun j => s (arith j))
    (fun j hj hj' => hs (arith j) hj hj') B h0 h1
  have hh := eval_rename_from arith arith.injective s he
  simp only [extend_update_store _ arith.injective,extend_pull_store _ arith.injective] at hh
  exact ⟨t,ht,hh⟩

lemma eval_cleanQuotient (s : Store (Fin 18))
    (hs : gcdScratch (fun j => s (arith j))) (hd : 0<wordValue (s 5))
    (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t≤400*(B+1)^2, Eval (quotient.rename arith) s
      (update s 0 (wordValue (s 0)/wordValue (s 5)).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_quotient (fun j => s (arith j)) hs hd B h0 h5
  have hh := eval_rename_from arith arith.injective s he
  simp only [extend_update_store _ arith.injective,extend_pull_store _ arith.injective] at hh
  exact ⟨t,ht,hh⟩

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

lemma eval_copy_clean {a b : Fin 18} (hab : a≠b) (ha : a≠17) (hb : b≠17)
    (s : Store (Fin 18)) (h17 : s 17=[]) :
    Eval (copy a b 17) s (update s b (s a)) (7*(s a).length+2*(s b).length+7) := by
  have hh := eval_copy hab ha hb s
  have heq : update (update s b (s a)) 17 []=update s b (s a) := by
    funext j; by_cases hj : j=b <;> by_cases hj17 : j=17 <;> simp_all
  rw [heq] at hh
  simpa [h17] using hh

lemma eval_ratio (n k : ℕ) (hk : k≤n) :
    ∃ t≤ratioCost n k, Eval ratio (factored n k)
      (update (input n k) 0 (n.choose k).bits) t := by
  let a := n.factorial
  let b := k.factorial
  let c := (n-k).factorial
  let s := factored n k
  let u1 := update s 0 b.bits
  let u2 := update u1 1 c.bits
  let u3 := update (update u2 0 (b*c).bits) 1 []
  let u4 := update u3 5 (b*c).bits
  let u5 := update u4 0 a.bits
  let u6 := update u5 0 (a/(b*c)).bits
  let u7 := update u6 5 []
  let u8 := update u7 10 []
  let u9 := update u8 11 []
  let u10 := update u9 12 []
  have ha : a.bits.length≤1+n*(n+1) := factorial_bits_length n
  have hb : b.bits.length≤1+k*(k+1) := factorial_bits_length k
  have hc : c.bits.length≤1+(n-k)*((n-k)+1) := factorial_bits_length (n-k)
  have hp : (b*c).bits.length≤b.bits.length+c.bits.length := by
    simpa using product_bits_length b.bits c.bits
  have hal : a.bits.length≤width n k := by unfold width;omega
  have hbl : b.bits.length≤width n k := by unfold width;omega
  have hcl : c.bits.length≤width n k := by unfold width;omega
  have hpl : (b*c).bits.length≤width n k := by unfold width;omega
  have e1 : Eval (copy 11 0 17) s u1 (7*b.bits.length+7) := by
    simpa [u1,s,factored,prepared,input,b] using
      eval_copy_clean (a:=(11 : Fin 18)) (b:=0) (by decide) (by decide) (by decide) s (by simp [s,factored,prepared,input])
  have e2 : Eval (copy 16 1 17) u1 u2 (7*c.bits.length+7) := by
    simpa [u2,u1,s,factored,prepared,input,c] using
      eval_copy_clean (a:=(16 : Fin 18)) (b:=1) (by decide) (by decide) (by decide) u1 (by simp [u1,s,factored,prepared,input])
  have hf : ∀ j : Fin 18, 2≤j.val → j.val<8 → u2 j=[] := by
    intro j hj hj'
    simp [u2,u1,s,factored,prepared,input,show j≠0 by omega,show j≠1 by omega,
      show j≠10 by omega,show j≠11 by omega,show j≠12 by omega,show j≠13 by omega,
      show j≠14 by omega,show j≠15 by omega,show j≠16 by omega]
  obtain ⟨t3,ht3,h3⟩ := eval_cleanMul u2 hf (width n k)
    (by simpa [u2,u1] using hbl) (by simpa [u2] using hcl)
  have e3 : Eval cleanMul u2 u3 t3 := by simpa [u3,u2,u1] using h3
  have e4 : Eval (copy 0 5 17) u3 u4 (7*(b*c).bits.length+7) := by
    simpa [u4,u3,u2,u1,s,factored,prepared,input] using
      eval_copy_clean (a:=(0 : Fin 18)) (b:=5) (by decide) (by decide) (by decide) u3 (by simp [u3,u2,u1,s,factored,prepared,input])
  have e5 : Eval (copy 10 0 17) u4 u5 (7*a.bits.length+2*(b*c).bits.length+7) := by
    simpa [u5,u4,u3,u2,u1,s,factored,prepared,input,a] using
      eval_copy_clean (a:=(10 : Fin 18)) (b:=0) (by decide) (by decide) (by decide) u4 (by simp [u4,u3,u2,u1,s,factored,prepared,input])
  have hg : gcdScratch (fun j => u5 (arith j)) := by
    change (u5 1=[] ∧ u5 2=[] ∧ u5 3=[] ∧ u5 4=[] ∧ u5 8=[] ∧ u5 9=[]) ∧ u5 6=[] ∧ u5 7=[]
    simp [u5,u4,u3,u2,u1,s,factored,prepared,input]
  obtain ⟨t6,ht6,h6⟩ := eval_cleanQuotient u5 hg (by simp [u5,u4,b,c,Nat.factorial_pos])
    (width n k) (by simpa [u5] using hal) (by simpa [u5,u4] using hpl)
  have e6 : Eval (quotient.rename arith) u5 u6 t6 := by simpa [u6,u5,u4] using h6
  have e7 : Eval (clear 5) u6 u7 (2*(b*c).bits.length+1) := by simpa [u7,u6,u5,u4] using eval_clear (5 : Fin 18) u6
  have e8 : Eval (clear 10) u7 u8 (2*a.bits.length+1) := by simpa [u8,u7,u6,u5,u4,u3,u2,u1,s,factored,a] using eval_clear (10 : Fin 18) u7
  have e9 : Eval (clear 11) u8 u9 (2*b.bits.length+1) := by simpa [u9,u8,u7,u6,u5,u4,u3,u2,u1,s,factored,b] using eval_clear (11 : Fin 18) u8
  have e10 : Eval (clear 12) u9 u10 (2*(n-k)+1) := by simpa [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,s,factored,prepared] using eval_clear (12 : Fin 18) u9
  have e11 := eval_clear (16 : Fin 18) u10
  have heq : update u10 16 []=update (input n k) 0 (n.choose k).bits := by
    funext j; fin_cases j <;>
      simp [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,s,factored,prepared,input,a,b,c,
        Nat.choose_eq_factorial_div_factorial hk,Nat.sub_eq_zero_of_le hk]
  rw [heq] at e11
  have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 e11)))))))))
  refine ⟨_,?_,hh⟩
  have hlen : u10 16=c.bits := by simp [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,s,factored,c]
  rw [hlen]
  unfold ratioCost
  omega

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

/-- A single finite program for every binomial coefficient; the inputs are
unary counters, not a factorial oracle. The out-of-range case is tested by the
actual stack guard. -/
theorem eval_choose (n k : ℕ) : ∃ t≤cost n k,
    Eval choose (input n k) (update (input n k) 0 (n.choose k).bits) t := by
  have ep := eval_prepare n k
  by_cases hk : k≤n
  · obtain ⟨t1,ht1,h1⟩ := eval_allFactors n k
    obtain ⟨t2,ht2,h2⟩ := eval_ratio n k hk
    have ec : Eval compute (prepared n k) (update (input n k) 0 (n.choose k).bits) (1+t1+t2) := Eval.seq h1 h2
    have hg : prepared n k 13=[] := by simp [prepared,Nat.sub_eq_zero_of_le hk]
    have hb : Eval (.branch 13 compute discard discard) (prepared n k)
        (update (input n k) 0 (n.choose k).bits) (1+(1+t1+t2)) := Eval.branchNone hg ec
    refine ⟨_,?_,Eval.seq ep hb⟩
    unfold cost;omega
  · have hlt : n<k := Nat.lt_of_not_ge hk
    let u := update (prepared n k) 12 []
    have e1 : Eval (clear 12) (prepared n k) u 1 := by
      simpa [u,prepared,Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)] using eval_clear (12 : Fin 18) (prepared n k)
    have e2 := eval_clear (13 : Fin 18) u
    have hx : update u 13 []=update (input n k) 0 (n.choose k).bits := by
      funext j; fin_cases j <;> simp [u,prepared,input,Nat.choose_eq_zero_of_lt hlt]
    rw [hx] at e2
    have ec : Eval discard (prepared n k) (update (input n k) 0 (n.choose k).bits) (2*(k-n)+3) := by
      convert Eval.seq e1 e2 using 1 <;> simp [discard,u,prepared] ; omega
    have hp : 0<k-n := Nat.sub_pos_of_lt hlt
    obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    have hg : prepared n k 13=true::List.replicate l true := by simp [prepared,hl,List.replicate_succ]
    have hb : Eval (.branch 13 compute discard discard) (prepared n k)
        (update (input n k) 0 (n.choose k).bits) (1+(2*(k-n)+3)) := Eval.branchTrue hg ec
    refine ⟨_,?_,Eval.seq ep hb⟩
    unfold cost;omega

/-- The exact binary binomial coefficient with a fixed polynomial bound
in the unary input length. -/

theorem eval_choose_polynomial (n k : ℕ) : ∃ t≤3000000*(n+k+1)^10,
    Eval choose (input n k) (update (input n k) 0 (n.choose k).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_choose n k
  exact ⟨t,ht.trans (cost_bound n k),he⟩

end RationalHitting.StackLanguage.Binomial

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.DenseRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

def packLoop (a b : Fin 3) : Program (Fin 3) :=
  .loop a (.seq (.transfer a b) (.push b false))

lemma eval_packLoop (a b : Fin 3) (hab : a ≠ b) (s : Store (Fin 3)) :
    Eval (packLoop a b) s (update (update s a []) b (pairWord (s a).reverse++s b))
      (4*(s a).length+1) := by
  generalize he : s a = w
  induction w generalizing s with
  | nil =>
    have hh : update (update s a []) b (s b) = s := by
      funext k; by_cases hka : k=a <;> by_cases hkb : k=b <;> simp_all
    simpa [packLoop,he,hh] using
      (Eval.whileNil (p := Program.seq (.transfer a b) (.push b false)) he)
  | cons x w ih =>
    let u := update (update s a w) b (x::s b)
    let v := update u b (false::x::s b)
    have h1 : Eval (Program.transfer a b) s u 1 := by
      simpa [u,transfer_cons hab s x w he] using Eval.transfer a b s
    have h2 : Eval (Program.push b false) u v 1 := by simpa [u,v] using Eval.push b false u
    have h3 := ih v (by simp [v,u,hab])
    have hh := Eval.whileCons (by simp [he]) (Eval.seq h1 h2) h3
    have heq : update (update v a []) b (pairWord w.reverse++v b) =
        update (update s a []) b (pairWord (x::w).reverse++s b) := by
      funext k; by_cases hka : k=a <;> by_cases hkb : k=b <;>
        simp_all [v,u,List.reverse_cons,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 <;> simp [packLoop] ; omega

/-- Consume a binary word, prepending one encoded reversed record. -/
def packRecord : Program (Fin 3) := .seq (.push 1 true) (packLoop 0 1)

lemma eval_packRecord (s : Store (Fin 3)) :
    Eval packRecord s (update (update s 0 []) 1 (codeWord (s 0).reverse++s 1))
      (4*(s 0).length+3) := by
  have h1 := Eval.push (1 : Fin 3) true s
  have h2 := eval_packLoop 0 1 (by decide) (update s 1 (true::s 1))
  have hh := Eval.seq h1 h2
  have heq : update (update (update s 1 (true::s 1)) 0 []) 1
      (pairWord (s 0).reverse++true::s 1) =
      update (update s 0 []) 1 (codeWord (s 0).reverse++s 1) := by
    funext k; by_cases h0 : k=0 <;> by_cases h1 : k=1 <;>
      simp_all [codeWord_pair,List.append_assoc]
  simp only [update_of_ne (by decide : (0 : Fin 3) ≠ 1),update_self,heq] at hh
  convert hh using 1 <;> simp [packRecord] ; omega

def unpackBody : Program (Fin 3) :=
  .branch 0 (.drop 2) (.seq (.drop 0) (.transfer 0 1)) (.seq (.drop 0) (.drop 2))

lemma eval_unpackLoop (w tail : List Bool) (s : Store (Fin 3))
    (h0 : s 0 = codeWord w++tail) (h2 : s 2 = [true]) :
    Eval (Program.loop 2 unpackBody) s
      (update (update (update s 0 tail) 1 (w.reverse++s 1)) 2 []) (5*w.length+6) := by
  induction w generalizing s with
  | nil =>
    let u := update s 0 tail
    let v := update u 2 []
    have h01 : s 0 = true::tail := by simpa [codeWord] using h0
    have hd0 : Eval (Program.drop 0) s u 1 := by simpa [u,h01] using Eval.drop (0 : Fin 3) s
    have hd2 : Eval (Program.drop 2) u v 1 := by simpa [v,u,h2] using Eval.drop (2 : Fin 3) u
    have hb : Eval unpackBody s v 4 := Eval.branchTrue h01 (Eval.seq hd0 hd2)
    have hnil := Eval.whileNil (p:=unpackBody) (by simp [v] : v 2 = [])
    have hh := Eval.whileCons (by simp [h2]) hb hnil
    have heq : v = update (update (update s 0 tail) 1 (([] : List Bool).reverse++s 1)) 2 [] := by
      funext k; fin_cases k <;> simp [v,u]
    simpa [heq] using hh
  | cons b w ih =>
    let u := update s 0 (b::codeWord w++tail)
    let v := update (update u 0 (codeWord w++tail)) 1 (b::s 1)
    have h01 : s 0 = false::b::codeWord w++tail := by simpa [codeWord] using h0
    have hd : Eval (Program.drop 0) s u 1 := by simpa [u,h01] using Eval.drop (0 : Fin 3) s
    have ht : Eval (Program.transfer 0 1) u v 1 := by
      have ht := Eval.transfer (0 : Fin 3) 1 u
      rw [transfer_cons (by decide : (0 : Fin 3) ≠ 1) u b (codeWord w++tail) (by simp [u])] at ht
      simpa [v,u] using ht
    have hb : Eval unpackBody s v 4 := Eval.branchFalse h01 (Eval.seq hd ht)
    have hi := ih v (by simp [v]) (by simp [v,u,h2])
    have hh := Eval.whileCons (by simp [h2]) hb hi
    have heq : update (update (update v 0 tail) 1 (w.reverse++v 1)) 2 [] =
        update (update (update s 0 tail) 1 ((b::w).reverse++s 1)) 2 [] := by
      funext k; fin_cases k <;> simp [v,u,List.reverse_cons,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 ; simp ; omega

/-- Remove one self-delimiting record; produce its reversed binary word. -/
def unpackRecord : Program (Fin 3) := .seq (.push 2 true) (.loop 2 unpackBody)

lemma eval_unpackRecord (w tail : List Bool) (s : Store (Fin 3))
    (h0 : s 0 = codeWord w++tail) (h2 : s 2 = []) :
    Eval unpackRecord s
      (update (update (update s 0 tail) 1 (w.reverse++s 1)) 2 []) (5*w.length+8) := by
  have h1 := Eval.push (2 : Fin 3) true s
  have h2' := eval_unpackLoop w tail (update s 2 [true]) (by simp [h0]) (by simp)
  have hh := Eval.seq h1 (by simpa [h2] using h2')
  have heq : update (update (update (update s 2 [true]) 0 tail) 1 (w.reverse++s 1)) 2 [] =
      update (update (update s 0 tail) 1 (w.reverse++s 1)) 2 [] := by
    funext k; fin_cases k <;> simp
  simp only [heq] at hh
  convert hh using 1 <;> simp [unpackRecord] ; omega

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.SignedBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma wordValue_complement (w : List Bool) :
    wordValue (w.map Bool.not)+wordValue w+1=2^w.length := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih => cases b <;> simp [wordValue,pow_succ] at * <;> omega

def flipReverse (a b : K) : Program K :=
  .loop a (readBit a (fun x => .seq (.drop a) (.push b (!x))))

lemma eval_flipReverse {a b : K} (hab : a≠b) (s : Store K) :
    Eval (flipReverse a b) s
      (update (update s a []) b (((s a).map Bool.not).reverse ++ s b))
      (5*(s a).length+1) := by
  generalize he : s a=w
  induction w generalizing s with
  | nil =>
    have hh : update (update s a []) b (s b)=s := by
      funext k; by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all
    simpa [flipReverse,he,hh] using (Eval.whileNil (p:=readBit a (fun x => .seq (.drop a) (.push b (!x)))) he)
  | cons x w ih =>
    let u := update s a w
    let v := update u b ((!x)::s b)
    have h1 : Eval (Program.drop a) s u 1 := by simpa [u,he] using Eval.drop a s
    have h2 : Eval (Program.push b (!x)) u v 1 := by simpa [v,u,Ne.symm hab] using Eval.push b (!x) u
    have hr : Eval (readBit a (fun y => Program.seq (.drop a) (.push b (!y)))) s v 4 := by
      apply eval_readBit a _ s v 3
      simpa [he] using Eval.seq h1 h2
    have h3 := ih v (by simp [v,u,hab])
    have hh := Eval.whileCons (by simp [he]) hr h3
    have heq : update (update v a []) b ((w.map Bool.not).reverse++v b)=
        update (update s a []) b (((x::w).map Bool.not).reverse++s b) := by
      funext k; by_cases ha : k=a <;> by_cases hb : k=b <;>
        simp_all [v,u,List.reverse_cons,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 <;> simp [flipReverse] ; omega

def flipWord (a b : K) : Program K := .seq (flipReverse a b) (reverse b a)

lemma eval_flipWord {a b : K} (hab : a≠b) (s : Store K) (hb : s b=[]) :
    Eval (flipWord a b) s (update s a ((s a).map Bool.not)) (7*(s a).length+3) := by
  let u := update (update s a []) b ((s a).map Bool.not).reverse
  have e1 : Eval (flipReverse a b) s u (5*(s a).length+1) := by
    simpa [u,hb] using eval_flipReverse hab s
  have e2 := eval_reverse (a:=b) (b:=a) (Ne.symm hab) u
  have heq : update (update u b []) a ((u b).reverse++u a)=update s a ((s a).map Bool.not) := by
    funext k; by_cases ha : k=a <;> by_cases hc : k=b <;> simp_all [u]
  rw [heq] at e2
  have hh := Eval.seq e1 e2
  convert hh using 1 <;> simp [flipWord,u] ; omega

def absoluteWord (a b : List Bool) : List Bool :=
  let r := subtractWord a b false
  if r.2 then incrementWord (r.1.map Bool.not) else r.1

lemma absoluteWord_value (a b : List Bool) :
    wordValue (absoluteWord a b)=((wordValue a : ℤ)-(wordValue b : ℤ)).natAbs := by
  have hv := subtractWord_value a b false
  have hc := wordValue_complement (subtractWord a b false).1
  rw [subtractWord_length] at hc
  by_cases hlt : wordValue a<wordValue b
  · have hr := (subtractWord_borrow a b).mpr hlt
    simp only [absoluteWord,hr,ite_true,incrementWord_value]
    simp [hr,bitNat] at hv
    rw [Int.natAbs_natCast_sub_natCast_of_le (by omega)]
    omega
  · obtain ⟨hr,he⟩ := subtractWord_nonnegative (by omega : wordValue b≤wordValue a)
    simp [absoluteWord,hr,he,Int.natAbs_natCast_sub_natCast_of_ge (by omega : wordValue b≤wordValue a)]

/-- Convert the modular subtraction result to an absolute magnitude according
to its genuinely computed borrow bit. -/
def absolutize : Program (Fin 5) :=
  .seq (.branch 3 .skip .skip (.seq (flipWord 0 1) (increment 0 1 2))) (normalize 0 1 2)

lemma eval_absolutize (s : Store (Fin 5)) (c : Bool) (h3 : s 3=[c]) (h1 : s 1=[]) (h2 : s 2=[]) :
    ∃ t ≤ 30*(s 0).length+52, Eval absolutize s
      (update s 0 (wordValue (if c then incrementWord ((s 0).map Bool.not) else s 0)).bits) t := by
  let w := if c then incrementWord ((s 0).map Bool.not) else s 0
  have hw : w.length≤(s 0).length+1 := by
    cases c <;> simp only [w,Bool.false_eq_true,ite_true,ite_false]
    · omega
    · simpa using incrementWord_length ((s 0).map Bool.not)
  have hpre : ∃ t ≤ 14*(s 0).length+23,
      Eval (Program.branch (3 : Fin 5) .skip .skip (.seq (flipWord 0 1) (increment 0 1 2)))
        s (update s 0 w) t := by
    cases c with
    | false => exact ⟨2,by omega,by simpa [w] using Eval.branchFalse h3 (Eval.skip s)⟩
    | true =>
      let u := update s 0 ((s 0).map Bool.not)
      have e1 := eval_flipWord (a:=0) (b:=1) (by decide) s h1
      obtain ⟨t,ht,e2⟩ := eval_increment (a:=0) (tmp:=1) (flag:=2)
        (by decide) (by decide) (by decide) u
      have hh := Eval.branchTrue (p:=.skip) (q:=.skip) h3 (Eval.seq e1 e2)
      have heq : update (update (update u 0 (incrementWord (u 0))) 1 []) 2 []=update s 0 w := by
        funext k; fin_cases k <;> simp [u,w,h1,h2]
      rw [heq] at hh
      refine ⟨_,?_,hh⟩
      simp [u,h1,h2] at ht
      omega
  obtain ⟨t,ht,e1⟩ := hpre
  let v := update s 0 w
  obtain ⟨u,hu,e2⟩ := eval_normalize (a:=0) (tmp:=1) (flag:=2)
    (by decide) (by decide) (by decide) v
  have heq : update (update (update v 0 (normalizeWord (v 0))) 1 []) 2 []=
      update s 0 (wordValue w).bits := by
    funext k; fin_cases k <;> simp [v,h1,h2,normalizeWord_eq_bits]
  rw [heq] at e2
  refine ⟨1+t+u,?_,Eval.seq e1 e2⟩
  simp [v,h1,h2] at hu
  omega

/-- Signed difference of arbitrary naturals, in canonical signed magnitude. -/
def signedDifference : Program (Fin 5) := .seq subtract absolutize

lemma eval_signedDifference (s : Store (Fin 5)) (h2 : s 2=[]) (h3 : s 3=[]) (h4 : s 4=[]) :
    ∃ t ≤ 100*((s 0).length+(s 1).length+1), Eval signedDifference s
      (update (update (update s 0 (((wordValue (s 0):ℤ)-(wordValue (s 1):ℤ)).natAbs).bits) 1 [])
        3 [decide (wordValue (s 0)<wordValue (s 1))]) t := by
  obtain ⟨t,ht,e1⟩ := eval_subtract s
  let r := subtractWord (s 0) (s 1) false
  let v := update (update s 0 r.1) 1 []
  let u := update v 3 [r.2]
  have ev1 : Eval subtract s u t := by
    have he : update (update (update (update (update s 0 r.1) 1 []) 2 []) 3 [r.2]) 4 []=u := by
      funext k; fin_cases k <;> simp [u,v,h2,h4]
    change Eval subtract s (update (update (update (update (update s 0 r.1) 1 []) 2 []) 3 [r.2]) 4 []) t at e1
    simpa only [he] using e1
  obtain ⟨u',hu,e2⟩ := eval_absolutize u r.2 (by simp [u])
    (by simp [u,v]) (by simp [u,v,h2])
  have hh := Eval.seq ev1 e2
  have hr : r.2=decide (wordValue (s 0)<wordValue (s 1)) := by
    have he := subtractWord_borrow (s 0) (s 1)
    cases hc : r.2 <;> simp_all [r]
  have heq : update u 0 (wordValue (if r.2 then incrementWord ((u 0).map Bool.not) else u 0)).bits=
      update (update (update s 0 (((wordValue (s 0):ℤ)-(wordValue (s 1):ℤ)).natAbs).bits) 1 [])
        3 [decide (wordValue (s 0)<wordValue (s 1))] := by
    have hv : wordValue (if r.2 then incrementWord ((u 0).map Bool.not) else u 0)=
        ((wordValue (s 0):ℤ)-(wordValue (s 1):ℤ)).natAbs := by
      simpa [u,v,absoluteWord,r] using absoluteWord_value (s 0) (s 1)
    rw [hv]
    funext k; fin_cases k <;> simp [u,v,hr]
  rw [heq] at hh
  refine ⟨1+t+u',?_,hh⟩
  simp [u,v,r,subtractWord_length] at hu
  simp [h2,h3,h4] at ht
  omega

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.RationalBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

lemma eval_copy9 (s : Store (Fin 12)) (a b : Fin 12)
    (hab : a≠b) (ha : a≠9) (hb : b≠9) (h9 : s 9=[]) :
    Eval (copy a b 9) s (update s b (s a)) (7*(s a).length+2*(s b).length+7) := by
  have hh := eval_copy hab ha hb s
  have he : update (update s b (s a)) 9 []=update s b (s a) := by
    funext k; by_cases hk : k=9 <;> simp_all [Ne.symm hb]
  rw [he] at hh
  simpa [h9] using hh

/-- Euclid followed by two binary divisions, destructively producing the
coprime numerator and positive denominator magnitudes. -/
def fractionReduce : Program (Fin 12) :=
  .seq (copy 0 10 9) (.seq (copy 5 11 9) (.seq (gcdLoop.rename fractionArith)
    (.seq (copy 0 5 9) (.seq (copy 10 0 9) (.seq (quotient.rename fractionArith)
    (.seq (copy 0 10 9) (.seq (copy 11 0 9) (.seq (quotient.rename fractionArith)
    (.seq (copy 0 5 9) (.seq (copy 10 0 9) (.seq (clear 10) (clear 11))))))))))))

lemma eval_fractionReduce (s : Store (Fin 12)) (hs : fractionScratch s)
    (h10 : s 10=[]) (h11 : s 11=[])
    (hcan0 : (wordValue (s 0)).bits=s 0) (hcan5 : (wordValue (s 5)).bits=s 5)
    (hb : 0<wordValue (s 5)) (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ 3000*(B+1)^3,
      Eval fractionReduce s
        (update (update s 0 (wordValue (s 0)/Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits)
          5 (wordValue (s 5)/Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) t := by
  let A := wordValue (s 0)
  let D := wordValue (s 5)
  let g := Nat.gcd A D
  have hg : 0<g := Nat.gcd_pos_of_pos_right A hb
  have h9 : s 9=[] := hs 9 (by decide) (by decide)
  have hgl : g.bits.length≤B := by
    apply le_trans _ h5
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.le_of_dvd hb (Nat.gcd_dvd_right A D)).trans_lt (wordValue_lt _)
  have hAl : (A/g).bits.length≤B := by
    apply le_trans _ h0; rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.div_le_self _ _).trans_lt (wordValue_lt _)
  have hDl : (D/g).bits.length≤B := by
    apply le_trans _ h5; rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.div_le_self _ _).trans_lt (wordValue_lt _)
  let u1 := update s 10 (s 0)
  let u2 := update u1 11 (s 5)
  let u3 := update (update u2 0 g.bits) 5 []
  let u4 := update u3 5 g.bits
  let u5 := update u4 0 (s 0)
  let u6 := update u5 0 (A/g).bits
  let u7 := update u6 10 (A/g).bits
  let u8 := update u7 0 (s 5)
  let u9 := update u8 0 (D/g).bits
  let u10 := update u9 5 (D/g).bits
  let u11 := update u10 0 (A/g).bits
  let u12 := update u11 10 []
  have e1 : Eval (copy 0 10 9) s u1 (7*(s 0).length+7) := by
    simpa [u1,h10] using eval_copy9 s 0 10 (by decide) (by decide) (by decide) h9
  have e2 : Eval (copy 5 11 9) u1 u2 (7*(s 5).length+7) := by
    simpa [u2,u1,h11] using eval_copy9 u1 5 11 (by decide) (by decide) (by decide) (by simp [u1,h9])
  have hs2 : fractionScratch u2 :=
    fractionScratch_update _ (fractionScratch_update _ hs 10 (by simp) _) 11 (by simp) _
  obtain ⟨t3,ht3,e3⟩ := eval_fractionGcd u2 hs2 (by simpa [u2,u1] using hcan0)
    (by simpa [u2,u1] using hcan5) B (by simpa [u2,u1] using h0) (by simpa [u2,u1] using h5)
  change Eval (gcdLoop.rename fractionArith) u2 u3 t3 at e3
  have e4 : Eval (copy 0 5 9) u3 u4 (7*g.bits.length+7) := by
    simpa [u4,u3,u2,u1] using eval_copy9 u3 0 5 (by decide) (by decide) (by decide) (by simp [u3,u2,u1,h9])
  have e5 : Eval (copy 10 0 9) u4 u5 (7*(s 0).length+2*g.bits.length+7) := by
    simpa [u5,u4,u3,u2,u1] using eval_copy9 u4 10 0 (by decide) (by decide) (by decide)
      (by simp [u4,u3,u2,u1,h9])
  have hs5 : fractionScratch u5 := by
    apply fractionScratch_update _ (fractionScratch_update _
      (fractionScratch_update _ (fractionScratch_update _ hs2 0 (by simp) _) 5 (by simp) _)
      5 (by simp) _) 0 (by simp)
  obtain ⟨t6,ht6,e6⟩ := eval_fractionQuotient u5 hs5 (by simpa [u5,u4] using hg) B
    (by simpa [u5] using h0) (by simpa [u5,u4] using hgl)
  have ev6 : Eval (quotient.rename fractionArith) u5 u6 t6 := by
    simpa [u6,u5,u4,A] using e6
  have e7 : Eval (copy 0 10 9) u6 u7 (7*(A/g).bits.length+2*(s 0).length+7) := by
    simpa [u7,u6,u5,u4,u3,u2,u1] using eval_copy9 u6 0 10 (by decide) (by decide) (by decide)
      (by simp [u6,u5,u4,u3,u2,u1,h9])
  have e8 : Eval (copy 11 0 9) u7 u8 (7*(s 5).length+2*(A/g).bits.length+7) := by
    simpa [u8,u7,u6,u5,u4,u3,u2,u1] using eval_copy9 u7 11 0 (by decide) (by decide) (by decide)
      (by simp [u7,u6,u5,u4,u3,u2,u1,h9])
  have hs8 : fractionScratch u8 :=
    fractionScratch_update _ (fractionScratch_update _ (fractionScratch_update _ hs5
      0 (by simp) _) 10 (by simp) _) 0 (by simp) _
  obtain ⟨t9,ht9,e9⟩ := eval_fractionQuotient u8 hs8 (by simpa [u8,u7,u6,u5,u4] using hg) B
    (by simpa [u8] using h5) (by simpa [u8,u7,u6,u5,u4] using hgl)
  have ev9 : Eval (quotient.rename fractionArith) u8 u9 t9 := by
    simpa [u9,u8,u7,u6,u5,u4,D] using e9
  have e10 : Eval (copy 0 5 9) u9 u10 (7*(D/g).bits.length+2*g.bits.length+7) := by
    simpa [u10,u9,u8,u7,u6,u5,u4] using eval_copy9 u9 0 5 (by decide) (by decide) (by decide)
      (by simp [u9,u8,u7,u6,u5,u4,u3,u2,u1,h9])
  have e11 : Eval (copy 10 0 9) u10 u11 (7*(A/g).bits.length+2*(D/g).bits.length+7) := by
    simpa [u11,u10,u9,u8,u7] using eval_copy9 u10 10 0 (by decide) (by decide) (by decide)
      (by simp [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,h9])
  have e12 : Eval (clear 10) u11 u12 (2*(A/g).bits.length+1) := by
    simpa [u12,u11,u10,u9,u8,u7] using eval_clear (10 : Fin 12) u11
  have e13 := eval_clear (11 : Fin 12) u12
  have heq : update u12 11 [] = update (update s 0 (A/g).bits) 5 (D/g).bits := by
    funext k; fin_cases k <;> simp [u12,u11,u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,h10,h11]
  rw [heq] at e13
  have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq ev6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq ev9 (Eval.seq e10 (Eval.seq e11 (Eval.seq e12 e13)))))))))))
  refine ⟨_,?_,hh⟩
  simp only [show u12 11=s 5 by simp [u12,u11,u10,u9,u8,u7,u6,u5,u4,u3,u2,u1]]
  nlinarith [Nat.zero_le (B^3)]

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

/-- Consume a word, emitting its unary length, independently of its bits. -/
def unaryLength (a b : K) : Program K := .loop a (.seq (.drop a) (.push b true))

lemma eval_unaryLength {a b : K} (hab : a≠b) (s : Store K) :
    Eval (unaryLength a b) s
      (update (update s a []) b (List.replicate (s a).length true ++ s b))
      (4*(s a).length+1) := by
  generalize he : s a=w
  induction w generalizing s with
  | nil =>
    have hh : update (update s a []) b (s b)=s := by
      funext k; by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all
    simpa [unaryLength,he,hh] using (Eval.whileNil (p:=Program.seq (.drop a) (.push b true)) he)
  | cons x w ih =>
    let u := update s a w
    let v := update u b (true::s b)
    have e1 : Eval (Program.drop a) s u 1 := by simpa [u,he] using Eval.drop a s
    have e2 : Eval (Program.push b true) u v 1 := by simpa [v,u,Ne.symm hab] using Eval.push b true u
    have e3 := ih v (by simp [v,u,hab])
    have hh := Eval.whileCons (by simp [he]) (Eval.seq e1 e2) e3
    have heq : update (update v a []) b (List.replicate w.length true ++ v b) =
        update (update s a []) b (List.replicate (x::w).length true ++ s b) := by
      funext k; by_cases ha : k=a <;> by_cases hb : k=b <;>
        simp_all [v,u,List.replicate_add,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 <;> simp [unaryLength] ; omega

def encodeWord : Program (Fin 4) :=
  .seq (duplicateReverse 0 2 3) (.seq (reverse 2 1)
    (.seq (.push 1 false) (unaryLength 3 1)))

lemma eval_encodeWord (s : Store (Fin 4)) (h2 : s 2=[]) (h3 : s 3=[]) :
    Eval encodeWord s (update (update s 0 []) 1 (encodedWord (s 0)++s 1))
      (11*(s 0).length+7) := by
  let u := update (update (update s 0 []) 2 (s 0).reverse) 3 (s 0).reverse
  let v := update (update u 2 []) 1 (s 0++s 1)
  let z := update v 1 (false::s 0++s 1)
  have e1 : Eval (duplicateReverse 0 2 3) s u (5*(s 0).length+1) := by
    simpa [u,h2,h3] using eval_duplicateReverse (a:=0) (b:=2) (c:=3)
      (by decide) (by decide) (by decide) s
  have e2 : Eval (reverse 2 1) u v (2*(s 0).length+1) := by
    simpa [v,u] using eval_reverse (a:=2) (b:=1) (by decide) u
  have e3 : Eval (Program.push 1 false) v z 1 := by
    simpa [z,v,u] using Eval.push (1 : Fin 4) false v
  have e4 := eval_unaryLength (a:=3) (b:=1) (by decide) z
  have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
  have heq : update (update z 3 []) 1 (List.replicate (z 3).length true ++ z 1) =
      update (update s 0 []) 1 (encodedWord (s 0)++s 1) := by
    funext k; fin_cases k <;> simp [z,v,u,h2,h3,encodedWord,List.append_assoc]
  rw [heq] at hh
  convert hh using 1 <;> simp [encodeWord,z,v,u] ; omega

end RationalHitting.StackLanguage

namespace RationalHitting
namespace StackLanguage
open Function

lemma eval_encodeWord_rename {K : Type} [DecidableEq K] (f : Fin 4 → K)
    (hf : Injective f) (s : Store K) (h2 : s (f 2)=[]) (h3 : s (f 3)=[]) :
    Eval (encodeWord.rename f) s
      (update (update s (f 0) []) (f 1) (encodedWord (s (f 0))++s (f 1)))
      (11*(s (f 0)).length+7) := by
  have h := eval_rename_from f hf s (eval_encodeWord (fun k => s (f k)) h2 h3)
  simpa only [extend_update_store f hf,extend_pull_store f hf] using h

lemma eval_fractionReduce_rename {K : Type} [DecidableEq K] (f : Fin 12 → K)
    (hf : Injective f) (s : Store K) (hs : fractionScratch (fun k => s (f k)))
    (h10 : s (f 10)=[]) (h11 : s (f 11)=[]) (A D B : ℕ)
    (h0 : s (f 0)=A.bits) (h5 : s (f 5)=D.bits) (hD : 0<D)
    (ha : A.bits.length≤B) (hd : D.bits.length≤B) :
    ∃ t ≤ 3000*(B+1)^3, Eval (fractionReduce.rename f) s
      (update (update s (f 0) (A/Nat.gcd A D).bits) (f 5) (D/Nat.gcd A D).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_fractionReduce (fun k => s (f k)) hs h10 h11
    (by simp [h0]) (by simp [h5]) (by simpa [h5] using hD) B
    (by simpa [h0] using ha) (by simpa [h5] using hd)
  refine ⟨t,ht,?_⟩
  have h := eval_rename_from f hf s he
  simpa only [extend_update_store f hf,extend_pull_store f hf,h0,h5,wordValue_bits] using h

/-- Registers 12 and 13 hold signed-magnitude signs; 15 stores the canonical
result's sign and remains disjoint from the twelve arithmetic registers. -/
def fractionSign : Program (Fin 16) :=
  .branch 0 (.push 15 false)
    (readBit 12 (fun a => readBit 13 (fun b => .push 15 (a ^^ b))))
    (readBit 12 (fun a => readBit 13 (fun b => .push 15 (a ^^ b))))

lemma eval_fractionSign (s : Store (Fin 16)) (a b : Bool) (h12 : s 12=[a]) (h13 : s 13=[b]) :
    ∃ t ≤ 4, Eval fractionSign s
      (update s 15 ((if s 0=[] then false else a ^^ b)::s 15)) t := by
  cases h0 : s 0 with
  | nil =>
    refine ⟨2,by omega,?_⟩
    simpa [fractionSign,h0] using (Eval.branchNone h0 (Eval.push (15 : Fin 16) false s))
  | cons c w =>
    have hr : Eval (readBit 12 (fun a => readBit 13 (fun b => Program.push 15 (a ^^ b)))) s
        (update s 15 ((a ^^ b)::s 15)) 3 := by
      apply eval_readBit 12 _ s _ 2
      simp only [h12,List.headD_cons]
      apply eval_readBit 13 _ s _ 1
      simpa [h13] using Eval.push (15 : Fin 16) (a ^^ b) s
    cases c with
    | false => exact ⟨4,by omega,by simpa [fractionSign,h0] using Eval.branchFalse h0 hr⟩
    | true => exact ⟨4,by omega,by simpa [fractionSign,h0] using Eval.branchTrue h0 hr⟩

/-- Full signed canonical rational output. No gcd, comparison or sign oracle
occurs in this fixed finite binary-stack program. -/
def rationalEncode : Program (Fin 16) :=
  .seq fractionSign (.seq (fractionReduce.rename reduceReg)
    (.seq (encodeWord.rename denominatorReg)
      (.seq (encodeWord.rename numeratorReg) (.transfer 15 14))))

end StackLanguage
end RationalHitting

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Procedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Compositional finite-stack implementation. All the constants introduced
here describe actual finite programs, not arithmetic-operation oracles. -/
namespace RationalHitting.StackLanguage
open Function

variable {K L : Type} [DecidableEq K] [DecidableEq L]

def single (k : K) (w : List Bool) : Store K := update (fun _ => []) k w

@[simp] lemma single_self (k : K) (w : List Bool) : single k w k = w := by
  simp [single]
@[simp] lemma single_other {k j : K} (w : List Bool) (h : j≠k) : single k w j = [] := by
  simp [single,h]
@[simp] lemma single_nil (k : K) : single k [] = fun _ => [] := by
  funext j; by_cases h : j=k <;> simp [single,h]

lemma extend_single (f : K → L) (hf : Injective f) (k : K) (w : List Bool) :
    extend f (single k w) (fun _ => []) = single (f k) w := by
  rw [single, extend_update_store f hf]
  congr 1
  funext l
  by_cases h : ∃ a, f a=l
  · obtain ⟨a,rfl⟩ := h; simp [hf.extend_apply]
  · simp [extend_apply' _ _ _ h]

lemma Eval.rename_single {p : Program K} {i o : K} {x y : List Bool} {t : ℕ}
    (h : Eval p (single i x) (single o y) t) (f : K → L) (hf : Injective f) :
    Eval (p.rename f) (single (f i) x) (single (f o) y) t := by
  simpa only [extend_single f hf] using h.rename f hf (fun _ => [])

/-- A quantitative implementation, with completely clean stack input and
output. Both execution and result size are polynomially bounded. -/
structure Procedure {A B : Type} (ca : A → List Bool) (cb : B → List Bool) (f : A → B) where
  Registers : Type
  finite : Fintype Registers
  decEq : DecidableEq Registers
  input : Registers
  output : Registers
  program : @Program Registers
  bound : TimeBound
  correct : ∀ a, ∃ t ≤ bound.eval ((ca a).length+1),
    @Eval Registers decEq program (@single Registers decEq input (ca a))
      (@single Registers decEq output (cb (f a))) t
  size : ∀ a, (cb (f a)).length ≤ bound.eval ((ca a).length+1)

attribute [instance] Procedure.finite Procedure.decEq

/-- A compositional polynomial-time feasibility predicate. -/
def Feasible {A B : Type} (ca : A → List Bool) (cb : B → List Bool) (f : A → B) : Prop :=
  Nonempty (Procedure ca cb f)


/-- Order-preserving transfer, implemented using two stack reversals. -/
def move (a b tmp : K) : Program K := .seq (reverse a tmp) (reverse tmp b)

lemma eval_move {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (s : Store K) (hb : s b=[]) (ht : s tmp=[]) :
    Eval (move a b tmp) s (update (update s a []) b (s a)) (4*(s a).length+3) := by
  have h₁ := eval_reverse hat s
  have h₂ := eval_reverse hbt.symm (update (update s a []) tmp ((s a).reverse++s tmp))
  have hh := Eval.seq h₁ h₂
  have he : update (update (update (update s a []) tmp ((s a).reverse++s tmp)) tmp []) b
      (((update (update s a []) tmp ((s a).reverse++s tmp)) tmp).reverse ++
        (update (update s a []) tmp ((s a).reverse++s tmp)) b) =
      update (update s a []) b (s a) := by
    funext j
    by_cases hja : j=a <;> by_cases hjb : j=b <;> by_cases hjt : j=tmp <;>
      simp_all
  rw [he] at hh
  convert hh using 1 <;> simp [move,ht]; omega

lemma Eval.move_single {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (w : List Bool) :
    Eval (move a b tmp) (single a w) (single b w) (4*w.length+3) := by
  have h := eval_move hab hat hbt (single a w) (by simp [hab.symm]) (by simp [hat.symm])
  have he : update (update (single a w) a []) b w=single b w := by
    simp [single,update_idem]
  simpa only [single_self,he] using h

namespace Procedure
variable {A B C : Type} {ca : A → List Bool} {cb : B → List Bool} {cc : C → List Bool}
  {f : A → B} {g : B → C}

/-- Identity has no operation of unbounded cost. -/
def identity (ca : A → List Bool) : Procedure ca ca id where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .skip
  bound := TimeBound.variable+1
  correct a := ⟨1,by simp,Eval.skip _⟩
  size a := by simp; omega

/-- Composition uses disjoint scratch banks and an actual order-preserving
stack transfer. -/
def comp (q : Procedure cb cc g) (p : Procedure ca cb f) : Procedure ca cc (g ∘ f) where
  Registers := p.Registers ⊕ (q.Registers ⊕ Unit)
  finite := inferInstance
  decEq := inferInstance
  input := Sum.inl p.input
  output := Sum.inr (Sum.inl q.output)
  program := .seq (p.program.rename Sum.inl)
    (.seq (move (Sum.inl p.output) (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ())))
      (q.program.rename (Sum.inr ∘ Sum.inl)))
  bound := 5*p.bound + q.bound.comp (p.bound+1) + 5
  correct a := by
    obtain ⟨t,ht,he⟩ := p.correct a
    obtain ⟨u,hu,hq⟩ := q.correct (f a)
    refine ⟨1+t+(1+(4*(cb (f a)).length+3)+u),?_,?_⟩
    · have hsize := p.size a
      have hu' := hu.trans (q.bound.monotone (Nat.add_le_add_right hsize 1))
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_comp] at *
      omega
    · exact Eval.seq (he.rename_single Sum.inl Sum.inl_injective)
        (Eval.seq (Eval.move_single (by simp) (by simp) (by simp) _)
          (hq.rename_single (Sum.inr ∘ Sum.inl) (Sum.inr_injective.comp Sum.inl_injective)))
  size a := by
    have hs := (q.size (f a)).trans (q.bound.monotone (Nat.add_le_add_right (p.size a) 1))
    simp only [comp_apply,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_comp]
    omega

/-- Reinterpret equal input/output words, with no additional computation. -/
def recode {A' B' : Type} (p : Procedure ca cb f) (ca' : A' → List Bool)
    (cb' : B' → List Bool) (f' : A' → B') (e : A' → A)
    (hi : ∀ a, ca (e a)=ca' a) (ho : ∀ a, cb (f (e a))=cb' (f' a)) :
    Procedure ca' cb' f' where
  Registers := p.Registers
  finite := p.finite
  decEq := p.decEq
  input := p.input
  output := p.output
  program := p.program
  bound := p.bound
  correct a := by
    obtain ⟨t,ht,he⟩ := p.correct (e a)
    rw [hi,ho] at he
    rw [hi] at ht
    exact ⟨t,ht,he⟩
  size a := by simpa only [hi,ho] using p.size (e a)


end Procedure
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.ProcedurePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
variable {K L : Type} [DecidableEq K] [DecidableEq L]

def both (a b : K) (x y : List Bool) : Store K := update (single a x) b y
@[simp] lemma both_first {a b : K} (hab : a≠b) (x y : List Bool) : both a b x y a=x := by
  simp [both,hab]
@[simp] lemma both_second (a b : K) (x y : List Bool) : both a b x y b=y := by simp [both]
lemma both_comm {a b : K} (hab : a≠b) (x y : List Bool) : both a b x y=both b a y x := by
  exact update_comm hab _ _ _
@[simp] lemma both_nil_left (a b : K) (y : List Bool) : both a b [] y=single b y := by
  simp [both,single]
@[simp] lemma both_nil_right {a b : K} (hab : a≠b) (x : List Bool) : both a b x []=single a x := by
  exact update_eq_self_iff.mpr (by simp [hab.symm])

lemma extend_single_both (f : K → L) (hf : Injective f) (i : K) (x : List Bool)
    (k : L) (y : List Bool) (hk : ∀ a, f a≠k) :
    extend f (single i x) (single k y)=both (f i) k x y := by
  funext l
  by_cases hl : ∃ a, f a=l
  · obtain ⟨a,rfl⟩ := hl
    by_cases ha : a=i
    · subst a; simp [hf.extend_apply,both,hk]
    · have hf' : f a≠f i := fun hh => ha (hf hh)
      simp [hf.extend_apply,single,both,ha,hf',hk]
  · have hli : l≠f i := fun hh => hl ⟨i,hh.symm⟩
    rw [extend_apply' _ _ _ hl]
    by_cases hlk : l=k <;> simp [both,single,hli,hlk]

lemma Eval.rename_both {p : Program K} {i o : K} {x y : List Bool} {t : ℕ}
    (h : Eval p (single i x) (single o y) t) (f : K → L) (hf : Injective f)
    (k : L) (z : List Bool) (hk : ∀ a, f a≠k) :
    Eval (p.rename f) (both (f i) k x z) (both (f o) k y z) t := by
  simpa only [extend_single_both f hf _ _ k z hk] using h.rename f hf (single k z)

lemma eval_copy_single {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp) (w : List Bool) :
    Eval (copy a b tmp) (single a w) (both a b w w) (7*w.length+7) := by
  have he : update (update (single a w) b w) tmp []=both a b w w := by
    apply update_eq_self_iff.mpr
    simp [single,hat.symm,hbt.symm]
  simpa only [single_self,single_other _ hab.symm,single_other _ hat.symm,List.length_nil,
    Nat.mul_zero,Nat.add_zero,he] using eval_copy hab hat hbt (single a w)

/-- Prefix a record in its original order, consuming the first stack. -/
def prependRecord (a b tmp : K) : Program K :=
  .seq (reverse a tmp) (packRecord.rename (threeRegs tmp b a))

lemma eval_prependRecord {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (s : Store K) (ht : s tmp=[]) :
    Eval (prependRecord a b tmp) s
      (update (update s a []) b (codeWord (s a)++s b)) (6*(s a).length+5) := by
  let f := threeRegs tmp b a
  have hf : Injective f := threeRegs_inj hbt.symm hat.symm hab.symm
  let u := update (update s a []) tmp (s a).reverse
  have h₁ : Eval (reverse a tmp) s u (2*(s a).length+1) := by
    simpa only [ht,List.append_nil] using eval_reverse hat s
  have h₂ := eval_rename_from f hf u (eval_packRecord (fun k => u (f k)))
  simp only [extend_update_store f hf,extend_pull_store f hf] at h₂
  have he : update (update u (f 0) []) (f 1) (codeWord (u (f 0)).reverse++u (f 1)) =
      update (update s a []) b (codeWord (s a)++s b) := by
    funext k
    by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hkt : k=tmp <;>
      simp_all [u,f,threeRegs]
  rw [he] at h₂
  have hh := Eval.seq h₁ h₂
  convert hh using 1 <;> simp [prependRecord,u,f,threeRegs] ; omega

lemma eval_prependRecord_both {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (x y : List Bool) :
    Eval (prependRecord a b tmp) (both a b x y) (single b (codeWord x++y)) (6*x.length+5) := by
  have ht : both a b x y tmp=[] := by simp [both,single,hat.symm,hbt.symm]
  have he : update (update (both a b x y) a []) b (codeWord x++y)=single b (codeWord x++y) := by
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all [both,single]
  simpa only [both_first hab,both_second,he] using eval_prependRecord hab hat hbt (both a b x y) ht

namespace Procedure
variable {A B C : Type} {ca : A → List Bool} {cb : B → List Bool} {cc : C → List Bool}
  {f : A → B} {g : A → C}

def pair (p : Procedure ca cb f) (q : Procedure ca cc g) :
    Procedure ca (pairCode cb cc) (fun a => (f a,g a)) where
  Registers := p.Registers ⊕ (q.Registers ⊕ Unit)
  finite := inferInstance
  decEq := inferInstance
  input := Sum.inl p.input
  output := Sum.inr (Sum.inl q.output)
  program := .seq (copy (Sum.inl p.input) (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ())))
    (.seq (p.program.rename Sum.inl)
      (.seq (q.program.rename (Sum.inr ∘ Sum.inl))
        (prependRecord (Sum.inl p.output) (Sum.inr (Sum.inl q.output)) (Sum.inr (Sum.inr ())))))
  bound := 7*TimeBound.variable + 7*p.bound + q.bound + 16
  correct a := by
    obtain ⟨t,ht,hp⟩ := p.correct a
    obtain ⟨u,hu,hq⟩ := q.correct a
    refine ⟨1+(7*(ca a).length+7)+(1+t+(1+u+(6*(cb (f a)).length+5))),?_,?_⟩
    · have hs := p.size a
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable]
      omega
    · have hp' := hp.rename_both (Sum.inl : p.Registers → p.Registers ⊕ (q.Registers ⊕ Unit)) Sum.inl_injective (Sum.inr (Sum.inl q.input)) (ca a)
        (by intro k; simp)
      have hq' := hq.rename_both (Sum.inr ∘ Sum.inl : q.Registers → p.Registers ⊕ (q.Registers ⊕ Unit)) (Sum.inr_injective.comp Sum.inl_injective)
        (Sum.inl p.output) (cb (f a)) (by intro k; simp)
      simp only [comp_apply] at hq'
      rw [both_comm (by simp : (Sum.inr (Sum.inl q.input) : p.Registers ⊕ (q.Registers ⊕ Unit))≠Sum.inl p.output),
        both_comm (by simp : (Sum.inr (Sum.inl q.output) : p.Registers ⊕ (q.Registers ⊕ Unit))≠Sum.inl p.output)] at hq'
      exact Eval.seq (eval_copy_single (by simp) (by simp) (by simp) _)
        (Eval.seq hp' (Eval.seq hq' (eval_prependRecord_both (by simp) (by simp) (by simp) _ _)))
  size a := by
    have hp := p.size a
    have hq := q.size a
    simp only [pairCode_length,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable]
    omega

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma eval_clear_both {a b : K} (hab : a≠b) (x y : List Bool) :
    Eval (clear a) (both a b x y) (single b y) (2*x.length+1) := by
  have he : update (both a b x y) a []=single b y := by
    funext k; by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all [both,single]
  simpa only [both_first hab,he] using eval_clear a (both a b x y)

lemma eval_reverse_both {a b : K} (hab : a≠b) (x y : List Bool) :
    Eval (reverse a b) (both a b x y) (single b (x.reverse++y)) (2*x.length+1) := by
  have he : update (update (both a b x y) a []) b (x.reverse++y)=single b (x.reverse++y) := by
    funext k; by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all [both,single]
  simpa only [both_first hab,both_second,he] using eval_reverse hab (both a b x y)

lemma eval_reverse_single {a b : K} (hab : a≠b) (x : List Bool) :
    Eval (reverse a b) (single a x) (single b x.reverse) (2*x.length+1) := by
  simpa only [both_nil_right hab,List.append_nil] using eval_reverse_both hab x []

lemma eval_clear_single (a : K) (x : List Bool) :
    Eval (clear a) (single a x) (fun _ => []) (2*x.length+1) := by
  simpa [single,update_idem] using eval_clear a (single a x)

/-- A finite literal is written by a finite sequence; it is not a primitive
which can materialize a word of unbounded length in one step. -/
def pushWord (k : K) : List Bool → Program K
  | [] => .skip
  | b::w => .seq (pushWord k w) (.push k b)
lemma eval_pushWord (k : K) (w : List Bool) (s : Store K) :
    Eval (pushWord k w) s (update s k (w++s k)) (2*w.length+1) := by
  induction w with
  | nil => simpa [pushWord] using Eval.skip s
  | cons b w ih =>
    have hp := Eval.push k b (update s k (w++s k))
    have hh := Eval.seq ih hp
    convert hh using 1 <;> simp [pushWord]; omega

lemma eval_unpack_pair (x y : List Bool) :
    Eval unpackRecord (single (0 : Fin 3) (codeWord x++y))
      (both 0 1 y x.reverse) (5*x.length+8) := by
  have he := eval_unpackRecord x y (single (0 : Fin 3) (codeWord x++y)) (by simp) (by simp)
  have hs : update (update (update (single (0 : Fin 3) (codeWord x++y)) 0 y) 1 x.reverse) 2 [] =
      both 0 1 y x.reverse := by
    funext k; fin_cases k <;> simp [single,both]
  simpa only [single_other _ (by decide : (1 : Fin 3)≠0),List.append_nil,hs] using he

namespace Procedure
variable {A B : Type}

def const (ca : A → List Bool) (cb : B → List Bool) (b : B) : Procedure ca cb (fun _ => b) where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .seq (clear ()) (pushWord () (cb b))
  bound := 2*TimeBound.variable + TimeBound.const (2*(cb b).length+3)
  correct a := by
    refine ⟨1+(2*(ca a).length+1)+(2*(cb b).length+1),?_,?_⟩
    · simp; omega
    · exact Eval.seq (eval_clear_single () _) (by simpa [single] using eval_pushWord () (cb b) (fun _ => []))
  size a := by simp; omega

def fst (ca : A → List Bool) (cb : B → List Bool) : Procedure (pairCode ca cb) ca Prod.fst where
  Registers := Fin 3
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 2
  program := .seq unpackRecord (.seq (clear 0) (reverse 1 2))
  bound := 12*TimeBound.variable+12
  correct a := by
    refine ⟨1+(5*(ca a.1).length+8)+(1+(2*(cb a.2).length+1)+(2*(ca a.1).length+1)),?_,?_⟩
    · simp; omega
    · exact Eval.seq (eval_unpack_pair (ca a.1) (cb a.2))
        (Eval.seq (eval_clear_both (by decide) _ _)
          (by simpa only [List.reverse_reverse,List.length_reverse] using
            eval_reverse_single (by decide : (1 : Fin 3)≠2) (ca a.1).reverse))
  size a := by simp; omega

def snd (ca : A → List Bool) (cb : B → List Bool) : Procedure (pairCode ca cb) cb Prod.snd where
  Registers := Fin 3
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 0
  program := .seq unpackRecord (clear 1)
  bound := 12*TimeBound.variable+12
  correct a := by
    refine ⟨1+(5*(ca a.1).length+8)+(2*(ca a.1).length+1),?_,?_⟩
    · simp; omega
    · apply Eval.seq (eval_unpack_pair (ca a.1) (cb a.2))
      rw [both_comm (by decide : (0 : Fin 3)≠1)]
      simpa only [List.length_reverse] using eval_clear_both (by decide : (1 : Fin 3)≠0) (ca a.1).reverse (cb a.2)
  size a := by simp; omega

def appendWord : Procedure (pairCode id id) id (fun p : List Bool×List Bool => p.1++p.2) where
  Registers := Fin 3
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 0
  program := .seq unpackRecord (reverse 1 0)
  bound := 12*TimeBound.variable+12
  correct a := by
    refine ⟨1+(5*a.1.length+8)+(2*a.1.length+1),?_,?_⟩
    · simp; omega
    · apply Eval.seq (eval_unpack_pair a.1 a.2)
      rw [both_comm (by decide : (0 : Fin 3)≠1)]
      simpa only [List.length_reverse,List.reverse_reverse,id_eq] using
        eval_reverse_both (by decide : (1 : Fin 3)≠0) a.1.reverse a.2
  size a := by simp; omega

def reverseWord : Procedure id id (List.reverse : List Bool → List Bool) where
  Registers := Fin 2
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 1
  program := reverse 0 1
  bound := 2*TimeBound.variable+1
  correct a := ⟨2*a.length+1,by simp,eval_reverse_single (by decide) a⟩
  size a := by simp; omega

end Procedure
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.ProcedureControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
namespace Procedure
variable {A B : Type} {ca : A → List Bool} {cb : B → List Bool} {f : A → B}

/-- Give a procedure a single external input/output port. The two transfers
are real stack programs; scratch registers remain clean. -/
def toPort (p : Procedure ca cb f) : Procedure ca cb f where
  Registers := p.Registers ⊕ Fin 2
  finite := inferInstance
  decEq := inferInstance
  input := Sum.inr 0
  output := Sum.inr 0
  program := .seq (move (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.rename Sum.inl) (move (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound := 5*p.bound+4*TimeBound.variable+8
  correct a := by
    obtain ⟨t,ht,hp⟩ := p.correct a
    refine ⟨1+(4*(ca a).length+3)+(1+t+(4*(cb (f a)).length+3)),?_,?_⟩
    · have hs := p.size a
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable]
      omega
    · exact Eval.seq (Eval.move_single (by simp) (by simp) (by simp) _)
        (Eval.seq (hp.rename_single Sum.inl Sum.inl_injective)
          (Eval.move_single (by simp) (by simp) (by simp) _))
  size a := by
    have hs := p.size a
    simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable]
    omega

end Procedure

def splitPair {K : Type} [DecidableEq K] (a b tmp : K) : Program K :=
  .seq (unpackRecord.rename (threeRegs b tmp a)) (reverse tmp a)

lemma eval_splitPair {K : Type} [DecidableEq K] {a b tmp : K}
    (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp) (x y : List Bool) :
    Eval (splitPair a b tmp) (single b (codeWord x++y)) (both a b x y) (7*x.length+10) := by
  let f := threeRegs b tmp a
  have hf : Injective f := threeRegs_inj hbt hab.symm hat.symm
  have he := (eval_unpack_pair x y).rename f hf (fun _ => [])
  have hx : extend f (both (0 : Fin 3) 1 y x.reverse) (fun _ => [])=both b tmp y x.reverse := by
    simp only [both,extend_update_store f hf,extend_single f hf]
    rfl
  rw [extend_single f hf,hx] at he
  have hrev := eval_reverse hat.symm (both b tmp y x.reverse)
  have heq : update (update (both b tmp y x.reverse) tmp []) a
      ((both b tmp y x.reverse tmp).reverse++both b tmp y x.reverse a)=both a b x y := by
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=tmp <;>
      simp_all [both,single]
  rw [heq] at hrev
  have hh := Eval.seq he hrev
  convert hh using 1 <;> simp [splitPair,f,threeRegs,both] ; omega

lemma extend_both {K L : Type} [DecidableEq K] [DecidableEq L] (f : K → L) (hf : Injective f)
    (i j : K) (x y : List Bool) :
    extend f (both i j x y) (fun _ => [])=both (f i) (f j) x y := by
  simp only [both,extend_update_store f hf,extend_single f hf]

namespace Procedure
variable {A B C K : Type} [Fintype K] [DecidableEq K]
  {ca : A → List Bool} {cb : B → List Bool} {cc : C → List Bool} {f : A×B → C}

/-- Package an independently proved two-input clean register routine as a
serialized procedure. Its polynomial bound is not an operation oracle: the
actual Eval proof is required. -/
def fromBinary (p : Program K) (i j o : K) (hij : i≠j) (bnd : TimeBound)
    (hp : ∀ a b, ∃ t ≤ bnd.eval ((ca a).length+(cb b).length+1),
      Eval p (both i j (ca a) (cb b)) (single o (cc (f (a,b)))) t)
    (hs : ∀ a b, (cc (f (a,b))).length ≤ bnd.eval ((ca a).length+(cb b).length+1)) :
    Procedure (pairCode ca cb) cc f where
  Registers := K ⊕ Unit
  finite := inferInstance
  decEq := inferInstance
  input := Sum.inl j
  output := Sum.inl o
  program := .seq (splitPair (Sum.inl i) (Sum.inl j) (Sum.inr ())) (p.rename Sum.inl)
  bound := bnd + 7*TimeBound.variable+12
  correct a := by
    obtain ⟨t,ht,he⟩ := hp a.1 a.2
    refine ⟨1+(7*(ca a.1).length+10)+t,?_,?_⟩
    · have hh : (ca a.1).length+(cb a.2).length+1 ≤ (pairCode ca cb a).length+1 := by simp; omega
      have ht' := ht.trans (bnd.monotone hh)
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable]
      simp only [pairCode_length] at *
      omega
    · exact Eval.seq (eval_splitPair (by simpa using hij) (by simp) (by simp) _ _)
        (by simpa only [extend_single Sum.inl Sum.inl_injective,extend_both Sum.inl Sum.inl_injective]
          using he.rename (Sum.inl : K → K ⊕ Unit) Sum.inl_injective (fun _ => []))
  size a := by
    have hh : (ca a.1).length+(cb a.2).length+1 ≤ (pairCode ca cb a).length+1 := by simp; omega
    have ht := (hs a.1 a.2).trans (bnd.monotone hh)
    simp only [Prod.mk.eta] at ht
    simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable]
    omega

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

namespace Procedure
variable {A B K : Type} [Fintype K] [DecidableEq K]
  {ca : A → List Bool} {cb : B → List Bool} {f g : A → B}

def rename (p : Procedure ca cb f) (e : p.Registers → K) (he : Injective e) : Procedure ca cb f where
  Registers := K
  finite := inferInstance
  decEq := inferInstance
  input := e p.input
  output := e p.output
  program := p.program.rename e
  bound := p.bound
  correct a := by
    obtain ⟨t,ht,he'⟩ := p.correct a
    exact ⟨t,ht,he'.rename_single e he⟩
  size := p.size

/-- Deterministic Boolean branching on a serialized pair. Only the selected
finite subprogram runs; the tag is physically consumed. -/
def branch (p : Procedure ca cb f) (q : Procedure ca cb g) :
    Procedure (pairCode boolCode ca) cb (fun a => if a.1 then f a.2 else g a.2) := by
  let R := (p.Registers ⊕ q.Registers) ⊕ Fin 3
  let e₁ : p.toPort.Registers → R := Sum.map Sum.inl Fin.castSucc
  let e₂ : q.toPort.Registers → R := Sum.map Sum.inr Fin.castSucc
  have he₁ : Injective e₁ := Sum.inl_injective.sumMap (Fin.castSucc_injective 2)
  have he₂ : Injective e₂ := Sum.inr_injective.sumMap (Fin.castSucc_injective 2)
  let p' := p.toPort.rename e₁ he₁
  let q' := q.toPort.rename e₂ he₂
  let port : R := Sum.inr 0
  let flag : R := Sum.inr 2
  let tmp : R := Sum.inr 1
  have hfp : flag≠port := by simp [flag,port,R]
  have hft : flag≠tmp := by simp [flag,tmp,R]
  have hpt : port≠tmp := by simp [port,tmp,R]
  have hp : p'.input=port ∧ p'.output=port := ⟨rfl,rfl⟩
  have hq : q'.input=port ∧ q'.output=port := ⟨rfl,rfl⟩
  let P := Program.seq (splitPair flag port tmp)
    (.branch flag .skip (.seq (.drop flag) q'.program) (.seq (.drop flag) p'.program))
  refine {
    Registers := R
    finite := inferInstance
    decEq := inferInstance
    input := port
    output := port
    program := P
    bound := p'.bound+q'.bound+25
    correct := ?_
    size := ?_ }
  · intro a
    have hs := eval_splitPair (a:=flag) (b:=port) (tmp:=tmp) hfp hft hpt
      (boolCode a.1) (ca a.2)
    simp only [boolCode_length] at hs
    have hd : Eval (.drop flag) (both flag port (boolCode a.1) (ca a.2)) (single port (ca a.2)) 1 := by
      have hh := Eval.drop flag (both flag port (boolCode a.1) (ca a.2))
      have hx : update (both flag port (boolCode a.1) (ca a.2)) flag [] = single port (ca a.2) := by
        rw [both_comm hfp]
        simp only [both,update_idem]
        exact update_eq_self_iff.mpr (by simp [hfp])
      rw [both_first hfp] at hh
      change Eval _ _ (update (both flag port (boolCode a.1) (ca a.2)) flag []) 1 at hh
      rw [hx] at hh
      exact hh
    have hlen : (ca a.2).length+1≤(pairCode boolCode ca a).length+1 := by simp
    cases hb : a.1 with
    | false =>
      obtain ⟨t,ht,he⟩ := q'.correct a.2
      rw [hq.1,hq.2] at he
      refine ⟨1+17+(1+(1+1+t)),?_,?_⟩
      · have ht' := ht.trans (q'.bound.monotone hlen)
        simp only [TimeBound.eval_add,TimeBound.eval_numeral]
        omega
      · simp only [Bool.false_eq_true,↓reduceIte]
        exact Eval.seq hs (Eval.branchFalse (ls:=[]) (by simp only [both_first hfp,boolCode,hb]) (Eval.seq hd he))
    | true =>
      obtain ⟨t,ht,he⟩ := p'.correct a.2
      rw [hp.1,hp.2] at he
      refine ⟨1+17+(1+(1+1+t)),?_,?_⟩
      · have ht' := ht.trans (p'.bound.monotone hlen)
        simp only [TimeBound.eval_add,TimeBound.eval_numeral]
        omega
      · simp only [↓reduceIte]
        exact Eval.seq hs (Eval.branchTrue (ls:=[]) (by simp only [both_first hfp,boolCode,hb]) (Eval.seq hd he))
  · intro a
    have hlen : (ca a.2).length+1≤(pairCode boolCode ca a).length+1 := by simp
    have h₁ := (p'.size a.2).trans (p'.bound.monotone hlen)
    have h₂ := (q'.size a.2).trans (q'.bound.monotone hlen)
    simp only [TimeBound.eval_add,TimeBound.eval_numeral]
    split <;> omega

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

namespace Procedure
variable {A : Type} {ca : A → List Bool} {f : A → A}

def iterateProgram (p : Procedure ca ca f) : Program (p.Registers ⊕ Unit) :=
  .loop (Sum.inr ()) (.seq (p.program.rename Sum.inl) (.drop (Sum.inr ())))

lemma eval_iterateProgram (p : Procedure ca ca f) (hport : p.output=p.input)
    (n : ℕ) (a : A) (B : ℕ) (hb : ∀ i≤n, (ca (f^[i] a)).length≤B) :
    ∃ t≤n*(p.bound.eval (B+1)+3)+1,
    Eval (iterateProgram p) (both (Sum.inl p.input) (Sum.inr ()) (ca a) (unaryCode n))
      (single (Sum.inl p.input) (ca (f^[n] a))) t := by
  induction n generalizing a with
  | zero =>
    refine ⟨1,by simp,?_⟩
    simpa only [unaryCode_zero,both_nil_right (by simp : (Sum.inl p.input : p.Registers ⊕ Unit)≠Sum.inr ()),iterate_zero,id_eq,iterateProgram] using
      (Eval.whileNil (p:=.seq (p.program.rename Sum.inl) (.drop (Sum.inr ())))
        (show both (Sum.inl p.input) (Sum.inr ()) (ca a) [] (Sum.inr ())=[] by simp))
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := p.correct a
    have hsize := hb 0 (by omega)
    simp only [iterate_zero,id_eq] at hsize
    have hu' := hu.trans (p.bound.monotone (Nat.add_le_add_right hsize 1))
    have hb' : ∀ i≤n, (ca (f^[i] (f a))).length≤B := by
      intro i hi
      simpa only [iterate_succ_apply] using hb (i+1) (by omega)
    obtain ⟨v,hv,hev⟩ := ih (f a) hb'
    rw [hport] at he
    have he' := he.rename_both (Sum.inl : p.Registers → p.Registers ⊕ Unit) Sum.inl_injective
      (Sum.inr ()) (unaryCode (n+1)) (by intro k; simp)
    have hd : Eval (.drop (Sum.inr ()))
        (both (Sum.inl p.input) (Sum.inr ()) (ca (f a)) (unaryCode (n+1)))
        (both (Sum.inl p.input) (Sum.inr ()) (ca (f a)) (unaryCode n)) 1 := by
      simpa only [both,both_second,unaryCode_succ,List.tail_cons,update_self,update_idem] using
        Eval.drop (Sum.inr ()) (both (Sum.inl p.input) (Sum.inr ()) (ca (f a)) (unaryCode (n+1)))
    refine ⟨1+(1+u+1)+v,?_,?_⟩
    · linarith only [hu',hv]
    · have hh := Eval.whileCons (by simp :
        both (Sum.inl p.input) (Sum.inr ()) (ca a) (unaryCode (n+1)) (Sum.inr ())≠[])
        (Eval.seq he' hd) hev
      simpa only [iterateProgram,iterate_succ_apply] using hh

/-- Bounded iteration is compiled to a real finite loop. The semantic size
invariant is a proof obligation, not a loop oracle or added main hypothesis. -/
def iterate (p : Procedure ca ca f) (Q : TimeBound)
    (hQ : ∀ (n : ℕ) (a : A) (i : ℕ), i≤n →
      (ca (f^[i] a)).length≤Q.eval ((pairCode unaryCode ca (n,a)).length+1)) :
    Procedure (pairCode unaryCode ca) ca (fun a => f^[a.1] a.2) := by
  let q := p.toPort
  let r : Procedure (pairCode unaryCode ca) ca (fun a => f^[a.1] a.2) := {
    Registers := (q.Registers ⊕ Unit) ⊕ Unit
    finite := inferInstance
    decEq := inferInstance
    input := Sum.inl (Sum.inl q.input)
    output := Sum.inl (Sum.inl q.input)
    program := .seq (splitPair (Sum.inl (Sum.inr ())) (Sum.inl (Sum.inl q.input)) (Sum.inr ()))
      ((iterateProgram q).rename Sum.inl)
    bound := TimeBound.variable*(q.bound.comp (Q+1)+3)+7*TimeBound.variable+Q+12
    correct a := by
      obtain ⟨t,ht,he⟩ := eval_iterateProgram q rfl a.1 a.2
        (Q.eval ((pairCode unaryCode ca a).length+1)) (by simpa only [Prod.mk.eta] using hQ a.1 a.2)
      refine ⟨1+(7*a.1+10)+t,?_,?_⟩
      · have hn : a.1 ≤ (pairCode unaryCode ca a).length+1 := by simp; omega
        have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
        simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
          TimeBound.eval_variable,TimeBound.eval_comp]
        omega
      · have hs := eval_splitPair (tmp:=Sum.inr ()) (by simp : (Sum.inl (Sum.inr ()) : (q.Registers ⊕ Unit) ⊕ Unit)≠Sum.inl (Sum.inl q.input))
          (by simp) (by simp) (unaryCode a.1) (ca a.2)
        simp only [unaryCode_length] at hs
        rw [both_comm (by simp : (Sum.inl (Sum.inr ()) : (q.Registers ⊕ Unit) ⊕ Unit)≠Sum.inl (Sum.inl q.input))] at hs
        exact Eval.seq hs (by
          simpa only [extend_both Sum.inl Sum.inl_injective,
            extend_single Sum.inl Sum.inl_injective] using
            he.rename (Sum.inl : (q.Registers ⊕ Unit) → (q.Registers ⊕ Unit) ⊕ Unit) Sum.inl_injective (fun _ => []))
    size a := by
      have hs := hQ a.1 a.2 a.1 le_rfl
      simp only [Prod.mk.eta] at hs
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
          TimeBound.eval_variable,TimeBound.eval_comp]
      omega }
  exact r

end Procedure
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Feasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
namespace Feasible
variable {A B C D : Type} {ca : A → List Bool} {cb : B → List Bool}
  {cc : C → List Bool} {cd : D → List Bool} {f : A → B} {g : B → C}

theorem fst (ca : A → List Bool) (cb : B → List Bool) :
    Feasible (pairCode ca cb) ca Prod.fst := ⟨Procedure.fst ca cb⟩
theorem snd (ca : A → List Bool) (cb : B → List Bool) :
    Feasible (pairCode ca cb) cb Prod.snd := ⟨Procedure.snd ca cb⟩

end Feasible
end RationalHitting.StackLanguage


namespace RationalHitting.TimeBound

def power (p : TimeBound) : ℕ → TimeBound
  | 0 => 1
  | n+1 => power p n*p
instance instPowNat : Pow TimeBound ℕ := ⟨power⟩
@[simp] lemma eval_pow (p : TimeBound) (k n : ℕ) : (p^k).eval n=(p.eval n)^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (p^k*p).eval n=(p.eval n)^(k+1)
    rw [eval_mul,ih,pow_succ]
end RationalHitting.TimeBound


namespace RationalHitting.StackLanguage
open Function

lemma add_bits_length (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length := by
  have hh := wordValue_lt (addWord a.bits b.bits)
  simp only [addWord_value,wordValue_bits] at hh
  exact (by rw [Nat.size_eq_bits_len,Nat.size_le]; exact hh :
    (a+b).bits.length≤(addWord a.bits b.bits).length) |>.trans (addWord_length _ _)

lemma eval_normalize_single {K : Type} [DecidableEq K] {a tmp flag : K}
    (hat : a≠tmp) (haf : a≠flag) (htf : tmp≠flag) (w : List Bool) :
    ∃ t≤7*w.length+16, Eval (normalize a tmp flag) (single a w)
      (single a (wordValue w).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_normalize hat haf htf (single a w)
  have hx : update (update (update (single a w) a (normalizeWord w)) tmp []) flag []=
      single a (wordValue w).bits := by
    funext k
    by_cases ha : k=a <;> by_cases ht : k=tmp <;> by_cases hf : k=flag <;>
      simp_all [single]
  rw [single_self,hx] at he
  refine ⟨t,?_,he⟩
  simpa [hat.symm,haf.symm] using ht

def addClean : Program (Fin 5) := .seq (add 0 1 2 3 4) (normalize 0 3 4)
lemma eval_addClean (a b : ℕ) : ∃ t≤50*(a.bits.length+b.bits.length+1)^2,
    Eval addClean (both (0 : Fin 5) 1 a.bits b.bits) (single 0 (a+b).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_add (a:=(0 : Fin 5)) (b:=1) (out:=2) (tmp:=3) (flag:=4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (both 0 1 a.bits b.bits)
  have hx : update (update (update (update (update (both (0 : Fin 5) 1 a.bits b.bits)
      0 (addWord a.bits b.bits)) 1 []) 2 []) 3 []) 4 []=single 0 (addWord a.bits b.bits) := by
    funext k; fin_cases k <;> simp [single,both]
  simp only [both_first (by decide : (0 : Fin 5)≠1),both_second,hx] at he
  obtain ⟨u,hu,he'⟩ := eval_normalize_single (a:=(0 : Fin 5)) (tmp:=3) (flag:=4)
    (by decide) (by decide) (by decide) (addWord a.bits b.bits)
  simp only [addWord_value,wordValue_bits] at he'
  refine ⟨1+t+u,?_,Eval.seq he he'⟩
  have hl := addWord_length a.bits b.bits
  simp [both,single] at ht
  nlinarith only [ht,hu,hl,Nat.zero_le (a.bits.length^2),Nat.zero_le (b.bits.length^2)]

namespace Procedure

def binaryAdd : Procedure (pairCode Nat.bits Nat.bits) Nat.bits (fun a => a.1+a.2) :=
  fromBinary addClean 0 1 0 (by decide) (50*TimeBound.variable^2)
    (by intro a b; simpa using eval_addClean a b) (by
      intro a b
      have h := add_bits_length a b
      simp
      linarith only [h,Nat.zero_le ((a.bits.length+b.bits.length)^2)])

def binaryMul : Procedure (pairCode Nat.bits Nat.bits) Nat.bits (fun a => a.1*a.2) :=
  fromBinary multiplyClean 0 1 0 (by decide) (200*(TimeBound.variable+1)^4)
    (by
      intro a b
      obtain ⟨t,ht,he⟩ := eval_multiplyClean (both (0 : Fin 8) 1 a.bits b.bits)
        (by intro k hk; simp [both,single,show k≠0 by omega,show k≠1 by omega])
        (a.bits.length+b.bits.length+1) (by simp; omega) (by simp; omega)
      have hx : update (update (both (0 : Fin 8) 1 a.bits b.bits) 0 (a*b).bits) 1 []=
          single 0 (a*b).bits := by funext k; by_cases h0 : k=0 <;> by_cases h1 : k=1 <;> simp_all [both,single]
      simp only [both_first (by decide : (0 : Fin 8)≠1),both_second,wordValue_bits,hx] at he
      exact ⟨t,ht,he⟩)
    (by
      intro a b
      have hl : (a*b).bits.length≤a.bits.length+b.bits.length := by
        simpa only [wordValue_bits] using product_bits_length a.bits b.bits
      have hpow : a.bits.length+b.bits.length+2≤(a.bits.length+b.bits.length+2)^4 :=
        Nat.le_self_pow (by omega) _
      simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_pow,
        TimeBound.eval_add,TimeBound.eval_variable,]
      simp only [Nat.add_assoc, show (1:ℕ)+1=2 from rfl] at hpow ⊢
      omega)

end Procedure
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Tabulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage

export Coding (code)

/-- Polynomial time means a concrete finite clean stack program and actual
step bound, through Procedure. It is not machine advice or an oracle. -/
@[fun_prop] def Poly {A B : Type} [Coding A] [Coding B] (f : A → B) : Prop :=
  Feasible code code f

namespace Poly
open Function
variable {A B C D : Type} [Coding A] [Coding B] [Coding C] [Coding D]

@[fun_prop] theorem fst : Poly (Prod.fst : A×B → A) := Feasible.fst code code
@[fun_prop] theorem snd : Poly (Prod.snd : A×B → B) := Feasible.snd code code

end Poly
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.ListProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

namespace Procedure

def padEmpty (w : List Bool) : Procedure _root_.id _root_.id
    (fun a : List Bool => if a=[] then w else a) where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .branch () (pushWord () w) .skip .skip
  bound := TimeBound.variable+TimeBound.const (2*w.length+3)
  correct a := by
    cases a with
    | nil =>
      refine ⟨1+(2*w.length+1),by simp,?_⟩
      have h := eval_pushWord () w (single () [])
      simp only [single_self,List.append_nil] at h
      have e : update (single () []) () w=single () w := by simp [single]
      rw [e] at h
      exact Eval.branchNone (by simp) h
    | cons b a =>
      refine ⟨2,by simp; omega,?_⟩
      cases b
      · exact Eval.branchFalse (ls:=a) (by simp [single]) (Eval.skip _)
      · exact Eval.branchTrue (ls:=a) (by simp [single]) (Eval.skip _)
  size a := by split_ifs <;> simp_all <;> omega

def wordEmpty : Procedure _root_.id boolCode (fun a : List Bool => a.isEmpty) where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .branch () (.push () true) (.seq (clear ()) (.push () false))
    (.seq (clear ()) (.push () false))
  bound := 2*TimeBound.variable+4
  correct a := by
    cases a with
    | nil =>
      refine ⟨2,by simp,?_⟩
      have h : Eval (.push () true) (single () []) (single () (boolCode true)) 1 := by
        simpa [single,boolCode] using Eval.push () true (single () [])
      exact Eval.branchNone (by simp) h
    | cons b a =>
      have h := Eval.seq (eval_clear_single () (b::a)) (Eval.push () false (fun _ : Unit => []))
      have h' : Eval (.seq (clear ()) (.push () false)) (single () (b::a))
          (single () (boolCode false)) (2*(b::a).length+3) := by
        convert h using 1 <;> simp [single,boolCode]; omega
      refine ⟨1+(2*(b::a).length+3),by simp; omega,?_⟩
      cases b
      · exact Eval.branchFalse (ls:=a) (by simp [single]) h'
      · exact Eval.branchTrue (ls:=a) (by simp [single]) h'
  size a := by simp

end Procedure

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

def countRecordsBody : Program (Fin 2) :=
  .branch 0 .skip (.seq (.drop 0) (.drop 0)) (.seq (.drop 0) (.push 1 true))
def countRecords : Program (Fin 2) := .loop 0 countRecordsBody

lemma drop_both_left (w v : List Bool) :
    Eval (.drop (0 : Fin 2)) (both 0 1 w v) (both 0 1 w.tail v) 1 := by
  convert Eval.drop (0 : Fin 2) (both 0 1 w v) using 1
  funext k; fin_cases k <;> simp [both,single]
lemma push_both_right (w v : List Bool) (b : Bool) :
    Eval (.push (1 : Fin 2) b) (both 0 1 w v) (both 0 1 w (b::v)) 1 := by
  simpa [both] using Eval.push (1 : Fin 2) b (both 0 1 w v)

lemma eval_countRecords (w v : List Bool) : ∃ t≤5*w.length+1,
    Eval countRecords (both 0 1 w v)
      (single 1 (unaryCode (recordCount w)++v)) t := by
  cases w with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simpa [countRecords,both,single,recordCount,unaryCode] using
      (Eval.whileNil (p:=countRecordsBody) (show both (0 : Fin 2) 1 [] v 0=[] by simp [both,single]))
  | cons b w =>
    cases b with
    | false =>
      obtain ⟨t,ht,he⟩ := eval_countRecords w.tail v
      have hb : Eval countRecordsBody (both 0 1 (false::w) v) (both 0 1 w.tail v) 4 :=
        Eval.branchFalse (ls:=w) (by simp [both,single])
          (Eval.seq (drop_both_left (false::w) v) (drop_both_left w v))
      refine ⟨1+4+t,?_,?_⟩
      · simp at ht ⊢; omega
      · simpa only [recordCount_false,countRecords] using Eval.whileCons (by simp [both,single]) hb he
    | true =>
      obtain ⟨t,ht,he⟩ := eval_countRecords w (true::v)
      have hb : Eval countRecordsBody (both 0 1 (true::w) v) (both 0 1 w (true::v)) 4 :=
        Eval.branchTrue (ls:=w) (by simp [both,single])
          (Eval.seq (drop_both_left (true::w) v) (push_both_right w v true))
      have hout : unaryCode (recordCount w)++true::v=unaryCode (recordCount (true::w))++v := by
        simp only [recordCount,unaryCode,List.replicate_add,List.replicate_one,List.append_assoc,
          List.singleton_append]
      rw [hout] at he
      exact ⟨1+4+t,by simp at ht ⊢;omega,Eval.whileCons (by simp [both,single]) hb he⟩
termination_by w.length

namespace Procedure

def listLength {A : Type} (ca : A → List Bool) : Procedure (listCode ca) unaryCode List.length where
  Registers := Fin 2
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 1
  program := countRecords
  bound := 5*TimeBound.variable+1
  correct a := by
    obtain ⟨t,ht,he⟩ := eval_countRecords (listCode ca a) []
    refine ⟨t,by simp;omega,?_⟩
    simpa [both_nil_right (by decide : (0 : Fin 2)≠1),recordCount_listCode] using he
  size a := by
    have hh := length_le_listCode ca a
    simpa only [unaryCode_length,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_variable] using (by omega : a.length≤5*((listCode ca a).length+1)+1)

end Procedure
end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.SignedArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

instance instCodingInt : Coding ℤ := ⟨intCode⟩

lemma difference_bits_length (a b : ℕ) :
    ((a:ℤ)-(b:ℤ)).natAbs.bits.length≤a.bits.length+b.bits.length := by
  have h := Int.natAbs_sub_le (a:ℤ) (b:ℤ)
  simp only [Int.natAbs_natCast] at h
  exact (nat_bits_mono h).trans (add_bits_length a b)

def differenceAbs : Program (Fin 5) := .seq signedDifference (clear 3)
def differenceSign : Program (Fin 5) := .seq signedDifference (clear 0)

lemma eval_difference_base (a b : ℕ) : ∃ t≤100*(a.bits.length+b.bits.length+1),
    Eval signedDifference (both (0 : Fin 5) 1 a.bits b.bits)
      (both 0 3 (((a:ℤ)-(b:ℤ)).natAbs).bits [decide (a<b)]) t := by
  obtain ⟨t,ht,he⟩ := eval_signedDifference (both (0 : Fin 5) 1 a.bits b.bits)
    (by simp [both,single]) (by simp [both,single]) (by simp [both,single])
  have hx : update (update (update (both (0 : Fin 5) 1 a.bits b.bits)
       0 (((a:ℤ)-(b:ℤ)).natAbs).bits) 1 []) 3 [decide (a<b)]=
       both 0 3 (((a:ℤ)-(b:ℤ)).natAbs).bits [decide (a<b)] := by
    funext k; fin_cases k <;> simp [both,single]
  simp only [both_first (by decide : (0 : Fin 5)≠1),both_second,wordValue_bits,hx] at ht he
  exact ⟨t,ht,he⟩

lemma eval_differenceAbs (a b : ℕ) : ∃ t≤200*(a.bits.length+b.bits.length+1),
    Eval differenceAbs (both (0 : Fin 5) 1 a.bits b.bits)
      (single 0 (((a:ℤ)-(b:ℤ)).natAbs).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_difference_base a b
  have hc : Eval (clear (3 : Fin 5))
      (both 0 3 (((a:ℤ)-(b:ℤ)).natAbs).bits [decide (a<b)])
      (single 0 (((a:ℤ)-(b:ℤ)).natAbs).bits) 3 := by
    rw [both_comm (by decide : (0 : Fin 5)≠3)]
    exact eval_clear_both (by decide) _ _
  exact ⟨1+t+3,by omega,Eval.seq he hc⟩

lemma eval_differenceSign (a b : ℕ) : ∃ t≤200*(a.bits.length+b.bits.length+1),
    Eval differenceSign (both (0 : Fin 5) 1 a.bits b.bits)
      (single 3 [decide (a<b)]) t := by
  obtain ⟨t,ht,he⟩ := eval_difference_base a b
  have hc := eval_clear_both (by decide : (0 : Fin 5)≠3)
    (((a:ℤ)-(b:ℤ)).natAbs).bits [decide (a<b)]
  have hl := difference_bits_length a b
  exact ⟨1+t+(2*(((a:ℤ)-(b:ℤ)).natAbs).bits.length+1),by omega,Eval.seq he hc⟩

namespace Procedure

def differenceAbs : Procedure (pairCode Nat.bits Nat.bits) Nat.bits
    (fun a => ((a.1:ℤ)-(a.2:ℤ)).natAbs) :=
  fromBinary StackLanguage.differenceAbs 0 1 0 (by decide) (200*TimeBound.variable)
    (by intro a b; simpa using eval_differenceAbs a b)
    (by intro a b; have h := difference_bits_length a b; simp;omega)

def differenceSign : Procedure (pairCode Nat.bits Nat.bits) boolCode
    (fun a => decide (a.1<a.2)) :=
  fromBinary StackLanguage.differenceSign 0 1 3 (by decide) (200*TimeBound.variable)
    (by intro a b; simpa [boolCode] using eval_differenceSign a b) (by intro a b;simp;omega)

end Procedure
namespace Poly

@[fun_prop] theorem natDifferenceAbs : Poly (fun a : ℕ×ℕ => ((a.1:ℤ)-(a.2:ℤ)).natAbs) :=
  ⟨Procedure.differenceAbs⟩
@[fun_prop] theorem natLt : Poly (fun a : ℕ×ℕ => decide (a.1<a.2)) := ⟨Procedure.differenceSign⟩

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

@[simp] lemma unary_code_length (n : Unary) : (code n).length=n.val := by
  change (unaryCode n.val).length=n.val
  simp
@[simp] lemma nat_code_length (n : ℕ) : (code n).length=n.bits.length := rfl
@[simp] lemma prod_code_length {A B : Type} [Coding A] [Coding B] (a : A×B) :
    (code a).length=2*(code a.1).length+1+(code a.2).length := pairCode_length ..

namespace Procedure

def unaryPred : Procedure unaryCode unaryCode Nat.pred where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .drop ()
  bound := TimeBound.variable+1
  correct a := by
    refine ⟨1,by simp,?_⟩
    have h := Eval.drop () (single () (unaryCode a))
    convert h using 1
    · funext k
      cases k
      simp [single,unaryCode,List.tail_replicate]
  size a := by simp; omega

end Procedure

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

@[simp] lemma int_code_length (a : ℤ) : (code a).length=a.natAbs.bits.length+3 := intCode_length a

end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.DenseDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

@[simp] lemma list_code_length_nil {A : Type} [Coding A] : (code ([] : List A)).length=0 := rfl
@[simp] lemma list_code_cons {A : Type} [Coding A] (a : A) (l : List A) :
    (code (a::l)).length=2*(code a).length+1+(code l).length := by
  change (listCode code (a::l)).length=2*(code a).length+1+(listCode code l).length
  simp

end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.UnaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
open Function

abbrev DivState := Unary×(Unary×Unary)
end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.RationalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

def chooseClean : Program (Fin 18) := .seq Binomial.choose (.seq (clear 14) (clear 15))

lemma eval_chooseClean (n k : ℕ) : ∃ t≤4000000*(n+k+1)^10,
    Eval chooseClean (both (14 : Fin 18) 15 (unaryCode n) (unaryCode k))
      (single 0 (n.choose k).bits) t := by
  obtain ⟨t,ht,he⟩ := Binomial.eval_choose_polynomial n k
  have hin : Binomial.input n k=both (14:Fin 18) 15 (unaryCode n) (unaryCode k) := rfl
  let s := update (Binomial.input n k) 0 (n.choose k).bits
  have e1 := eval_clear (14:Fin 18) s
  have e2 := eval_clear (15:Fin 18) (update s 14 [])
  have hout : update (update s 14 []) 15 []=single 0 (n.choose k).bits := by
    funext j;fin_cases j <;> simp [s,Binomial.input,single]
  rw [hout] at e2
  have hcat := Eval.seq he (Eval.seq e1 e2)
  have hn : (s 14).length=n := by simp [s,Binomial.input]
  have hk : ((update s 14 []) 15).length=k := by simp [s,Binomial.input]
  rw [hn] at e1
  rw [hk] at e2
  refine ⟨1+t+(1+(2*n+1)+(2*k+1)),?_,?_⟩
  · have hp : n+k+1≤(n+k+1)^10 := Nat.le_self_pow (by omega) _
    omega
  · simpa only [chooseClean,hin,hn,hk] using hcat

namespace Procedure

def choose : Procedure (pairCode unaryCode unaryCode) Nat.bits (fun a => a.1.choose a.2) :=
  fromBinary chooseClean 14 15 0 (by decide) (4000000*TimeBound.variable^10)
    (by intro a b;simpa using eval_chooseClean a b)
    (by
      intro n k
      have h := nat_bits_mono (Nat.choose_le_two_pow n k)
      simp only [Nat.size_eq_bits_len,Nat.size_pow] at h
      have hp : n+k+1≤(n+k+1)^10 := Nat.le_self_pow (by omega) _
      simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_pow,
        TimeBound.eval_variable,unaryCode_length,Nat.size_eq_bits_len]
      omega)

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

variable {K : Type} [DecidableEq K]

def unpackInt (a sg : K) : Program K := .seq (.drop a) (.seq (.transfer a sg) (.drop a))

lemma eval_unpackInt {a sg : K} (has : a≠sg) (s : Store K) (z : ℤ) (hz : s a=intCode z) :
    Eval (unpackInt a sg) s (update (update s a z.natAbs.bits) sg (decide (z<0)::s sg)) 5 := by
  have h : s a=false::decide (z<0)::true::z.natAbs.bits := hz
  let u := update s a (decide (z<0)::true::z.natAbs.bits)
  let v := update (update s a (true::z.natAbs.bits)) sg (decide (z<0)::s sg)
  have e1 : Eval (.drop a) s u 1 := by simpa [u,h] using Eval.drop a s
  have e2 : Eval (.transfer a sg) u v 1 := by
    simpa [transfer_cons has u (decide (z<0)) (true::z.natAbs.bits) (by simp [u]),u,v,has.symm] using
      Eval.transfer a sg u
  have e3 : Eval (.drop a) v (update (update s a z.natAbs.bits) sg (decide (z<0)::s sg)) 1 := by
    have he := Eval.drop a v
    convert he using 1
    funext k;by_cases ha : k=a <;> by_cases hs : k=sg <;> simp_all [v]
  exact Eval.seq e1 (Eval.seq e2 e3)

def rationalClean : Program (Fin 16) := .seq (unpackInt 0 12) (.seq (unpackInt 5 13)
  (.seq rationalEncode (.seq (clear 12) (clear 13))))

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

namespace Unary
instance instMul : Mul Unary := ⟨fun a b => ⟨a.val*b.val⟩⟩
end Unary

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.TaylorComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage

abbrev Params := Unary×Unary×Unary×Unary×Unary
namespace Params
abbrev n (p : Params) : ℕ := p.1.val
abbrev N (p : Params) : ℕ := p.2.1.val
abbrev m (p : Params) : ℕ := p.2.2.1.val
abbrev q (p : Params) : ℕ := p.2.2.2.1.val
abbrev H (p : Params) : ℕ := p.2.2.2.2.val

def of (n s : ℕ) : Params :=
  (⟨n⟩,⟨Parameters.N n s⟩,⟨Parameters.M n s⟩,
    ⟨CyclotomicRing.degree (Parameters.exponent n s)⟩,⟨Parameters.H n s⟩)
end Params

namespace Params
def BB (a : Unary) : Unary := ⟨Parameters.B a.val⟩
def DD (a : Unary×Unary) : Unary := ⟨Parameters.delta a.1.val a.2.val⟩
def threshold (a : Unary×Unary) : Unary := BB a.2 * DD a
def MM (a : Unary×Unary) : Unary := ⟨Parameters.M a.1.val a.2.val⟩
def NN (a : Unary×Unary) : Unary := ⟨Parameters.N a.1.val a.2.val⟩
def HH (a : Unary×Unary) : Unary := ⟨Parameters.H a.1.val a.2.val⟩
def QQ (a : Unary×Unary) : Unary := ⟨CyclotomicRing.degree (Parameters.exponent a.1.val a.2.val)⟩
end Params
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.LiftComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open scoped BigOperators
namespace Runtime

abbrev EntryArgs := (Unary×Unary×Unary)×(ℤ×ℤ×ℤ×ℤ)×(Unary×Unary)

end Runtime
end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.MatrixComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
open Function

namespace Procedure

def encodeWord : Procedure _root_.id _root_.id StackLanguage.encodedWord where
  Registers := Fin 4
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 1
  program := StackLanguage.encodeWord
  bound := 15*TimeBound.variable
  correct a := by
    refine ⟨11*a.length+7,by simp;omega,?_⟩
    have hh := eval_encodeWord (single (0:Fin 4) a) (by simp [single]) (by simp [single])
    have hout : update (update (single (0:Fin 4) a) 0 []) 1
        (encodedWord ((single (0:Fin 4) a) 0)++(single (0:Fin 4) a) 1)=
        single 1 (encodedWord a) := by
      funext j;fin_cases j <;> simp [single]
    rw [hout] at hh
    simpa [single] using hh
  size a := by simp [encodedWord];omega
end Procedure

end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.OutputComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

/-- Strip the one literal separator of the required unary input, remembering
its first field in a separate finite stack. -/
def unaryScanBody : Program (Fin 3) :=
  .branch 0 (clear 2) (.seq (.drop 0) (clear 2)) (.transfer 0 1)

def unaryScan : Program (Fin 3) := .loop 2 unaryScanBody

lemma eval_unaryScan (n : ℕ) (w : List Bool) (s : Store (Fin 3))
    (h0 : s 0=List.replicate n true++false::w) (h2 : s 2=[true]) :
    Eval unaryScan s
      (update (update (update s 0 w) 1 (List.replicate n true++s 1)) 2 [])
      (3*n+8) := by
  unfold unaryScan
  induction n generalizing s with
  | zero =>
    have hs : s 0=false::w := by simpa using h0
    have hd := Eval.drop (0:Fin 3) s
    have hc := eval_clear (2:Fin 3) (update s 0 w)
    simp only [update_of_ne (by decide : (2:Fin 3)≠0),h2,List.length_singleton] at hc
    have hb : Eval unaryScanBody s (update (update s 0 w) 2 []) 6 := by
      exact Eval.branchFalse hs (Eval.seq (by simpa [hs] using hd) hc)
    have hl := Eval.whileCons (by simp [h2]) hb
      (Eval.whileNil (p:=unaryScanBody) (by simp : (update (update s 0 w) 2 []) 2=[]))
    have he : update (update (update s 0 w) 1 (List.replicate 0 true++s 1)) 2 []=
        update (update s 0 w) 2 [] := by
      funext j
      fin_cases j <;> simp
    rw [he]
    exact hl
  | succ n ih =>
    let s' := update (update s 0 (List.replicate n true++false::w)) 1 (true::s 1)
    have hs : s 0=true::(List.replicate n true++false::w) := by
      simpa only [List.replicate_succ,List.cons_append] using h0
    have ht : Eval (Program.transfer (0:Fin 3) 1) s s' 1 := by
      simpa only [transfer_cons (by decide : (0:Fin 3)≠1) s true _ hs] using Eval.transfer (0:Fin 3) 1 s
    have hb : Eval unaryScanBody s s' 2 := Eval.branchTrue hs ht
    have hh := ih s' (by simp [s']) (by simp [s',h2])
    have he : update (update (update s' 0 w) 1 (List.replicate n true++s' 1)) 2 []=
        update (update (update s 0 w) 1 (List.replicate (n+1) true++s 1)) 2 [] := by
      funext j
      fin_cases j <;> simp [s',List.replicate_succ',List.append_assoc]
    rw [he] at hh
    have hl := Eval.whileCons (by simp [h2]) hb hh
    convert hl using 1; omega

namespace Procedure

/-- A fixed three-stack parser for the *literal*, unescaped unary input.
Its output is the ordinary typed pair coding used by the closure library. -/
def unaryInput : Procedure
    (fun a : ℕ×ℕ => ExecutableGenerator.unaryWord a.1 a.2)
    (code : Unary×Unary → List Bool) (fun a => (Unary.mk a.1,Unary.mk a.2)) where
  Registers := Fin 3
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 0
  program := .seq (.push 2 true) (.seq unaryScan (prependRecord 1 0 2))
  bound := 20*TimeBound.variable
  correct a := by
    let w := List.replicate a.2 true
    let s := single (0:Fin 3) (ExecutableGenerator.unaryWord a.1 a.2)
    have hi : Eval (Program.push (2:Fin 3) true) s (update s 2 [true]) 1 := by
      simpa [s,single] using Eval.push (2:Fin 3) true s
    have hh := eval_unaryScan a.1 w (update s 2 [true])
      (by simp [s,single,w,ExecutableGenerator.unaryWord]) (by simp)
    have he : update (update (update (update s 2 [true]) 0 w) 1
        (List.replicate a.1 true++(update s 2 [true]) 1)) 2 [] =
        both (1:Fin 3) 0 (List.replicate a.1 true) w := by
      funext j
      fin_cases j <;> simp [s,single,both]
    rw [he] at hh
    have hf := eval_prependRecord_both (a:=(1:Fin 3)) (b:=0) (tmp:=2)
      (by decide) (by decide) (by decide) (List.replicate a.1 true) w
    refine ⟨9*a.1+16,?_,?_⟩
    · simp [ExecutableGenerator.unaryWord];omega
    · have hr := Eval.seq hi (Eval.seq hh hf)
      convert hr using 1 <;> simp [w,code,pairCode,unaryCode]; omega
  size a := by
    change (pairCode unaryCode unaryCode a).length≤_
    simp [ExecutableGenerator.unaryWord,pairCode,unaryCode];omega

end Procedure
end RationalHitting.StackLanguage


end OAI
end


