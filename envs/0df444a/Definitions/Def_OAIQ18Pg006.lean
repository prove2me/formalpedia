-- Prove2me | Definitions.Def_OAIQ18Pg006
-- name    : OAIQ18Pg006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:57:52.96296+00:00
-- url     : https://prove2.me/theorems/acf368a9-9d3e-4091-9efa-0dd2d1072cdb
-- title:
--   Definitions bundle OAIQ18Pg006 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 363 declarations of OpenAI's Lean: 180 definitions and 183 theorems. The definitions and types are `OAI.SourceBurnside.CountLength.program`, `OAI.SourceBurnside.CountLength.store`, `OAI.SourceBurnside.CountLength.work`, `OAI.SourceBurnside.DropPadding.store`, `OAI.SourceBurnside.FiniteSteinbergPresentation.fromSteinberg`, `OAI.SourceBurnside.FiniteSteinbergPresentation.seed`, `OAI.SourceBurnside.FiniteSteinbergPresentation.toSteinberg`, `OAI.SourceBurnside.FiniteTable.Cell.checkerRank`, `OAI.SourceBurnside.HeaderProgram.digit`, `OAI.SourceBurnside.HeaderProgram.digits`, `OAI.SourceBurnside.HeaderProgram.program`, `OAI.SourceBurnside.HeaderProgram.scanPrefix`, `OAI.SourceBurnside.HeaderProgram.step`, `OAI.SourceBurnside.HeaderProgram.store`, `OAI.SourceBurnside.PackFamily.store`, `OAI.SourceBurnside.PadRegister.store`, `OAI.SourceBurnside.RawAssembler.store`, `OAI.SourceBurnside.RawHeader.program`, `OAI.SourceBurnside.RawHeader.readTask`, `OAI.SourceBurnside.RawHeader.store`, `OAI.SourceBurnside.RawNumberPrep.count`, `OAI.SourceBurnside.RawNumberPrep.makeUnary`, `OAI.SourceBurnside.RawNumberPrep.parsed`, `OAI.SourceBurnside.RawNumberPrep.raw`, `OAI.SourceBurnside.RawNumberPrep.readHeader`, `OAI.SourceBurnside.RawNumberPrep.store`, `OAI.SourceBurnside.RawPadSeed.store`, `OAI.SourceBurnside.RawPolynomial.size`, `OAI.SourceBurnside.RawPreparedInputs.inputs`, `OAI.SourceBurnside.RawPreparedInputs.packed`, `OAI.SourceBurnside.SourceMachine.bits`, `OAI.SourceBurnside.SourceMachine.scalars`, `OAI.SourceBurnside.SteinbergQuotient.Quot`, `OAI.SourceBurnside.SteinbergQuotient.fromCoeff`, `OAI.SourceBurnside.SteinbergQuotient.killedIdeal`, `OAI.SourceBurnside.SteinbergQuotient.normal`, `OAI.SourceBurnside.SteinbergQuotient.proj`, `OAI.SourceBurnside.SteinbergQuotient.quotientRoot`, `OAI.SourceBurnside.SteinbergQuotient.rootRelations`, `OAI.SourceBurnside.SteinbergQuotient.toCoeff` and 140 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Algebra_MatrixTests`, `PeriodicGroups_Algebra_WordAlgebra`, `PeriodicGroups_Formulas_PredicateCompilation`, `PeriodicGroups_Machines_ArithmeticDevices`, `PeriodicGroups_Machines_BinaryRegisters`, `PeriodicGroups_Machines_Compilation`, `PeriodicGroups_Machines_InputEncoding`, `PeriodicGroups_Machines_ProgramAssembly`, `PeriodicGroups_Machines_RegisterLoops`, `PeriodicGroups_Machines_RegisterOperators`, `PeriodicGroups_Machines_TapePrograms`, `PeriodicGroups_Rules_TemplateHierarchy`, `PeriodicGroups_Rules_WordRewriting`, `PeriodicGroups_Steinberg_BandFactorization`, `PeriodicGroups_Steinberg_CoefficientQuotients`.
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`; the bundles `OAIQ18Pg000` and `OAIQ18Pg001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ18Pg009` and `OAIQ18Pg011`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg000
import Definitions.Def_OAIQ18Pg001

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_TapePrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.StackMachine
open OneTape
noncomputable section

variable {K Γ Q : Type*} [DecidableEq K]

lemma tape_push (s : K → List Γ) (k : K) (a : Γ) :
    tape (Function.update s k (s k++[a])) =
    Function.update (tape s) ((s k).length+1)
      ⟨false,Function.update (tape s ((s k).length+1)).track k (some a)⟩ := by
  funext j
  by_cases hj : j=(s k).length+1
  · subst j
    have hpos : (0:ℤ)<(s k).length+1 := by omega
    simp only [Function.update_self,tape,show (s k).length+(1:ℤ)≠0 by omega,
      decide_false,ite_eq_left hpos]
    congr 1
    funext i
    by_cases hi : i=k
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  · rw [Function.update_of_ne hj]
    simp only [tape]
    congr 1
    funext i
    by_cases hi : i=k
    · subst i
      simp only [Function.update_self]
      by_cases hpos : 0<j
      · simp only [ite_eq_left hpos]
        by_cases hl : j.toNat-1 < (s k).length
        · exact List.getElem?_append_left hl
        · have hm : (s k).length<j.toNat-1 := by omega
          rw [List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by omega)]
      · simp [hpos]
    · simp [Function.update_of_ne hi]

lemma step_push_write (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K) (a : Γ)
    (q : Q) :
    OneTape.step (compile P) (place s (.pushFind k a q) ((s k).length+1))=
      place (Function.update s k (s k++[a])) (.back q) (s k).length := by
  have hn : (s k).length+(1:ℤ)≠0 := by omega
  simp [OneTape.step,compile,place,tape_track_succ,OneTape.Move.shift,hn,tape_push]

lemma run_push (P : Q → Instr K Γ Q) (C : Config K Γ Q) (k : K) (a : Γ)
    (q : Q) (h : P C.state=.push k a q) :
    OneTape.run (compile P) (encode C) (2*(C.store k).length+3)=
      encode (next P C) := by
  have hs : OneTape.step (compile P) (encode C)=
      place C.store (.pushFind k a q) 1 := by
    simp [OneTape.step,encode,compile,place,h,OneTape.Move.shift]
  rw [show 2*(C.store k).length+3=((C.store k).length+((C.store k).length+2))+1 by omega,
    OneTape.run_succ_start,hs,OneTape.run_from,run_push_scan _ _ _ _ _ _ (by omega),
    OneTape.run_succ_start,step_push_write]
  simpa [next,h,encode] using run_back P (Function.update C.store k (C.store k++[a])) q
    (C.store k).length

lemma tape_pop (s : K → List Γ) (k : K) (hn : 0<(s k).length) :
    tape (Function.update s k (s k).dropLast) =
    Function.update (tape s) (s k).length
      ⟨false,Function.update (tape s (s k).length).track k none⟩ := by
  funext j
  by_cases hj : j=(s k).length
  · subst j
    have hpos : (0:ℤ)<(s k).length := by omega
    simp only [Function.update_self,tape,show (s k).length≠(0:ℤ) by omega,
      decide_false,ite_eq_left hpos,Int.toNat_natCast]
    congr 1
    funext i
    by_cases hi : i=k
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  · rw [Function.update_of_ne hj]
    simp only [tape]
    congr 1
    funext i
    by_cases hi : i=k
    · subst i
      simp only [Function.update_self]
      by_cases hpos : 0<j
      · simp only [ite_eq_left hpos,List.getElem?_dropLast]
        split_ifs with hl
        · rfl
        · symm
          apply List.getElem?_eq_none
          omega
      · simp [hpos]
    · simp [Function.update_of_ne hi]

lemma step_pop_read (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) (hn : 0<(s k).length) :
    OneTape.step (compile P) (place s (.popRead k q) (s k).length)=
      place (Function.update s k (s k).dropLast) (.back (q (s k).getLast?))
        ((s k).length-1:ℕ) := by
  have hnil : s k≠[] := by intro he; simp [he] at hn
  have ht : (tape s (s k).length).track k=(s k).getLast? := by
    simp [tape,List.getLast?_eq_getElem?]
  simp [OneTape.step,compile,place,OneTape.Move.shift,hnil,ht,tape_pop s k hn]
  omega

lemma run_pop (P : Q → Instr K Γ Q) (C : Config K Γ Q) (k : K)
    (q : Option Γ → Q) (h : P C.state=.pop k q) :
    OneTape.run (compile P) (encode C) (2*(C.store k).length+3)=
      encode (next P C) := by
  have hs : OneTape.step (compile P) (encode C)=
      place C.store (.popFind k q) 1 := by
    simp [OneTape.step,encode,compile,place,h,OneTape.Move.shift]
  rw [show 2*(C.store k).length+3=((C.store k).length+((C.store k).length+2))+1 by omega,
    OneTape.run_succ_start,hs,OneTape.run_from,run_pop_scan _ _ _ _ _ (by omega),
    OneTape.run_succ_start,step_pop_turn]
  by_cases hn : 0<(C.store k).length
  · rw [OneTape.run_succ_start,step_pop_read _ _ _ _ hn]
    have he := run_back P (Function.update C.store k (C.store k).dropLast)
      (q (C.store k).getLast?) ((C.store k).length-1)
    simpa [next,h,encode,Nat.sub_add_cancel hn] using he
  · have hz : C.store k=[] := List.length_eq_zero_iff.mp (by omega)
    simp only [hz,List.length_nil,Nat.cast_zero,OneTape.run]
    rw [step_pop_empty]
    have hu := Function.update_eq_self k C.store
    rw [hz] at hu
    simp [encode,next,h,hz,hu]

theorem compile_next (P : Q → Instr K Γ Q) (C : Config K Γ Q) :
    OneTape.run (compile P) (encode C) (ticks P C)=encode (next P C) := by
  cases h : P C.state with
  | halt => simp [ticks,next,h,OneTape.run]
  | push k a q => simpa [ticks,h] using run_push P C k a q h
  | pop k q => simpa [ticks,h] using run_pop P C k q h

theorem compile_exec (P : Q → Instr K Γ Q) (C : Config K Γ Q) (n : ℕ) :
    OneTape.run (compile P) (encode C) (clock P C n)=encode (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clock,OneTape.run_from,ih,compile_next]
    rfl

theorem compile_finish (P : Q → Instr K Γ Q) (C : Config K Γ Q) (n T : ℕ)
    (halted : P (exec P C n).state=.halt) (time : clock P C n≤T) :
    OneTape.run (compile P) (encode C) T=encode (exec P C n) := by
  rw [←Nat.add_sub_of_le time,OneTape.run_from,compile_exec,halt_run _ _ halted]

end
end SourceBurnside.StackMachine

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_BinaryRegisters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

def clear (k : K) : Program K := .loop k (fun _ => .skip)

lemma clear_run (k : K) (r : Store K) :
    Run (clear k) r (2*(r k).length+1) (Function.update r k []) := by
  generalize hv : r k=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update r k []=r := by rw [←hv];exact Function.update_eq_self k r
    rw [he]
    exact Run.loop_nil r k _ hv
  | append_singleton v a ih =>
    have hr : Function.update r k v k=v := Function.update_self ..
    have hh := Run.loop_cons r k (fun _ => Program.skip) v a
      (Function.update r k v) (Function.update (Function.update r k v) k [])
      1 (2*v.length+1) hv (Run.skip _) (ih _ hr)
    convert hh using 1 <;> simp [clear]
    omega

end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Binary.Add
open Program
lemma adder_equation (a b c : Bool) : bit (low a b c)+2*bit (high a b c)=bit a+bit b+bit c := by
  cases a <;> cases b <;> cases c <;> decide

def store (xs ys out : List Bool) (c : Bool) : Store K := ![xs.reverse,ys.reverse,out,[c]]

def fullAdder (a b : Bool) : Program K := .pop 3 (fun z =>
  .seq (.push 2 (low a b (z.getD false))) (.push 3 (high a b (z.getD false))))
def step (a : Bool) : Program K := .pop 1 (fun z => fullAdder a (z.getD false))
def firstPass : Program K := .loop 0 step

def partialStore (xs ys out : List Bool) : Store K := ![xs.reverse,ys.reverse,out,[]]

lemma pop_carry (xs ys out : List Bool) (c : Bool) :
    Function.update (store xs ys out c) 3 []=partialStore xs ys out := by
  funext k;fin_cases k <;> simp [store,partialStore]
lemma fullAdder_push (xs ys out : List Bool) (a b c : Bool) :
    Function.update (Function.update (partialStore xs ys out) 2 (out++[low a b c])) 3
      [high a b c]=store xs ys (out++[low a b c]) (high a b c) := by
  funext k;fin_cases k <;> simp [store,partialStore]

lemma fullAdder_run (xs ys out : List Bool) (a b c : Bool) :
    Run (fullAdder a b) (store xs ys out c) 3 (store xs ys (out++[low a b c]) (high a b c)) := by
  let s := partialStore xs ys out
  let t := Function.update s 2 (out++[low a b c])
  have h1 := Run.push s (2:K) (low a b c)
  have h1' : Run (.push 2 (low a b c)) s 1 t := by simpa [s,t,partialStore] using h1
  have h2 := Run.push t (3:K) (high a b c)
  have h2' : Run (.push 3 (high a b c)) t 1 (store xs ys (out++[low a b c]) (high a b c)) := by
    have hh : t 3=[] := by simp [t,s,partialStore]
    rw [hh,List.nil_append] at h2
    simpa only [t,s,fullAdder_push] using h2
  have hs := Run.seq _ _ s t _ 1 1 h1' h2'
  unfold fullAdder
  refine Run.pop (store xs ys out c) (3:K) _ 2 _ ?_
  change Run (.seq (.push 2 (low a b c)) (.push 3 (high a b c)))
    (Function.update (store xs ys out c) 3 []) 2 _
  rw [pop_carry]
  exact hs

lemma pop_right (xs ys out : List Bool) (c : Bool) :
    Function.update (store xs ys out c) 1 ys.reverse.dropLast=store xs ys.tail out c := by
  funext k;fin_cases k <;> simp [store]
lemma pop_left (a : Bool) (xs ys out : List Bool) (c : Bool) :
    Function.update (store (a::xs) ys out c) 0 xs.reverse=store xs ys out c := by
  funext k;fin_cases k <;> simp [store]

lemma step_run (xs ys out : List Bool) (a c : Bool) :
    Run (step a) (store xs ys out c) 4
      (store xs ys.tail (out++[low a (ys.head?.getD false) c]) (high a (ys.head?.getD false) c)) := by
  unfold step
  refine Run.pop (store xs ys out c) (1:K) _ 3 _ ?_
  change Run (fullAdder a (ys.reverse.getLast?.getD false))
    (Function.update (store xs ys out c) 1 ys.reverse.dropLast) 3 _
  rw [List.getLast?_reverse,pop_right]
  exact fullAdder_run xs ys.tail out a (ys.head?.getD false) c

lemma firstPass_run (xs ys out : List Bool) (c : Bool) :
    Run firstPass (store xs ys out c) (5*xs.length+1)
      (store [] (scan xs ys c).2.1 (out++(scan xs ys c).1) (scan xs ys c).2.2) := by
  induction xs generalizing ys out c with
  | nil => simpa [scan,firstPass] using Run.loop_nil (store [] ys out c) (0:K) step (by rfl)
  | cons a xs ih =>
    let b := ys.head?.getD false
    let last := scan xs ys.tail (high a b c)
    have hb : Run (step a) (Function.update (store (a::xs) ys out c) 0 xs.reverse) 4
        (store xs ys.tail (out++[low a b c]) (high a b c)) := by
      rw [pop_left];exact step_run xs ys out a c
    have ht := ih ys.tail (out++[low a b c]) (high a b c)
    have hh := Run.loop_cons (store (a::xs) ys out c) (0:K) step xs.reverse a _ _
      4 (5*xs.length+1) (by simp [store,List.reverse_cons]) hb ht
    convert hh using 1 <;> simp [firstPass,scan,b,List.append_assoc]
    omega

lemma scan_value (xs ys : List Bool) (c : Bool) :
    value xs+value ys+bit c =
      value (scan xs ys c).1+2^xs.length*(value (scan xs ys c).2.1+bit (scan xs ys c).2.2) := by
  induction xs generalizing ys c with
  | nil => simp [scan,value]
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hh := ih [] (high a false c)
      have hf := adder_equation a false c
      simp only [scan,List.head?_nil,Option.getD_none,List.tail_nil,value,List.length_cons,
        Nat.pow_succ] at *
      change bit (low a false c)+2*bit (high a false c)=bit a+0+bit c at hf
      nlinarith
    | cons b ys =>
      have hh := ih ys (high a b c)
      have hf := adder_equation a b c
      simp only [scan,List.head?_cons,Option.getD_some,List.tail_cons,value,List.length_cons,
        Nat.pow_succ] at *
      nlinarith

lemma value_lt (xs : List Bool) : value xs<2^xs.length := by
  induction xs with
  | nil => simp [value]
  | cons a xs ih => cases a <;> simp [value,bit,Nat.pow_succ] <;> omega

def fixedAdd : Program K := .seq firstPass (Binary.move 2 0)

theorem fixedAdd_run (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length) :
    Run fixedAdd (store xs ys [] c) (7*xs.length+2)
      (store (scan xs ys c).1 [] [] (scan xs ys c).2.2) := by
  let z := (scan xs ys c).1
  let d := (scan xs ys c).2.2
  have he : (scan xs ys c).2.1=[] := by rw [scan_remaining,hlen,List.drop_length]
  have h1 : Run firstPass (store xs ys [] c) (5*xs.length+1) (store [] [] z d) := by
    simpa only [he,List.nil_append,z,d] using firstPass_run xs ys [] c
  have h2 := Binary.move_run (2:K) 0 (by decide) (store [] [] z d)
  have hh : Function.update (Function.update (store [] [] z d) 2 []) 0
      ((store [] [] z d) 0++((store [] [] z d) 2).reverse)=store z [] [] d := by
    funext k;fin_cases k <;> simp [store]
  rw [hh] at h2
  have hz : ((store [] [] z d) 2).length=xs.length := scan_length xs ys c
  rw [hz] at h2
  have H := Run.seq firstPass (Binary.move 2 0) _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

lemma scan_sum (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length) :
    value xs+value ys+bit c=value (scan xs ys c).1+2^xs.length*bit (scan xs ys c).2.2 := by
  have hr : (scan xs ys c).2.1=[] := by rw [scan_remaining,hlen,List.drop_length]
  simpa only [hr,value,Nat.zero_add] using scan_value xs ys c

lemma scan_mod (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length) :
    value (scan xs ys c).1=(value xs+value ys+bit c)%2^xs.length := by
  have hz := value_lt (scan xs ys c).1
  rw [scan_length] at hz
  rw [scan_sum xs ys c hlen,Nat.add_mod]
  simp only [Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt hz]

lemma scan_exact (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length)
    (hbound : value xs+value ys+bit c<2^xs.length) :
    value (scan xs ys c).1=value xs+value ys+bit c ∧ (scan xs ys c).2.2=false := by
  constructor
  · rw [scan_mod xs ys c hlen,Nat.mod_eq_of_lt hbound]
  · have hh := scan_sum xs ys c hlen
    cases he : (scan xs ys c).2.2
    · rfl
    · rw [he] at hh
      change value xs+value ys+bit c=value (scan xs ys c).1+2^xs.length*1 at hh
      omega

end SourceBurnside.Structured.Binary.Add

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

def mapMove (f : Bool → Bool) (src dst : K) : Program K := .loop src (fun b => .push dst (f b))
def mapInPlace (f : Bool → Bool) (src tmp : K) : Program K := .seq (mapMove f src tmp) (move tmp src)

lemma mapMove_run (f : Bool → Bool) (src dst : K) (hne : src≠dst) (r : Store K) :
    Run (mapMove f src dst) r (2*(r src).length+1)
      (Function.update (Function.update r src []) dst (r dst++((r src).reverse.map f))) := by
  generalize hv : r src=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update (Function.update r src []) dst (r dst++(([]:List Bool).reverse.map f))=r := by
      funext k
      by_cases h1 : k=dst
      · subst k;simp
      · by_cases h2 : k=src
        · subst k;simp [hne,hv]
        · simp [h1,h2]
    rw [he]
    exact Run.loop_nil r src _ hv
  | append_singleton v a ih =>
    let r1 := Function.update r src v
    let r2 := Function.update r1 dst (r1 dst++[f a])
    have h2 : r2 src=v := by simp [r2,r1,hne]
    have ht := ih r2 h2
    have hh := Run.loop_cons r src (fun b => Program.push dst (f b)) v a r2
      (Function.update (Function.update r2 src []) dst (r2 dst++v.reverse.map f))
      1 (2*v.length+1) hv (Run.push r1 dst (f a)) ht
    have he : Function.update (Function.update r2 src []) dst (r2 dst++v.reverse.map f)=
        Function.update (Function.update r src []) dst (r dst++((v++[a]).reverse.map f)) := by
      funext k
      by_cases h1 : k=dst
      · subst k;simp [r2,r1,Ne.symm hne,List.reverse_append,List.append_assoc]
      · by_cases h2 : k=src
        · subst k;simp [h1]
        · simp [r2,r1,h1,h2]
    rw [he] at hh
    convert hh using 1 <;> first | rfl | simp;omega

lemma mapInPlace_run (f : Bool → Bool) (src tmp : K) (hne : src≠tmp) (r : Store K) (ht : r tmp=[]) :
    Run (mapInPlace f src tmp) r (4*(r src).length+2)
      (Function.update r src ((r src).map f)) := by
  let s := Function.update (Function.update r src []) tmp ((r src).reverse.map f)
  have h1 : Run (mapMove f src tmp) r (2*(r src).length+1) s := by
    simpa [s,ht] using mapMove_run f src tmp hne r
  have h2 := move_run tmp src (Ne.symm hne) s
  have he : Function.update (Function.update s tmp []) src (s src++(s tmp).reverse)=
      Function.update r src ((r src).map f) := by
    funext k
    by_cases h1 : k=src
    · subst k;simp [s,hne,List.map_reverse]
    · by_cases h2 : k=tmp
      · subst k;simp [h1,ht]
      · simp [s,h1,h2]
  rw [he] at h2
  have hl : (s tmp).length=(r src).length := by simp [s]
  rw [hl] at h2
  have H := Run.seq (mapMove f src tmp) (move tmp src) r s _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured
namespace Program
variable {K L : Type*}
def relabel (f : K → L) : Program K → Program L
  | .skip => .skip
  | .push k b => .push (f k) b
  | .pop k b => .pop (f k) (fun a => relabel f (b a))
  | .seq p q => .seq (relabel f p) (relabel f q)
  | .loop k b => .loop (f k) (fun a => relabel f (b a))
end Program

variable {K L : Type*} [DecidableEq K] [DecidableEq L]
def Agrees (f : K → L) (r : Store K) (R : Store L) := ∀k,R (f k)=r k
def Outside (f : K → L) (R S : Store L) := ∀l,(∀k,f k≠l) → S l=R l

lemma agrees_update (f : K → L) (hf : Function.Injective f) (r : Store K) (R : Store L)
    (h : Agrees f r R) (k : K) (v : List Bool) :
    Agrees f (Function.update r k v) (Function.update R (f k) v) := by
  intro j
  by_cases he : j=k
  · subst j;simp
  · have hh : f j≠f k := fun e => he (hf e)
    simp [he,hh,h j]
omit [DecidableEq K] in
lemma outside_update (f : K → L) (R : Store L) (k : K) (v : List Bool) :
    Outside f R (Function.update R (f k) v) := by
  intro l hl
  exact Function.update_of_ne (Ne.symm (hl k)) v R
omit [DecidableEq K] [DecidableEq L] in
lemma outside_refl (f : K → L) (R : Store L) : Outside f R R := fun _ _ => rfl
omit [DecidableEq K] [DecidableEq L] in
lemma Outside.trans {f : K → L} {R S T : Store L} (h : Outside f R S) (h' : Outside f S T) :
    Outside f R T := fun l hl => (h' l hl).trans (h l hl)

theorem Run.relabel {P : Program K} {r s : Store K} {n : ℕ} (h : Run P r n s)
    (f : K → L) (hf : Function.Injective f) :
    ∀R,Agrees f r R → ∃S,Run (P.relabel f) R n S ∧ Agrees f s S ∧ Outside f R S := by
  induction h with
  | skip r => intro R hR;exact ⟨R,Run.skip R,hR,outside_refl f R⟩
  | push r k b =>
    intro R hR
    refine ⟨Function.update R (f k) (r k++[b]),?_,agrees_update f hf r R hR k _,outside_update f R k _⟩
    simpa only [Program.relabel,hR k] using Run.push R (f k) b
  | pop r k b n s h ih =>
    intro R hR
    obtain ⟨S,hS,ha,ho⟩ := ih (Function.update R (f k) (r k).dropLast)
      (agrees_update f hf r R hR k _)
    refine ⟨S,?_,ha,(outside_update f R k _).trans ho⟩
    unfold Program.relabel
    refine Run.pop R (f k) _ n S ?_
    simpa only [hR k] using hS
  | seq p q r s t n m hp hq ihp ihq =>
    intro R hR
    obtain ⟨S,hS,ha,ho⟩ := ihp R hR
    obtain ⟨T,hT,hb,hp⟩ := ihq S ha
    exact ⟨T,Run.seq _ _ R S T n m hS hT,hb,ho.trans hp⟩
  | loop_nil r k b hr =>
    intro R hR
    exact ⟨R,Run.loop_nil R (f k) _ ((hR k).trans hr),hR,outside_refl f R⟩
  | loop_cons r k b v a s t n m hr hb ht ihb iht =>
    intro R hR
    obtain ⟨S,hS,ha,ho⟩ := ihb (Function.update R (f k) v) (agrees_update f hf r R hR k v)
    obtain ⟨T,hT,hb,hp⟩ := iht S ha
    refine ⟨T,Run.loop_cons R (f k) _ v a S T n m ((hR k).trans hr) hS hT,
      hb,((outside_update f R k v).trans ho).trans hp⟩

end SourceBurnside.Structured

namespace SourceBurnside.Structured.Binary.Add
open Program
lemma complement_value (xs : List Bool) : value xs+value (xs.map not)=2^xs.length-1 := by
  induction xs with
  | nil => simp [value]
  | cons a xs ih =>
    have hp : 0<2^xs.length := by positivity
    cases a <;> simp only [List.map_cons, value, List.length_cons, Bool.not_false, Bool.not_true, bit, Bool.false_eq_true, ↓reduceIte, Nat.pow_succ] at * <;> omega

lemma subtract_equation (xs ys : List Bool) (hlen : xs.length=ys.length) :
    value xs+2^xs.length = value ys+value (scan xs (ys.map not) true).1+
      2^xs.length*bit (scan xs (ys.map not) true).2.2 := by
  have h := scan_sum xs (ys.map not) true (by simp [hlen])
  have hy := complement_value ys
  have hp : 0<2^ys.length := by positivity
  change value xs+value (ys.map not)+1= _ at h
  rw [hlen] at h ⊢
  omega

lemma subtract_carry (xs ys : List Bool) (hlen : xs.length=ys.length) :
    (scan xs (ys.map not) true).2.2=true ↔ value ys≤value xs := by
  have hh := subtract_equation xs ys hlen
  have hz := value_lt (scan xs (ys.map not) true).1
  rw [scan_length] at hz
  cases he : (scan xs (ys.map not) true).2.2 <;>
    simp [he,bit] at hh <;> simp <;> omega

lemma subtract_exact (xs ys : List Bool) (hlen : xs.length=ys.length) (hle : value ys≤value xs) :
    value (scan xs (ys.map not) true).1=value xs-value ys := by
  have hh := subtract_equation xs ys hlen
  rw [(subtract_carry xs ys hlen).mpr hle] at hh
  simp only [bit,ite_true,Nat.mul_one] at hh
  omega

def fixedSubtract : Program K := .seq (Binary.mapInPlace not 1 2) fixedAdd

theorem fixedSubtract_run (xs ys : List Bool) (hlen : xs.length=ys.length) :
    Run fixedSubtract (store xs ys [] true) (11*xs.length+4)
      (store (scan xs (ys.map not) true).1 [] [] (scan xs (ys.map not) true).2.2) := by
  have h1 := Binary.mapInPlace_run not (1:K) 2 (by decide) (store xs ys [] true) (by rfl)
  have he : Function.update (store xs ys [] true) 1 ((store xs ys [] true 1).map not)=
      store xs (ys.map not) [] true := by
    funext k;fin_cases k <;> simp [store,List.map_reverse]
  rw [he] at h1
  have hl : (store xs ys [] true 1).length=xs.length := by simp [store,hlen]
  rw [hl] at h1
  have h2 := fixedAdd_run xs (ys.map not) true (by simp [hlen])
  have H := Run.seq (Binary.mapInPlace not 1 2) fixedAdd _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

end SourceBurnside.Structured.Binary.Add

namespace SourceBurnside.Structured
open Program
variable {K L : Type*} [DecidableEq K] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
lemma agrees_outside_unique (f : K → L) (R S T : Store L) (s : Store K)
    (hS : Agrees f s S) (hT : Agrees f s T) (oS : Outside f R S) (oT : Outside f R T) : S=T := by
  funext l
  by_cases h : ∃k,f k=l
  · obtain ⟨k,rfl⟩ := h
    exact (hS k).trans (hT k).symm
  · have hn : ∀k,f k≠l := by simpa using h
    exact (oS l hn).trans (oT l hn).symm

lemma Run.relabel_to {P : Program K} {r s : Store K} {n : ℕ} (h : Run P r n s)
    (f : K → L) (hf : Function.Injective f) (R S : Store L)
    (ha : Agrees f r R) (hb : Agrees f s S) (ho : Outside f R S) :
    Run (P.relabel f) R n S := by
  obtain ⟨T,hT,hb',ho'⟩ := h.relabel f hf R ha
  rwa [agrees_outside_unique f R T S s hb' hb ho' ho] at hT

namespace Binary

def patch4 (f : Fin 4 → K) (r : Store K) (s : Store (Fin 4)) : Store K :=
  Function.update (Function.update (Function.update (Function.update r (f 0) (s 0)) (f 1) (s 1))
    (f 2) (s 2)) (f 3) (s 3)

lemma patch4_agrees (f : Fin 4 → K) (hf : Function.Injective f) (r : Store K) (s : Store (Fin 4)) :
    Agrees f s (patch4 f r s) := by
  intro k
  have hi : ∀i j : Fin 4, i≠j → f i≠f j := fun _ _ h => hf.ne h
  fin_cases k <;> simp [patch4,hi]

lemma patch4_outside (f : Fin 4 → K) (r : Store K) (s : Store (Fin 4)) :
    Outside f r (patch4 f r s) := by
  intro k hk
  simp [patch4,Ne.symm (hk 0),Ne.symm (hk 1),Ne.symm (hk 2),Ne.symm (hk 3)]

lemma patch4_run {P : Program (Fin 4)} {r s : Store (Fin 4)} {n : ℕ} (h : Run P r n s)
    (f : Fin 4 → K) (hf : Function.Injective f) (R : Store K) (ha : Agrees f r R) :
    Run (P.relabel f) R n (patch4 f R s) :=
  h.relabel_to f hf R _ ha (patch4_agrees f hf R s) (patch4_outside f R s)

lemma fixedAdd_call (f : Fin 4 → K) (hf : Function.Injective f) (R : Store K)
    (xs ys : List Bool) (c : Bool) (hlen : xs.length=ys.length)
    (ha : Agrees f (Add.store xs ys [] c) R) :
    Run (Add.fixedAdd.relabel f) R (7*xs.length+2)
      (patch4 f R (Add.store (Add.scan xs ys c).1 [] [] (Add.scan xs ys c).2.2)) :=
  patch4_run (Add.fixedAdd_run xs ys c hlen) f hf R ha

end Binary
end SourceBurnside.Structured

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

def dropFront (src tmp : K) : Program K :=
  .seq (move src tmp) (.pop tmp (fun _ => move tmp src))
def shift (src tmp : K) : Program K := .seq (dropFront src tmp) (.push src false)

lemma dropFront_run (src tmp : K) (hne : src≠tmp) (r : Store K) (ht : r tmp=[]) :
    Run (dropFront src tmp) r (2*(r src).length+2*(r src).tail.length+3)
      (Function.update r src (r src).tail) := by
  let s := Function.update (Function.update r src []) tmp (r src).reverse
  let s' := Function.update s tmp (r src).reverse.dropLast
  have h1 : Run (move src tmp) r (2*(r src).length+1) s := by
    simpa [s,ht] using move_run src tmp hne r
  have h2 := move_run tmp src (Ne.symm hne) s'
  have he : Function.update (Function.update s' tmp []) src (s' src++(s' tmp).reverse)=
      Function.update r src (r src).tail := by
    funext k
    by_cases hk : k=src
    · subst k;simp [s',s,hne]
    · by_cases hkt : k=tmp
      · subst k;simp [s',s,ht,hk]
      · simp [s',s,hk,hkt]
  rw [he] at h2
  have hl : (s' tmp).length=(r src).tail.length := by simp [s',List.length_tail]
  rw [hl] at h2
  have h2' : Run (.pop tmp (fun _ => move tmp src)) s (1+(2*(r src).tail.length+1))
      (Function.update r src (r src).tail) := by
    refine Run.pop s tmp _ _ _ ?_
    simpa only [s',s,Function.update_self] using h2
  have H := Run.seq (move src tmp) (.pop tmp (fun _ => move tmp src)) _ _ _ _ _ h1 h2'
  convert H using 1 <;> first | rfl | omega

lemma shift_run (src tmp : K) (hne : src≠tmp) (r : Store K) (ht : r tmp=[])
    (hx : r src≠[]) :
    Run (shift src tmp) r (4*(r src).length+2)
      (Function.update r src ((r src).tail++[false])) := by
  have h1 := dropFront_run src tmp hne r ht
  have h2 := Run.push (Function.update r src (r src).tail) src false
  simp only [Function.update_self,Function.update_idem] at h2
  have H := Run.seq (dropFront src tmp) (.push src false) _ _ _ _ _ h1 h2
  have hn : 0<(r src).length := List.length_pos_iff.mpr hx
  have hl := List.length_tail (l:=r src)
  convert H using 1 <;> first | rfl | omega

namespace Add

lemma double_value (xs : List Bool) (hx : xs≠[]) :
    value (double xs)=(2*value xs)%2^xs.length := by
  induction xs using List.reverseRecOn with
  | nil => exact False.elim (hx rfl)
  | append_singleton xs a ih =>
    have hval : value (double (xs++[a]))=2*value xs := by simp [double,value,bit]
    rw [hval,value_append]
    have he : 2*(value xs+2^xs.length*value [a])=2*value xs+2^(xs++[a]).length*value [a] := by
      simp [Nat.pow_succ];ring
    rw [he,Nat.add_mod]
    have hb : 2*value xs<2^(xs++[a]).length := by
      have hv := value_lt xs
      simp [Nat.pow_succ];omega
    simp only [Nat.mul_mod_right, Nat.add_zero, Nat.mod_eq_of_lt hb]

end Add
end SourceBurnside.Structured.Binary

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_ArithmeticDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary.Multiply
open Program

def store (acc x y : List Bool) : Store K := ![acc.reverse,x.reverse,y.reverse,[],[],[]]

def addX : Program K :=
  .seq (copy 1 3 4) (.seq (.push 5 false) (.seq (Add.fixedAdd.relabel regs) (clear 5)))

def addStore (acc x y : List Bool) (c : List Bool) : Store K := ![acc.reverse,x.reverse,y.reverse,x.reverse,[],c]
def carryStore (acc x y : List Bool) (c : Bool) : Store K := ![acc.reverse,x.reverse,y.reverse,[],[],[c]]

lemma addX_run (acc x y : List Bool) (hlen : acc.length=x.length) :
    Run addX (store acc x y) (12*x.length+8) (store (Add.scan acc x false).1 x y) := by
  have h1 := copy_run (1:K) 3 4 (by decide) (by decide) (by decide) (store acc x y) (by rfl)
  have he1 : Function.update (store acc x y) 3 ((store acc x y) 3++(store acc x y) 1)=
      addStore acc x y [] := by funext k;fin_cases k <;> simp [store,addStore]
  rw [he1] at h1
  have hl1 : (store acc x y 1).length=x.length := by simp [store]
  rw [hl1] at h1
  have h2 := Run.push (addStore acc x y []) (5:K) false
  have he2 : Function.update (addStore acc x y []) 5 ((addStore acc x y []) 5++[false])=
      addStore acc x y [false] := by funext k;fin_cases k <;> simp [addStore]
  rw [he2] at h2
  let z := (Add.scan acc x false).1
  let c := (Add.scan acc x false).2.2
  have h3 := fixedAdd_call regs regs_injective (addStore acc x y [false]) acc x false hlen (by
    intro k;fin_cases k <;> rfl)
  have he3 : patch4 regs (addStore acc x y [false]) (Add.store z [] [] c)=carryStore z x y c := by
    funext k;fin_cases k <;> simp [patch4,regs,Add.store,carryStore,addStore]
  rw [he3,hlen] at h3
  have h4 := clear_run (5:K) (carryStore z x y c)
  have he4 : Function.update (carryStore z x y c) 5 []=store z x y := by
    funext k;fin_cases k <;> simp [carryStore,store]
  rw [he4] at h4
  change Run (clear (5:K)) (carryStore z x y c) 3 (store z x y) at h4
  have H := Run.seq (copy 1 3 4) _ _ _ _ _ _ h1
    (Run.seq (.push 5 false) _ _ _ _ _ _ h2
    (Run.seq (Add.fixedAdd.relabel regs) (clear 5) _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | omega

def step (b : Bool) : Program K := .seq (if b then addX else .skip) (shift 1 4)

lemma step_run (b : Bool) (acc x y : List Bool) (hlen : acc.length=x.length) (hx : x≠[]) :
    Run (step b) (store acc x y) (stepCost b x.length) (store (plusIf b acc x) (Add.double x) y) := by
  have h1 : Run (if b then addX else .skip) (store acc x y)
      (if b then 12*x.length+8 else 1) (store (plusIf b acc x) x y) := by
    cases b
    · exact Run.skip _
    · exact addX_run acc x y hlen
  have h2 := shift_run (1:K) 4 (by decide) (store (plusIf b acc x) x y) (by rfl)
    (by simpa [store] using hx)
  have he2 : Function.update (store (plusIf b acc x) x y) 1
      ((store (plusIf b acc x) x y 1).tail++[false])=store (plusIf b acc x) (Add.double x) y := by
    funext k;fin_cases k <;> simp [store,Add.double_reverse]
  rw [he2] at h2
  have hl : (store (plusIf b acc x) x y 1).length=x.length := by simp [store]
  rw [hl] at h2
  have H := Run.seq (if b then addX else .skip) (shift 1 4) _ _ _ _ _ h1 h2
  cases b <;> convert H using 1 <;> first | rfl | simp [stepCost];omega

def program : Program K := .loop 2 step

lemma program_run (acc x y : List Bool) (hx : x≠[]) (hlen : acc.length=x.length) :
    Run program (store acc x y) (time x.length y) (store (scan acc x y).1 (scan acc x y).2 []) := by
  induction y generalizing acc x with
  | nil => exact Run.loop_nil (store acc x []) (2:K) step (by rfl)
  | cons b ys ih =>
    have hp := plusIf_length b acc x
    have hd := Add.double_length x hx
    have ht := ih (plusIf b acc x) (Add.double x) (by simp [Add.double]) (by omega)
    have hs := step_run b acc x ys hlen hx
    have he : Function.update (store acc x (b::ys)) 2 ys.reverse=store acc x ys := by
      funext k;fin_cases k <;> simp [store]
    have hb : Run (step b) (Function.update (store acc x (b::ys)) 2 ys.reverse) (stepCost b x.length)
        (store (plusIf b acc x) (Add.double x) ys) := by rw [he];exact hs
    rw [hd] at ht
    have H := Run.loop_cons (store acc x (b::ys)) (2:K) step ys.reverse b _ _ _ _
      (by simp [store,List.reverse_cons]) hb ht
    convert H using 1 <;> first | rfl | simp [time];omega

lemma time_bound (n : ℕ) (ys : List Bool) : time n ys≤ys.length*(16*n+11)+1 := by
  induction ys with
  | nil => simp [time]
  | cons b ys ih => cases b <;> simp [time,stepCost] <;> nlinarith

lemma plusIf_modEq (b : Bool) (acc x : List Bool) (hlen : acc.length=x.length) :
    Nat.ModEq (2^x.length) (Add.value (plusIf b acc x)) (Add.value acc+Add.bit b*Add.value x) := by
  cases b
  · simp only [plusIf,Bool.false_eq_true,↓reduceIte,Add.bit,Nat.zero_mul,Nat.add_zero]
    exact Nat.ModEq.rfl
  · simp only [plusIf,↓reduceIte,Add.bit,Nat.one_mul]
    rw [Add.scan_mod acc x false hlen]
    simp only [Add.bit,Bool.false_eq_true,↓reduceIte,Nat.add_zero,hlen]
    exact Nat.mod_modEq _ _

lemma scan_modEq (acc x y : List Bool) (hx : x≠[]) (hlen : acc.length=x.length) :
    Nat.ModEq (2^x.length) (Add.value (scan acc x y).1) (Add.value acc+Add.value x*Add.value y) := by
  induction y generalizing acc x with
  | nil => simp [scan,Add.value,Nat.ModEq]
  | cons b ys ih =>
    have hp := plusIf_length b acc x
    have hd := Add.double_length x hx
    have hi := ih (plusIf b acc x) (Add.double x) (by simp [Add.double]) (by omega)
    rw [hd] at hi
    have hxmod : Nat.ModEq (2^x.length) (Add.value (Add.double x)) (2*Add.value x) := by
      rw [Add.double_value x hx];exact Nat.mod_modEq _ _
    have hm := (plusIf_modEq b acc x hlen).add (hxmod.mul_right (Add.value ys))
    have he : Add.value acc+Add.bit b*Add.value x+2*Add.value x*Add.value ys=
        Add.value acc+Add.value x*Add.value (b::ys) := by simp only [Add.value];ring
    rw [he] at hm
    exact hi.trans hm

lemma scan_value (acc x y : List Bool) (hx : x≠[]) (hlen : acc.length=x.length) :
    Add.value (scan acc x y).1=(Add.value acc+Add.value x*Add.value y)%2^x.length := by
  have h := scan_modEq acc x y hx hlen
  change Add.value (scan acc x y).1%2^x.length=_ at h
  have hb := Add.value_lt (scan acc x y).1
  rw [(scan_length acc x y hx hlen).1,hlen] at hb
  rwa [Nat.mod_eq_of_lt hb] at h

end SourceBurnside.Structured.Binary.Multiply

namespace SourceBurnside.Structured.Binary
open Program

def roll {K : Type*} (src tmp : K) (b : Bool) : Program K := .seq (dropFront src tmp) (.push src b)
lemma roll_run {K : Type*} [DecidableEq K] (src tmp : K) (hne : src≠tmp) (b : Bool)
    (r : Store K) (ht : r tmp=[]) (hx : r src≠[]) :
    Run (roll src tmp b) r (4*(r src).length+2)
      (Function.update r src ((r src).tail++[b])) := by
  have h1 := dropFront_run src tmp hne r ht
  have h2 := Run.push (Function.update r src (r src).tail) src b
  simp only [Function.update_self,Function.update_idem] at h2
  have H := Run.seq (dropFront src tmp) (.push src b) _ _ _ _ _ h1 h2
  have hn : 0<(r src).length := List.length_pos_iff.mpr hx
  have hl := List.length_tail (l:=r src)
  convert H using 1 <;> first | rfl | omega

lemma rollBits_value (b : Bool) (xs : List Bool) (hx : xs≠[]) :
    Add.value (rollBits b xs)=(2*Add.value xs+Add.bit b)%2^xs.length := by
  induction xs using List.reverseRecOn with
  | nil => exact False.elim (hx rfl)
  | append_singleton xs a ih =>
    have hval : Add.value (rollBits b (xs++[a]))=2*Add.value xs+Add.bit b := by
      simp [rollBits,Add.value];omega
    rw [hval,Add.value_append]
    have he : 2*(Add.value xs+2^xs.length*Add.value [a])+Add.bit b=
        (2*Add.value xs+Add.bit b)+2^(xs++[a]).length*Add.value [a] := by
      simp [Nat.pow_succ];ring
    rw [he,Nat.add_mod]
    have hb : 2*Add.value xs+Add.bit b<2^(xs++[a]).length := by
      have hv := Add.value_lt xs
      cases b <;> simp [Nat.pow_succ,Add.bit] <;> omega
    simp only [Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt hb]

namespace Divide

def store (q r d ys : List Bool) : Store K := ![q.reverse,r.reverse,d.reverse,ys.reverse,[],[],[],[]]
def scratchStore (q r d ys v w c : List Bool) : Store K :=
  ![q.reverse,r.reverse,d.reverse,ys.reverse,v.reverse,w.reverse,[],c]
def trialStore (q r d ys z : List Bool) (c : Bool) : Store K :=
  scratchStore q r d ys z [] [c]

def choose (c : Bool) : Program K :=
  .seq (if c then .seq (clear 1) (copy 4 1 6) else .skip)
    (.seq (clear 4) (roll 0 6 c))

lemma choose_run (q r d ys z : List Bool) (c : Bool)
    (hqr : q.length=r.length) (hz : z.length=r.length) (hr : r≠[]) :
    Run (choose c) (scratchStore q r d ys z [] []) (chooseTime c r.length)
      (store (rollBits c q) (if c then z else r) d ys) := by
  let s := scratchStore q (if c then z else r) d ys z [] []
  have h1 : Run (if c then .seq (clear 1) (copy 4 1 6) else .skip)
      (scratchStore q r d ys z [] []) (if c then 7*r.length+3 else 1) s := by
    cases c
    · exact Run.skip _
    · change Run _ _ (7*r.length+3) s
      have ha := clear_run (1:K) (scratchStore q r d ys z [] [])
      let a := scratchStore q [] d ys z [] []
      have he : Function.update (scratchStore q r d ys z [] []) 1 []=a := by
        funext k;fin_cases k <;> simp [a,scratchStore]
      rw [he] at ha
      have hl : (scratchStore q r d ys z [] [] 1).length=r.length := by simp [scratchStore]
      rw [hl] at ha
      have hb := copy_run (4:K) 1 6 (by decide) (by decide) (by decide) a (by rfl)
      have he' : Function.update a 1 (a 1++a 4)=s := by
        funext k;fin_cases k <;> simp [a,s,scratchStore]
      rw [he'] at hb
      have hl' : (a 4).length=r.length := by simp [a,scratchStore,hz]
      rw [hl'] at hb
      have H := Run.seq (clear 1) (copy 4 1 6) _ _ _ _ _ ha hb
      convert H using 1 <;> first | rfl | omega
  have h2 := clear_run (4:K) s
  have he2 : Function.update s 4 []=store q (if c then z else r) d ys := by
    funext k;fin_cases k <;> simp [s,scratchStore,store]
  rw [he2] at h2
  have hl2 : (s 4).length=r.length := by simp [s,scratchStore,hz]
  rw [hl2] at h2
  have hqn : q≠[] := by intro he;have hn := List.length_pos_iff.mpr hr;simp [he] at hqr;omega
  have h3 := roll_run (0:K) 6 (by decide) c (store q (if c then z else r) d ys) (by rfl)
    (by simpa [store] using hqn)
  have he3 : Function.update (store q (if c then z else r) d ys) 0
      ((store q (if c then z else r) d ys 0).tail++[c])=
      store (rollBits c q) (if c then z else r) d ys := by
    funext k;fin_cases k <;> simp [store,rollBits_reverse]
  rw [he3] at h3
  have hl3 : (store q (if c then z else r) d ys 0).length=r.length := by simp [store,hqr]
  rw [hl3] at h3
  have H := Run.seq (if c then .seq (clear 1) (copy 4 1 6) else .skip) _ _ _ _ _ _ h1
    (Run.seq (clear 4) (roll 0 6 c) _ _ _ _ _ h2 h3)
  cases c <;> convert H using 1 <;> first | rfl | simp [chooseTime];omega

def makeTrial : Program K := .seq (copy 1 4 6) (.seq (copy 2 5 6)
  (.seq (.push 7 true) (Add.fixedSubtract.relabel regs)))

lemma makeTrial_run (q r d ys : List Bool) (hrd : r.length=d.length) :
    Run makeTrial (store q r d ys) (21*r.length+9)
      (trialStore q r d ys (trial r d).1 (carry r d)) := by
  have h1 := copy_run (1:K) 4 6 (by decide) (by decide) (by decide) (store q r d ys) (by rfl)
  have he1 : Function.update (store q r d ys) 4 ((store q r d ys) 4++(store q r d ys) 1)=
      scratchStore q r d ys r [] [] := by funext k;fin_cases k <;> simp [store,scratchStore]
  rw [he1] at h1
  have hl1 : (store q r d ys 1).length=r.length := by simp [store]
  rw [hl1] at h1
  have h2 := copy_run (2:K) 5 6 (by decide) (by decide) (by decide)
    (scratchStore q r d ys r [] []) (by rfl)
  have he2 : Function.update (scratchStore q r d ys r [] []) 5
      ((scratchStore q r d ys r [] []) 5++(scratchStore q r d ys r [] []) 2)=
      scratchStore q r d ys r d [] := by funext k;fin_cases k <;> simp [scratchStore]
  rw [he2] at h2
  have hl2 : (scratchStore q r d ys r [] [] 2).length=r.length := by simp [scratchStore,hrd]
  rw [hl2] at h2
  have h3 := Run.push (scratchStore q r d ys r d []) (7:K) true
  have he3 : Function.update (scratchStore q r d ys r d []) 7
      ((scratchStore q r d ys r d []) 7++[true])=scratchStore q r d ys r d [true] := by
    funext k;fin_cases k <;> simp [scratchStore]
  rw [he3] at h3
  have h4 := patch4_run (Add.fixedSubtract_run r d hrd) regs regs_injective
    (scratchStore q r d ys r d [true]) (by intro k;fin_cases k <;> rfl)
  have he4 : patch4 regs (scratchStore q r d ys r d [true])
      (Add.store (Add.scan r (d.map not) true).1 [] [] (Add.scan r (d.map not) true).2.2)=
      trialStore q r d ys (trial r d).1 (carry r d) := by
    funext k;fin_cases k <;> simp [patch4,regs,Add.store,trialStore,scratchStore,trial,carry]
  rw [he4] at h4
  have H := Run.seq (copy 1 4 6) _ _ _ _ _ _ h1
    (Run.seq (copy 2 5 6) _ _ _ _ _ _ h2
    (Run.seq (.push 7 true) (Add.fixedSubtract.relabel regs) _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | omega

def step (b : Bool) : Program K := .seq (roll 1 6 b)
  (.seq makeTrial (.pop 7 (fun c => choose (c.getD false))))

lemma step_run (b : Bool) (q r d ys : List Bool) (hqr : q.length=r.length)
    (hrd : r.length=d.length) (hr : r≠[]) :
    Run (step b) (store q r d ys) (stepTime b r d)
      (store (oneStep b q r d).1 (oneStep b q r d).2 d ys) := by
  let r' := rollBits b r
  have hrlen : r'.length=r.length := rollBits_length b r hr
  have hr'n : r'≠[] := by simp [r',rollBits]
  have h1 := roll_run (1:K) 6 (by decide) b (store q r d ys) (by rfl)
    (by simpa [store] using hr)
  have he1 : Function.update (store q r d ys) 1 ((store q r d ys 1).tail++[b])=store q r' d ys := by
    funext k;fin_cases k <;> simp [store,r',rollBits_reverse]
  rw [he1] at h1
  have hl1 : (store q r d ys 1).length=r.length := by simp [store]
  rw [hl1] at h1
  have h2 := makeTrial_run q r' d ys (hrlen.trans hrd)
  let c := carry r' d
  let z := (trial r' d).1
  have hz : z.length=r'.length := Add.scan_length r' (d.map not) true
  have h3 := choose_run q r' d ys z c (hqr.trans hrlen.symm) hz hr'n
  have he3 : Function.update (trialStore q r' d ys z c) 7
      ((trialStore q r' d ys z c) 7).dropLast=scratchStore q r' d ys z [] [] := by
    funext k;fin_cases k <;> simp [trialStore,scratchStore]
  have h3' : Run (.pop 7 (fun c => choose (c.getD false))) (trialStore q r' d ys z c)
      (1+chooseTime c r'.length) (store (rollBits c q) (if c then z else r') d ys) := by
    refine Run.pop _ (7:K) _ _ _ ?_
    change Run (choose c) _ _ _
    rw [he3];exact h3
  have H := Run.seq (roll 1 6 b) _ _ _ _ _ _ h1
    (Run.seq makeTrial (.pop 7 (fun c => choose (c.getD false))) _ _ _ _ _ h2 h3')
  rw [hrlen] at H
  convert H using 1 <;> first | rfl | simp [stepTime,r',c];omega

def scan (q r d : List Bool) : List Bool → List Bool × List Bool
  | [] => (q,r)
  | b::ys => scan (oneStep b q r d).1 (oneStep b q r d).2 d ys

def time (q r d : List Bool) : List Bool → ℕ
  | [] => 1
  | b::ys => 1+stepTime b r d+time (oneStep b q r d).1 (oneStep b q r d).2 d ys

def program : Program K := .loop 3 step

lemma scan_lengths (q r d ys : List Bool) (hqr : q.length=r.length) (hr : r≠[]) :
    (scan q r d ys).1.length=q.length ∧ (scan q r d ys).2.length=r.length := by
  induction ys generalizing q r with
  | nil => exact ⟨rfl,rfl⟩
  | cons b ys ih =>
    have h := oneStep_lengths b q r d hqr hr
    have hn : (oneStep b q r d).2≠[] := by
      intro he;have hp := List.length_pos_iff.mpr hr;simp [he] at h;omega
    have hh := ih (oneStep b q r d).1 (oneStep b q r d).2 (by omega) hn
    exact ⟨hh.1.trans h.1,hh.2.trans h.2⟩

lemma program_run (q r d ys : List Bool) (hqr : q.length=r.length)
    (hrd : r.length=d.length) (hr : r≠[]) :
    Run program (store q r d ys) (time q r d ys) (store (scan q r d ys).1 (scan q r d ys).2 d []) := by
  induction ys generalizing q r with
  | nil => exact Run.loop_nil (store q r d []) (3:K) step (by rfl)
  | cons b ys ih =>
    have h := oneStep_lengths b q r d hqr hr
    have hn : (oneStep b q r d).2≠[] := by
      intro he;have hp := List.length_pos_iff.mpr hr;simp [he] at h;omega
    have ht := ih (oneStep b q r d).1 (oneStep b q r d).2 (by omega) (h.2.trans hrd) hn
    have hs := step_run b q r d ys hqr hrd hr
    have he : Function.update (store q r d (b::ys)) 3 ys.reverse=store q r d ys := by
      funext k;fin_cases k <;> simp [store]
    have hb : Run (step b) (Function.update (store q r d (b::ys)) 3 ys.reverse) (stepTime b r d)
        (store (oneStep b q r d).1 (oneStep b q r d).2 d ys) := by rw [he];exact hs
    have H := Run.loop_cons (store q r d (b::ys)) (3:K) step ys.reverse b _ _ _ _
      (by simp [store,List.reverse_cons]) hb ht
    convert H using 1 <;> first | rfl | simp [time];omega

lemma time_bound (q r d ys : List Bool) (hqr : q.length=r.length) (hr : r≠[]) :
    time q r d ys≤ys.length*(38*r.length+19)+1 := by
  induction ys generalizing q r with
  | nil => simp [time]
  | cons b ys ih =>
    have h := oneStep_lengths b q r d hqr hr
    have hn : (oneStep b q r d).2≠[] := by
      intro he;have hp := List.length_pos_iff.mpr hr;simp [he] at h;omega
    have hh := ih (oneStep b q r d).1 (oneStep b q r d).2 (by omega) hn
    have hs : stepTime b r d≤38*r.length+18 := by
      unfold stepTime chooseTime;split <;> omega
    rw [h.2] at hh
    simp only [time,List.length_cons]
    nlinarith

lemma oneStep_value (b : Bool) (q r d : List Bool) (hqr : q.length=r.length)
    (hrd : r.length=d.length) (hr : r≠[]) (hd : 0<Add.value d)
    (_hds : 2*Add.value d≤2^r.length) (hrem : Add.value r<Add.value d)
    (hbound : 2*(Add.value q*Add.value d+Add.value r)+Add.bit b<2^r.length) :
    Add.value (oneStep b q r d).1*Add.value d+Add.value (oneStep b q r d).2=
      2*(Add.value q*Add.value d+Add.value r)+Add.bit b ∧
    Add.value (oneStep b q r d).2<Add.value d := by
  let r' := rollBits b r
  let c := carry r' d
  let z := if c then (trial r' d).1 else r'
  have hrlen : r'.length=d.length := (rollBits_length b r hr).trans hrd
  have hb : Add.bit b≤1 := by cases b <;> decide
  have hrb : 2*Add.value r+Add.bit b<2^r.length := by omega
  have hrv : Add.value r'=2*Add.value r+Add.bit b := by
    rw [rollBits_value b r hr,Nat.mod_eq_of_lt hrb]
  have hc : c=true ↔ Add.value d≤Add.value r' := Add.subtract_carry r' d hrlen
  have hz : Add.value z+Add.bit c*Add.value d=Add.value r' ∧ Add.value z<Add.value d := by
    cases he : c
    · have hn : Add.value r'<Add.value d := by rw [he] at hc;simp at hc;omega
      simp only [z,he,Bool.false_eq_true,↓reduceIte,Add.bit,Nat.zero_mul,Nat.add_zero]
      exact ⟨trivial,hn⟩
    · have hn : Add.value d≤Add.value r' := hc.mp he
      have hv := Add.subtract_exact r' d hrlen hn
      change Add.value (trial r' d).1=Add.value r'-Add.value d at hv
      simp only [z,he,↓reduceIte,Add.bit,Nat.one_mul]
      rw [hv]
      constructor <;> omega
  have hbalance : (2*Add.value q+Add.bit c)*Add.value d+Add.value z=
      2*(Add.value q*Add.value d+Add.value r)+Add.bit b := by nlinarith [hz.1]
  have hqb : 2*Add.value q+Add.bit c<2^r.length := by
    have hh : 2*Add.value q+Add.bit c≤(2*Add.value q+Add.bit c)*Add.value d := by
      exact Nat.le_mul_of_pos_right _ hd
    omega
  have hqn : q≠[] := by intro he;have hn := List.length_pos_iff.mpr hr;simp [he] at hqr;omega
  have hqv : Add.value (rollBits c q)=2*Add.value q+Add.bit c := by
    rw [rollBits_value c q hqn,hqr,Nat.mod_eq_of_lt hqb]
  change Add.value (rollBits c q)*Add.value d+Add.value z=_ ∧ Add.value z<Add.value d
  rw [hqv]
  exact ⟨hbalance,hz.2⟩

lemma feed_le (N : ℕ) (ys : List Bool) : N≤feed N ys := by
  induction ys generalizing N with
  | nil => rfl
  | cons b ys ih => exact (by omega : N≤2*N+Add.bit b).trans (ih _)

lemma scan_value (q r d ys : List Bool) (hqr : q.length=r.length)
    (hrd : r.length=d.length) (hr : r≠[]) (hd : 0<Add.value d)
    (hds : 2*Add.value d≤2^r.length) (hrem : Add.value r<Add.value d)
    (hbound : feed (Add.value q*Add.value d+Add.value r) ys<2^r.length) :
    Add.value (scan q r d ys).1*Add.value d+Add.value (scan q r d ys).2=
      feed (Add.value q*Add.value d+Add.value r) ys ∧
    Add.value (scan q r d ys).2<Add.value d := by
  induction ys generalizing q r with
  | nil => exact ⟨rfl,hrem⟩
  | cons b ys ih =>
    have h := oneStep_lengths b q r d hqr hr
    have hn : (oneStep b q r d).2≠[] := by
      intro he;have hp := List.length_pos_iff.mpr hr;simp [he] at h;omega
    have hb : 2*(Add.value q*Add.value d+Add.value r)+Add.bit b<2^r.length :=
      (feed_le _ ys).trans_lt hbound
    have hv := oneStep_value b q r d hqr hrd hr hd hds hrem hb
    have hd' : 2*Add.value d≤2^(oneStep b q r d).2.length := by rw [h.2];exact hds
    have hb' : feed (Add.value (oneStep b q r d).1*Add.value d+Add.value (oneStep b q r d).2) ys<
        2^(oneStep b q r d).2.length := by rw [hv.1,h.2];exact hbound
    have hh := ih (oneStep b q r d).1 (oneStep b q r d).2 (by omega) (h.2.trans hrd) hn hd' hv.2 hb'
    simpa only [scan,feed,hv.1] using hh

lemma zero_value (n : ℕ) : Add.value (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,Add.value,Add.bit,ih]

theorem division (d ys : List Bool) (hd : 0<Add.value d) (hds : 2*Add.value d≤2^d.length)
    (hinput : Add.value ys.reverse<2^d.length) :
    let z := List.replicate d.length false
    let result := scan z z d ys
    Add.value result.1=Add.value ys.reverse/Add.value d ∧
    Add.value result.2=Add.value ys.reverse%Add.value d ∧
    ∃n,n≤ys.length*(38*d.length+19)+1 ∧ Run program (store z z d ys) n (store result.1 result.2 d []) := by
  dsimp only
  let z := List.replicate d.length false
  have hdlen : 0<d.length := by
    by_contra h;have he : d=[] := List.length_eq_zero_iff.mp (by omega)
    simp [he,Add.value] at hd
  have hz : z≠[] := by simp [z,hdlen.ne']
  have hzl : z.length=d.length := by simp [z]
  have hzv : Add.value z=0 := zero_value d.length
  have hb : feed (Add.value z*Add.value d+Add.value z) ys<2^z.length := by
    simpa only [hzv,Nat.zero_mul,Nat.add_zero,feed_value,Nat.mul_zero,Nat.zero_add,hzl] using hinput
  have hv := scan_value z z d ys rfl hzl hz hd (hzl ▸ hds) (by rw [hzv];exact hd) hb
  simp only [hzv,Nat.zero_mul,Nat.zero_add,feed_value,Nat.mul_zero] at hv
  have hdiv : Add.value ys.reverse/Add.value d=Add.value (scan z z d ys).1 :=
    Nat.div_eq_of_lt_le (by nlinarith [hv.1]) (by nlinarith [hv.1,hv.2])
  have hmod : Add.value ys.reverse%Add.value d=Add.value (scan z z d ys).2 := by
    have hh := Nat.mod_add_div (Add.value ys.reverse) (Add.value d)
    rw [hdiv] at hh;nlinarith [hv.1]
  refine ⟨hdiv.symm,hmod.symm,time z z d ys,?_,program_run z z d ys rfl hzl hz⟩
  simpa only [hzl] using time_bound z z d ys rfl hz

end Divide
end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Device
open Program Binary

variable {ι : Type} [DecidableEq ι]

attribute [instance] Realizer.finiteW Realizer.eqW

variable {f : (ι → ℕ) → ℕ} {Pre : ℕ → (ι → ℕ) → Prop}

lemma Realizer.transport {L : Type} [DecidableEq L] (D : Realizer f Pre)
    (e : ι ⊕ D.W → L) (he : Function.Injective e) (n : ℕ) (hn : 0<n)
    (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n) (hPre : Pre n (values xs))
    (R : Store L) (hi : ∀i,R (e (.inl i))=xs i) (hw : ∀w,R (e (.inr w))=[]) :
    ∃t y,t≤D.coefficient*(n+1)^2 ∧ y.length=n ∧ Add.value y.reverse=f (values xs) ∧
      Run (D.program.relabel e) R t (Function.update R (e (.inr D.out)) y) := by
  obtain ⟨t,y,ht,hy,hv,hr⟩ := D.spec n hn xs hxs hPre
  have ha : Agrees e (input xs) R := by intro k;cases k <;> simp_all [input]
  exact ⟨t,y,ht,hy,hv,hr.relabel_to e he R _ ha
    (agrees_update e he (input xs) R ha (.inr D.out) y) (outside_update e R (.inr D.out) y)⟩

namespace Compose
variable {g : (ι → ℕ) → ℕ} {Q : ℕ → (ι → ℕ) → Prop}
variable {op : ℕ → ℕ → ℕ} {Adm : ℕ → (Fin 2 → ℕ) → Prop}
variable (F : Realizer f Pre) (G : Realizer g Q)
variable (O : Realizer (fun ab : Fin 2 → ℕ => op (ab 0) (ab 1)) Adm)

abbrev Work := F.W ⊕ (G.W ⊕ O.W)

def left : ι ⊕ F.W → ι ⊕ Work F G O := Sum.map id Sum.inl
def right : ι ⊕ G.W → ι ⊕ Work F G O := Sum.map id (Sum.inr ∘ Sum.inl)
def call : Fin 2 ⊕ O.W → ι ⊕ Work F G O
  | .inl i => if i=0 then .inr (.inl F.out) else .inr (.inr (.inl G.out))
  | .inr w => .inr (.inr (.inr w))

lemma left_injective : Function.Injective (left F G O) := by
  intro firstValue secondValue equality
  cases firstValue <;> cases secondValue <;>
    simp_all [-Sum.update_elim_inr, -Sum.elim_update_right, left]
lemma right_injective : Function.Injective (right F G O) := by
  intro firstValue secondValue equality
  cases firstValue <;> cases secondValue <;>
    simp_all [-Sum.update_elim_inr, -Sum.elim_update_right, right]
lemma call_injective : Function.Injective (call F G O) := by
  intro x y h
  cases x with
  | inl i => cases y with
    | inl j => fin_cases i <;> fin_cases j <;> simp_all [call]
    | inr w => fin_cases i <;> simp_all [call]
  | inr v => cases y with
    | inl j => fin_cases j <;> simp_all [call]
    | inr w => simpa [-Sum.update_elim_inr, -Sum.elim_update_right, call] using h

def body : Program (ι ⊕ Work F G O) :=
  .seq (F.program.relabel (left F G O)) (.seq (G.program.relabel (right F G O))
    (.seq (O.program.relabel (call F G O))
      (.seq (clear (.inr (.inl F.out))) (clear (.inr (.inr (.inl G.out)))))))

lemma body_run (n : ℕ) (hn : 0<n) (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n)
    (hF : Pre n (values xs)) (hG : Q n (values xs))
    (hO : Adm n ![f (values xs),g (values xs)]) :
    ∃t y,t≤(F.coefficient+G.coefficient+O.coefficient+6)*(n+1)^2 ∧ y.length=n ∧
      Add.value y.reverse=op (f (values xs)) (g (values xs)) ∧
      Run (body F G O) (input xs) t (result xs (.inr (.inr O.out)) y) := by
  let R : Store (ι ⊕ Work F G O) := input xs
  obtain ⟨tf,yf,htf,hyf,hvf,hf⟩ := F.transport (left F G O) (left_injective F G O)
    n hn xs hxs hF R (by intro i;rfl) (by intro w;rfl)
  let Rf := Function.update R (.inr (.inl F.out)) yf
  change Run (F.program.relabel (left F G O)) R tf Rf at hf
  obtain ⟨tg,yg,htg,hyg,hvg,hg⟩ := G.transport (right F G O) (right_injective F G O)
    n hn xs hxs hG Rf (by intro i;simp [-Sum.update_elim_inr, -Sum.elim_update_right, Rf,R,input,right]) (by intro w;simp [-Sum.update_elim_inr, -Sum.elim_update_right, Rf,R,input,right])
  let Rg := Function.update Rf (.inr (.inr (.inl G.out))) yg
  change Run (G.program.relabel (right F G O)) Rf tg Rg at hg
  let ab : Fin 2 → List Bool := ![yf,yg]
  have hab : ∀i,(ab i).length=n := by intro i;fin_cases i <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, ab,hyf,hyg]
  have hav : values ab=![f (values xs),g (values xs)] := by
    funext i;fin_cases i
    · exact hvf
    · exact hvg
  obtain ⟨top,yo,hto,hyo,hvo,ho⟩ := O.transport (call F G O) (call_injective F G O) n hn ab hab
    (by rw [hav];exact hO) Rg (by intro i;fin_cases i <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, Rg,Rf,call,ab])
    (by intro w;simp [-Sum.update_elim_inr, -Sum.elim_update_right, Rg,Rf,R,input,call])
  let Ro := Function.update Rg (.inr (.inr (.inr O.out))) yo
  change Run (O.program.relabel (call F G O)) Rg top Ro at ho
  have hclearF := clear_run (.inr (.inl F.out)) Ro
  let Ra := Function.update Ro (.inr (.inl F.out)) []
  have hcleanFlen : (Ro (.inr (.inl F.out))).length=n := by simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ro,Rg,Rf,hyf]
  rw [hcleanFlen] at hclearF
  have hclearG := clear_run (.inr (.inr (.inl G.out))) Ra
  have hcleanGlen : (Ra (.inr (.inr (.inl G.out)))).length=n := by simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,hyg]
  rw [hcleanGlen] at hclearG
  have he : Function.update Ra (.inr (.inr (.inl G.out))) []=result xs (.inr (.inr O.out)) yo := by
    funext k
    cases k with
    | inl i => simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,R,result,input]
    | inr w => cases w with
      | inl w => by_cases hw : w=F.out <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,R,result,input,hw]
      | inr w => cases w with
        | inl w => by_cases hw : w=G.out <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,R,result,input,hw]
        | inr w => simp [-Sum.update_elim_inr, -Sum.elim_update_right, Ra,Ro,Rg,Rf,R,result,input]
  rw [he] at hclearG
  have H := Run.seq (F.program.relabel (left F G O)) _ _ _ _ _ _ hf
    (Run.seq (G.program.relabel (right F G O)) _ _ _ _ _ _ hg
    (Run.seq (O.program.relabel (call F G O)) _ _ _ _ _ _ ho
    (Run.seq (clear (.inr (.inl F.out))) (clear (.inr (.inr (.inl G.out)))) _ _ _ _ _ hclearF hclearG)))
  refine ⟨tf+(tg+(top+((2*n+1)+(2*n+1)))),yo,?_,hyo,?_,H⟩
  · nlinarith
  · simpa only [hav,Matrix.cons_val_zero,Matrix.cons_val_one] using hvo

def realizer : Realizer (fun vs => op (f vs) (g vs))
    (fun n vs => Pre n vs ∧ Q n vs ∧ Adm n ![f vs,g vs]) where
  W := Work F G O
  finiteW := inferInstance
  eqW := inferInstance
  out := .inr (.inr O.out)
  program := body F G O
  coefficient := F.coefficient+G.coefficient+O.coefficient+6
  spec := by
    intro n hn xs hxs h
    exact body_run F G O n hn xs hxs h.1 h.2.1 h.2.2

end Compose

def read (i : ι) : Realizer (fun vs => vs i) (fun _ _ => True) where
  W := Fin 2
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := copy (.inl i) (.inr 0) (.inr 1)
  coefficient := 7
  spec := by
    intro n hn xs hxs _
    have h := copy_run (.inl i) (.inr (0:Fin 2)) (.inr 1) (by simp) (by simp) (by simp)
      (input xs) (by rfl)
    have hl : (input (W:=Fin 2) xs (.inl i)).length=n := hxs i
    rw [hl] at h
    change Run (copy (.inl i) (.inr (0:Fin 2)) (.inr 1)) (input xs) (5*n+2)
      (result xs 0 (xs i)) at h
    exact ⟨5*n+2,xs i,by nlinarith,hxs i,rfl,h⟩

end SourceBurnside.Structured.Device

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_RegisterOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type} [DecidableEq K]

def pushList (k : K) : List Bool → Program K
  | [] => .skip
  | a::w => .seq (.push k a) (pushList k w)
lemma pushList_run (k : K) (w : List Bool) (r : Store K) :
    Run (pushList k w) r (w.length+1) (Function.update r k (r k++w)) := by
  induction w generalizing r with
  | nil => simpa [pushList] using Run.skip r
  | cons a w ih =>
    have H := Run.seq (.push k a) (pushList k w) r _ _ 1 (w.length+1)
      (Run.push r k a) (ih (Function.update r k (r k++[a])))
    simpa [pushList,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H

def dropN (k : K) : ℕ → Program K
  | 0 => .skip
  | n+1 => .pop k (fun _ => dropN k n)
lemma dropN_run (k : K) (m n : ℕ) (r : Store K) (hr : r k=List.replicate n false) :
    Run (dropN k m) r (m+1) (Function.update r k (List.replicate (n-m) false)) := by
  induction m generalizing n r with
  | zero => simpa [dropN,←hr] using Run.skip r
  | succ m ih =>
    let s := Function.update r k (r k).dropLast
    have hs : s k=List.replicate (n-1) false := by simp [s,hr,List.dropLast_replicate]
    have H := Run.pop r k (fun _ => dropN k m) (m+1) _ (ih (n-1) s hs)
    simpa [dropN,s,Nat.sub_sub,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using H

end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Device
section
open Program Binary
variable {ι : Type} [DecidableEq ι]
namespace Constant

def program (i : ι) (bs : List Bool) : Program (L ι) :=
  .seq (copy (.inl i) (.inr 0) (.inr 1)) (.seq (mapInPlace (fun _ => false) (.inr 0) (.inr 1))
    (.seq (dropN (.inr 0) bs.length) (pushList (.inr 0) bs)))

lemma program_run (i : ι) (bs : List Bool) (xs : ι → List Bool) (n : ℕ) (hs : (xs i).length=n) :
    Run (program i bs) (input xs) (9*n+2*bs.length+6)
      (result xs (0:Fin 2) (List.replicate (n-bs.length) false++bs)) := by
  let r : Store (L ι) := input xs
  let s := Function.update r (.inr (0:Fin 2)) (xs i)
  have H1 := copy_run (.inl i) (.inr (0:Fin 2)) (.inr 1) (by simp) (by simp) (by simp) r (by rfl)
  change Run (copy (.inl i) (.inr (0:Fin 2)) (.inr 1)) r (5*(xs i).length+2) s at H1
  rw [hs] at H1
  have H2 := mapInPlace_run (fun _ => false) (.inr (0:Fin 2)) (.inr 1) (by simp) s
    (by simp [s,r,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  let z := Function.update r (.inr (0:Fin 2)) (List.replicate n false)
  have hsz : Function.update s (.inr 0) ((s (.inr 0)).map (fun _ => false))=z := by
    simp [s,z,hs]
  rw [hsz] at H2
  have hl : (s (.inr 0)).length=n := by simp [s,hs]
  rw [hl] at H2
  have H3 := dropN_run (.inr (0:Fin 2)) bs.length n z (by simp [z])
  let t := Function.update r (.inr (0:Fin 2)) (List.replicate (n-bs.length) false)
  change Run (dropN (.inr (0:Fin 2)) bs.length) z (bs.length+1)
    (Function.update z (.inr 0) (List.replicate (n-bs.length) false)) at H3
  have hzt : Function.update z (.inr 0) (List.replicate (n-bs.length) false)=t := by simp [z,t]
  rw [hzt] at H3
  have H4 := pushList_run (.inr (0:Fin 2)) bs t
  have htf : Function.update t (.inr 0) (t (.inr 0)++bs)=
      result xs (0:Fin 2) (List.replicate (n-bs.length) false++bs) := by
    simp [t,result,r]
  rw [htf] at H4
  have H := Run.seq _ _ _ _ _ _ _ H1 (Run.seq _ _ _ _ _ _ _ H2 (Run.seq _ _ _ _ _ _ _ H3 H4))
  convert H using 1 <;> first | rfl | omega

lemma value_false (n : ℕ) : Add.value (List.replicate n false)=0 := by
  exact Divide.zero_value n
lemma value_bits (n : ℕ) : Add.value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Add.value]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases b <;> simp [Add.value,ih,Nat.bit,Add.bit]
    omega

end Constant

def constant (i : ι) (a : ℕ) : Realizer (fun _ : ι → ℕ => a) (fun n _ => a.bits.length≤n) where
  W := Fin 2
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := Constant.program i a.bits.reverse
  coefficient := 2*a.bits.length+15
  spec := by
    intro n hn xs hs hp
    let bs := a.bits.reverse
    let y := List.replicate (n-bs.length) false++bs
    have hl : bs.length≤n := by simpa [bs] using hp
    refine ⟨9*n+2*bs.length+6,y,?_,?_,?_,Constant.program_run i bs xs n (hs i)⟩
    · dsimp [bs];nlinarith [sq_nonneg (n:ℤ)]
    · simp [y];omega
    · simp [y,List.reverse_append,Add.value_append,Constant.value_false,bs,Constant.value_bits]

end

section
open Program Binary

namespace AddOperator

def load : Program L := .seq (copy (Sum.inl 0) (Sum.inr 0) (Sum.inr 2))
  (.seq (copy (Sum.inl 1) (Sum.inr 1) (Sum.inr 2)) (.push (Sum.inr 3) false))
def program : Program L := .seq load (.seq (Add.fixedAdd.relabel Sum.inr) (clear (Sum.inr 3)))

def loaded (xs : Fin 2 → List Bool) : Store L := Sum.elim xs
  (Add.store (xs 0).reverse (xs 1).reverse [] false)

def first (xs : Fin 2 → List Bool) : Store L := Function.update (input xs) (Sum.inr 0) (xs 0)
def second (xs : Fin 2 → List Bool) : Store L := Function.update (first xs) (Sum.inr 1) (xs 1)

lemma load_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    Run load (input xs) (10*n+5) (loaded xs) := by
  have h1 := copy_run (Sum.inl (0:Fin 2)) (Sum.inr (0:Fin 4)) (Sum.inr 2) (by simp) (by simp) (by simp)
    (input xs) (by rfl)
  change Run (copy (Sum.inl (0:Fin 2)) (Sum.inr (0:Fin 4)) (Sum.inr 2)) (input xs)
    (5*(xs 0).length+2) (first xs) at h1
  rw [hs] at h1
  have h2 := copy_run (Sum.inl (1:Fin 2)) (Sum.inr (1:Fin 4)) (Sum.inr 2) (by simp) (by simp) (by simp)
    (first xs) (by simp [first,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update (first xs) (Sum.inr 1) ((first xs) (Sum.inr 1)++(first xs) (Sum.inl 1))=second xs := by
    simp [second,first,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have hl2 : ((first xs) (Sum.inl 1)).length=n := by simp [first,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have h3 := Run.push (second xs) (Sum.inr (3:Fin 4)) false
  have he3 : Function.update (second xs) (Sum.inr 3) ((second xs) (Sum.inr 3)++[false])=loaded xs := by
    funext k;cases k with
    | inl i => simp [loaded,second,first,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,second,first,input,Add.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have H := Run.seq (copy (Sum.inl 0) (Sum.inr 0) (Sum.inr 2)) _ _ _ _ _ _ h1
    (Run.seq (copy (Sum.inl 1) (Sum.inr 1) (Sum.inr 2)) (.push (Sum.inr 3) false) _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

lemma program_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    let z := (Add.scan (xs 0).reverse (xs 1).reverse false).1
    Run program (input xs) (17*n+10) (result xs (0:Fin 4) z.reverse) := by
  dsimp only
  let a := (xs 0).reverse
  let b := (xs 1).reverse
  let z := (Add.scan a b false).1
  let c := (Add.scan a b false).2.2
  have he : a.length=b.length := by simp only [a,b,List.length_reverse,hs]
  have h1 := load_run xs n hs
  let R : Store L := Sum.elim xs (Add.store z [] [] c)
  have h2 : Run (Add.fixedAdd.relabel Sum.inr) (loaded xs) (7*a.length+2) R := by
    refine (Add.fixedAdd_run a b false he).relabel_to Sum.inr Sum.inr_injective (loaded xs) R
      (by intro k;rfl) (by intro k;rfl) ?_
    intro l hl;cases l with
    | inl i => rfl
    | inr k => exact False.elim (hl k rfl)
  have hl : a.length=n := by simp [a,hs]
  rw [hl] at h2
  have h3 := clear_run (Sum.inr (3:Fin 4)) R
  have he3 : Function.update R (Sum.inr 3) []=result xs (0:Fin 4) z.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,Add.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  change Run (clear (Sum.inr (3:Fin 4))) R 3 (result xs 0 z.reverse) at h3
  have H := Run.seq load _ _ _ _ _ _ h1
    (Run.seq (Add.fixedAdd.relabel Sum.inr) (clear (Sum.inr 3)) _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

end AddOperator

def add : Realizer (fun vs : Fin 2 → ℕ => vs 0+vs 1) (fun n vs => vs 0+vs 1<2^n) where
  W := Fin 4
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := AddOperator.program
  coefficient := 27
  spec := by
    intro n hn xs hs hpre
    let a := (xs 0).reverse
    let b := (xs 1).reverse
    let z := (Add.scan a b false).1
    have he : a.length=b.length := by simp only [a,b,List.length_reverse,hs]
    have hl : a.length=n := by simp [a,hs]
    have hz : z.length=n := (Add.scan_length a b false).trans hl
    refine ⟨17*n+10,z.reverse,by nlinarith,by simpa using hz,?_,AddOperator.program_run xs n hs⟩
    simp only [List.reverse_reverse]
    change Add.value z=Add.value a+Add.value b
    change Add.value a+Add.value b<2^n at hpre
    have hb : Add.value a+Add.value b+Add.bit false<2^a.length := by
      simpa only [Add.bit,Bool.false_eq_true,↓reduceIte,Nat.add_zero,hl] using hpre
    simpa only [Add.bit,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using (Add.scan_exact a b false he hb).1

end

section
open Program Binary

namespace SubOperator

def load : Program L := .seq (copy (Sum.inl 0) (Sum.inr 0) (Sum.inr 2))
  (.seq (copy (Sum.inl 1) (Sum.inr 1) (Sum.inr 2)) (.push (Sum.inr 3) true))
def program : Program L := .seq load (.seq (Add.fixedSubtract.relabel Sum.inr) (clear (Sum.inr 3)))

def loaded (xs : Fin 2 → List Bool) : Store L := Sum.elim xs
  (Add.store (xs 0).reverse (xs 1).reverse [] true)

def first (xs : Fin 2 → List Bool) : Store L := Function.update (input xs) (Sum.inr 0) (xs 0)
def second (xs : Fin 2 → List Bool) : Store L := Function.update (first xs) (Sum.inr 1) (xs 1)

lemma load_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    Run load (input xs) (10*n+5) (loaded xs) := by
  have h1 := copy_run (Sum.inl (0:Fin 2)) (Sum.inr (0:Fin 4)) (Sum.inr 2) (by simp) (by simp) (by simp)
    (input xs) (by rfl)
  change Run (copy (Sum.inl (0:Fin 2)) (Sum.inr (0:Fin 4)) (Sum.inr 2)) (input xs)
    (5*(xs 0).length+2) (first xs) at h1
  rw [hs] at h1
  have h2 := copy_run (Sum.inl (1:Fin 2)) (Sum.inr (1:Fin 4)) (Sum.inr 2) (by simp) (by simp) (by simp)
    (first xs) (by simp [first,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update (first xs) (Sum.inr 1) ((first xs) (Sum.inr 1)++(first xs) (Sum.inl 1))=second xs := by
    simp [second,first,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have hl2 : ((first xs) (Sum.inl 1)).length=n := by simp [first,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have h3 := Run.push (second xs) (Sum.inr (3:Fin 4)) true
  have he3 : Function.update (second xs) (Sum.inr 3) ((second xs) (Sum.inr 3)++[true])=loaded xs := by
    funext k;cases k with
    | inl i => simp [loaded,second,first,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,second,first,input,Add.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have H := Run.seq (copy (Sum.inl 0) (Sum.inr 0) (Sum.inr 2)) _ _ _ _ _ _ h1
    (Run.seq (copy (Sum.inl 1) (Sum.inr 1) (Sum.inr 2)) (.push (Sum.inr 3) true) _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

lemma program_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    let z := (Add.scan (xs 0).reverse ((xs 1).reverse.map not) true).1
    Run program (input xs) (21*n+12) (result xs (0:Fin 4) z.reverse) := by
  dsimp only
  let a := (xs 0).reverse
  let b := (xs 1).reverse
  let z := (Add.scan a (b.map not) true).1
  let c := (Add.scan a (b.map not) true).2.2
  have he : a.length=b.length := by simp only [a,b,List.length_reverse,hs]
  have h1 := load_run xs n hs
  let R : Store L := Sum.elim xs (Add.store z [] [] c)
  have h2 : Run (Add.fixedSubtract.relabel Sum.inr) (loaded xs) (11*a.length+4) R := by
    refine (Add.fixedSubtract_run a b he).relabel_to Sum.inr Sum.inr_injective (loaded xs) R
      (by intro k;rfl) (by intro k;rfl) ?_
    intro l hl;cases l with
    | inl i => rfl
    | inr k => exact False.elim (hl k rfl)
  have hl : a.length=n := by simp [a,hs]
  rw [hl] at h2
  have h3 := clear_run (Sum.inr (3:Fin 4)) R
  have he3 : Function.update R (Sum.inr 3) []=result xs (0:Fin 4) z.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,Add.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  change Run (clear (Sum.inr (3:Fin 4))) R 3 (result xs 0 z.reverse) at h3
  have H := Run.seq load _ _ _ _ _ _ h1
    (Run.seq (Add.fixedSubtract.relabel Sum.inr) (clear (Sum.inr 3)) _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

end SubOperator

def subtract : Realizer (fun vs : Fin 2 → ℕ => vs 0-vs 1) (fun _ vs => vs 1≤vs 0) where
  W := Fin 4
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := SubOperator.program
  coefficient := 33
  spec := by
    intro n hn xs hs hpre
    let a := (xs 0).reverse
    let b := (xs 1).reverse
    let z := (Add.scan a (b.map not) true).1
    have he : a.length=b.length := by simp only [a,b,List.length_reverse,hs]
    have hl : a.length=n := by simp [a,hs]
    have hz : z.length=n := (Add.scan_length a (b.map not) true).trans hl
    refine ⟨21*n+12,z.reverse,by nlinarith,by simpa using hz,?_,SubOperator.program_run xs n hs⟩
    simp only [List.reverse_reverse]
    exact Add.subtract_exact a b he hpre

end

section
open Program Binary
namespace CompareOperator

def finish : Program L := .seq (mapInPlace (fun _ => false) (.inr 0) (.inr 2))
  (.pop (.inr 0) (fun _ => .pop (.inr 3) (fun b => .push (.inr 0) (b.getD false))))
def program : Program L := .seq SubOperator.load (.seq (Add.fixedSubtract.relabel Sum.inr) finish)

lemma padded_value (n : ℕ) (b : Bool) : Add.value (padded n b).reverse=Add.bit b := by
  simp [-Sum.update_elim_inr,-Sum.elim_update_right,padded,List.reverse_append,Add.value,Constant.value_false]

lemma finish_run (xs : Fin 2 → List Bool) (z : List Bool) (c : Bool) :
    Run finish (Sum.elim xs (Add.store z [] [] c)) (4*z.length+5)
      (result xs (0:Fin 4) (padded z.length c)) := by
  let R : Store L := Sum.elim xs (Add.store z [] [] c)
  let S := Function.update R (.inr (0:Fin 4)) (List.replicate z.length false)
  have h1 := mapInPlace_run (fun _ => false) (.inr (0:Fin 4)) (.inr 2) (by simp) R (by rfl)
  have he : Function.update R (.inr 0) ((R (.inr 0)).map (fun _ => false))=S := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,S,R,Add.store]
  rw [he] at h1
  have hl : (R (.inr 0)).length=z.length := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,R,Add.store]
  rw [hl] at h1
  let U := Function.update S (.inr (0:Fin 4)) (List.replicate (z.length-1) false)
  let V := Function.update U (.inr (3:Fin 4)) []
  have hpush := Run.push V (.inr (0:Fin 4)) c
  have hpf : Function.update V (.inr 0) (V (.inr 0)++[c])=result xs (0:Fin 4) (padded z.length c) := by
    funext k;cases k with
    | inl i => simp [-Sum.update_elim_inr,-Sum.elim_update_right,V,U,S,R,result,input]
    | inr i => fin_cases i <;> simp [-Sum.update_elim_inr,-Sum.elim_update_right,V,U,S,R,result,input,Add.store,padded]
  rw [hpf] at hpush
  have hc : U (.inr 3)=[c] := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,U,S,R,Add.store]
  have h2 : Run (.pop (.inr (3:Fin 4)) (fun b => Program.push (.inr 0) (b.getD false))) U 2
      (result xs 0 (padded z.length c)) := by
    refine Run.pop U (.inr 3) _ 1 _ ?_
    simpa [hc,V] using hpush
  have hz : S (.inr 0)=List.replicate z.length false := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,S]
  have h3 : Run (.pop (.inr (0:Fin 4)) (fun _ => Program.pop (.inr 3) (fun b => .push (.inr 0) (b.getD false)))) S 3
      (result xs 0 (padded z.length c)) := by
    refine Run.pop S (.inr 0) _ 2 _ ?_
    simpa [hz,U,List.dropLast_replicate] using h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h3
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma program_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    let c := (Add.scan (xs 0).reverse ((xs 1).reverse.map not) true).2.2
    Run program (input xs) (25*n+14) (result xs (0:Fin 4) (padded n c)) := by
  dsimp only
  let a := (xs 0).reverse
  let b := (xs 1).reverse
  let z := (Add.scan a (b.map not) true).1
  let c := (Add.scan a (b.map not) true).2.2
  have he : a.length=b.length := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,a,b,hs]
  have h1 := SubOperator.load_run xs n hs
  let R : Store L := Sum.elim xs (Add.store z [] [] c)
  have h2 : Run (Add.fixedSubtract.relabel Sum.inr) (SubOperator.loaded xs) (11*a.length+4) R := by
    refine (Add.fixedSubtract_run a b he).relabel_to Sum.inr Sum.inr_injective (SubOperator.loaded xs) R
      (by intro k;rfl) (by intro k;rfl) ?_
    intro l hl;cases l with
    | inl i => rfl
    | inr k => exact False.elim (hl k rfl)
  have hl : a.length=n := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,a,hs]
  have hz : z.length=n := (Add.scan_length a (b.map not) true).trans hl
  rw [hl] at h2
  have h3 := finish_run xs z c
  rw [hz] at h3
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega
end CompareOperator

def lessEqualReversed : Realizer (fun vs : Fin 2 → ℕ => if vs 1≤vs 0 then 1 else 0) (fun _ _ => True) where
  W := Fin 4
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := CompareOperator.program
  coefficient := 39
  spec := by
    intro n hn xs hs hpre
    let a := (xs 0).reverse
    let b := (xs 1).reverse
    let c := (Add.scan a (b.map not) true).2.2
    have he : a.length=b.length := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,a,b,hs]
    refine ⟨25*n+14,CompareOperator.padded n c,by nlinarith,CompareOperator.padded_length n hn c,?_,CompareOperator.program_run xs n hs⟩
    rw [CompareOperator.padded_value]
    change Add.bit c=if Add.value b≤Add.value a then 1 else 0
    have hh : c=true ↔ Add.value b≤Add.value a := Add.subtract_carry a b he
    cases hc : c <;> simp_all [Add.bit]

end

section
open Program Binary
namespace MultiplyOperator

def load : Program L := .seq (copy (.inl 0) (.inr 0) (.inr 4))
  (.seq (mapInPlace (fun _ => false) (.inr 0) (.inr 4))
  (.seq (copy (.inl 0) (.inr 1) (.inr 4)) (copy (.inl 1) (.inr 2) (.inr 4))))
def program : Program L := .seq load (.seq (Multiply.program.relabel Sum.inr) (clear (.inr 1)))
def loaded (xs : Fin 2 → List Bool) (n : ℕ) : Store L :=
  Sum.elim xs (Multiply.store (List.replicate n false) (xs 0).reverse (xs 1).reverse)

lemma load_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    Run load (input xs) (19*n+8) (loaded xs n) := by
  let R : Store L := input xs
  let R1 := Function.update R (.inr (0:Fin 6)) (xs 0)
  let R2 := Function.update R (.inr (0:Fin 6)) (List.replicate n false)
  let R3 := Function.update R2 (.inr (1:Fin 6)) (xs 0)
  have h1 := copy_run (.inl (0:Fin 2)) (.inr (0:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R (by rfl)
  change Run (copy (.inl (0:Fin 2)) (.inr (0:Fin 6)) (.inr 4)) R (5*(xs 0).length+2) R1 at h1
  rw [hs] at h1
  have h2 := mapInPlace_run (fun _ => false) (.inr (0:Fin 6)) (.inr 4) (by simp) R1
    (by simp [R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update R1 (.inr 0) ((R1 (.inr 0)).map (fun _ => false))=R2 := by simp [R1,R2,hs]
  rw [he2] at h2
  have hl2 : (R1 (.inr 0)).length=n := by simp [R1,hs]
  rw [hl2] at h2
  have h3 := copy_run (.inl (0:Fin 2)) (.inr (1:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R2
    (by simp [R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he3 : Function.update R2 (.inr 1) (R2 (.inr 1)++R2 (.inl 0))=R3 := by
    simp [R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have hl3 : (R2 (.inl 0)).length=n := by simp [R2,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl3] at h3
  have h4 := copy_run (.inl (1:Fin 2)) (.inr (2:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R3
    (by simp [R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he4 : Function.update R3 (.inr 2) (R3 (.inr 2)++R3 (.inl 1))=loaded xs n := by
    funext k;cases k with
    | inl i => simp [loaded,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,Multiply.store,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he4] at h4
  have hl4 : (R3 (.inl 1)).length=n := by simp [R3,R2,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl4] at h4
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | omega

lemma program_run (xs : Fin 2 → List Bool) (n : ℕ) (hn : 0<n) (hs : ∀i,(xs i).length=n) :
    let z := (Multiply.scan (List.replicate n false) (xs 0).reverse (xs 1).reverse).1
    Run program (input xs) (21*n+9+Multiply.time n (xs 1).reverse) (result xs (0:Fin 6) z.reverse) := by
  dsimp only
  let acc := List.replicate n false
  let x := (xs 0).reverse
  let y := (xs 1).reverse
  let z := (Multiply.scan acc x y).1
  let xx := (Multiply.scan acc x y).2
  have hl : x.length=n := by simp [x,hs]
  have ha : acc.length=x.length := by simp [acc,hl]
  have hx : x≠[] := by intro hh;rw [hh] at hl;simp at hl;omega
  have h1 := load_run xs n hs
  let R : Store L := Sum.elim xs (Multiply.store z xx [])
  have h2 : Run (Multiply.program.relabel Sum.inr) (loaded xs n) (Multiply.time n y) R := by
    have hh := (Multiply.program_run acc x y hx ha).relabel_to Sum.inr Sum.inr_injective (loaded xs n) R
      (by intro k;rfl) (by intro k;rfl) (by
        intro l hl;cases l with
        | inl i => rfl
        | inr k => exact False.elim (hl k rfl))
    simpa [hl] using hh
  have h3 := clear_run (.inr (1:Fin 6)) R
  have he3 : Function.update R (.inr 1) []=result xs (0:Fin 6) z.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,Multiply.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have hl3 : (R (.inr 1)).length=n := by
    have hh := (Multiply.scan_length acc x y hx ha).2
    simp only [R,Sum.elim_inr,Multiply.store,Matrix.cons_val_one,Matrix.cons_val_zero,List.length_reverse]
    exact hh.trans hl
  rw [hl3] at h3
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  change Run program (input xs) (21*n+9+Multiply.time n y) (result xs (0:Fin 6) z.reverse)
  convert H using 1 <;> first | rfl | omega
end MultiplyOperator

def multiply : Realizer (fun vs : Fin 2 → ℕ => vs 0*vs 1) (fun n vs => vs 0*vs 1<2^n) where
  W := Fin 6
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := MultiplyOperator.program
  coefficient := 42
  spec := by
    intro n hn xs hs hpre
    let acc := List.replicate n false
    let x := (xs 0).reverse
    let y := (xs 1).reverse
    let z := (Multiply.scan acc x y).1
    have hl : x.length=n := by simp [x,hs]
    have hy : y.length=n := by simp [y,hs]
    have ha : acc.length=x.length := by simp [acc,hl]
    have hx : x≠[] := by intro hh;rw [hh] at hl;simp at hl;omega
    have hz : z.length=n := (Multiply.scan_length acc x y hx ha).1.trans (by simp [acc])
    refine ⟨21*n+9+Multiply.time n y,z.reverse,?_,by simpa using hz,?_,MultiplyOperator.program_run xs n hn hs⟩
    · have ht := Multiply.time_bound n y
      rw [hy] at ht
      nlinarith
    · simp only [List.reverse_reverse]
      have hv := Multiply.scan_value acc x y hx ha
      simp only [acc,Constant.value_false,Nat.zero_add,hl] at hv
      exact hv.trans (Nat.mod_eq_of_lt hpre)

end

open Program Binary
namespace DivideOperator

def load : Program L := .seq (copy (.inl 0) (.inr 0) (.inr 6))
  (.seq (mapInPlace (fun _ => false) (.inr 0) (.inr 6))
  (.seq (copy (.inr 0) (.inr 1) (.inr 6))
  (.seq (copy (.inl 1) (.inr 2) (.inr 6))
  (.seq (copy (.inl 0) (.inr 4) (.inr 6)) (move (.inr 4) (.inr 3))))))
def program (rem : Bool) : Program L := .seq load (.seq (Divide.program.relabel Sum.inr)
  (.seq (clear (.inr (other rem))) (clear (.inr 2))))
def loaded (xs : Fin 2 → List Bool) (n : ℕ) : Store L :=
  Sum.elim xs (Divide.store (List.replicate n false) (List.replicate n false) (xs 1).reverse (xs 0))

lemma load_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    Run load (input xs) (26*n+11) (loaded xs n) := by
  let R : Store L := input xs
  let R1 := Function.update R (.inr (0:Fin 8)) (xs 0)
  let R2 := Function.update R (.inr (0:Fin 8)) (List.replicate n false)
  let R3 := Function.update R2 (.inr (1:Fin 8)) (List.replicate n false)
  let R4 := Function.update R3 (.inr (2:Fin 8)) (xs 1)
  let R5 := Function.update R4 (.inr (4:Fin 8)) (xs 0)
  have h1 := copy_run (.inl (0:Fin 2)) (.inr (0:Fin 8)) (.inr 6) (by simp) (by simp) (by simp) R (by rfl)
  change Run (copy (.inl (0:Fin 2)) (.inr (0:Fin 8)) (.inr 6)) R (5*(xs 0).length+2) R1 at h1
  rw [hs] at h1
  have h2 := mapInPlace_run (fun _ => false) (.inr (0:Fin 8)) (.inr 6) (by simp) R1
    (by simp [R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update R1 (.inr 0) ((R1 (.inr 0)).map (fun _ => false))=R2 := by simp [R1,R2,hs]
  rw [he2] at h2
  have hl2 : (R1 (.inr 0)).length=n := by simp [R1,hs]
  rw [hl2] at h2
  have h3 := copy_run (.inr (0:Fin 8)) (.inr (1:Fin 8)) (.inr 6) (by simp) (by simp) (by simp) R2
    (by simp [R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he3 : Function.update R2 (.inr 1) (R2 (.inr 1)++R2 (.inr 0))=R3 := by
    simp [R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have hl3 : (R2 (.inr 0)).length=n := by simp [R2]
  rw [hl3] at h3
  have h4 := copy_run (.inl (1:Fin 2)) (.inr (2:Fin 8)) (.inr 6) (by simp) (by simp) (by simp) R3
    (by simp [R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he4 : Function.update R3 (.inr 2) (R3 (.inr 2)++R3 (.inl 1))=R4 := by
    simp [R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he4] at h4
  have hl4 : (R3 (.inl 1)).length=n := by simp [R3,R2,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl4] at h4
  have h5 := copy_run (.inl (0:Fin 2)) (.inr (4:Fin 8)) (.inr 6) (by simp) (by simp) (by simp) R4
    (by simp [R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he5 : Function.update R4 (.inr 4) (R4 (.inr 4)++R4 (.inl 0))=R5 := by
    simp [R5,R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he5] at h5
  have hl5 : (R4 (.inl 0)).length=n := by simp [R4,R3,R2,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl5] at h5
  have h6 := move_run (.inr (4:Fin 8)) (.inr 3) (by simp) R5
  have he6 : Function.update (Function.update R5 (.inr 4) []) (.inr 3) (R5 (.inr 3)++(R5 (.inr 4)).reverse)=loaded xs n := by
    funext k;cases k with
    | inl i => simp [loaded,R5,R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,Divide.store,R5,R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he6] at h6
  have hl6 : (R5 (.inr 4)).length=n := by simp [R5,hs]
  rw [hl6] at h6
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3
    (Run.seq _ _ _ _ _ _ _ h4 (Run.seq _ _ _ _ _ _ _ h5 h6))))
  convert H using 1 <;> first | rfl | omega

lemma finish_run (xs : Fin 2 → List Bool) (q r d : List Bool) (rem : Bool) (n : ℕ)
    (hs : q.length=n ∧ r.length=n ∧ d.length=n) :
    Run (.seq (clear (.inr (other rem))) (clear (.inr (2:Fin 8)))) (Sum.elim xs (Divide.store q r d []))
      (4*n+2) (result xs (chosen rem) (if rem then r.reverse else q.reverse)) := by
  let R : Store L := Sum.elim xs (Divide.store q r d [])
  have h1 := clear_run (.inr (other rem)) R
  have hl1 : (R (.inr (other rem))).length=n := by
    cases rem <;> simp [R,other,Divide.store,hs.1,hs.2.1]
  rw [hl1] at h1
  let S := Function.update R (.inr (other rem)) []
  have h2 := clear_run (.inr (2:Fin 8)) S
  have hl2 : (S (.inr 2)).length=n := by cases rem <;> simp [S,R,other,Divide.store,hs.2.2,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have he2 : Function.update S (.inr 2) []=result xs (chosen rem) (if rem then r.reverse else q.reverse) := by
    funext k;cases k with
    | inl i => cases rem <;> simp [S,R,chosen,other,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => cases rem <;> fin_cases i <;> simp [S,R,chosen,other,result,input,Divide.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | omega

lemma program_correct (xs : Fin 2 → List Bool) (n : ℕ) (hn : 0<n) (hs : ∀i,(xs i).length=n)
    (hd : 0<values xs 1) (hd2 : 2*values xs 1≤2^n) (rem : Bool) :
    ∃t y,t≤101*(n+1)^2 ∧ y.length=n ∧
      Add.value y.reverse=(if rem then values xs 0%values xs 1 else values xs 0/values xs 1) ∧
      Run (program rem) (input xs) t (result xs (chosen rem) y) := by
  let d := (xs 1).reverse
  let ys := xs 0
  let z := List.replicate n false
  let qr := Divide.scan z z d ys
  have hdl : d.length=n := by simp [d,hs]
  have hzl : z.length=n := by simp [z]
  have hzn : z≠[] := by simp [z,hn.ne']
  have hi : Add.value ys.reverse<2^d.length := by rw [hdl];simpa [ys,←hs 0] using Add.value_lt (xs 0).reverse
  have hc := Divide.division d ys hd (hdl ▸ hd2) hi
  change Add.value (Divide.scan (List.replicate d.length false) (List.replicate d.length false) d ys).1=_ ∧ _ at hc
  rw [hdl] at hc
  obtain ⟨hq,hr,t,ht,htRun⟩ := hc
  have hqrl := Divide.scan_lengths z z d ys rfl hzn
  have hql : qr.1.length=n := hqrl.1.trans hzl
  have hrl : qr.2.length=n := hqrl.2.trans hzl
  let R : Store L := Sum.elim xs (Divide.store qr.1 qr.2 d [])
  have H1 := load_run xs n hs
  have H2 : Run (Divide.program.relabel Sum.inr) (loaded xs n) t R :=
    htRun.relabel_to Sum.inr Sum.inr_injective (loaded xs n) R (by intro k;rfl) (by intro k;rfl) (by
      intro l hl;cases l with
      | inl i => rfl
      | inr k => exact False.elim (hl k rfl))
  have H3 := finish_run xs qr.1 qr.2 d rem n ⟨hql,hrl,hdl⟩
  have H := Run.seq _ _ _ _ _ _ _ H1 (Run.seq _ _ _ _ _ _ _ H2 H3)
  refine ⟨30*n+13+t,if rem then qr.2.reverse else qr.1.reverse,?_,?_,?_,?_⟩
  · have hys : ys.length=n := hs 0
    rw [hys] at ht
    nlinarith
  · cases rem <;> simp [hql,hrl]
  · cases rem <;> simp only [Bool.false_eq_true,↓reduceIte,List.reverse_reverse] <;> assumption
  · convert H using 1 <;> first | rfl | omega
end DivideOperator

def divide (rem : Bool) : Realizer
    (fun vs : Fin 2 → ℕ => if rem then vs 0%vs 1 else vs 0/vs 1)
    (fun n vs => 0<vs 1 ∧ 2*vs 1≤2^n) where
  W := Fin 8
  finiteW := inferInstance
  eqW := inferInstance
  out := DivideOperator.chosen rem
  program := DivideOperator.program rem
  coefficient := 101
  spec := by
    intro n hn xs hs hp
    exact DivideOperator.program_correct xs n hn hs hp.1 hp.2 rem

end SourceBurnside.Structured.Device

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_RegisterLoops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary.Decrement
open Program

def store (xs out : List Bool) (b : Bool) : Store K := ![xs.reverse,out,[b]]
def partialStore (xs out : List Bool) : Store K := ![xs.reverse,out,[]]
lemma bit_equation (a b : Bool) : Add.bit a+2*Add.bit (borrow a b)=Add.bit (low a b)+Add.bit b := by
  cases a <;> cases b <;> decide

def step (a : Bool) : Program K := .pop 2 (fun b =>
  .seq (.push 1 (low a (b.getD false))) (.push 2 (borrow a (b.getD false))))
def pass : Program K := .loop 0 step
def program : Program K := .seq pass (move 1 0)

lemma step_run (xs out : List Bool) (a b : Bool) :
    Run (step a) (store xs out b) 3 (store xs (out++[low a b]) (borrow a b)) := by
  have h1 := Run.push (partialStore xs out) (1:K) (low a b)
  let t := Function.update (partialStore xs out) 1 (out++[low a b])
  have hx : Run (.push (1:K) (low a b)) (partialStore xs out) 1 t := by simpa [partialStore,t] using h1
  have h2 := Run.push t (2:K) (borrow a b)
  have he2 : Function.update t 2 (t 2++[borrow a b])=store xs (out++[low a b]) (borrow a b) := by
    funext k;fin_cases k <;> simp [t,partialStore,store]
  rw [he2] at h2
  have hs := Run.seq _ _ _ _ _ _ _ hx h2
  unfold step
  refine Run.pop (store xs out b) (2:K) _ 2 _ ?_
  change Run (.seq (.push 1 (low a b)) (.push 2 (borrow a b)))
    (Function.update (store xs out b) 2 []) 2 _
  have he : Function.update (store xs out b) 2 []=partialStore xs out := by funext k;fin_cases k <;> simp [store,partialStore]
  rw [he];exact hs

lemma pass_run (xs out : List Bool) (b : Bool) :
    Run pass (store xs out b) (4*xs.length+1) (store [] (out++(scan xs b).1) (scan xs b).2) := by
  induction xs generalizing out b with
  | nil => simpa [pass,scan] using Run.loop_nil (store [] out b) (0:K) step (by rfl)
  | cons a xs ih =>
    have he : Function.update (store (a::xs) out b) 0 xs.reverse=store xs out b := by
      funext k;fin_cases k <;> simp [store]
    have hb := step_run xs out a b
    have ht := ih (out++[low a b]) (borrow a b)
    have H := Run.loop_cons (store (a::xs) out b) (0:K) step xs.reverse a _ _ 3 (4*xs.length+1)
      (by simp [store]) (by rw [he];exact hb) ht
    have hs : store [] (out++[low a b]++(scan xs (borrow a b)).1) (scan xs (borrow a b)).2=
        store [] (out++(scan (a::xs) b).1) (scan (a::xs) b).2 := by simp [scan,List.append_assoc]
    rw [hs] at H
    convert H using 1 <;> first | rfl | simp;omega

lemma program_run (xs : List Bool) (b : Bool) :
    Run program (store xs [] b) (6*xs.length+2) (store (scan xs b).1 [] (scan xs b).2) := by
  have h1 := pass_run xs [] b
  simp only [List.nil_append] at h1
  have h2 := move_run (1:K) 0 (by decide) (store [] (scan xs b).1 (scan xs b).2)
  have he2 : Function.update (Function.update (store [] (scan xs b).1 (scan xs b).2) 1 []) 0
      (store [] (scan xs b).1 (scan xs b).2 0++(store [] (scan xs b).1 (scan xs b).2 1).reverse)=
      store (scan xs b).1 [] (scan xs b).2 := by
    funext k;fin_cases k <;> simp [store]
  rw [he2] at h2
  have hl : (store [] (scan xs b).1 (scan xs b).2 1).length=xs.length := scan_length xs b
  rw [hl] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

lemma scan_equation (xs : List Bool) (b : Bool) :
    Add.value xs+2^xs.length*Add.bit (scan xs b).2=Add.value (scan xs b).1+Add.bit b := by
  induction xs generalizing b with
  | nil => simp [scan,Add.value]
  | cons a xs ih =>
    have hi := ih (borrow a b)
    have hb := bit_equation a b
    simp only [scan,List.length_cons,Add.value,Nat.pow_succ]
    nlinarith
lemma scan_borrow (xs : List Bool) : (scan xs true).2=true ↔ Add.value xs=0 := by
  have hh := scan_equation xs true
  have hz := Add.value_lt (scan xs true).1
  rw [scan_length] at hz
  have hx := Add.value_lt xs
  cases hb : (scan xs true).2 <;> simp [hb,Add.bit] at hh <;> simp <;> omega
lemma scan_value (xs : List Bool) (hx : 0<Add.value xs) :
    Add.value (scan xs true).1=Add.value xs-1 := by
  have hb : (scan xs true).2=false := by
    cases h : (scan xs true).2
    · rfl
    · have hh := (scan_borrow xs).mp h;omega
  have hh := scan_equation xs true
  simp only [hb,Add.bit,Bool.false_eq_true,↓reduceIte,Nat.mul_zero,Nat.add_zero] at hh
  omega

end SourceBurnside.Structured.Binary.Decrement

namespace SourceBurnside.Structured.Device
open Program Binary
variable {ι : Type} [DecidableEq ι]

lemma last_value (w : List Bool) (hw : w≠[]) (hv : Add.value w.reverse≤1) :
    ∃v b,w=v++[b] ∧ Add.value w.reverse=Add.bit b := by
  induction w using List.reverseRecOn with
  | nil => exact False.elim (hw rfl)
  | append_singleton v b ih =>
    refine ⟨v,b,rfl,?_⟩
    cases b <;> simp [List.reverse_append,Add.value,Add.bit] at * <;> omega

namespace Branch
variable {f g h : (ι → ℕ) → ℕ} {P Q S : ℕ → (ι → ℕ) → Prop}
variable (C : Realizer f P) (A : Realizer g Q) (B : Realizer h S)
abbrev Work := C.W ⊕ (A.W ⊕ (B.W ⊕ Unit))
abbrev L := ι ⊕ Work C A B

def flag : L C A B := .inr (.inl C.out)
def out : L C A B := .inr (.inr (.inr (.inr ())))
def cond : ι ⊕ C.W → L C A B := Sum.map id Sum.inl
def yes : ι ⊕ A.W → L C A B
  | .inl i => .inl i
  | .inr w => if w=A.out then out C A B else .inr (.inr (.inl w))
def no : ι ⊕ B.W → L C A B
  | .inl i => .inl i
  | .inr w => if w=B.out then out C A B else .inr (.inr (.inr (.inl w)))
lemma cond_injective : Function.Injective (cond C A B) := by
  intro firstValue secondValue equality
  cases firstValue <;> cases secondValue <;> simp_all [cond]
lemma yes_injective : Function.Injective (yes C A B) := by
  intro x y hh;cases x with
  | inl i => cases y with
    | inl j => simpa [yes] using hh
    | inr w => by_cases hw : w=A.out <;> simp_all [yes,out]
  | inr v => cases y with
    | inl i => by_cases hv : v=A.out <;> simp_all [yes,out]
    | inr w => by_cases hv : v=A.out <;> by_cases hw : w=A.out <;> simp_all [yes,out]
lemma no_injective : Function.Injective (no C A B) := by
  intro x y hh;cases x with
  | inl i => cases y with
    | inl j => simpa [no] using hh
    | inr w => by_cases hw : w=B.out <;> simp_all [no,out]
  | inr v => cases y with
    | inl i => by_cases hv : v=B.out <;> simp_all [no,out]
    | inr w => by_cases hv : v=B.out <;> by_cases hw : w=B.out <;> simp_all [no,out]

def body (b : Bool) : Program (L C A B) := .seq
  (if b then A.program.relabel (yes C A B) else B.program.relabel (no C A B)) (clear (flag C A B))
def program : Program (L C A B) := .seq (C.program.relabel (cond C A B))
  (.pop (flag C A B) (fun b => body C A B (b.getD false)))
def pending (xs : ι → List Bool) (v : List Bool) : Store (L C A B) := Function.update (input xs) (flag C A B) v

lemma finish_run (xs : ι → List Bool) (v y : List Bool) :
    Run (clear (flag C A B)) (Function.update (pending C A B xs v) (out C A B) y) (2*v.length+1)
      (Function.update (input xs) (out C A B) y) := by
  have h := clear_run (flag C A B) (Function.update (pending C A B xs v) (out C A B) y)
  have hl : (Function.update (pending C A B xs v) (out C A B) y) (flag C A B)=v := by simp [pending,flag,out]
  rw [hl] at h
  have he : Function.update (Function.update (pending C A B xs v) (out C A B) y) (flag C A B) []=
      Function.update (input xs) (out C A B) y := by
    funext k
    by_cases hk : k=flag C A B
    · subst k;simp [flag,out,input]
    · by_cases ho : k=out C A B
      · subst k
        have hfo : out C A B≠flag C A B := by simp [flag,out]
        simp only [Function.update_of_ne hfo,Function.update_self]
      · simp only [pending,Function.update_of_ne hk,Function.update_of_ne ho]
  rwa [he] at h

lemma branch_call {j : (ι → ℕ) → ℕ} {Ad : ℕ → (ι → ℕ) → Prop} (D : Realizer j Ad)
    (e : ι ⊕ D.W → L C A B) (he : Function.Injective e) (ho : e (.inr D.out)=out C A B)
    (n : ℕ) (hn : 0<n) (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n) (hp : Ad n (values xs))
    (v : List Bool) (hinit : ∀i,pending C A B xs v (e (.inl i))=xs i)
    (hwork : ∀w,pending C A B xs v (e (.inr w))=[]) :
    ∃t y,t≤D.coefficient*(n+1)^2+2*v.length+1 ∧ y.length=n ∧ Add.value y.reverse=j (values xs) ∧
      Run (.seq (D.program.relabel e) (clear (flag C A B))) (pending C A B xs v) t
        (Function.update (input xs) (out C A B) y) := by
  obtain ⟨t,y,ht,hy,hval,hRun⟩ := D.transport e he n hn xs hxs hp (pending C A B xs v) hinit hwork
  rw [ho] at hRun
  have hclear := finish_run C A B xs v y
  exact ⟨t+(2*v.length+1),y,by omega,hy,hval,Run.seq _ _ _ _ _ _ _ hRun hclear⟩

lemma body_run (b : Bool) (n : ℕ) (hn : 0<n) (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n)
    (v : List Bool) (hp : if b then Q n (values xs) else S n (values xs)) :
    ∃t y,t≤(A.coefficient+B.coefficient)*(n+1)^2+2*v.length+1 ∧ y.length=n ∧
      Add.value y.reverse=(if b then g (values xs) else h (values xs)) ∧
      Run (body C A B b) (pending C A B xs v) t (Function.update (input xs) (out C A B) y) := by
  cases b
  · obtain ⟨t,y,ht,hy,hv,hR⟩ := branch_call C A B B (no C A B) (no_injective C A B)
      (by simp [no]) n hn xs hxs hp v
      (by intro i;simp [pending,no,flag,input,-Sum.update_elim_inr,-Sum.elim_update_right])
      (by intro w;by_cases hw : w=B.out <;> simp [pending,no,flag,out,input,hw,-Sum.update_elim_inr,-Sum.elim_update_right])
    exact ⟨t,y,by nlinarith,hy,hv,hR⟩
  · obtain ⟨t,y,ht,hy,hv,hR⟩ := branch_call C A B A (yes C A B) (yes_injective C A B)
      (by simp [yes]) n hn xs hxs hp v
      (by intro i;simp [pending,yes,flag,input,-Sum.update_elim_inr,-Sum.elim_update_right])
      (by intro w;by_cases hw : w=A.out <;> simp [pending,yes,flag,out,input,hw,-Sum.update_elim_inr,-Sum.elim_update_right])
    exact ⟨t,y,by nlinarith,hy,hv,hR⟩

lemma program_run (n : ℕ) (hn : 0<n) (xs : ι → List Bool) (hxs : ∀i,(xs i).length=n)
    (hP : P n (values xs)) (hf : f (values xs)≤1)
    (hp : if f (values xs)=0 then S n (values xs) else Q n (values xs)) :
    ∃t y,t≤(C.coefficient+A.coefficient+B.coefficient+4)*(n+1)^2 ∧ y.length=n ∧
      Add.value y.reverse=(if f (values xs)=0 then h (values xs) else g (values xs)) ∧
      Run (program C A B) (input xs) t (Function.update (input xs) (out C A B) y) := by
  obtain ⟨tc,yc,htc,hyc,hvc,hc⟩ := C.transport (cond C A B) (cond_injective C A B) n hn xs hxs hP
    (input xs) (by intro i;rfl) (by intro w;rfl)
  have hc' : Run (C.program.relabel (cond C A B)) (input xs) tc (pending C A B xs yc) := hc
  have hyn : yc≠[] := by intro he;rw [he] at hyc;simp at hyc;omega
  obtain ⟨v,b,hvb,hval⟩ := last_value yc hyn (hvc ▸ hf)
  have hb : f (values xs)=Add.bit b := hvc.symm.trans hval
  have had : if b then Q n (values xs) else S n (values xs) := by cases b <;> simpa [hb,Add.bit] using hp
  obtain ⟨tb,y,htb,hy,hyv,hr⟩ := body_run C A B b n hn xs hxs v had
  have pp : pending C A B xs yc (flag C A B)=v++[b] := by simp [pending,hvb]
  have pu : Function.update (pending C A B xs yc) (flag C A B) v=pending C A B xs v := by simp [pending]
  have hpop : Run (.pop (flag C A B) (fun bb => body C A B (bb.getD false)))
      (pending C A B xs yc) (1+tb) (Function.update (input xs) (out C A B) y) := by
    refine Run.pop _ _ _ _ _ ?_
    simpa only [pp,List.getLast?_concat,List.dropLast_concat,Option.getD_some,pu] using hr
  have H := Run.seq _ _ _ _ _ _ _ hc' hpop
  refine ⟨tc+(1+tb),y,?_,hy,?_,H⟩
  · have hvlen : v.length+1=n := by rw [hvb,List.length_append,List.length_singleton] at hyc;exact hyc
    nlinarith
  · cases b <;> simpa [hb,Add.bit] using hyv

def realizer : Realizer (fun vs => if f vs=0 then h vs else g vs)
    (fun n vs => P n vs ∧ f vs≤1 ∧ (if f vs=0 then S n vs else Q n vs)) where
  W := Work C A B
  finiteW := inferInstance
  eqW := inferInstance
  out := .inr (.inr (.inr ()))
  program := program C A B
  coefficient := C.coefficient+A.coefficient+B.coefficient+4
  spec := by
    intro n hn xs hs hp
    exact program_run C A B n hn xs hs hp.1 hp.2.1 hp.2.2
end Branch
end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Binary.Power
open Program

def store (cnt acc ys : List Bool) : Store K := ![cnt.reverse,acc.reverse,[],[],[],ys.reverse]
def trial (cnt acc ys : List Bool) (b : List Bool) : Store K := ![cnt.reverse,acc.reverse,[],b,[],ys.reverse]

def finish (b : Bool) : Program K := if b then mapInPlace (fun _ => false) 0 4 else shift 1 4
def step : Program K := .seq (.push 3 true) (.seq (Decrement.program.relabel regs)
  (.pop 3 (fun b => finish (b.getD false))))
def program : Program K := .loop 5 (fun _ => step)

lemma finish_run (cnt acc ys : List Bool) (b : Bool) (hlen : cnt.length=acc.length) (ha : acc≠[]) :
    Run (finish b) (store cnt acc ys) (4*cnt.length+2)
      (store (if b then List.replicate cnt.length false else cnt) (if b then acc else Add.double acc) ys) := by
  cases b
  · have H := shift_run (1:K) 4 (by decide) (store cnt acc ys) (by rfl) (by simpa [store] using ha)
    have he : Function.update (store cnt acc ys) 1 ((store cnt acc ys 1).tail++[false])=store cnt (Add.double acc) ys := by
      funext k;fin_cases k <;> simp [store,Add.double_reverse]
    rw [he] at H
    have hl : (store cnt acc ys 1).length=cnt.length := by simp [store,hlen]
    rw [hl] at H
    exact H
  · have H := mapInPlace_run (fun _ => false) (0:K) 4 (by decide) (store cnt acc ys) (by rfl)
    have he : Function.update (store cnt acc ys) 0 ((store cnt acc ys 0).map (fun _ => false))=
        store (List.replicate cnt.length false) acc ys := by
      funext k;fin_cases k <;> simp [store]
    rw [he] at H
    simpa [store,finish] using H

lemma step_run (cnt acc ys : List Bool) (hlen : cnt.length=acc.length) (ha : acc≠[]) :
    Run step (store cnt acc ys) (10*cnt.length+6) (store (oneStep cnt acc).1 (oneStep cnt acc).2 ys) := by
  have h1 := Run.push (store cnt acc ys) (3:K) true
  have he1 : Function.update (store cnt acc ys) 3 ((store cnt acc ys 3)++[true])=trial cnt acc ys [true] := by
    funext k;fin_cases k <;> simp [store,trial]
  rw [he1] at h1
  let dc := Decrement.scan cnt true
  have h2 : Run (Decrement.program.relabel regs) (trial cnt acc ys [true]) (6*cnt.length+2)
      (trial dc.1 acc ys [dc.2]) := by
    refine (Decrement.program_run cnt true).relabel_to regs regs_injective _ _ ?_ ?_ ?_
    · intro k;fin_cases k <;> rfl
    · intro k;fin_cases k <;> rfl
    · intro l hl;fin_cases l
      · exact False.elim (hl 0 rfl)
      · rfl
      · exact False.elim (hl 1 rfl)
      · exact False.elim (hl 2 rfl)
      · rfl
      · rfl
  have hdlen : dc.1.length=cnt.length := Decrement.scan_length cnt true
  have h3 : Run (.pop (3:K) (fun b => finish (b.getD false))) (trial dc.1 acc ys [dc.2])
      (1+(4*cnt.length+2)) (store (oneStep cnt acc).1 (oneStep cnt acc).2 ys) := by
    refine Run.pop _ _ _ _ _ ?_
    have hc : trial dc.1 acc ys [dc.2] 3=[dc.2] := rfl
    have he : Function.update (trial dc.1 acc ys [dc.2]) 3 []=store dc.1 acc ys := by
      funext k;fin_cases k <;> simp [trial,store]
    simp only [hc,List.getLast?_singleton,Option.getD_some,List.dropLast_singleton,he]
    have H := finish_run dc.1 acc ys dc.2 (hdlen.trans hlen) ha
    rw [hdlen] at H
    cases hb : dc.2 <;> simpa [oneStep,dc,hb] using H
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

lemma program_run (cnt acc ys : List Bool) (hlen : cnt.length=acc.length) (ha : acc≠[]) :
    Run program (store cnt acc ys) ((10*cnt.length+7)*ys.length+1)
      (store (iter ys.length cnt acc).1 (iter ys.length cnt acc).2 []) := by
  induction ys generalizing cnt acc with
  | nil => exact Run.loop_nil (store cnt acc []) (5:K) (fun _ => step) (by rfl)
  | cons b ys ih =>
    have hh := oneStep_lengths cnt acc ha
    have hn : (oneStep cnt acc).2≠[] := by intro he;have hp := List.length_pos_iff.mpr ha;rw [he] at hh;simp at hh;omega
    have hlen' : (oneStep cnt acc).1.length=(oneStep cnt acc).2.length := by omega
    have ht := ih (oneStep cnt acc).1 (oneStep cnt acc).2 hlen' hn
    rw [hh.1] at ht
    have he : Function.update (store cnt acc (b::ys)) 5 ys.reverse=store cnt acc ys := by
      funext k;fin_cases k <;> simp [store]
    have hs := step_run cnt acc ys hlen ha
    have H := Run.loop_cons (store cnt acc (b::ys)) (5:K) (fun _ => step) ys.reverse b _ _ _ _
      (by simp [store]) (by rw [he];exact hs) ht
    convert H using 1 <;> first | rfl | simp;ring

lemma oneStep_counter (cnt acc : List Bool) : Add.value (oneStep cnt acc).1=Add.value cnt-1 := by
  by_cases hz : Add.value cnt=0
  · have hb := (Decrement.scan_borrow cnt).mpr hz
    simp [oneStep,hb,Divide.zero_value,hz]
  · have hb : (Decrement.scan cnt true).2=false := Bool.eq_false_iff.mpr (by intro h;exact hz ((Decrement.scan_borrow cnt).mp h))
    simpa [oneStep,hb] using Decrement.scan_value cnt (by omega)

lemma oneStep_value (cnt acc : List Bool) (ha : acc≠[]) :
    Add.value (oneStep cnt acc).2=
      if Add.value cnt=0 then Add.value acc else (2*Add.value acc)%2^acc.length := by
  by_cases hz : Add.value cnt=0
  · have hb := (Decrement.scan_borrow cnt).mpr hz
    simp [oneStep,hb,hz]
  · have hb : (Decrement.scan cnt true).2=false := Bool.eq_false_iff.mpr (by intro h;exact hz ((Decrement.scan_borrow cnt).mp h))
    simp [oneStep,hb,hz,Add.double_value acc ha]

lemma iter_value (m : ℕ) (cnt acc : List Bool) (ha : acc≠[]) :
    Add.value (iter m cnt acc).2=(Add.value acc*2^(min m (Add.value cnt)))%2^acc.length := by
  induction m generalizing cnt acc with
  | zero => simpa [iter] using (Nat.mod_eq_of_lt (Add.value_lt acc)).symm
  | succ m ih =>
    have hl := oneStep_lengths cnt acc ha
    have hn : (oneStep cnt acc).2≠[] := by intro he;have hp := List.length_pos_iff.mpr ha;rw [he] at hl;simp at hl;omega
    have H := ih (oneStep cnt acc).1 (oneStep cnt acc).2 hn
    change Add.value (iter m (oneStep cnt acc).1 (oneStep cnt acc).2).2=_
    rw [H,oneStep_counter,oneStep_value cnt acc ha,hl.2]
    by_cases hz : Add.value cnt=0
    · simp [hz]
    · have hm : min (m+1) (Add.value cnt)=min m (Add.value cnt-1)+1 := by omega
      rw [ite_eq_right hz,hm,Nat.pow_succ]
      rw [Nat.mod_mul_mod]
      congr 1
      ring
end SourceBurnside.Structured.Binary.Power

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type} [DecidableEq K]
def one (src tmp : K) : Program K := .seq (mapInPlace (fun _ => false) src tmp) (.pop src (fun _ => .push src true))
lemma one_run (src tmp : K) (hne : src≠tmp) (r : Store K) (ht : r tmp=[]) :
    Run (one src tmp) r (4*(r src).length+4)
      (Function.update r src (Device.CompareOperator.padded (r src).length true)) := by
  let s := Function.update r src (List.replicate (r src).length false)
  have h1 := mapInPlace_run (fun _ => false) src tmp hne r ht
  have he1 : Function.update r src ((r src).map (fun _ => false))=s := by simp [s]
  rw [he1] at h1
  let t := Function.update r src (List.replicate ((r src).length-1) false)
  have h2 : Run (.pop src (fun _ => Program.push src true)) s 2
      (Function.update r src (Device.CompareOperator.padded (r src).length true)) := by
    refine Run.pop s src _ 1 _ ?_
    have h3 := Run.push t src true
    simpa [t,s,Device.CompareOperator.padded,List.dropLast_replicate] using h3
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rfl
end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Device
open Program Binary
namespace PowerOperator

def load : Program L := .seq (copy (.inl 0) (.inr 0) (.inr 4))
  (.seq (copy (.inl 0) (.inr 1) (.inr 4))
  (.seq (one (.inr 1) (.inr 4)) (copy (.inl 0) (.inr 5) (.inr 4))))
def program : Program L := .seq load (.seq (Power.program.relabel Sum.inr) (clear (.inr 0)))
def loaded (xs : Fin 1 → List Bool) (n : ℕ) : Store L :=
  Sum.elim xs (Power.store (xs 0).reverse (CompareOperator.padded n true).reverse (xs 0).reverse)

lemma load_run (xs : Fin 1 → List Bool) (n : ℕ) (hs : (xs 0).length=n) :
    Run load (input xs) (19*n+10) (loaded xs n) := by
  let R : Store L := input xs
  let R1 := Function.update R (.inr (0:Fin 6)) (xs 0)
  let R2 := Function.update R1 (.inr (1:Fin 6)) (xs 0)
  let R3 := Function.update R1 (.inr (1:Fin 6)) (CompareOperator.padded n true)
  have h1 := copy_run (.inl (0:Fin 1)) (.inr (0:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R (by rfl)
  change Run (copy (.inl (0:Fin 1)) (.inr (0:Fin 6)) (.inr 4)) R (5*(xs 0).length+2) R1 at h1
  rw [hs] at h1
  have h2 := copy_run (.inl (0:Fin 1)) (.inr (1:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R1
    (by simp [R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update R1 (.inr 1) (R1 (.inr 1)++R1 (.inl 0))=R2 := by
    simp [R2,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have hl2 : (R1 (.inl 0)).length=n := by simp [R1,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have h3 := one_run (.inr (1:Fin 6)) (.inr 4) (by simp) R2
    (by simp [R2,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have hl3 : (R2 (.inr 1)).length=n := by simp [R2,hs]
  rw [hl3] at h3
  have he3 : Function.update R2 (.inr 1) (CompareOperator.padded n true)=R3 := by simp [R3,R2]
  rw [he3] at h3
  have h4 := copy_run (.inl (0:Fin 1)) (.inr (5:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R3
    (by simp [R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he4 : Function.update R3 (.inr 5) (R3 (.inr 5)++R3 (.inl 0))=loaded xs n := by
    funext k;cases k with
    | inl i => simp [loaded,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,Power.store,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he4] at h4
  have hl4 : (R3 (.inl 0)).length=n := by simp [R3,R1,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl4] at h4
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | omega

lemma program_correct (xs : Fin 1 → List Bool) (n : ℕ) (hn : 0<n) (hs : (xs 0).length=n)
    (hsmall : values xs 0<n) :
    ∃t y,t≤50*(n+1)^2 ∧ y.length=n ∧ Add.value y.reverse=2^(values xs 0) ∧
      Run program (input xs) t (result xs (1:Fin 6) y) := by
  let cnt := (xs 0).reverse
  let acc := (CompareOperator.padded n true).reverse
  let ys := (xs 0).reverse
  let qr := Power.iter ys.length cnt acc
  have hcnt : cnt.length=n := by simp [cnt,hs]
  have hacc : acc.length=n := by simpa [acc] using CompareOperator.padded_length n hn true
  have hav : Add.value acc=1 := by simp [acc,CompareOperator.padded_value,Add.bit]
  have ha : acc≠[] := by intro h;rw [h] at hacc;simp at hacc;omega
  have hy : ys.length=n := by simp [ys,hs]
  have hl := Power.iter_lengths ys.length cnt acc ha
  have hc' : qr.1.length=n := hl.1.trans hcnt
  have ha' : qr.2.length=n := hl.2.trans hacc
  let R : Store L := Sum.elim xs (Power.store qr.1 qr.2 [])
  have H1 := load_run xs n hs
  have H2 : Run (Power.program.relabel Sum.inr) (loaded xs n) ((10*n+7)*n+1) R := by
    have H := (Power.program_run cnt acc ys (hcnt.trans hacc.symm) ha).relabel_to Sum.inr Sum.inr_injective
      (loaded xs n) R (by intro k;rfl) (by intro k;rfl) (by
        intro l hl;cases l with
        | inl i => rfl
        | inr k => exact False.elim (hl k rfl))
    simpa [hcnt,hy] using H
  have H3 := clear_run (.inr (0:Fin 6)) R
  have hl3 : (R (.inr 0)).length=n := by simp only [R,Sum.elim_inr,Power.store,Matrix.cons_val_zero,List.length_reverse];exact hc'
  rw [hl3] at H3
  have he3 : Function.update R (.inr 0) []=result xs (1:Fin 6) qr.2.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,Power.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at H3
  have H := Run.seq _ _ _ _ _ _ _ H1 (Run.seq _ _ _ _ _ _ _ H2 H3)
  refine ⟨(10*n+7)*n+21*n+12,qr.2.reverse,by nlinarith,by simpa using ha',?_,?_⟩
  · simp only [List.reverse_reverse]
    have hv := Power.iter_value ys.length cnt acc ha
    rw [hy,hacc,hav,Nat.one_mul] at hv
    change Add.value (Power.iter n cnt acc).2 = 2^min n (values xs 0)%2^n at hv
    rw [Nat.min_eq_right (Nat.le_of_lt hsmall)] at hv
    have hp : 2^(values xs 0)<2^n := Nat.pow_lt_pow_right (by decide) hsmall
    simpa [qr,hy] using hv.trans (Nat.mod_eq_of_lt hp)
  · convert H using 1 <;> first | rfl | omega
end PowerOperator

def powerTwo : Realizer (fun vs : Fin 1 → ℕ => 2^(vs 0)) (fun n vs => vs 0<n) where
  W := Fin 6
  finiteW := inferInstance
  eqW := inferInstance
  out := 1
  program := PowerOperator.program
  coefficient := 50
  spec := by
    intro n hn xs hs hp
    exact PowerOperator.program_correct xs n hn (hs 0) hp
end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Device
open Program Binary
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable {f : (ι → ℕ) → ℕ} {P : ℕ → (ι → ℕ) → Prop}

def Realizer.weaken (D : Realizer f P) (Q : ℕ → (ι → ℕ) → Prop)
    (h : ∀n vs,Q n vs → P n vs) : Realizer f Q where
  W := D.W
  finiteW := D.finiteW
  eqW := D.eqW
  out := D.out
  program := D.program
  coefficient := D.coefficient
  spec := by intro n hn xs hs hp;exact D.spec n hn xs hs (h n (values xs) hp)

def Realizer.reinput (D : Realizer f P) (e : ι → κ) (he : Function.Injective e) :
    Realizer (fun vs => f (vs ∘ e)) (fun n vs => P n (vs ∘ e)) where
  W := D.W
  finiteW := D.finiteW
  eqW := D.eqW
  out := D.out
  program := D.program.relabel (Sum.map e id)
  coefficient := D.coefficient
  spec := by
    intro n hn xs hs hp
    have he' : Function.Injective (Sum.map e (id:D.W → D.W)) := by
      intro x y hxy;cases x <;> cases y
      · exact congrArg Sum.inl (he (by simpa using hxy))
      · simp at hxy
      · simp at hxy
      · simpa using hxy
    have H := D.transport (Sum.map e id) he' n hn (xs ∘ e) (by intro i;exact hs (e i)) hp
      (input xs) (by intro i;rfl) (by intro w;rfl)
    exact H

def composeUnary {g : (Fin 1 → ℕ) → ℕ} {Q : ℕ → (Fin 1 → ℕ) → Prop}
    (D : Realizer f P) (O : Realizer g Q) :
    Realizer (fun vs => g (fun _ => f vs)) (fun n vs => P n vs ∧ Q n (fun _ => f vs)) := by
  let e : Fin 1 → Fin 2 := fun _ => 0
  let O' := O.reinput e (by intro i j h;exact Subsingleton.elim i j)
  have hh := Compose.realizer (op:=fun a _ => g (fun _ => a)) D D O'
  exact hh.weaken _ (by intro n vs h;exact ⟨h.1,h.1,h.2⟩)

end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Binary.Increment
open Program

def store (xs out : List Bool) (b : Bool) : Store K := ![xs.reverse,out,[b]]
def partialStore (xs out : List Bool) : Store K := ![xs.reverse,out,[]]
lemma bit_equation (a b : Bool) : Add.bit a+Add.bit b=Add.bit (low a b)+2*Add.bit (carry a b) := by
  cases a <;> cases b <;> decide

def step (a : Bool) : Program K := .pop 2 (fun b =>
  .seq (.push 1 (low a (b.getD false))) (.push 2 (carry a (b.getD false))))
def pass : Program K := .loop 0 step
def program : Program K := .seq pass (move 1 0)

lemma step_run (xs out : List Bool) (a b : Bool) :
    Run (step a) (store xs out b) 3 (store xs (out++[low a b]) (carry a b)) := by
  have h1 := Run.push (partialStore xs out) (1:K) (low a b)
  let t := Function.update (partialStore xs out) 1 (out++[low a b])
  have hx : Run (.push (1:K) (low a b)) (partialStore xs out) 1 t := by simpa [partialStore,t] using h1
  have h2 := Run.push t (2:K) (carry a b)
  have he2 : Function.update t 2 (t 2++[carry a b])=store xs (out++[low a b]) (carry a b) := by
    funext k;fin_cases k <;> simp [t,partialStore,store]
  rw [he2] at h2
  have hs := Run.seq _ _ _ _ _ _ _ hx h2
  unfold step
  refine Run.pop (store xs out b) (2:K) _ 2 _ ?_
  change Run (.seq (.push 1 (low a b)) (.push 2 (carry a b)))
    (Function.update (store xs out b) 2 []) 2 _
  have he : Function.update (store xs out b) 2 []=partialStore xs out := by funext k;fin_cases k <;> simp [store,partialStore]
  rw [he];exact hs

lemma pass_run (xs out : List Bool) (b : Bool) :
    Run pass (store xs out b) (4*xs.length+1) (store [] (out++(scan xs b).1) (scan xs b).2) := by
  induction xs generalizing out b with
  | nil => simpa [pass,scan] using Run.loop_nil (store [] out b) (0:K) step (by rfl)
  | cons a xs ih =>
    have he : Function.update (store (a::xs) out b) 0 xs.reverse=store xs out b := by
      funext k;fin_cases k <;> simp [store]
    have hb := step_run xs out a b
    have ht := ih (out++[low a b]) (carry a b)
    have H := Run.loop_cons (store (a::xs) out b) (0:K) step xs.reverse a _ _ 3 (4*xs.length+1)
      (by simp [store]) (by rw [he];exact hb) ht
    have hs : store [] (out++[low a b]++(scan xs (carry a b)).1) (scan xs (carry a b)).2=
        store [] (out++(scan (a::xs) b).1) (scan (a::xs) b).2 := by simp [scan,List.append_assoc]
    rw [hs] at H
    convert H using 1 <;> first | rfl | simp;omega

lemma program_run (xs : List Bool) (b : Bool) :
    Run program (store xs [] b) (6*xs.length+2) (store (scan xs b).1 [] (scan xs b).2) := by
  have h1 := pass_run xs [] b
  simp only [List.nil_append] at h1
  have h2 := move_run (1:K) 0 (by decide) (store [] (scan xs b).1 (scan xs b).2)
  have he2 : Function.update (Function.update (store [] (scan xs b).1 (scan xs b).2) 1 []) 0
      (store [] (scan xs b).1 (scan xs b).2 0++(store [] (scan xs b).1 (scan xs b).2 1).reverse)=
      store (scan xs b).1 [] (scan xs b).2 := by
    funext k;fin_cases k <;> simp [store]
  rw [he2] at h2
  have hl : (store [] (scan xs b).1 (scan xs b).2 1).length=xs.length := scan_length xs b
  rw [hl] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega

lemma scan_equation (xs : List Bool) (b : Bool) :
    Add.value xs+Add.bit b=Add.value (scan xs b).1+2^xs.length*Add.bit (scan xs b).2 := by
  induction xs generalizing b with
  | nil => simp [scan,Add.value]
  | cons a xs ih =>
    have hi := ih (carry a b)
    have hb := bit_equation a b
    simp only [scan,List.length_cons,Add.value,Nat.pow_succ]
    nlinarith
lemma scan_value (xs : List Bool) (hx : Add.value xs+1<2^xs.length) :
    Add.value (scan xs true).1=Add.value xs+1 := by
  have hh := scan_equation xs true
  have hb : (scan xs true).2=false := by
    cases h : (scan xs true).2
    · rfl
    · simp [h,Add.bit] at hh;omega
  simp [hb,Add.bit] at hh
  omega
end SourceBurnside.Structured.Binary.Increment

namespace SourceBurnside.Structured.Binary.BitSize
open Program

def store (xs cnt len : List Bool) : Store K := ![xs.reverse,cnt.reverse,len.reverse,[],[]]
def trial (xs cnt len : List Bool) (flag : List Bool) : Store K := ![xs.reverse,cnt.reverse,len.reverse,[],flag]

def finish (a : Bool) : Program K := if a then .seq (clear 2) (copy 1 2 3) else .skip
def step (a : Bool) : Program K := .seq (.push 4 true) (.seq (Increment.program.relabel regs)
  (.pop 4 (fun _ => finish a)))
def program : Program K := .loop 0 step

lemma finish_run (a : Bool) (xs cnt len : List Bool) (h : cnt.length=len.length) :
    ∃t,t≤7*cnt.length+3 ∧ Run (finish a) (store xs cnt len) t (store xs cnt (if a then cnt else len)) := by
  cases a
  · exact ⟨1,by omega,Run.skip _⟩
  · let R := store xs cnt len
    let S := Function.update R (2:K) []
    have h1 := clear_run (2:K) R
    have hl : (R 2).length=cnt.length := by simp [R,store,h]
    rw [hl] at h1
    have h2 := copy_run (1:K) 2 3 (by decide) (by decide) (by decide) S (by simp [S,R,store])
    have he : Function.update S 2 (S 2++S 1)=store xs cnt cnt := by
      funext k;fin_cases k <;> simp [S,R,store]
    rw [he] at h2
    have hl2 : (S 1).length=cnt.length := by simp [S,R,store]
    rw [hl2] at h2
    refine ⟨7*cnt.length+3,le_rfl,?_⟩
    have H := Run.seq _ _ _ _ _ _ _ h1 h2
    convert H using 1 <;> first | rfl | omega

lemma step_run (a : Bool) (xs cnt len : List Bool) (h : cnt.length=len.length) :
    ∃t,t≤13*cnt.length+7 ∧ Run (step a) (store xs cnt len) t
      (store xs (oneStep a cnt len).1 (oneStep a cnt len).2) := by
  have h1 := Run.push (store xs cnt len) (4:K) true
  have he1 : Function.update (store xs cnt len) 4 ((store xs cnt len 4)++[true])=trial xs cnt len [true] := by
    funext k;fin_cases k <;> simp [store,trial]
  rw [he1] at h1
  let dc := Increment.scan cnt true
  have h2 : Run (Increment.program.relabel regs) (trial xs cnt len [true]) (6*cnt.length+2)
      (trial xs dc.1 len [dc.2]) := by
    refine (Increment.program_run cnt true).relabel_to regs regs_injective _ _ ?_ ?_ ?_
    · intro k;fin_cases k <;> rfl
    · intro k;fin_cases k <;> rfl
    · intro l hl;fin_cases l
      · rfl
      · exact False.elim (hl 0 rfl)
      · rfl
      · exact False.elim (hl 1 rfl)
      · exact False.elim (hl 2 rfl)
  have hdc : dc.1.length=cnt.length := Increment.scan_length cnt true
  obtain ⟨t,ht,h3⟩ := finish_run a xs dc.1 len (hdc.trans h)
  have h4 : Run (.pop (4:K) (fun _ => finish a)) (trial xs dc.1 len [dc.2]) (1+t)
      (store xs (oneStep a cnt len).1 (oneStep a cnt len).2) := by
    refine Run.pop _ _ _ _ _ ?_
    have hc : trial xs dc.1 len [dc.2] 4=[dc.2] := rfl
    have he : Function.update (trial xs dc.1 len [dc.2]) 4 []=store xs dc.1 len := by
      funext k;fin_cases k <;> simp [trial,store]
    simpa only [hc,List.getLast?_singleton,List.dropLast_singleton,he,oneStep] using h3
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h4)
  refine ⟨1+(6*cnt.length+2+(1+t)),by rw [hdc] at ht;omega,H⟩

lemma program_run (xs cnt len : List Bool) (h : cnt.length=len.length) :
    ∃t,t≤(13*cnt.length+8)*xs.length+1 ∧
      Run program (store xs cnt len) t (store [] (iter xs cnt len).1 (iter xs cnt len).2) := by
  induction xs generalizing cnt len with
  | nil => exact ⟨1,by simp,Run.loop_nil _ _ _ rfl⟩
  | cons a xs ih =>
    obtain ⟨t,ht,H⟩ := step_run a xs cnt len h
    have hh := oneStep_lengths a cnt len h
    obtain ⟨u,hu,U⟩ := ih (oneStep a cnt len).1 (oneStep a cnt len).2 (hh.1.trans (h.trans hh.2.symm))
    have he : Function.update (store (a::xs) cnt len) 0 xs.reverse=store xs cnt len := by
      funext k;fin_cases k <;> simp [store]
    refine ⟨1+t+u,?_,?_⟩
    · rw [hh.1] at hu;simp only [List.length_cons];nlinarith
    · have HH := Run.loop_cons (store (a::xs) cnt len) (0:K) step xs.reverse a _ _ t u (by simp [store]) (by rw [he];exact H) U
      convert HH using 1 <;> first | rfl | omega

lemma iter_value (xs cnt len : List Bool) (h : cnt.length=len.length)
    (hb : Add.value cnt+xs.length<2^cnt.length) :
    Add.value (iter xs cnt len).1=Add.value cnt+xs.length ∧
      Add.value (iter xs cnt len).2=measure xs (Add.value cnt) (Add.value len) := by
  induction xs generalizing cnt len with
  | nil => simp [iter,measure]
  | cons a xs ih =>
    have hc : Add.value cnt+1<2^cnt.length := by simp only [List.length_cons] at hb;omega
    have hv := Increment.scan_value cnt hc
    have hh := oneStep_lengths a cnt len h
    have hstep : Add.value (oneStep a cnt len).1=Add.value cnt+1 := hv
    have hlen : Add.value (oneStep a cnt len).2=if a then Add.value cnt+1 else Add.value len := by
      cases a <;> simp [oneStep,hv]
    have hi := ih (oneStep a cnt len).1 (oneStep a cnt len).2 (hh.1.trans (h.trans hh.2.symm))
      (by rw [hh.1,hstep];simp only [List.length_cons] at hb;omega)
    simpa [iter,measure,hstep,hlen,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi

lemma measure_value (xs : List Bool) (p r : ℕ) :
    measure xs p r=if Add.value xs=0 then r else p+(Add.value xs).size := by
  induction xs generalizing p r with
  | nil => simp [measure,Add.value]
  | cons a xs ih =>
    rw [measure,ih]
    have hb : Add.value (a::xs)=Nat.bit a (Add.value xs) := by
      cases a <;> simp [Add.value,Add.bit,Nat.bit]
      omega
    rw [hb]
    by_cases hz : Add.value xs=0
    · cases a <;> simp [hz,Nat.bit]
    · have hne : Nat.bit a (Add.value xs)≠0 := by
        cases a <;> simp [Nat.bit]
        omega
      simp [hz,hne,Nat.size_bit hne,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm]
end SourceBurnside.Structured.Binary.BitSize

namespace SourceBurnside.Structured.Device
open Program Binary
namespace SizeOperator

def load : Program L := .seq (copy (.inl 0) (.inr 0) (.inr 3))
  (.seq (copy (.inl 0) (.inr 1) (.inr 3))
  (.seq (mapInPlace (fun _ => false) (.inr 1) (.inr 3))
  (.seq (copy (.inl 0) (.inr 2) (.inr 3)) (one (.inr 2) (.inr 3)))))
def program : Program L := .seq load (.seq (BitSize.program.relabel Sum.inr) (clear (.inr 1)))
def loaded (xs : Fin 1 → List Bool) (n : ℕ) : Store L :=
  Sum.elim xs (BitSize.store (xs 0).reverse (List.replicate n false) (CompareOperator.padded n true).reverse)

lemma load_run (xs : Fin 1 → List Bool) (n : ℕ) (hs : (xs 0).length=n) :
    Run load (input xs) (23*n+12) (loaded xs n) := by
  let R : Store L := input xs
  let R1 := Function.update R (.inr (0:Fin 5)) (xs 0)
  let R2 := Function.update R1 (.inr (1:Fin 5)) (xs 0)
  let R3 := Function.update R1 (.inr (1:Fin 5)) (List.replicate n false)
  let R4 := Function.update R3 (.inr (2:Fin 5)) (xs 0)
  have h1 := copy_run (.inl (0:Fin 1)) (.inr (0:Fin 5)) (.inr 3) (by simp) (by simp) (by simp) R rfl
  change Run (copy (.inl (0:Fin 1)) (.inr (0:Fin 5)) (.inr 3)) R (5*(xs 0).length+2) R1 at h1
  rw [hs] at h1
  have h2 := copy_run (.inl (0:Fin 1)) (.inr (1:Fin 5)) (.inr 3) (by simp) (by simp) (by simp) R1
    (by simp [R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update R1 (.inr 1) (R1 (.inr 1)++R1 (.inl 0))=R2 := by
    simp [R2,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have hl2 : (R1 (.inl 0)).length=n := by simp [R1,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have h3 := mapInPlace_run (fun _ => false) (.inr (1:Fin 5)) (.inr 3) (by simp) R2
    (by simp [R2,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have hl3 : (R2 (.inr 1)).length=n := by simp [R2,hs]
  rw [hl3] at h3
  have he3 : Function.update R2 (.inr 1) ((R2 (.inr 1)).map (fun _ => false))=R3 := by simp [R3,R2,hs]
  rw [he3] at h3
  have h4 := copy_run (.inl (0:Fin 1)) (.inr (2:Fin 5)) (.inr 3) (by simp) (by simp) (by simp) R3
    (by simp [R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he4 : Function.update R3 (.inr 2) (R3 (.inr 2)++R3 (.inl 0))=R4 := by
    simp [R4,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he4] at h4
  have hl4 : (R3 (.inl 0)).length=n := by simp [R3,R1,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl4] at h4
  have h5 := one_run (.inr (2:Fin 5)) (.inr 3) (by simp) R4
    (by simp [R4,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have hl5 : (R4 (.inr 2)).length=n := by simp [R4,hs]
  rw [hl5] at h5
  have he5 : Function.update R4 (.inr 2) (CompareOperator.padded n true)=loaded xs n := by
    funext k;cases k with
    | inl i => simp [loaded,R4,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,BitSize.store,R4,R3,R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he5] at h5
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3 (Run.seq _ _ _ _ _ _ _ h4 h5)))
  convert H using 1 <;> first | rfl | omega

lemma program_correct (xs : Fin 1 → List Bool) (n : ℕ) (hn : 0<n) (hs : (xs 0).length=n) :
    ∃t y,t≤60*(n+1)^2 ∧ y.length=n ∧
      Add.value y.reverse=(if values xs 0=0 then 1 else (values xs 0).size) ∧
      Run program (input xs) t (result xs (2:Fin 5) y) := by
  let ys := (xs 0).reverse
  let cnt := List.replicate n false
  let len := (CompareOperator.padded n true).reverse
  let qr := BitSize.iter ys cnt len
  have hy : ys.length=n := by simp [ys,hs]
  have hc : cnt.length=n := List.length_replicate
  have hl : len.length=n := by simpa [len] using CompareOperator.padded_length n hn true
  have hlen : cnt.length=len.length := hc.trans hl.symm
  have hcv : Add.value cnt=0 := Divide.zero_value n
  have hlv : Add.value len=1 := by simp [len,CompareOperator.padded_value,Add.bit]
  have hls := BitSize.iter_lengths ys cnt len hlen
  have hc' : qr.1.length=n := hls.1.trans hc
  have hl' : qr.2.length=n := hls.2.trans hl
  obtain ⟨t,ht,H2'⟩ := BitSize.program_run ys cnt len hlen
  let R : Store L := Sum.elim xs (BitSize.store [] qr.1 qr.2)
  have H2 : Run (BitSize.program.relabel Sum.inr) (loaded xs n) t R := by
    exact H2'.relabel_to Sum.inr Sum.inr_injective _ _ (by intro k;rfl) (by intro k;rfl)
      (by intro k hk;cases k with
          | inl i => rfl
          | inr j => exact False.elim (hk j rfl))
  have H1 := load_run xs n hs
  have H3 := clear_run (.inr (1:Fin 5)) R
  have hl3 : (R (.inr 1)).length=n := by simp only [R,Sum.elim_inr,BitSize.store,Matrix.cons_val_one,Matrix.cons_val_zero,List.length_reverse];exact hc'
  rw [hl3] at H3
  have he3 : Function.update R (.inr 1) []=result xs (2:Fin 5) qr.2.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,BitSize.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at H3
  have H := Run.seq _ _ _ _ _ _ _ H1 (Run.seq _ _ _ _ _ _ _ H2 H3)
  refine ⟨23*n+12+(t+(2*n+1)),qr.2.reverse,?_,by simpa using hl',?_,H⟩
  · rw [hc,hy] at ht;nlinarith
  · simp only [List.reverse_reverse]
    have hv := (BitSize.iter_value ys cnt len hlen (by rw [hcv,hc,hy,Nat.zero_add];exact Nat.lt_two_pow_self)).2
    rw [BitSize.measure_value,hcv,hlv] at hv
    simp only [Nat.zero_add] at hv
    change Add.value qr.2=(if Add.value ys=0 then 1 else (Add.value ys).size)
    exact hv
end SizeOperator

def bitLength : Realizer (fun vs : Fin 1 → ℕ => if vs 0=0 then 1 else (vs 0).size) (fun _ _ => True) where
  W := Fin 5
  finiteW := inferInstance
  eqW := inferInstance
  out := 2
  program := SizeOperator.program
  coefficient := 60
  spec := by intro n hn xs hs hp;exact SizeOperator.program_correct xs n hn (hs 0)
end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Device

namespace Formula
variable {ι : Type} [DecidableEq ι]

def Safe (n : ℕ) (vs : ι → ℕ) : Formula ι → Prop
  | .read _ => True
  | .constant a => a.bits.length≤n
  | .add x y => x.Safe n vs ∧ y.Safe n vs ∧ x.eval vs+y.eval vs<2^n
  | .sub x y => x.Safe n vs ∧ y.Safe n vs ∧ y.eval vs≤x.eval vs
  | .mul x y => x.Safe n vs ∧ y.Safe n vs ∧ x.eval vs*y.eval vs<2^n
  | .div x y | .mod x y => x.Safe n vs ∧ y.Safe n vs ∧ 0<y.eval vs ∧ 2*y.eval vs≤2^n
  | .le x y => x.Safe n vs ∧ y.Safe n vs
  | .powTwo x => x.Safe n vs ∧ x.eval vs<n
  | .bitLength x => x.Safe n vs
  | .branch c a b => c.Safe n vs ∧ c.eval vs≤1 ∧ (if c.eval vs=0 then b.Safe n vs else a.Safe n vs)

def compile (base : ι) : (e : Formula ι) → Realizer e.eval (fun n vs => e.Safe n vs)
  | .read i => Device.read i
  | .constant a => Device.constant base a
  | .add x y => Compose.realizer (compile base x) (compile base y) Device.add
  | .sub x y => Compose.realizer (compile base x) (compile base y) Device.subtract
  | .mul x y => Compose.realizer (compile base x) (compile base y) Device.multiply
  | .div x y => Compose.realizer (op:=Nat.div) (Adm:=fun n vs => 0<vs 1 ∧ 2*vs 1≤2^n) (compile base x) (compile base y) (Device.divide false)
  | .mod x y => Compose.realizer (op:=Nat.mod) (Adm:=fun n vs => 0<vs 1 ∧ 2*vs 1≤2^n) (compile base x) (compile base y) (Device.divide true)
  | .le x y => (Compose.realizer (Adm:=fun _ _ => True) (op:=fun a b => if b≤a then 1 else 0) (compile base y) (compile base x) Device.lessEqualReversed).weaken (fun n vs => (Formula.le x y).Safe n vs)
      (by intro n vs h;exact ⟨h.2,h.1,trivial⟩)
  | .powTwo x => composeUnary (compile base x) Device.powerTwo
  | .bitLength x => (composeUnary (compile base x) Device.bitLength).weaken (fun n vs => x.Safe n vs)
      (by intro n vs h;exact ⟨h,trivial⟩)
  | .branch c a b => Branch.realizer (compile base c) (compile base a) (compile base b)

end Formula
end SourceBurnside.Structured.Device

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_PredicateCompilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.Structured.Device.Formula
section
variable {ι : Type}

def Bounded (n : ℕ) (v : ι → ℕ) : Formula ι → Prop
  | .read _ => True
  | .constant a => a.bits.length≤n
  | .add x y => x.Bounded n v ∧ y.Bounded n v ∧ x.eval v+y.eval v<2^n
  | .sub x y => x.Bounded n v ∧ y.Bounded n v
  | .mul x y => x.Bounded n v ∧ y.Bounded n v ∧ x.eval v*y.eval v<2^n
  | .div x y | .mod x y => x.Bounded n v ∧ y.Bounded n v ∧ 2*y.eval v≤2^n
  | .le x y => x.Bounded n v ∧ y.Bounded n v
  | .powTwo x => x.Bounded n v ∧ x.eval v<n
  | .bitLength x => x.Bounded n v
  | .branch c a b => c.Bounded n v ∧ (if c.eval v=0 then b.Bounded n v else a.Bounded n v)
lemma compare_boolean (x y : Formula ι) (v : ι → ℕ) : (Formula.le x y).eval v≤1 := by
  change (if x.eval v≤y.eval v then 1 else 0)≤1
  split <;> omega
lemma totalize_safe {e : Formula ι} {n : ℕ} {v : ι → ℕ} (hn : 0<n) (he : e.Bounded n v) :
    e.totalize.Safe n v := by
  have H0 : (Formula.constant 0 : Formula ι).Safe n v := by change (Nat.bits 0).length≤n;simp
  have H1 : (Formula.constant 1 : Formula ι).Safe n v := by change (Nat.bits 1).length≤n;norm_num;omega
  induction e with
  | read i => trivial
  | constant a => exact he
  | add x y hx hy => exact ⟨hx he.1,hy he.2.1,by simpa using he.2.2⟩
  | sub x y hx hy =>
    have Hx := hx he.1
    have Hy := hy he.2
    refine ⟨⟨Hy,Hx⟩,compare_boolean _ _ _,?_⟩
    change (if (if y.totalize.eval v≤x.totalize.eval v then 1 else 0)=0 then _ else _)
    simp only [totalize_eval]
    by_cases h : y.eval v≤x.eval v
    · simp only [ite_eq_left h,Nat.one_ne_zero,ite_false]
      exact ⟨Hx,Hy,by simpa using h⟩
    · simpa only [ite_eq_right h,ite_true] using H0
  | mul x y hx hy => exact ⟨hx he.1,hy he.2.1,by simpa using he.2.2⟩
  | div x y hx hy =>
    have Hx := hx he.1
    have Hy := hy he.2.1
    refine ⟨⟨H1,Hy⟩,compare_boolean _ _ _,?_⟩
    change (if (if 1≤y.totalize.eval v then 1 else 0)=0 then _ else _)
    simp only [totalize_eval]
    by_cases h : 1≤y.eval v
    · simp only [ite_eq_left h,Nat.one_ne_zero,ite_false]
      exact ⟨Hx,Hy,by rw [totalize_eval];omega,by simpa using he.2.2⟩
    · simpa only [ite_eq_right h,ite_true] using H0
  | mod x y hx hy =>
    have Hx := hx he.1
    have Hy := hy he.2.1
    refine ⟨⟨H1,Hy⟩,compare_boolean _ _ _,?_⟩
    change (if (if 1≤y.totalize.eval v then 1 else 0)=0 then _ else _)
    simp only [totalize_eval]
    by_cases h : 1≤y.eval v
    · simp only [ite_eq_left h,Nat.one_ne_zero,ite_false]
      exact ⟨Hx,Hy,by rw [totalize_eval];omega,by simpa using he.2.2⟩
    · simpa only [ite_eq_right h,ite_true] using Hx
  | le x y hx hy => exact ⟨hx he.1,hy he.2⟩
  | powTwo x hx => exact ⟨hx he.1,by simpa using he.2⟩
  | bitLength x hx => exact hx he
  | branch c a b hc ha hb =>
    refine ⟨⟨H1,hc he.1⟩,compare_boolean _ _ _,?_⟩
    change (if (if 1 ≤ c.totalize.eval v then 1 else 0)=0 then _ else _)
    simp only [totalize_eval]
    by_cases h : c.eval v=0
    · simpa [h] using hb (by simpa only [h,ite_true] using he.2)
    · simpa only [ite_eq_left (show 1 ≤ c.eval v by omega),Nat.one_ne_zero,ite_false] using ha (by simpa only [ite_eq_right h] using he.2)
end

section
variable {ι : Type}
lemma bounded_mono {e : Formula ι} {m n : ℕ} {v : ι → ℕ} (hmn : m≤n) (he : e.Bounded m v) :
    e.Bounded n v := by
  have hp : 2^m≤2^n := Nat.pow_le_pow_right (by omega) hmn
  induction e with
  | read i => trivial
  | constant a => exact he.trans hmn
  | add x y hx hy => exact ⟨hx he.1,hy he.2.1,he.2.2.trans_le hp⟩
  | sub x y hx hy => exact ⟨hx he.1,hy he.2⟩
  | mul x y hx hy => exact ⟨hx he.1,hy he.2.1,he.2.2.trans_le hp⟩
  | div x y hx hy => exact ⟨hx he.1,hy he.2.1,he.2.2.trans hp⟩
  | mod x y hx hy => exact ⟨hx he.1,hy he.2.1,he.2.2.trans hp⟩
  | le x y hx hy => exact ⟨hx he.1,hy he.2⟩
  | powTwo x hx => exact ⟨hx he.1,he.2.trans_le hmn⟩
  | bitLength x hx => exact hx he
  | branch c a b hc ha hb =>
    refine ⟨hc he.1,?_⟩
    by_cases h : c.eval v=0
    · simpa only [h,ite_true] using hb (by simpa only [h,ite_true] using he.2)
    · simpa only [ite_eq_right h] using ha (by simpa only [ite_eq_right h] using he.2)

def weight : Formula ι → ℕ
  | .read _ => 1
  | .constant a => a.size+1
  | .add x y | .sub x y | .mul x y | .div x y | .mod x y | .le x y => x.weight+y.weight+2
  | .powTwo x | .bitLength x => x.weight+2
  | .branch c a b => c.weight+a.weight+b.weight+2
lemma weight_pos (e : Formula ι) : 0<e.weight := by cases e <;> simp [weight]
lemma width_pos (e : Formula ι) (M : ℕ) : 0<e.weight*(M+1) := Nat.mul_pos e.weight_pos (by omega)
lemma width_binary {x y : Formula ι} (M : ℕ) :
    x.weight*(M+1)+y.weight*(M+1)+2≤(x.weight+y.weight+2)*(M+1) := by nlinarith

theorem bounded_of_exponents (e : Formula ι) (M : ℕ) (v : ι → ℕ)
    (hv : ∀i,v i<2^(M+1)) (he : e.Exponents M v) :
    e.Bounded (e.weight*(M+1)) v ∧ e.eval v<2^(e.weight*(M+1)) := by
  induction e with
  | read i => simpa [Bounded,weight,eval] using And.intro True.intro (hv i)
  | constant a =>
    have hw : a.size≤(a.size+1)*(M+1) := by nlinarith
    exact ⟨by change a.bits.length≤_;simpa only [Nat.size_eq_bits_len,weight] using hw,
      bound_pow_mono ((Nat.size_le).mp (le_refl a.size)) hw⟩
  | add x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,hyv⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    have hb := binary_value_bound hxv hyv (show x.weight*(M+1)+y.weight*(M+1)+1≤(x.weight+y.weight+2)*(M+1) by omega)
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy,hb.1⟩,hb.1⟩
  | sub x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,_⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy⟩,
      (Nat.sub_le _ _).trans_lt (bound_pow_mono hxv (by simp only [weight];omega))⟩
  | mul x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,hyv⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    have hb := binary_value_bound hxv hyv (show x.weight*(M+1)+y.weight*(M+1)+1≤(x.weight+y.weight+2)*(M+1) by omega)
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy,hb.2.1⟩,hb.2.1⟩
  | div x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,hyv⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    have hb := binary_value_bound hxv hyv (show x.weight*(M+1)+y.weight*(M+1)+1≤(x.weight+y.weight+2)*(M+1) by omega)
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy,hb.2.2⟩,
      (Nat.div_le_self _ _).trans_lt (bound_pow_mono hxv (by simp only [weight];omega))⟩
  | mod x y hx hy =>
    obtain ⟨hx,hxv⟩ := hx he.1
    obtain ⟨hy,hyv⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    have hb := binary_value_bound hxv hyv (show x.weight*(M+1)+y.weight*(M+1)+1≤(x.weight+y.weight+2)*(M+1) by omega)
    exact ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy,hb.2.2⟩,
      (Nat.mod_le _ _).trans_lt (bound_pow_mono hxv (by simp only [weight];omega))⟩
  | le x y hx hy =>
    obtain ⟨hx,_⟩ := hx he.1
    obtain ⟨hy,_⟩ := hy he.2
    have hsum := width_binary (x:=x) (y:=y) M
    refine ⟨⟨bounded_mono (by simp only [weight];omega) hx,bounded_mono (by simp only [weight];omega) hy⟩,?_⟩
    have hn := width_pos (x.le y) M
    have hpow : 1<2^((x.le y).weight*(M+1)) := Nat.one_lt_two_pow hn.ne'
    exact (compare_boolean x y v).trans_lt hpow
  | powTwo x hx =>
    obtain ⟨hx,_⟩ := hx he.1
    have hw : x.weight*(M+1)≤(x.weight+2)*(M+1) := by nlinarith
    have hM : M<(x.weight+2)*(M+1) := by nlinarith
    exact ⟨⟨bounded_mono hw hx,he.2.trans_lt hM⟩,Nat.pow_lt_pow_right (by omega) (he.2.trans_lt hM)⟩
  | bitLength x hx =>
    obtain ⟨hx,hxv⟩ := hx he
    have hw : x.weight*(M+1)≤(x.weight+2)*(M+1) := by nlinarith
    have hn := width_pos (x.bitLength) M
    refine ⟨bounded_mono hw hx,?_⟩
    have hs : (x.eval v).size≤x.weight*(M+1) := (Nat.size_le).mpr hxv
    change (if x.eval v=0 then 1 else (x.eval v).size) < _
    split
    · exact Nat.one_lt_two_pow hn.ne'
    · exact (hs.trans hw).trans_lt Nat.lt_two_pow_self
  | branch c a b hc ha hb =>
    obtain ⟨hc,_⟩ := hc he.1
    have hcN : c.weight*(M+1)≤(c.weight+a.weight+b.weight+2)*(M+1) := Nat.mul_le_mul_right _ (by omega)
    have haN : a.weight*(M+1)≤(c.weight+a.weight+b.weight+2)*(M+1) := Nat.mul_le_mul_right _ (by omega)
    have hbN : b.weight*(M+1)≤(c.weight+a.weight+b.weight+2)*(M+1) := Nat.mul_le_mul_right _ (by omega)
    by_cases h : c.eval v=0
    · obtain ⟨hb,hbv⟩ := hb (by simpa [Exponents,h] using he.2)
      exact ⟨⟨bounded_mono hcN hc,by simpa only [ite_eq_left h,weight] using bounded_mono hbN hb⟩,by simpa only [eval,h,ite_true,weight] using bound_pow_mono hbv hbN⟩
    · obtain ⟨ha,hav⟩ := ha (by simpa [Exponents,h] using he.2)
      exact ⟨⟨bounded_mono hcN hc,by simpa only [ite_eq_right h,weight] using bounded_mono haN ha⟩,by simpa only [eval,ite_eq_right h,weight] using bound_pow_mono hav haN⟩
end

section
variable {ι : Type} [DecidableEq ι]

theorem timed_total (base : ι) (e : Formula ι) :
    ∃D : Realizer e.totalize.eval (fun n v => e.totalize.Safe n v),
      ∀M xs,(∀i,(xs i).length=e.weight*(M+1)) →
        (∀i,values xs i<2^(M+1)) → e.Exponents M (values xs) →
        ∃t y,t≤D.coefficient*(e.weight*(M+1)+1)^2 ∧ y.length=e.weight*(M+1) ∧
          Binary.Add.value y.reverse=e.eval (values xs) ∧ Run D.program (input xs) t (result xs D.out y) := by
  refine ⟨compile base e.totalize,?_⟩
  intro M xs hl hv he
  have hB := (bounded_of_exponents e M (values xs) hv he).1
  obtain ⟨t,y,ht,hy,hv',hr⟩ := (compile base e.totalize).spec _ (width_pos e M) xs hl (totalize_safe (width_pos e M) hB)
  exact ⟨t,y,ht,hy,by simpa using hv',hr⟩
end

end SourceBurnside.Structured.Device.Formula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_Compilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.HeaderProgram
open Structured Structured.Program Structured.Binary

def store (todo : List Bool) (count : ℕ) (out ctl : List Bool) : Store K :=
  ![todo.reverse,List.replicate count true,out,ctl]
def step : Program K := .pop 0 (fun a =>
  if a=some true then .seq (.push 1 true) (.push 3 true) else .skip)
def scanPrefix : Program K := .loop 3 (fun _ => step)
def digit : Program K := .pop 0 (fun a => match a with
  | some b => .push 2 b | none => .skip)
def digits : Program K := .loop 1 (fun _ => digit)
def program : Program K := .seq (.push 3 true) (.seq scanPrefix digits)
lemma step_true (todo out : List Bool) (n : ℕ) :
    Run step (store (true::todo) n out []) 3 (store todo (n+1) out [true]) := by
  refine Run.pop _ _ _ 2 _ ?_
  have h : store (true::todo) n out [] 0=todo.reverse++[true] := by simp [store]
  have he : Function.update (store (true::todo) n out []) 0 todo.reverse=store todo n out [] := by
    funext i;fin_cases i <;> simp [store]
  simp only [h,List.getLast?_concat,List.dropLast_concat,he,ite_true]
  have H := Run.seq (.push (1:K) true) (.push 3 true) (store todo n out []) _ _ 1 1
    (Run.push _ _ _) (Run.push _ _ _)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext i;fin_cases i <;> simp [store,List.replicate_add]
lemma step_false (todo out : List Bool) (n : ℕ) :
    Run step (store (false::todo) n out []) 2 (store todo n out []) := by
  refine Run.pop _ _ _ 1 _ ?_
  have h : store (false::todo) n out [] 0=todo.reverse++[false] := by simp [store]
  have he : Function.update (store (false::todo) n out []) 0 todo.reverse=store todo n out [] := by
    funext i;fin_cases i <;> simp [store]
  simpa only [h,List.getLast?_concat,List.dropLast_concat,he,Bool.false_eq_true,
    Option.some.injEq,ite_false] using Run.skip (store todo n out [])
lemma prefix_run (k : ℕ) (todo out : List Bool) (n : ℕ) :
    Run scanPrefix (store (List.replicate k true++false::todo) n out [true]) (4*k+4)
      (store todo (n+k) out []) := by
  induction k generalizing n with
  | zero =>
    have he : Function.update (store (false::todo) n out [true]) 3 []=store (false::todo) n out [] := by
      funext i;fin_cases i <;> simp [store]
    have H := Run.loop_cons (store (false::todo) n out [true]) (3:K) (fun _ => step) [] true
      (store todo n out []) (store todo n out []) 2 1 rfl
      (by rw [he];exact step_false todo out n) (Run.loop_nil _ _ _ rfl)
    simpa [scanPrefix] using H
  | succ k ih =>
    let rest := List.replicate k true++false::todo
    have he : Function.update (store (true::rest) n out [true]) 3 []=store (true::rest) n out [] := by
      funext i;fin_cases i <;> simp [store]
    have H := Run.loop_cons (store (true::rest) n out [true]) (3:K) (fun _ => step) [] true
      (store rest (n+1) out [true]) (store todo (n+1+k) out []) 3 (4*k+4) rfl
      (by rw [he];exact step_true rest out n) (ih (n+1))
    convert H using 1 <;> try simp only [scanPrefix,List.replicate_succ,List.cons_append,rest]
    all_goals first | omega | (congr 1; omega)
lemma digit_run (b : Bool) (todo out : List Bool) (n : ℕ) :
    Run digit (store (b::todo) n out []) 2 (store todo n (out++[b]) []) := by
  refine Run.pop _ _ _ 1 _ ?_
  have h : store (b::todo) n out [] 0=todo.reverse++[b] := by simp [store]
  have he : Function.update (store (b::todo) n out []) 0 todo.reverse=store todo n out [] := by
    funext i;fin_cases i <;> simp [store]
  simp only [h,List.getLast?_concat,List.dropLast_concat,he]
  convert Run.push (store todo n out []) (2:K) b using 1
  all_goals try with_reducible_and_instances rfl
  funext i;fin_cases i <;> simp [store]
lemma digits_run (bits todo out : List Bool) :
    Run digits (store (bits++todo) bits.length out []) (3*bits.length+1) (store todo 0 (out++bits) []) := by
  induction bits generalizing out with
  | nil => simpa [digits] using Run.loop_nil (store todo 0 out []) (1:K) (fun _ => digit) rfl
  | cons b bits ih =>
    have he : Function.update (store (b::bits++todo) (bits.length+1) out []) 1
        (List.replicate bits.length true)=store (b::bits++todo) bits.length out [] := by
      funext i;fin_cases i <;> simp [store]
    have H := Run.loop_cons (store (b::bits++todo) (bits.length+1) out []) (1:K) (fun _ => digit)
      (List.replicate bits.length true) true (store (bits++todo) bits.length (out++[b]) [])
      (store todo 0 ((out++[b])++bits) []) 2 (3*bits.length+1)
      (by simp [store,List.replicate_add])
      (by rw [he];exact digit_run b (bits++todo) out bits.length) (ih (out++[b]))
    convert H using 1 <;> simp only [digits,List.length_cons,List.cons_append,List.append_assoc,List.nil_append]
    omega

theorem header_run (bits todo : List Bool) :
    Run program (store (UniversalInput.header bits++todo) 0 [] []) (7*bits.length+6)
      (store todo 0 bits []) := by
  let src := UniversalInput.header bits++todo
  have h1 := Run.push (store src 0 [] []) (3:K) true
  have he : Function.update (store src 0 [] []) 3 ((store src 0 [] [] 3)++[true])=store src 0 [] [true] := by
    funext i;fin_cases i <;> simp [store]
  rw [he] at h1
  have h2 : Run scanPrefix (store src 0 [] [true]) (4*bits.length+4) (store (bits++todo) bits.length [] []) := by
    simpa [src,UniversalInput.header,List.append_assoc] using prefix_run bits.length (bits++todo) [] 0
  have h3 : Run digits (store (bits++todo) bits.length [] []) (3*bits.length+1) (store todo 0 bits []) := by
    simpa only [List.nil_append] using digits_run bits todo []
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega
end SourceBurnside.HeaderProgram

namespace SourceBurnside.RawHeader
open Structured Structured.Program Structured.Binary
def store (todo h l z : List Bool) : Store K := ![todo.reverse,[],h,[],l,z]
def readTask : Program K := .pop 0 (fun a => match a with | some b => .push 5 b | none => .skip)
def program : Program K := .seq (HeaderProgram.program.relabel heightSlots)
  (.seq (HeaderProgram.program.relabel aritySlots) readTask)
lemma height_run (bits todo l z : List Bool) :
    Run (HeaderProgram.program.relabel heightSlots) (store (UniversalInput.header bits++todo) [] l z)
      (7*bits.length+6) (store todo bits l z) := by
  refine (HeaderProgram.header_run bits todo).relabel_to heightSlots heightSlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)
    · exact False.elim (hi 3 rfl)
    · rfl
    · rfl
lemma arity_run (bits todo h z : List Bool) :
    Run (HeaderProgram.program.relabel aritySlots) (store (UniversalInput.header bits++todo) h [] z)
      (7*bits.length+6) (store todo h bits z) := by
  refine (HeaderProgram.header_run bits todo).relabel_to aritySlots aritySlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · rfl
    · exact False.elim (hi 3 rfl)
    · exact False.elim (hi 2 rfl)
    · rfl
lemma task_run (z : Bool) (todo h l : List Bool) :
    Run readTask (store (z::todo) h l []) 2 (store todo h l [z]) := by
  refine Run.pop _ _ _ 1 _ ?_
  have he : Function.update (store (z::todo) h l []) 0 todo.reverse=store todo h l [] := by
    funext i;fin_cases i <;> simp [store]
  have hs : store (z::todo) h l [] 0=todo.reverse++[z] := by simp [store]
  simp only [hs,List.getLast?_concat,List.dropLast_concat,he]
  convert Run.push (store todo h l []) (5:K) z using 1
  all_goals try with_reducible_and_instances rfl
  funext i;fin_cases i <;> simp [store]

end SourceBurnside.RawHeader

namespace SourceBurnside.DropPadding
open Structured Structured.Program Structured.Binary
def store (xs : List Bool) (n : ℕ) : Store K := ![xs,List.replicate n false]
end SourceBurnside.DropPadding

namespace SourceBurnside.PadRegister
open Structured Structured.Program Structured.Binary
def store (xs : List Bool) (n : ℕ) (out aux : List Bool) : Store K :=
  ![xs,List.replicate n false,out,[],aux]
lemma result_value (xs : List Bool) (n : ℕ) :
    Add.value (List.replicate (n-xs.length) false++xs).reverse=Add.value xs.reverse := by
  simp [List.reverse_append,Add.value_append,Device.Constant.value_false]
end SourceBurnside.PadRegister

namespace SourceBurnside.WrappedInput
open StackMachine UniversalStack
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (src dst : K) (hne : src≠dst)
include hne
omit hne in
lemma enc_header (n : ℕ) : InitialFormula.enc n=UniversalInput.header (InitialFormula.bin n) := by
  simp [InitialFormula.enc,UniversalInput.header]

end
end SourceBurnside.WrappedInput

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_InputEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]
def appendMap (f : Bool → Bool) (src dst tmp aux : K) : Program K :=
  .seq (copy src tmp aux) (mapMove f tmp dst)
lemma appendMap_run (f : Bool → Bool) (src dst tmp aux : K)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux) (htd : tmp≠dst)
    (r : Store K) (ht : r tmp=[]) (ha : r aux=[]) :
    Run (appendMap f src dst tmp aux) r (7*(r src).length+3)
      (Function.update r dst (r dst++((r src).reverse.map f))) := by
  have h1 := copy_run src tmp aux hst hsa hta r ha
  simp only [ht,List.nil_append] at h1
  have h2 := mapMove_run f tmp dst htd (Function.update r tmp (r src))
  have he : Function.update (Function.update (Function.update r tmp (r src)) tmp []) dst
      ((Function.update r tmp (r src)) dst++((Function.update r tmp (r src)) tmp).reverse.map f)=
      Function.update r dst (r dst++(r src).reverse.map f) := by
    funext i
    by_cases hd : i=dst
    · subst i;simp [Ne.symm htd]
    · by_cases hj : i=tmp
      · subst i;simp [htd,ht]
      · simp [hd,hj]
  rw [he] at h2
  simp only [Function.update_self] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega
lemma appendReverse_run (src dst tmp aux : K)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux) (htd : tmp≠dst)
    (r : Store K) (ht : r tmp=[]) (ha : r aux=[]) :
    Run (appendMap id src dst tmp aux) r (7*(r src).length+3)
      (Function.update r dst (r dst++(r src).reverse)) := by
  simpa only [List.map_id_fun,id_eq] using appendMap_run id src dst tmp aux hst hsa hta htd r ht ha
lemma appendOnes_run (src dst tmp aux : K)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux) (htd : tmp≠dst)
    (r : Store K) (ht : r tmp=[]) (ha : r aux=[]) :
    Run (appendMap (fun _ => true) src dst tmp aux) r (7*(r src).length+3)
      (Function.update r dst (r dst++List.replicate (r src).length true)) := by
  simpa [List.map_const] using
    appendMap_run (fun _ => true) src dst tmp aux hst hsa hta htd r ht ha
end SourceBurnside.Structured.Binary

namespace SourceBurnside.TakePrefix
open Structured Structured.Program
def store (todo : List Bool) (count : ℕ) (out : List Bool) : Store K :=
  ![todo.reverse,List.replicate count false,out]
def step : Program K := .pop 0 (fun a => match a with | some b => .push 2 b | none => .skip)
def program : Program K := .loop 1 (fun _ => step)
lemma step_run (b : Bool) (todo out : List Bool) (n : ℕ) :
    Run step (store (b::todo) n out) 2 (store todo n (out++[b])) := by
  refine Run.pop _ _ _ 1 _ ?_
  have hs : store (b::todo) n out 0=todo.reverse++[b] := by simp [store]
  have he : Function.update (store (b::todo) n out) 0 todo.reverse=store todo n out := by
    funext i;fin_cases i <;> simp [store]
  simp only [hs,List.getLast?_concat,List.dropLast_concat,he]
  convert Run.push (store todo n out) (2:K) b using 1
  all_goals try with_reducible_and_instances rfl
  funext i;fin_cases i <;> simp [store]

lemma program_run (v todo out : List Bool) :
    Run program (store (v++todo) v.length out) (3*v.length+1) (store todo 0 (out++v)) := by
  induction v generalizing out with
  | nil => simpa [program] using Run.loop_nil (store todo 0 out) (1:K) (fun _ => step) rfl
  | cons b v ih =>
    have he : Function.update (store ((b::v)++todo) (b::v).length out) 1 (List.replicate v.length false)=
        store (b::(v++todo)) v.length out := by
      funext i;fin_cases i <;> simp [store]
    have hs : store ((b::v)++todo) (b::v).length out 1=List.replicate v.length false++[false] := by
      simp only [store,Matrix.cons_val_one,Matrix.cons_val_zero,List.length_cons,List.replicate_add,
        List.replicate_one]
    have H := Run.loop_cons (store ((b::v)++todo) (b::v).length out) (1:K) (fun _ => step)
      (List.replicate v.length false) false (store (v++todo) v.length (out++[b]))
      (store todo 0 ((out++[b])++v)) 2 (3*v.length+1) hs
      (by rw [he];exact step_run b (v++todo) out v.length) (ih (out++[b]))
    convert H using 1 <;> first | rfl | (simp only [List.length_cons,List.append_assoc,List.singleton_append] <;> omega)
end SourceBurnside.TakePrefix

namespace SourceBurnside.TwoInputQuote
open Structured Structured.Program Structured.Binary

def store (todo bits v : List Bool) (count : ℕ) (out : List Bool) : Store K :=
  ![todo.reverse,bits,v,List.replicate count false,[],[],out]
def readHeader : Program K := HeaderProgram.program.relabel headerSlots
def reverseBin : Program K := appendMap id 1 2 4 5
def makeUnary : Program K := BinaryUnary.program.relabel unarySlots
def takeCode : Program K := TakePrefix.program.relabel takeSlots
def qcopyCode : Program K := appendMap id 2 6 4 5
def qcopyBin : Program K := appendMap id 1 6 4 5
def qones : Program K := appendMap (fun _ => true) 1 6 4 5
def qheader : Program K := .seq qcopyBin (.seq (.push 6 false) qones)
def qstage : Program K := .seq qcopyCode qheader
def quote : Program K := .seq qstage (.seq qstage (.push 6 true))
def program : Program K := .seq readHeader (.seq reverseBin (.seq makeUnary (.seq takeCode quote)))
lemma readHeader_run (n : ℕ) (todo : List Bool) :
    Run readHeader (store (InitialFormula.enc n++todo) [] [] 0 [])
      (7*InitialFormula.binSize n+6) (store todo (InitialFormula.bin n) [] 0 []) := by
  have H := HeaderProgram.header_run (InitialFormula.bin n) todo
  rw [←WrappedInput.enc_header,InitialFormula.bin_length] at H
  refine H.relabel_to headerSlots headerSlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 2 rfl)
    · rfl
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 3 rfl)
    · rfl
    · rfl
lemma reverseBin_run (bits todo : List Bool) :
    Run reverseBin (store todo bits [] 0 []) (7*bits.length+3) (store todo bits bits.reverse 0 []) := by
  have H := appendReverse_run (1:K) 2 4 5 (by decide) (by decide) (by decide) (by decide)
    (store todo bits [] 0 []) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma makeUnary_run (n : ℕ) (todo : List Bool) :
    ∃t,t≤(7*n+5)*InitialFormula.binSize n+1 ∧
      Run makeUnary (store todo (InitialFormula.bin n) (InitialFormula.bin n).reverse 0 []) t
        (store todo (InitialFormula.bin n) [] n []) := by
  obtain ⟨t,ht,H⟩ := BinaryUnary.numeral_run n
  refine ⟨t,ht,H.relabel_to unarySlots unarySlots_injective _ _ ?_ ?_ ?_⟩
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · rfl
    · rfl
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)
    · exact False.elim (hi 3 rfl)
    · rfl
lemma takeCode_run (v todo bits : List Bool) :
    Run takeCode (store (v++todo) bits [] v.length []) (3*v.length+1) (store todo bits v 0 []) := by
  refine (TakePrefix.program_run v todo []).relabel_to takeSlots takeSlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact False.elim (hi 0 rfl)
    · rfl
    · exact False.elim (hi 2 rfl)
    · exact False.elim (hi 1 rfl)
    · rfl
    · rfl
    · rfl
lemma qcopyCode_run (v bits out todo : List Bool) :
    Run qcopyCode (store todo bits v 0 out) (7*v.length+3) (store todo bits v 0 (out++v.reverse)) := by
  have H := appendReverse_run (2:K) 6 4 5 (by decide) (by decide) (by decide) (by decide)
    (store todo bits v 0 out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma qcopyBin_run (v bits out todo : List Bool) :
    Run qcopyBin (store todo bits v 0 out) (7*bits.length+3) (store todo bits v 0 (out++bits.reverse)) := by
  have H := appendReverse_run (1:K) 6 4 5 (by decide) (by decide) (by decide) (by decide)
    (store todo bits v 0 out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma qones_run (v bits out todo : List Bool) :
    Run qones (store todo bits v 0 out) (7*bits.length+3) (store todo bits v 0 (out++List.replicate bits.length true)) := by
  have H := appendOnes_run (1:K) 6 4 5 (by decide) (by decide) (by decide) (by decide)
    (store todo bits v 0 out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma qpush_run (v bits out todo : List Bool) (b : Bool) :
    Run (.push (6:K) b) (store todo bits v 0 out) 1 (store todo bits v 0 (out++[b])) := by
  convert Run.push (store todo bits v 0 out) (6:K) b using 1
  all_goals try with_reducible_and_instances rfl
  funext i;fin_cases i <;> simp [store]
lemma qheader_run (v bits out todo : List Bool) :
    Run qheader (store todo bits v 0 out) (14*bits.length+7)
      (store todo bits v 0 (out++(UniversalInput.header bits).reverse)) := by
  have H := Run.seq _ _ _ _ _ _ _ (qcopyBin_run v bits out todo)
    (Run.seq _ _ _ _ _ _ _ (qpush_run v bits (out++bits.reverse) todo false)
      (qones_run v bits (out++bits.reverse++[false]) todo))
  convert H using 1 <;> first | rfl | simp only [UniversalInput.header,List.reverse_append,
    List.reverse_cons,List.reverse_replicate,List.append_assoc] | omega
lemma qstage_run (v bits out todo : List Bool) :
    Run qstage (store todo bits v 0 out) (7*v.length+14*bits.length+10)
      (store todo bits v 0 (out++(UniversalInput.header bits++v).reverse)) := by
  have H := Run.seq _ _ _ _ _ _ _ (qcopyCode_run v bits out todo) (qheader_run v bits (out++v.reverse) todo)
  convert H using 1 <;> first | rfl | simp only [List.reverse_append,List.append_assoc] | omega
end SourceBurnside.TwoInputQuote

namespace SourceBurnside.RawPadSeed
open Structured Structured.Program Structured.Binary
def store {r : ℕ} (v : Fin r → List Bool) (n : ℕ) : Store (K r)
  | .inl i => v i
  | .inr 0 => List.replicate n false
  | .inr _ => []
end SourceBurnside.RawPadSeed

namespace SourceBurnside.CountLength
open Structured Structured.Program Structured.Binary
def store (xs : List Bool) (n : ℕ) (cnt len : List Bool) : Store K :=
  ![xs,List.replicate n false,cnt,len,[],[],[]]
def work (xs : List Bool) (n : ℕ) : Store K :=
  ![xs,List.replicate n false,List.replicate n false,List.replicate n false,xs,[],[]]
def program : Program K := .seq (copy 1 2 5) (.seq (copy 1 3 5)
  (.seq (copy 0 4 5) (.seq (BitSize.program.relabel slots) (clear 3))))
lemma program_run (xs : List Bool) (n : ℕ) :
    ∃t,t≤(13*n+13)*xs.length+12*n+8 ∧
      Run program (store xs n [] []) t (store xs n (countBits xs n) []) := by
  have h1 := copy_run (1:K) 2 5 (by decide) (by decide) (by decide) (store xs n [] []) rfl
  have he1 : Function.update (store xs n [] []) 2 ((store xs n [] [] 2)++(store xs n [] [] 1))=
      store xs n (List.replicate n false) [] := by
    funext i;fin_cases i <;> simp [store]
  rw [he1] at h1
  have hn1 : (store xs n [] [] 1).length=n := by simp [store]
  rw [hn1] at h1
  have h2 := copy_run (1:K) 3 5 (by decide) (by decide) (by decide) (store xs n (List.replicate n false) []) rfl
  have he2 : Function.update (store xs n (List.replicate n false) []) 3
      ((store xs n (List.replicate n false) [] 3)++(store xs n (List.replicate n false) [] 1))=
      store xs n (List.replicate n false) (List.replicate n false) := by
    funext i;fin_cases i <;> simp [store]
  rw [he2] at h2
  have hn2 : (store xs n (List.replicate n false) [] 1).length=n := by simp [store]
  rw [hn2] at h2
  have h3 := copy_run (0:K) 4 5 (by decide) (by decide) (by decide)
    (store xs n (List.replicate n false) (List.replicate n false)) rfl
  have he3 : Function.update (store xs n (List.replicate n false) (List.replicate n false)) 4
      ((store xs n (List.replicate n false) (List.replicate n false) 4)++
        (store xs n (List.replicate n false) (List.replicate n false) 0))=work xs n := by
    funext i;fin_cases i <;> simp [store,work]
  rw [he3] at h3
  let pair := BitSize.iter xs.reverse (List.replicate n false) (List.replicate n false)
  obtain ⟨t,ht,H⟩ := BitSize.program_run xs.reverse (List.replicate n false) (List.replicate n false) rfl
  simp only [List.length_reverse,List.length_replicate] at ht
  have h4 : Run (BitSize.program.relabel slots) (work xs n) t (store xs n pair.1.reverse pair.2.reverse) := by
    refine H.relabel_to slots slots_injective _ _ ?_ ?_ ?_
    · intro i;fin_cases i <;> simp [BitSize.store,work,slots]
    · intro i;fin_cases i <;> rfl
    · intro i hi;fin_cases i
      · rfl
      · rfl
      · exact False.elim (hi 1 rfl)
      · exact False.elim (hi 2 rfl)
      · exact False.elim (hi 0 rfl)
      · exact False.elim (hi 3 rfl)
      · exact False.elim (hi 4 rfl)
  have h5 := clear_run (3:K) (store xs n pair.1.reverse pair.2.reverse)
  have he5 : Function.update (store xs n pair.1.reverse pair.2.reverse) 3 []=store xs n pair.1.reverse [] := by
    funext i;fin_cases i <;> simp [store]
  rw [he5] at h5
  have hp := (BitSize.iter_lengths xs.reverse (List.replicate n false) (List.replicate n false) rfl).2
  have hl5 : (store xs n pair.1.reverse pair.2.reverse 3).length=n := by
    change pair.2.reverse.length=n
    simpa only [List.length_reverse,List.length_replicate] using hp
  rw [hl5] at h5
  have HH := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2
    (Run.seq _ _ _ _ _ _ _ h3 (Run.seq _ _ _ _ _ _ _ h4 h5)))
  refine ⟨(5*n+2)+((5*n+2)+((5*xs.length+2)+(t+(2*n+1)))),?_,?_⟩
  · nlinarith
  · exact HH
lemma countBits_value (xs : List Bool) (n : ℕ) (h : xs.length<2^n) :
    Add.value (countBits xs n).reverse=xs.length := by
  have H := (BitSize.iter_value xs.reverse (List.replicate n false) (List.replicate n false) rfl
    (by simpa only [Device.Constant.value_false,List.length_replicate,List.length_reverse,Nat.zero_add] using h)).1
  simpa only [countBits,List.reverse_reverse,Device.Constant.value_false,List.length_reverse,Nat.zero_add] using H
end SourceBurnside.CountLength

namespace SourceBurnside.PackFamily
open Structured Structured.Program

def store {r : ℕ} (v out : Fin r → List Bool) (n : ℕ) : Store (K r)
  | .inl (.inl i) => v i
  | .inl (.inr i) => out i
  | .inr 0 => List.replicate n false
  | .inr _ => []
end SourceBurnside.PackFamily

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_ProgramAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.RawNumberPrep
open Structured Structured.Program Structured.Binary

def store (v : Fin 6 → List Bool) (n : ℕ) (cl dl : List Bool) : Store K
  | .inl i => v i
  | .inr 0 => List.replicate n false
  | .inr 1 => cl
  | .inr 2 => dl
  | .inr _ => []
def raw (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : Fin 6 → List Bool :=
  ![code.reverse,InitialFormula.bin h,InitialFormula.bin l,[z],data.reverse,List.replicate h false]
def parsed (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : Fin 6 → List Bool :=
  ![code.reverse,InitialFormula.bin h,InitialFormula.bin l,[z],data.reverse,[]]
def readHeader : Program K := RawHeader.program.relabel headerSlots
def makeUnary : Program K := .seq (appendMap id (.inl 1) (.inr 3) (.inr 5) (.inr 6))
  (BinaryUnary.program.relabel unarySlots)
lemma unary_run (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    ∃t,t≤(7*h+12)*InitialFormula.binSize h+4 ∧
      Run makeUnary (store (parsed code h l z data) 0 [] []) t (store (raw code h l z data) 0 [] []) := by
  let r := store (parsed code h l z data) 0 [] []
  let s := Function.update r (.inr 3) (InitialFormula.bin h).reverse
  have h1 := appendReverse_run (.inl 1 : K) (.inr 3) (.inr 5) (.inr 6)
    (by decide) (by decide) (by decide) (by decide) r rfl rfl
  have hs : Function.update r (.inr 3) (r (.inr 3)++(r (.inl 1)).reverse)=s := rfl
  rw [hs] at h1
  have hn : (r (.inl 1)).length=InitialFormula.binSize h := InitialFormula.bin_length h
  rw [hn] at h1
  obtain ⟨t,ht,H⟩ := BinaryUnary.numeral_run h
  have h2 : Run (BinaryUnary.program.relabel unarySlots) s t (store (raw code h l z data) 0 [] []) := by
    refine H.relabel_to unarySlots unarySlots_injective _ _ ?_ ?_ ?_
    · intro i;fin_cases i <;> simp [s,r,store,parsed,unarySlots,BinaryUnary.store]
    · intro i;fin_cases i <;> rfl
    · intro i hi
      cases i with
      | inl i =>
        fin_cases i
        all_goals first | rfl | exact False.elim (hi 1 rfl)
      | inr i =>
        fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  exact ⟨7*InitialFormula.binSize h+3+t,by nlinarith,Run.seq _ _ _ _ _ _ _ h1 h2⟩

def count (b : Bool) : Program K := CountLength.program.relabel (countSlots b)
lemma count_run (b : Bool) (v : Fin 6 → List Bool) (n : ℕ) (other : List Bool) :
    ∃t,t≤(13*n+13)*(v (if b then 4 else 0)).length+12*n+8 ∧
      Run (count b) (store v n (if b then other else []) (if b then [] else other)) t
        (store v n (if b then other else CountLength.countBits (v 0) n)
          (if b then CountLength.countBits (v 4) n else other)) := by
  obtain ⟨t,ht,H⟩ := CountLength.program_run (v (if b then 4 else 0)) n
  refine ⟨t,ht,H.relabel_to (countSlots b) (countSlots_injective b) _ _ ?_ ?_ ?_⟩
  · intro i;cases b <;> fin_cases i <;> rfl
  · intro i;cases b <;> fin_cases i <;> rfl
  · intro i hi
    cases i with
    | inl i => rfl
    | inr i =>
      cases b <;> fin_cases i
      all_goals first | rfl | exact False.elim (hi 2 rfl)

end SourceBurnside.RawNumberPrep

namespace SourceBurnside.RawPreparedInputs
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open FiniteTable.Codec
def inputs (n : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : I → List Bool :=
  ![code.reverse,CountLength.countBits code.reverse n,InitialFormula.bin h,InitialFormula.bin l,[z],
    data.reverse,CountLength.countBits data.reverse n]
lemma agrees_inputs (n : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    Agrees fields (inputs n code h l z data)
      (RawNumberPrep.store (RawNumberPrep.raw code h l z data) n
        (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n)) := by
  intro i;fin_cases i <;> rfl
def packed (n : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : I → List Bool :=
  fun i => PackFamily.pad (inputs n code h l z data i) n
end SourceBurnside.RawPreparedInputs

namespace SourceBurnside.Structured
variable {A B : Type*} [DecidableEq A] [DecidableEq B]

lemma Run.extend_left {p : Program A} {r s : Store A} {t : ℕ} (h : Run p r t s) (u : Store B) :
    Run (p.relabel Sum.inl) (Sum.elim r u) t (Sum.elim s u) := by
  refine h.relabel_to Sum.inl Sum.inl_injective _ _ (by intro a;rfl) (by intro a;rfl) ?_
  intro x hx;cases x with
  | inl a => exact False.elim (hx a rfl)
  | inr b => rfl
end SourceBurnside.Structured

namespace SourceBurnside.RawAssembler
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
def store (r : Store RawNumberPrep.K) (out : Fin 7 → List Bool) : Store K := Sum.elim r out
end SourceBurnside.RawAssembler

namespace SourceBurnside.RawPolynomial
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
def size (h l : ℕ) (code data : List Bool) : ℕ := h+code.length+data.length+InitialFormula.binSize l+1
end SourceBurnside.RawPolynomial

namespace SourceBurnside.Structured
variable {A B : Type*} [DecidableEq A] [DecidableEq B]
lemma Run.extend_right {p : Program B} {r s : Store B} {t : ℕ} (h : Run p r t s) (u : Store A) :
    Run (p.relabel Sum.inr) (Sum.elim u r) t (Sum.elim u s) := by
  refine h.relabel_to Sum.inr Sum.inr_injective _ _ (by intro a;rfl) (by intro a;rfl) ?_
  intro x hx;cases x with
  | inr a => exact False.elim (hx a rfl)
  | inl b => rfl
end SourceBurnside.Structured

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

namespace Cell

def checkerRank (c : Cell q) : ℕ := match c.checker with
  | .passed _ => 0 | .head _ => 1 | .idle => 2

end Cell

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TemplateHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
variable {q H h D : ℕ} [NeZero q]
def bits {n : ℕ} (w : Fin n→ZMod 2) : Fin n→Bool := fun j => Addressable.unbit (w j)
def scalars {n : ℕ} (w : Fin n→Bool) : Fin n→ZMod 2 := fun j => Addressable.bit (w j)
@[simp] lemma bits_scalars {n : ℕ} (w : Fin n→Bool) : bits (scalars w)=w := by
  funext j
  exact Addressable.unbit_bit _
@[simp] lemma scalars_bits {n : ℕ} (w : Fin n→ZMod 2) : scalars (bits w)=w := by
  funext j
  exact Addressable.bit_unbit _
end
end SourceBurnside.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_WordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.WordAlgebra

noncomputable section
open Classical

variable {α : Type u} {K : Type v} [Ring K]

namespace Table

variable (T : Table α)

@[simp] lemma detect_self (w : Word α) : T.detect w (monomial (K := K) w) = 1 := by
  rw [monomial, detect_single, ite_eq_left ((conGen T.rep).refl w)]

def annihilator (L : Polynomial K α →+ K) : TwoSidedIdeal (Polynomial K α) :=
  TwoSidedIdeal.mk' {f | ∀ a b, L (a * f * b) = 0}
    (by intro a b; simp)
    (by intro f g hf hg a b; simp [mul_add, add_mul, hf a b, hg a b])
    (by intro f hf a b; simp [hf a b])
    (by intro f g hg a b; simpa only [mul_assoc] using hg (a * f) b)
    (by intro f g hf a b; simpa only [mul_assoc] using hf a (g * b))

@[simp] lemma mem_annihilator (L : Polynomial K α →+ K) (f : Polynomial K α) :
    f ∈ annihilator L ↔ ∀ a b, L (a * f * b) = 0 := by simp [annihilator]

def Homogeneous : Prop := ∀ v w, T.rep v w → v.length = w.length

end Table

end

end SourceBurnside.WordAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_MatrixTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α β K : Type*} [CommRing K]
def wordHom (T : Table α) : FreeMonoid α →* T.Algebra (K:=K) where
  toFun := T.word
  map_one' := T.word_one
  map_mul' := T.word_mul

def substitution (U : Table α) (T : Table β) (f : FreeMonoid α →* FreeMonoid β)
    (hr : ∀a b,U.rep a b → T.word (K:=K) (f a)=T.word (f b))
    (hz : ∀a∈U.zero,T.word (K:=K) (f a)=0) : U.Algebra (K:=K) →ₐ[K] T.Algebra (K:=K) := by
  let F := MonoidAlgebra.lift K (T.Algebra (K:=K)) (FreeMonoid α) ((wordHom T).comp f)
  have H : U.ideal (K:=K) ≤ TwoSidedIdeal.ker F := by
    apply TwoSidedIdeal.span_le.mpr
    rintro v (⟨a,b,hab,rfl⟩|⟨a,ha,rfl⟩)
    · change F (monomial a-monomial b)=0
      simp only [map_sub,F,monomial,MonoidAlgebra.lift_single,one_smul,
        MonoidHom.comp_apply,wordHom,MonoidHom.coe_mk,OneHom.coe_mk]
      exact sub_eq_zero.mpr (hr a b hab)
    · change F (monomial a)=0
      simpa only [F,monomial,MonoidAlgebra.lift_single,one_smul,
        MonoidHom.comp_apply,wordHom,MonoidHom.coe_mk,OneHom.coe_mk] using hz a ha
  apply RingCon.liftₐ _ F
  intro a b hab
  change F a=F b
  apply sub_eq_zero.mp
  rw [←map_sub]
  exact H ((U.ideal (K:=K)).rel_iff a b |>.mp hab)
@[simp] lemma substitution_word (U : Table α) (T : Table β) (f : FreeMonoid α →* FreeMonoid β)
    (hr : ∀a b,U.rep a b → T.word (K:=K) (f a)=T.word (f b))
    (hz : ∀a∈U.zero,T.word (K:=K) (f a)=0) (w : FreeMonoid α) :
    substitution U T f hr hz (U.word w)=T.word (f w) := by
  change (MonoidAlgebra.lift K (T.Algebra (K:=K)) (FreeMonoid α) ((wordHom T).comp f)) (monomial w)=_
  simp [monomial,MonoidAlgebra.lift_single,wordHom]
end
end SourceBurnside.WordAlgebra.Table

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside
namespace FiniteSteinbergPresentation
open MonomialCompletion
variable {n : ℕ} {α : Type u}

noncomputable def seed : Seed n α (Group n α) where
  g p w := if h : w.length ≤ 2 then PresentedGroup.of (p, ⟨w, h⟩) else 1
  square p w hw := by
    simp only [dite_eq_left hw]
    have h := PresentedGroup.one_of_mem (Rel.square p ⟨w, hw⟩)
    simp only [map_pow, gen] at h
    exact h
  commute p q u v hu hv h₁ h₂ := by
    simp only [dite_eq_left hu, dite_eq_left hv]
    apply (bracket_eq_one_iff _ _).mp
    have h := PresentedGroup.one_of_mem (Rel.commute p q h₁ h₂ ⟨u, hu⟩ ⟨v, hv⟩)
    simp only [map_bracket, gen] at h
    exact h
  product i j k hij hjk hik u v huv := by
    have hu : u.length ≤ 2 := by omega
    have hv : v.length ≤ 2 := by omega
    have hw : (u ++ v).length ≤ 2 := by simp only [List.length_append]; omega
    simp only [dite_eq_left hu, dite_eq_left hv, dite_eq_left hw]
    have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem
      (Rel.product i j k hij hjk hik ⟨u, hu⟩ ⟨v, hv⟩ huv)
    simp only [map_bracket, gen] at h
    exact h

@[simp] theorem seed_short (p : Root n) (w : ShortWord α) :
    seed.g p w.val = (PresentedGroup.of (p, w) : Group n α) := by simp [seed, w.property]

noncomputable def toSteinberg : Group n α →* Steinberg n (Polynomial α) :=
  PresentedGroup.toGroup (f := fun g : Gen n α => Steinberg.x g.1 (monomial g.2.val)) (by
    intro r hr
    cases hr with
    | square p w =>
      simp only [map_pow, gen, FreeGroup.lift_apply_of]
      rw [pow_two, ← Steinberg.x_add, monomial_add_self, Steinberg.x_zero]
    | commute p q h₁ h₂ u v =>
      simp only [map_bracket, gen, FreeGroup.lift_apply_of]
      exact (bracket_eq_one_iff _ _).mpr (Steinberg.x_commute p q h₁ h₂ _ _)
    | product i j k hij hjk hik u v h =>
      simp only [map_mul, map_inv, map_bracket, gen, FreeGroup.lift_apply_of]
      rw [Steinberg.x_mul i j k hij hjk hik, monomial_append, mul_inv_cancel])

@[simp] theorem toSteinberg_of (p : Root n) (w : ShortWord α) :
    toSteinberg (PresentedGroup.of (p, w) : Group n α) = Steinberg.x p (monomial w.val) :=
  PresentedGroup.toGroup.of _

noncomputable def fromSteinberg (hn : 5 ≤ n) : Steinberg n (Polynomial α) →* Group n α :=
  MonomialCompletion.lift seed hn

@[simp] theorem fromSteinberg_x (hn : 5 ≤ n) (p : Root n) (f : Polynomial α) :
    fromSteinberg hn (Steinberg.x p f) = poly seed hn p f := by
  simp [fromSteinberg, MonomialCompletion.lift]

end FiniteSteinbergPresentation

namespace SteinbergQuotient

variable {n : ℕ} {R : Type u} [Ring R]

def killedIdeal {G : Type v} [Group G] (hn : 5 ≤ n) (f : Steinberg n R →* G) :
    TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {a | ∀ p, f (Steinberg.x p a) = 1}
    (by intro p; simp)
    (by intro a b ha hb p; rw [Steinberg.x_add, map_mul, ha, hb, one_mul])
    (by intro a ha p; rw [Steinberg.x_neg, map_inv, ha, inv_one])
    (by
      intro a b hb p
      obtain ⟨j, hji, hjk, _, _⟩ := exists_fresh hn p.row p.col p.row p.col
      rw [← Steinberg.x_mul p.row j p.col hji.symm hjk p.ne, map_bracket, hb]
      simp [bracket])
    (by
      intro a b ha p
      obtain ⟨j, hji, hjk, _, _⟩ := exists_fresh hn p.row p.col p.row p.col
      rw [← Steinberg.x_mul p.row j p.col hji.symm hjk p.ne, map_bracket, ha]
      simp [bracket])

@[simp] theorem mem_killedIdeal {G : Type v} [Group G] (hn : 5 ≤ n)
    (f : Steinberg n R →* G) (a : R) :
    a ∈ killedIdeal hn f ↔ ∀ p, f (Steinberg.x p a) = 1 := by
  simp [killedIdeal]

variable (S : Set R)

def rootRelations : Set (Steinberg n R) := {g | ∃ p a, a ∈ S ∧ g = Steinberg.x p a}

abbrev normal : Subgroup (Steinberg n R) := Subgroup.normalClosure (rootRelations (n := n) S)

abbrev Quot := Steinberg n R ⧸ normal (n := n) S

abbrev proj : Steinberg n R →* Quot (n := n) S := QuotientGroup.mk' (normal S)

 theorem killed (hn : 5 ≤ n) {a : R} (ha : a ∈ coeffIdeal S) (p : Root n) :
    proj S (Steinberg.x p a) = 1 := by
  have hs : coeffIdeal S ≤ killedIdeal hn (proj (n := n) S) := by
    apply TwoSidedIdeal.span_le.mpr
    intro b hb
    apply (mem_killedIdeal hn _ _).mpr
    intro q
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨q, b, hb, rfl⟩
  exact (mem_killedIdeal hn _ _).mp (hs ha) p

noncomputable def quotientRoot (hn : 5 ≤ n) (p : Root n) : Coeff S → Quot (n := n) S :=
  Quotient.lift (fun a => proj S (Steinberg.x p a)) (by
    intro a b hab
    have hk := killed S hn ((coeffIdeal S).rel_iff a b |>.mp hab) p
    rw [sub_eq_add_neg, Steinberg.x_add, Steinberg.x_neg, map_mul, map_inv] at hk
    exact mul_inv_eq_one.mp hk)

@[simp] theorem quotientRoot_mk (hn : 5 ≤ n) (p : Root n) (a : R) :
    quotientRoot S hn p ((coeffIdeal S).ringCon.mk' a) = proj S (Steinberg.x p a) := rfl

noncomputable def fromCoeff (hn : 5 ≤ n) : Steinberg n (Coeff S) →* Quot (n := n) S :=
  Steinberg.lift (quotientRoot S hn)
    (by
      intro p a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b
      rw [← map_add, quotientRoot_mk, quotientRoot_mk, quotientRoot_mk,
        Steinberg.x_add, map_mul])
    (by
      intro p q h₁ h₂ a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b

      exact (Steinberg.x_commute p q h₁ h₂ a b).map (proj S))
    (by
      intro i j k hij hjk hik a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b
      rw [← map_mul, quotientRoot_mk, quotientRoot_mk, quotientRoot_mk,
        ← map_bracket, Steinberg.x_mul])

@[simp] theorem fromCoeff_x (hn : 5 ≤ n) (p : Root n) (a : R) :
    fromCoeff S hn (Steinberg.x p ((coeffIdeal S).ringCon.mk' a)) =
      proj S (Steinberg.x p a) := by
  change quotientRoot S hn p ((coeffIdeal S).ringCon.mk' a) = _
  rfl

 theorem normal_le_ker : normal (n := n) S ≤ (Steinberg.map (n := n) (coeffIdeal S).ringCon.mk').ker := by
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨p, a, ha, rfl⟩
  change Steinberg.map (n := n) (coeffIdeal S).ringCon.mk' (Steinberg.x p a) = 1
  rw [Steinberg.map_x]
  have ha0 : (coeffIdeal S).ringCon.mk' a = 0 := by
    apply ((coeffIdeal S).ringCon.eq).mpr
    exact TwoSidedIdeal.subset_span ha
  rw [ha0, Steinberg.x_zero]

noncomputable def toCoeff : Quot (n := n) S →* Steinberg n (Coeff S) :=
  QuotientGroup.lift (normal S) (Steinberg.map (n := n) (coeffIdeal S).ringCon.mk') (normal_le_ker S)

@[simp] theorem toCoeff_proj (g : Steinberg n R) :
    toCoeff S (proj S g) = Steinberg.map (n := n) (coeffIdeal S).ringCon.mk' g := rfl

end SteinbergQuotient

end SourceBurnside
namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]
local instance polyAlgebra (T : Table α) : _root_.Algebra (_root_.Polynomial K) (_root_.Polynomial (T.Algebra (K:=K))) := _root_.Polynomial.algebra K _

def polynomialCoefficients (T : Table α) :
    T.Algebra (K:=_root_.Polynomial K) →ₐ[_root_.Polynomial K] _root_.Polynomial (T.Algebra (K:=K)) := by
  let g : FreeMonoid α →* _root_.Polynomial (T.Algebra (K:=K)) :=
    _root_.Polynomial.C.toMonoidHom.comp (wordHom T)
  let F := MonoidAlgebra.lift (_root_.Polynomial K) (_root_.Polynomial (T.Algebra (K:=K))) (FreeMonoid α) g
  have H : T.ideal (K:=_root_.Polynomial K) ≤ TwoSidedIdeal.ker F := by
    apply TwoSidedIdeal.span_le.mpr
    rintro v (⟨a,b,hab,rfl⟩|⟨a,ha,rfl⟩)
    · change F (monomial a-monomial b)=0
      simp only [map_sub,F,monomial,MonoidAlgebra.lift_single,one_smul,g,
        MonoidHom.comp_apply,wordHom,MonoidHom.coe_mk,OneHom.coe_mk]
      rw [T.word_rep hab,sub_self]
    · change F (monomial a)=0
      simp only [F,monomial,MonoidAlgebra.lift_single,one_smul,g,
        MonoidHom.comp_apply,wordHom,MonoidHom.coe_mk,OneHom.coe_mk]
      change _root_.Polynomial.C (T.word (K:=K) a)=0
      rw [T.word_zero ha, map_zero]
  apply RingCon.liftₐ _ F
  intro a b hab
  change F a=F b
  apply sub_eq_zero.mp
  exact (map_sub F a b).symm.trans (H ((T.ideal (K:=_root_.Polynomial K)).rel_iff a b |>.mp hab))
@[simp] lemma polynomialCoefficients_word (T : Table α) (w : FreeMonoid α) :
    T.polynomialCoefficients (K:=K) (T.word w)=_root_.Polynomial.C (T.word (K:=K) w) := by
  change (MonoidAlgebra.lift (_root_.Polynomial K) (_root_.Polynomial (T.Algebra (K:=K))) (FreeMonoid α)
    (_root_.Polynomial.C.toMonoidHom.comp (wordHom T))) (monomial w)=_
  simp [monomial,MonoidAlgebra.lift_single,wordHom]
end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]

def augmentation (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1) : T.Algebra (K:=K) →ₐ[K] K := by
  let F := MonoidAlgebra.lift K K (FreeMonoid α) (augWords (K:=K))
  have H : T.ideal (K:=K) ≤ TwoSidedIdeal.ker F := by
    apply TwoSidedIdeal.span_le.mpr
    rintro v (⟨a,b,hab,rfl⟩|⟨a,ha,rfl⟩)
    · change F (monomial a-monomial b)=0
      simp only [map_sub,F,monomial,MonoidAlgebra.lift_single,one_smul,augWords_spec]
      rw [hh a b hab,sub_self]
    · change F (monomial a)=0
      simp only [F,monomial,MonoidAlgebra.lift_single,one_smul,augWords_spec]
      exact ite_eq_right (fun h=>hz a ha (FreeMonoid.length_eq_zero.mp h))
  apply RingCon.liftₐ _ F
  intro a b hab
  change F a=F b
  apply sub_eq_zero.mp
  exact (map_sub F a b).symm.trans (H ((T.ideal (K:=K)).rel_iff a b |>.mp hab))
@[simp] lemma augmentation_word (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1) (w : FreeMonoid α) :
    T.augmentation (K:=K) hh hz (T.word w)=if w.length=0 then 1 else 0 := by
  change (MonoidAlgebra.lift K K (FreeMonoid α) (augWords (K:=K))) (monomial w)=_
  simp [monomial,MonoidAlgebra.lift_single,augWords_spec]
end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]

def gradingWords (T : Table α) : FreeMonoid α →* _root_.Polynomial (T.Algebra (K:=K)) where
  toFun w := _root_.Polynomial.monomial w.length (T.word w)
  map_one' := by simp
  map_mul' a b := by simp [FreeMonoid.length_mul,word_mul,_root_.Polynomial.monomial_mul_monomial]

def gradingHom (T : Table α) (hh : T.Homogeneous) :
    T.Algebra (K:=K) →ₐ[K] _root_.Polynomial (T.Algebra (K:=K)) := by
  let F := MonoidAlgebra.lift K (_root_.Polynomial (T.Algebra (K:=K))) (FreeMonoid α) T.gradingWords
  have hw (w : FreeMonoid α) : F (monomial w)=_root_.Polynomial.monomial w.length (T.word w) := by
    simp [F,monomial,MonoidAlgebra.lift_single,gradingWords]
  have H : T.ideal (K:=K) ≤ TwoSidedIdeal.ker F := by
    apply TwoSidedIdeal.span_le.mpr
    rintro v (⟨a,b,hab,rfl⟩|⟨a,ha,rfl⟩)
    · change F (monomial a-monomial b)=0
      rw [map_sub,hw,hw,hh a b hab,T.word_rep hab,sub_self]
    · change F (monomial a)=0
      rw [hw,T.word_zero ha]
      exact map_zero _
  apply RingCon.liftₐ _ F
  intro a b hab
  apply sub_eq_zero.mp
  exact (map_sub F a b).symm.trans (H ((T.ideal (K:=K)).rel_iff a b |>.mp hab))
@[simp] lemma gradingHom_word (T : Table α) (hh : T.Homogeneous) (w : FreeMonoid α) :
    T.gradingHom (K:=K) hh (T.word w)=_root_.Polynomial.monomial w.length (T.word w) := by
  change (MonoidAlgebra.lift K (_root_.Polynomial (T.Algebra (K:=K))) (FreeMonoid α) T.gradingWords) (monomial w)=_
  simp [monomial,MonoidAlgebra.lift_single,gradingWords]

def evalZero (T : Table α) : _root_.Polynomial (T.Algebra (K:=K)) →ₐ[K] T.Algebra (K:=K) :=
  _root_.Polynomial.eval₂AlgHom (AlgHom.id K _) 0 (fun _=>Commute.zero_right _)
def evalOne (T : Table α) : _root_.Polynomial (T.Algebra (K:=K)) →ₐ[K] T.Algebra (K:=K) :=
  _root_.Polynomial.eval₂AlgHom (AlgHom.id K _) 1 (fun _=>Commute.one_right _)
end
end SourceBurnside.WordAlgebra.Table

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BandFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
variable [Algebra (ZMod 2) R]
@[simp] lemma matrixSteinbergEval_x (T : Matrix (Fin N) (Fin N) (ZMod 2))
    (p : Root n) (a : Polynomial R) :
    matrixSteinbergEval T (Steinberg.x p a)=blockRoot p (matrixEval T a) := by
  rw [matrixSteinbergEval,MonoidHom.comp_apply,Steinberg.map_x,blockMap_x]
  rfl
end
end SourceBurnside.Kernel

end

end OAI
end


