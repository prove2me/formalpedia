-- Prove2me | Definitions.Def_OAIQWRHT001
-- name    : OAIQWRHT001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T22:12:49.897273+00:00
-- url     : https://prove2.me/theorems/550b602f-863f-4376-8348-f9bb21d80475
-- title:
--   OpenAI rational hitting lists split: definitions bundle OAIQWRHT001
-- statement:
--   One of the five definitions bundles (`OAIQWRHT000` to `OAIQWRHT004`) of the split of OpenAI's proof that one deterministic Turing machine writes, in polynomial time, a polynomial-size list of rational matrix tuples hitting every admissible nonzero noncommutative rational formula of size at most $s$ (`OAI.RationalHitting.main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/RationalHitting` (OpenAI, *Polynomial Hitting Lists for Noncommutative Rational Formulas*, OpenAI Math Release, September 24, 2026, result family 116, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. Among them are the cyclotomic grid construction of the list (`Generator.list`, `ExecutableGenerator.list`), the pencil certificates, the binary arithmetic procedures, the stack language with its time bounds, and the compiler to `Turing.TM0` machines. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`Formula`, `Evaluates`, `Admissible`, `Nonzero`, `Output`, `encodeOutput`, `Machine`, `run`, `OutputsWithin`, `Hits`, `MainStatement` and the rest) are not repeated: the bundles import them from the published bundle `Def_RationalHitting`. It imports no other bundle of this split.
--
--   Modules (some only in part): `BinaryDivision`, `BinaryFactorial`, `BinarySubtract`, `Compiler`, `Deformation`, `DenseDeterminant`, `DenseRecords`, `FiniteCompiler`, `GridComputation`, `InputAdapter`, `LiftComputation`, `ListProcedures`, `MatrixComputation`, `OutputAdapter`, `ProcedureControl`, `ProcedurePairs`, `Procedures`, `RationalArithmetic`, `RationalBinary`, `SignedArithmetic`, `StackLanguage`, `StackSimulation`, `Tabulation`, `TaylorComputation`, `UnaryArithmetic`.
--
--   The theorems the definitions do not need are proved in the three solutions of this split. One proves the published intermediate statement `OAI.RationalHitting.Generator.list_hits` (the paper's Proposition 5.1), one proves `OAI.RationalHitting.ExecutableGenerator.implementation` (Proposition 5.3) using it, and the third proves `OAI.RationalHitting.main` from both. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Polynomial Hitting Lists for Noncommutative Rational Formulas, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 116; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/RationalHitting at commit adc7f12

import Mathlib
import Definitions.Def_RationalHitting

section
-- module Solutions.OAIQW_RationalHitting.Deformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.ThreeLift
open Matrix Polynomial MvPolynomial
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [Field E] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- Embed t into a coefficient field, leaving p,r polynomial indeterminates. -/
def specialize (φ : K →+* E) (t : E) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) E :=
  eval₂Hom (MvPolynomial.C.comp φ) (Fin.cases (MvPolynomial.C t) MvPolynomial.X)

end
end RationalHitting.ThreeLift

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.StackLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime
open Turing

def exec {α : Type*} (step : α → Option α) : ℕ → α → Option α
  | 0,a => some a
  | t+1,a => (step a).bind (exec step t)

@[simp] lemma exec_zero {α : Type*} (step : α → Option α) (a : α) : exec step 0 a = some a := rfl

namespace OneToZero
variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

/-- Syntactic statement bound, fixed once the finite machine is fixed. -/
def weight : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q | .write _ q | .load _ q => weight q+1
  | .branch _ q r => max (weight q) (weight r)+1
  | .goto _ | .halt => 1

@[simp] theorem halts (M : Λ → TM1.Stmt Γ Λ σ) (a : TM1.Cfg Γ Λ σ)
    (h : TM1.step M a = none) : TM0.step (TM1to0.tr M) (TM1to0.trCfg M a) = none := by
  rcases a with ⟨l,v,T⟩
  cases l <;> simp_all [TM1.step,TM1to0.trCfg,TM0.step,TM1to0.tr]

end OneToZero
end RationalHitting.TMTime

/-! A finite structured binary-stack language. Every primitive is a push,
pop, or transfer. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime.StackToOne
open Turing Turing.TM2to1
open TM2to1.Λ'
open Function
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K]

def stackWeight : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q | .peek _ _ q | .pop _ _ q => stackWeight q+1
  | .load _ q => stackWeight q
  | .branch _ q r => max (stackWeight q) (stackWeight r)
  | .goto _ | .halt => 0

end RationalHitting.TMTime.StackToOne

namespace RationalHitting.TMTime.FiniteStates
open Turing
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]

noncomputable def stateEncode (S : Finset Λ) (q : Λ) : Fin (Fintype.card ↥S+1) :=
  if q=default then 0 else if h : q∈S then (Fintype.equivFin ↥S ⟨q,h⟩).succ else 0

noncomputable def stateDecode (S : Finset Λ) : Fin (Fintype.card ↥S+1) → Λ :=
  Fin.cases default (fun i => ((Fintype.equivFin ↥S).symm i).val)

@[simp] lemma stateEncode_default (S : Finset Λ) : stateEncode S default=0 := by
  simp [stateEncode]

noncomputable def machine (M : TM0.Machine Γ Λ) (S : Finset Λ) :
    TM0.Machine Γ (Fin (Fintype.card ↥S+1)) :=
  fun q a => (M (stateDecode S q) a).map (fun z => (stateEncode S z.1,z.2))

noncomputable def cfg (S : Finset Λ) (a : TM0.Cfg Γ Λ) :
    TM0.Cfg Γ (Fin (Fintype.card ↥S+1)) := ⟨stateEncode S a.q,a.Tape⟩

@[simp] lemma cfg_init (S : Finset Λ) (l : List Γ) :
    cfg S (TM0.init l)=TM0.init l := by
  simp [cfg,TM0.init]

end RationalHitting.TMTime.FiniteStates

/-! Quantitative finite-control compilation of stack programs,
with an explicit tape encoding. -/

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

abbrev TapeAlphabet (K : Type) := TM2to1.Γ' K (fun _ => Bool)

end RationalHitting.StackLanguage.Compiler

namespace RationalHitting.TMTime.Alphabet
open Turing
open TM1 TM1to1
variable {Γ Λ σ : Type*} [Inhabited Γ]
variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
variable (enc0 : enc default = List.Vector.replicate n false)
variable (encdec : ∀ a, dec (enc a) = a)

/-- Number of deferred writes along the longest branch. -/
def writesWeight : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q | .load _ q => writesWeight q
  | .write _ q => writesWeight q+1
  | .branch _ q r => max (writesWeight q) (writesWeight r)
  | .goto _ | .halt => 0

end RationalHitting.TMTime.Alphabet

namespace RationalHitting.StackLanguage.Compiler
open Turing RationalHitting.TMTime
open scoped BigOperators
variable {K : Type} [DecidableEq K] [Fintype K]

/- The alphabet is finite because the number of stacks is fixed. -/
noncomputable instance finiteTapeAlphabet : Fintype (TapeAlphabet K) := by
  unfold TapeAlphabet TM2to1.Γ'
  infer_instance

end RationalHitting.StackLanguage.Compiler

/-! Raw unary input adapter for the finite block-coded stack compiler.
The alphabet is exactly Fin 4. No list-processing oracle is an instruction. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.InputAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime.InputAdapter
open Turing
abbrev A := Fin 4
abbrev Q := Fin 10
abbrev V := Bool × Bool
abbrev Cfg := TM1.Cfg A Q V
abbrev Stmt := TM1.Stmt A Q V

def raw (b : Bool) : A := if b then 2 else 1
def bit (b : Bool) : A := if b then 1 else 0

def jump (q : Q) : Stmt := .goto (fun _ _ => q)
def move (d : Dir) (q : Q) : Stmt := .move d (jump q)
def leftTo (q r : Q) : Stmt :=
  .move .left (.branch (fun a _ => a==3) (jump r) (jump q))

def writeBits : List Bool → Stmt → Stmt
  | [],q => q
  | b::bs,q => .write (fun _ _ => bit b) (.move .right (writeBits bs q))

def M (code : Bool → Bool → List Bool) : Q → Stmt
  | 0 => .branch (fun a _ => a==0)
      (.write (fun _ _ => 3) (.move .right (.write (fun _ _ => 3)
        (.move .right (.write (fun _ _ => 3) (.move .left (.move .left
          (.load (fun _ _ => (true,false)) (jump 1))))))))) (move .right 0)
  | 1 => .write (fun _ _ => 0) (.move .left
      (.branch (fun a _ => a==0) (jump 6)
        (.load (fun a v => (v.1,a==2)) (.write (fun _ _ => 3) (move .right 2)))))
  | 2 => .branch (fun a _ => a==3) (move .right 3) (move .right 2)
  | 3 => .branch (fun a _ => a==3)
      (.branch (fun _ v => v.1)
        (.branch (fun _ v => v.2)
          (writeBits (code true true) (.write (fun _ _ => 3) (.load (fun _ v => (false,v.2)) (jump 4))))
          (writeBits (code true false) (.write (fun _ _ => 3) (.load (fun _ v => (false,v.2)) (jump 4)))))
        (.branch (fun _ v => v.2)
          (writeBits (code false true) (.write (fun _ _ => 3) (.load (fun _ v => (false,v.2)) (jump 4))))
          (writeBits (code false false) (.write (fun _ _ => 3) (.load (fun _ v => (false,v.2)) (jump 4))))))
      (move .right 3)
  | 4 => leftTo 4 5
  | 5 => leftTo 5 1
  | 6 => .branch (fun a _ => a==3) (move .right 7) (move .right 6)
  | 7 => .branch (fun a _ => a==3) (.write (fun _ _ => 0) (jump 8)) (move .right 7)
  | 8 => leftTo 8 9
  | _ => .write (fun _ _ => 0) (.move .right .halt)

@[simp] lemma head₂ (L R : List A) : (Tape.mk₂ L R).head=R.headI := rfl
@[simp] lemma right₂ (L : List A) (a : A) (R : List A) :
    (Tape.mk₂ L (a::R)).move .right=Tape.mk₂ (a::L) R := by simp [Tape.mk₂]
@[simp] lemma left₂ (a : A) (L R : List A) :
    (Tape.mk₂ (a::L) R).move .left=Tape.mk₂ L (a::R) := by simp [Tape.mk₂]
@[simp] lemma write₂ (L R : List A) (a : A) :
    (Tape.mk₂ L R).write a=Tape.mk₂ L (a::R.tail) := by simp [Tape.mk₂]

@[simp] lemma bit_ne_three (b : Bool) : bit b ≠ 3 := by cases b <;> decide
@[simp] lemma raw_ne_zero (b : Bool) : raw b ≠ 0 := by cases b <;> decide

def state (q : Q) (f b : Bool) (L R : List A) : Cfg := ⟨some q,(f,b),Tape.mk₂ L R⟩

def invariant (xs : List Bool) (k : ℕ) (out : List Bool) (f b : Bool) : Cfg :=
  state 1 f b (xs.map raw) (3::List.replicate k 0 ++ 3::out.map bit ++ [3])

def emit (code : Bool → Bool → List Bool) : Bool → List Bool → List Bool
  | _,[] => []
  | f,x::xs => code f x ++ emit code false xs

def cost (code : Bool → Bool → List Bool) : Bool → List Bool → ℕ → ℕ → ℕ
  | _,[],_,_ => 0
  | f,x::xs,k,L => 2*k+2*L+(code f x).length+7 +
      cost code false xs (k+1) (L+(code f x).length)

@[simp] lemma left_empty (R : List A) :
    (Tape.mk₂ [] R).move .left = Tape.mk₂ [] (0::R) := by simp [Tape.mk₂]

end RationalHitting.TMTime.InputAdapter

/-! Required reverse interface from a block-coded finite stack simulator to
literal Fin4 output digits. All registers of this transducer are finite. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.OutputAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime.OutputAdapter
open Turing
abbrev A := Fin 4
abbrev Q := Fin 10
abbrev Word (b : ℕ) := Fin b → Bool
abbrev V (b : ℕ) := Word b × Option Bool
abbrev Stmt (b : ℕ) := TM1.Stmt A Q (V b)
abbrev Cfg (b : ℕ) := TM1.Cfg A Q (V b)
def raw (x : Bool) : A := if x then 2 else 1
def bit (x : Bool) : A := if x then 1 else 0

def jump {b} (q : Q) : Stmt b := .goto (fun _ _ => q)
def move {b} (d : Dir) (q : Q) : Stmt b := .move d (jump q)
def leftTo {b} (q r : Q) : Stmt b :=
  .move .left (.branch (fun a _ => a==3) (jump r) (jump q))

def readBlock {b} : List (Fin b) → Stmt b → Stmt b
  | [],q => q
  | i::is,q => .load (fun a v => (Function.update v.1 i (a==1),v.2))
      (.write (fun _ _ => 0) (.move .right (readBlock is q)))

def block {b} (w : Word b) : List A := (List.finRange b).map (fun i => bit (w i))
def fill {b} (is : List (Fin b)) (w v : Word b) : Word b :=
  is.foldl (fun u i => Function.update u i (w i)) v

@[simp] lemma head₂ (L R : List A) : (Tape.mk₂ L R).head=R.headI := rfl
@[simp] lemma right₂ (L : List A) (a : A) (R : List A) :
    (Tape.mk₂ L (a::R)).move .right=Tape.mk₂ (a::L) R := by simp [Tape.mk₂]
@[simp] lemma left₂ (a : A) (L R : List A) :
    (Tape.mk₂ (a::L) R).move .left=Tape.mk₂ L (a::R) := by simp [Tape.mk₂]
@[simp] lemma left_empty (R : List A) :
    (Tape.mk₂ [] R).move .left=Tape.mk₂ [] (0::R) := by simp [Tape.mk₂]
@[simp] lemma write₂ (L R : List A) (a : A) :
    (Tape.mk₂ L R).write a=Tape.mk₂ L (a::R.tail) := by simp [Tape.mk₂]
@[simp] lemma bit_beq_one (x : Bool) : (bit x==1)=x := by cases x <;> decide
@[simp] lemma bit_ne_three (x : Bool) : bit x≠3 := by cases x <;> decide
@[simp] lemma raw_ne_three (x : Bool) : raw x≠3 := by cases x <;> decide

def M {b} (get : Word b → Option Bool) : Q → Stmt b
  | 0 => .move .left (.write (fun _ _ => 3) (.move .left (.write (fun _ _ => 3)
      (.move .left (.write (fun _ _ => 3) (.move .right (move .right 1)))))))
  | 1 => .write (fun _ _ => 0) (.move .right (readBlock (List.finRange b)
      (.load (fun _ v => (v.1,get v.1)) (.branch (fun _ v => v.2.isSome)
        (.move .left (.write (fun _ _ => 3) (jump 2))) (jump 5)))))
  | 2 => leftTo 2 3
  | 3 => .write (fun _ v => raw (v.2.getD false)) (.move .right
      (.write (fun _ _ => 3) (move .right 4)))
  | 4 => .branch (fun a _ => a==3) (jump 1) (move .right 4)
  | 5 => leftTo 5 6
  | 6 => .write (fun _ _ => 0) (jump 7)
  | 7 => leftTo 7 8
  | _ => .write (fun _ _ => 0) (.move .right .halt)

def state {b} (q : Q) (v : V b) (L R : List A) : Cfg b := ⟨some q,v,Tape.mk₂ L R⟩
def invariant {b} (gap : ℕ) (out : List Bool) (R : List A) (v : V b) : Cfg b :=
  state 1 v (List.replicate gap 0++3::(out.reverse.map raw)++[3]) (3::R)

def stream {b} (code : Bool → Bool → Word b) (stop : Bool → Word b) : Bool → List Bool → List A
  | f,[] => block (stop f)
  | f,x::xs => block (code f x)++stream code stop false xs

def cost (b gap len : ℕ) : ℕ → ℕ
  | 0 => gap+b+len+6
  | n+1 => 2*(gap+b)+3+cost b (gap+b-1) (len+1) n

end RationalHitting.TMTime.OutputAdapter

namespace RationalHitting.TMTime.OutputAdapter
open Turing

variable {K : Type} [DecidableEq K]
abbrev StackAlphabet (K : Type) := TM2to1.Γ' K (fun _ => Bool)
def code {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b) (f x : Bool) : Word b :=
  (enc (f,Function.update (fun _ => none) k (some x))).get
def stop {b} (enc : StackAlphabet K → List.Vector Bool b) (f : Bool) : Word b :=
  (enc (f,fun _ => none)).get

def getter {b} (k : K) (dec : List.Vector Bool b → StackAlphabet K) (w : Word b) : Option Bool :=
  (dec (List.Vector.ofFn w)).2 k

end RationalHitting.TMTime.OutputAdapter

/-! Literal tape-preserving linkage for the raw-input/stack/output compiler.
There is no implicit recoding between machines. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Compiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TMTime.Link
open Turing
variable {Γ Λ Δ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Δ]
local instance sumInhabited : Inhabited (Sum Λ Δ) := ⟨Sum.inl default⟩

def left (a : TM0.Cfg Γ Λ) : TM0.Cfg Γ (Sum Λ Δ) := ⟨Sum.inl a.q,a.Tape⟩
def right (a : TM0.Cfg Γ Δ) : TM0.Cfg Γ (Sum Λ Δ) := ⟨Sum.inr a.q,a.Tape⟩

def machine (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ) : TM0.Machine Γ (Sum Λ Δ)
  | .inl q,a => match F q a with
    | none => some (.inr default,.write a)
    | some (r,s) => some (.inl r,s)
  | .inr q,a => (G q a).map (fun (r,s) => (.inr r,s))

end RationalHitting.TMTime.Link

namespace RationalHitting.TMTime.BinaryLift
open Turing
abbrev A := Fin 4
def bit (b : Bool) : A := if b then 1 else 0
def bitMap : PointedMap Bool A := ⟨bit,rfl⟩
@[simp] lemma bit_read (b : Bool) : (bit b==1)=b := by cases b <;> decide
variable {Λ : Type*} [Inhabited Λ]
def stmt : TM0.Stmt Bool → TM0.Stmt A
  | .move d => .move d
  | .write b => .write (bit b)
def machine (F : TM0.Machine Bool Λ) : TM0.Machine A Λ :=
  fun q a => (F q (a==1)).map (fun (r,s) => (r,stmt s))
def cfg (a : TM0.Cfg Bool Λ) : TM0.Cfg A Λ := ⟨a.q,a.Tape.map bitMap⟩
lemma step (F : TM0.Machine Bool Λ) (a : TM0.Cfg Bool Λ) :
    TM0.step (machine F) (cfg a)=(TM0.step F a).map cfg := by
  rcases a with ⟨q,T⟩
  simp only [cfg,machine,TM0.step,Tape.map_fst,bitMap,bit_read,Option.map_map]
  congr 1
  funext ⟨r,s⟩
  cases s <;> simp only [Function.comp_apply,stmt,cfg,Tape.map_move,Tape.map_write,bitMap]
end RationalHitting.TMTime.BinaryLift

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

def bitNat (x : Bool) : ℕ := if x then 1 else 0
@[simp] lemma bitNat_false : bitNat false = 0 := rfl

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

lemma bitNat_le_one (x : Bool) : bitNat x ≤ 1 := by cases x <;> decide

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

/-- Euclid's product is halved at every ordered step. -/
lemma gcd_product_halving {a b : ℕ} (ha : 0<a) (hab : a≤b) :
    2*(a*(b%a)) ≤ a*b := by
  have hr := Nat.mod_lt b ha
  have hq : 1 ≤ b/a := (Nat.one_le_div_iff ha).mpr hab
  have hid := Nat.mod_add_div b a
  have hmul := Nat.mul_le_mul_left a hq
  have hhalf : 2*(b%a) ≤ b := by omega
  nlinarith

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

/-- Extra work registers for retaining numerator and denominator through Euclid. -/
def fractionArith : Fin 10 ↪ Fin 12 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 12 => x.val) h⟩

@[simp] lemma fractionArith_val (i : Fin 10) : (fractionArith i).val=i.val := rfl

end RationalHitting.StackLanguage

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

/-- Self-delimiting word records (distinct from the final output encoding). -/
def codeWord : List Bool → List Bool
  | [] => [true]
  | b::w => false::b::codeWord w

@[simp] theorem codeWord_length (w : List Bool) : (codeWord w).length = 2*w.length+1 := by
  induction w <;> simp_all [codeWord] ; omega

def pairWord (w : List Bool) : List Bool := w.flatMap (fun b => [false,b])
@[simp] lemma pairWord_nil : pairWord [] = [] := rfl
@[simp] lemma pairWord_cons (b : Bool) (w : List Bool) :
    pairWord (b::w) = false::b::pairWord w := rfl
@[simp] lemma pairWord_append (u v : List Bool) : pairWord (u++v) = pairWord u++pairWord v := by
  simp [pairWord]
lemma codeWord_pair (w : List Bool) : codeWord w = pairWord w++[true] := by
  induction w <;> simp_all [codeWord]

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
variable {K : Type} [DecidableEq K]

/-- Canonical output's self-delimiting natural-number encoding, applied to
an already canonical little-endian binary word. -/
def encodedWord (w : List Bool) : List Bool :=
  List.replicate w.length true ++ [false] ++ w

lemma digits_bool_bits (a : ℕ) :
    (Nat.digits 2 a).map (fun b => b != 0)=a.bits := by
  rw [Nat.digits_two_eq_bits,List.map_map]
  convert List.map_id a.bits using 1
  congr 1
  funext b; cases b <;> rfl

end RationalHitting.StackLanguage

namespace RationalHitting
namespace StackLanguage
open Function

lemma encodedWord_bits (a : ℕ) : encodedWord a.bits=encodeNat a := by
  simp [encodeNat,digits_bool_bits,encodedWord]

def reduceReg (i : Fin 12) : Fin 16 := ⟨i.val,by omega⟩
lemma reduceReg_inj : Injective reduceReg := by intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h

def denominatorReg : Fin 4 → Fin 16 := ![5,14,1,2]
def numeratorReg : Fin 4 → Fin 16 := ![0,14,1,2]
lemma denominatorReg_inj : Injective denominatorReg := by decide
lemma numeratorReg_inj : Injective numeratorReg := by decide

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


namespace RationalHitting

/-- A concrete syntax for nonnegative polynomial bounds. This is only used to
bound actual stack transitions, never as an additional machine instruction. -/
inductive TimeBound where
  | const : ℕ → TimeBound
  | variable : TimeBound
  | add : TimeBound → TimeBound → TimeBound
  | mul : TimeBound → TimeBound → TimeBound
  deriving DecidableEq

namespace TimeBound
instance instOfNat {n : ℕ} : OfNat TimeBound n := ⟨const n⟩
instance instAdd : Add TimeBound := ⟨add⟩
instance instMul : Mul TimeBound := ⟨mul⟩

def eval : TimeBound → ℕ → ℕ
  | .const c, _ => c
  | .variable, n => n
  | .add a b, n => a.eval n + b.eval n
  | .mul a b, n => a.eval n * b.eval n

@[simp] lemma eval_const (a n : ℕ) : (const a).eval n = a := rfl
@[simp] lemma eval_variable (n : ℕ) : variable.eval n = n := rfl
@[simp] lemma eval_add (a b : TimeBound) (n : ℕ) : (a+b).eval n=a.eval n+b.eval n := rfl
@[simp] lemma eval_mul (a b : TimeBound) (n : ℕ) : (a*b).eval n=a.eval n*b.eval n := rfl
@[simp] lemma eval_numeral (a n : ℕ) : (ofNat(a) : TimeBound).eval n = a := rfl

lemma monotone (p : TimeBound) : Monotone p.eval := by
  induction p with
  | const c => exact monotone_const
  | «variable» => exact monotone_id
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact fun a b h => Nat.mul_le_mul (hp h) (hq h)

/-- Substitution is again a polynomial with nonnegative coefficients. -/
def comp : TimeBound → TimeBound → TimeBound
  | .const c, _ => .const c
  | .variable, q => q
  | .add a b, q => a.comp q + b.comp q
  | .mul a b, q => a.comp q * b.comp q

@[simp] lemma eval_comp (p q : TimeBound) (n : ℕ) :
    (p.comp q).eval n = p.eval (q.eval n) := by
  induction p <;> simp_all [comp,eval]

end TimeBound
end RationalHitting


/-! Compositional finite-stack implementation. All the constants introduced
here describe actual finite programs, not arithmetic-operation oracles. -/

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

/-- Serialization of a typed pair. Only the first field needs a delimiter. -/
def pairCode {A B : Type} (ca : A → List Bool) (cb : B → List Bool) (p : A×B) : List Bool :=
  codeWord (ca p.1) ++ cb p.2
@[simp] lemma pairCode_length {A B : Type} (ca : A → List Bool) (cb : B → List Bool) (p : A×B) :
    (pairCode ca cb p).length=2*(ca p.1).length+1+(cb p.2).length := by
  simp [pairCode]

def threeRegs (a b c : K) : Fin 3 → K := ![a,b,c]
lemma threeRegs_inj {K : Type} [DecidableEq K] {a b c : K} (hab : a ≠ b)
  (hac : a ≠ c) (hbc : b ≠ c) : Function.Injective (RationalHitting.StackLanguage.threeRegs a b c) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [threeRegs]

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

def boolCode (b : Bool) : List Bool := [b]
@[simp] lemma boolCode_length (b : Bool) : (boolCode b).length=1 := rfl

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

/-- Unary loop count. These symbols are explicitly popped by the loop body. -/
def unaryCode (n : ℕ) : List Bool := List.replicate n true
@[simp] lemma unaryCode_length (n : ℕ) : (unaryCode n).length=n := by simp [unaryCode]
@[simp] lemma unaryCode_zero : unaryCode 0=[] := rfl
@[simp] lemma unaryCode_succ (n : ℕ) : unaryCode (n+1)=true::unaryCode n := rfl

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
open Function

/-- Reusable dense records. Individual word lengths need not be fixed. -/
def listCode {A : Type} (ca : A → List Bool) (l : List A) : List Bool :=
  l.flatMap (fun a => codeWord (ca a))
@[simp] lemma listCode_nil {A : Type} (ca : A → List Bool) : listCode ca []=[] := rfl
@[simp] lemma listCode_cons {A : Type} (ca : A → List Bool) (a : A) (l : List A) :
    listCode ca (a::l)=codeWord (ca a)++listCode ca l := rfl
@[simp] lemma listCode_append {A : Type} (ca : A → List Bool) (l m : List A) :
    listCode ca (l++m)=listCode ca l++listCode ca m := by simp [listCode]
@[simp] lemma listCode_singleton {A : Type} (ca : A → List Bool) (a : A) :
    listCode ca [a]=codeWord (ca a) := by simp
lemma length_le_listCode {A : Type} (ca : A → List Bool) (l : List A) :
    l.length≤(listCode ca l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp; omega
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

/-- A complete uniform table-building step: evaluation of a compiled callback,
indexed counter update, and append of an escaped dense record. -/
def tableStep {A B : Type} (f : A × ℕ → B) (a : A × (ℕ × List B)) : A × (ℕ × List B) :=
  (a.1, (a.2.1+1, a.2.2 ++ [f (a.1,a.2.1)]))

def tableStateCode {A B : Type} (ca : A → List Bool) (cb : B → List Bool) :=
  pairCode ca (pairCode unaryCode (listCode cb))

@[simp] lemma tableStateCode_length {A B : Type} (ca : A → List Bool)
    (cb : B → List Bool) (a : A × (ℕ × List B)) :
    (tableStateCode ca cb a).length = 2*(ca a.1).length+2*a.2.1+(listCode cb a.2.2).length+2 := by
  simp [tableStateCode]; omega

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

/-- Canonical storage format for the compositional finite-program proofs. -/
class Coding (A : Type) where
  code : A → List Bool
export Coding (code)

instance instCodingNat : Coding ℕ := ⟨Nat.bits⟩
instance instCodingBool : Coding Bool := ⟨boolCode⟩
instance instCodingProd {A B : Type} [Coding A] [Coding B] : Coding (A×B) := ⟨pairCode code code⟩
instance instCodingList {A : Type} [Coding A] : Coding (List A) := ⟨listCode code⟩
instance instCodingSubtype {A : Type} [Coding A] (P : A → Prop) : Coding {a // P a} := ⟨fun a => code a.val⟩

structure Unary where
  val : ℕ
  deriving DecidableEq
instance instCodingUnary : Coding Unary := ⟨fun n => unaryCode n.val⟩

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

/-- Count record delimiters, skipping both the escape bit and payload bit. -/
def recordCount : List Bool → ℕ
  | [] => 0
  | true::w => recordCount w+1
  | false::[] => 0
  | false::_::w => recordCount w

@[simp] lemma recordCount_false (w : List Bool) : recordCount (false::w)=recordCount w.tail := by
  cases w <;> rfl

lemma recordCount_codeWord (w tail : List Bool) :
    recordCount (codeWord w++tail)=recordCount tail+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [codeWord,recordCount] using ih

lemma recordCount_listCode {A : Type} (ca : A → List Bool) (l : List A) :
    recordCount (listCode ca l)=l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [recordCount_codeWord,ih]

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

def intCode (z : ℤ) : List Bool := pairCode boolCode Nat.bits (decide (z<0),z.natAbs)
@[simp] lemma intCode_length (z : ℤ) : (intCode z).length=z.natAbs.bits.length+3 := by
  simp [intCode];omega

lemma nat_bits_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length :=
  by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

def positivePart (z : ℤ) : ℕ := if decide (z<0) then 0 else z.natAbs
def negativePart (z : ℤ) : ℕ := if decide (z<0) then z.natAbs else 0

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

def sumStep (a : List ℤ×ℤ) : List ℤ×ℤ := (a.1.tail,a.2+a.1.headD 0)

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

structure DenseSquare where
  dim : ℕ
  val : Matrix (Fin dim) (Fin dim) ℤ

def DenseSquare.rows (a : DenseSquare) : List (List ℤ) :=
  (List.finRange a.dim).map fun i => (List.finRange a.dim).map fun j => a.val i j

instance instInhabitedDenseSquare : Inhabited DenseSquare := ⟨⟨0,0⟩⟩

def DenseSquare.get (a : DenseSquare) (i j : ℕ) : ℤ :=
  if hi : i<a.dim then if hj : j<a.dim then a.val ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

@[simp] lemma DenseSquare.get_fin (a : DenseSquare) (i j : Fin a.dim) :
    a.get i.val j.val=a.val i j := by simp [DenseSquare.get]

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function
open scoped BigOperators

def DenseSquare.of {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : DenseSquare := ⟨n,A⟩

def DenseSquare.step (A F : DenseSquare) : DenseSquare :=
  ⟨A.dim, BirdDet.Spec.stepEntry A.val (fun i j => F.get i.val j.val)⟩

@[simp] lemma DenseSquare.step_dim (A F : DenseSquare) : (A.step F).dim=A.dim := rfl
@[simp] lemma DenseSquare.step_of {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) :
    (DenseSquare.of A).step (DenseSquare.of F)=DenseSquare.of (BirdDet.Spec.stepEntry A F) := by
  simp [DenseSquare.step,DenseSquare.of,DenseSquare.get]

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

def birdState (a : DenseSquare×DenseSquare) : DenseSquare×DenseSquare := (a.1,a.1.step a.2)

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

def DenseSquare.detAlgorithm (A : DenseSquare) : ℤ :=
  if A.dim=0 then 1 else (-1:ℤ)^(A.dim-1)*((A.step)^[A.dim-1] A).get 0 0

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

def doubleBelow (t v : ℕ) : ℕ := if v≤t then v+v else v

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

variable {K : Type} [DecidableEq K]

abbrev NZInt := {z : ℤ // z≠0}

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
open scoped BigOperators

namespace Runtime

def taylorTerm (m : ℕ) (a t : ℤ) (i j r : ℕ) : ℤ :=
  ((-a)^(m-1-r-i)*((m-1-r).choose i : ℤ)) *
    (a^(j-r)*(j.choose r : ℤ))*t^r

def taylor (m : ℕ) (a t : ℤ) (i j : ℕ) : ℤ :=
  ((List.range m).map (fun r => taylorTerm m a t i j r)).sum

def padded (m N : ℕ) (a t : ℤ) (i j : ℕ) : ℤ :=
  if j<N then taylor m a t i j else 0

end Runtime
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

def signed (q z i j : ℕ) : ℤ :=
  if (z+j)%q=i then (-1)^((z+j)/q) else 0

def liftTerm (m N q : ℕ) (a t p r : ℤ) (u v i j x y k : ℕ) : ℤ :=
  if u=(v+y)%m then
    padded m N a t k ((k+(m-y)%m)%m)*
      signed q (((m-(x*k)%m)%m+(x*u)%m)%m) i j*p^x*r^y
  else 0

def lift (m N q : ℕ) (a t p r : ℤ) (u v i j : ℕ) : ℤ :=
  ((List.range m).map (fun x =>
    ((List.range m).map (fun y =>
      ((List.range m).map (fun k => liftTerm m N q a t p r u v i j x y k)).sum)).sum)).sum

def entry (m N q : ℕ) (a t p r : ℤ) (I J : ℕ) : ℤ :=
  lift m N q a t p r (I/q) (J/q) (I%q) (J%q)

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
variable {A : Type} [Coding A]

 def flattenStep (a : List (List A)×List A) : List (List A)×List A :=
  (a.1.tail,a.2++a.1.headD [])

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Runtime

def cramer (A B : DenseSquare) (i j : ℕ) : DenseSquare :=
  ⟨A.dim,fun r c => if c.val=i then B.get r.val j else A.val r c⟩

end Runtime
end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.GridComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
namespace Runtime

abbrev MatrixWordArgs := (DenseSquare×DenseSquare)×ℤ

end Runtime
end RationalHitting.StackLanguage


end OAI
end


