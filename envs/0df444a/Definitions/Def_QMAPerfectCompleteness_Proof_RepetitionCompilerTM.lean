-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerTM
-- name    : QMAPerfectCompleteness_Proof_RepetitionCompilerTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:40.649971+00:00
-- url     : https://prove2.me/theorems/0bf506f5-1770-4b98-99e4-16f231b35a17
-- title:
--   Finite transducer for fixed-count verifier repetition
-- statement:
--   Defines the actual finite stack machine for a fixed repetition count. It consumes literal copies of a source verifier packet, remaps proof and ancilla addresses, emits repeated gate bodies and the final AND circuit, writes the exact header and gate count, and clears its work stacks. Configuration and run interfaces support the separate code-identity and polynomial-runtime arguments.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RepetitionCompilerTM.lean, lines 16–2044.

/- Generated from Solutions.RepetitionCompilerTM by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FixedBlockCopy
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Concrete fixed-count repetition compiler. Its input is n literal copies of the source code,
produced by the checked FixedBlockCopy machine; each unary gate counter delimits one body. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.Repetition.CompilerTM
open QAlgorithms.Complexity (Str encNat)
open Uniformity

open Fin.NatCast in
@[simp high] lemma fin4_natCast_one : (Nat.cast 1 : Fin 4) = 1 := by decide

def arity (kind : Fin 4) : ℕ := if kind = 0 then 1 else if kind = 2 then 3 else 2

inductive Context (n : ℕ) where
  | body : Fin (n+1) → Fin 4 → Fin 3 → Context n
  | output : Fin (n+1) → Context n
  deriving DecidableEq, Fintype

inductive SumTask (n : ℕ) where
  | address : Context n → Bool → SumTask n
  | headerOutput : SumTask n
  | flagX : SumTask n
  | andFirst : Fin (n+1) → SumTask n
  | andLast : Fin (n+1) → SumTask n
  | loadOutput : Fin (n+1) → SumTask n
  deriving DecidableEq, Fintype

inductive AfterAddress (n : ℕ) where
  | body : Fin (n+1) → AfterAddress n
  | output : Fin (n+1) → AfterAddress n
  deriving DecidableEq, Fintype

inductive Source where
  | bound
  | ancilla
  | address : Fin 3 → Source
  | saved
  | output
  deriving DecidableEq, Fintype

inductive Dest where
  | header
  | body
  | address
  deriving DecidableEq, Fintype

inductive Label (n : ℕ) where
  | firstHeader : Fin 3 → Label n
  | skipHeader : Fin (n+1) → Fin 3 → Label n
  | readCount : Fin (n+1) → Label n
  | gate : Fin (n+1) → Label n
  | tag : Fin (n+1) → Fin 4 → Label n
  | readAddress : Fin (n+1) → Fin 4 → Fin 3 → Label n
  | compare : Context n → Label n
  | restoreBound : Context n → Bool → Label n
  | restoreAddress : Context n → Label n
  | sum : SumTask n → Fin 4 → Fin (n+2) → Label n
  | copyUnary : SumTask n → Fin 3 → Fin (n+2) → Bool → Label n
  | clearSources : AfterAddress n → Fin 3 → Label n
  | flagX : Label n
  | andFirst : Fin (n+1) → Label n
  | cleanup : Fin 4 → Label n
  | finish : Fin 3 → Label n
  deriving DecidableEq, Fintype

def addrKey (j : Fin 3) : Fin 15 := ⟨6+j.val,by have := j.isLt; omega⟩
def Source.key : Source → Fin 15
  | .bound => 2
  | .ancilla => 3
  | .address j => addrKey j
  | .saved => 10
  | .output => 4

def Dest.key : Dest → Fin 15
  | .header => 1
  | .body => 13
  | .address => 6

def Context.index {n : ℕ} : Context n → Fin (n+1)
  | .body j _ _ => j
  | .output j => j

def Context.address {n : ℕ} : Context n → Fin 3
  | .body _ _ a => a
  | .output _ => 0

def SumTask.dest {n : ℕ} : SumTask n → Dest
  | .headerOutput => .header
  | .loadOutput _ => .address
  | _ => .body

def SumTask.source {n : ℕ} (task : SumTask n) (part : Fin 3) : Source :=
  match task with
  | .loadOutput _ => if part = 0 then .output else .ancilla
  | .address ctx proof => if part = 0 then .bound else if part = 1 then .ancilla else
      if proof then .saved else .address ctx.address
  | _ => if part = 0 then .bound else .ancilla

def SumTask.copies {n : ℕ} (task : SumTask n) (part : Fin 3) : ℕ :=
  match task with
  | .address ctx proof => if part = 0 then (if proof then ctx.index.val else n) else
      if part = 1 then (if proof then 0 else ctx.index.val) else 1
  | .loadOutput _ => if part = 0 then 1 else 0
  | _ => if part.val < 2 then n else 0

def SumTask.literal {n : ℕ} : SumTask n → ℕ
  | .headerOutput => n
  | .flagX => 0
  | .andFirst j => j.val
  | .andLast j => j.val+1
  | _ => 0

def SumTask.delimiter {n : ℕ} : SumTask n → Bool
  | .loadOutput _ => false
  | _ => true

def sumReturn (n : ℕ) : SumTask n → Label n
  | .address ctx _ => .restoreAddress ctx
  | .headerOutput => .readCount 0
  | .flagX => .andFirst 0
  | .andFirst j => .sum (.loadOutput j) 0 0
  | .andLast j => if h : j.val+1<n then .andFirst ⟨j.val+1,by omega⟩ else .cleanup 0
  | .loadOutput j => .compare (.output j)

def afterMapped (n : ℕ) : Context n → Label n
  | .body j kind a => if h : a.val+1<arity kind then
      .compare (.body j kind ⟨a.val+1,by unfold arity at h; split_ifs at h <;> omega⟩)
      else .clearSources (.body j) 0
  | .output j => .clearSources (.output j) 0

def afterClear (n : ℕ) : AfterAddress n → Label n
  | .body j => .gate j
  | .output j => .sum (.andLast j) 0 0



abbrev machine (n : ℕ) : FinTM2 where
  K := Fin 15
  k₀ := 0
  k₁ := 14
  Γ _ := Bool
  Λ := Label n
  main := .firstHeader 0
  σ := Bool × Bool
  initialState := (false,false)
  m l := match l with
    | .firstHeader j => .peek 0 (fun _ a => (a.isSome,a.getD false))
      (.pop 0 (fun v _ => v) (.branch Prod.snd
        (if j.val < 2 then
          .push ⟨2+j.val,by have := j.isLt; omega⟩ (fun _ => true)
            (Statement.pushMany 1 (List.replicate n true) (.goto (fun _ => .firstHeader j)))
          else .push 4 (fun _ => true) (.goto (fun _ => .firstHeader j)))
        (if j.val = 0 then .push 1 (fun _ => false)
          (Statement.pushMany 1 (List.replicate (n+1) true) (.goto (fun _ => .firstHeader 1)))
          else if j.val = 1 then .push 1 (fun _ => false) (.goto (fun _ => .firstHeader 2))
          else .load (fun _ => (false,false)) (.goto (fun _ => .sum .headerOutput 0 0)))))
    | .skipHeader j field => .peek 0 (fun _ a => (a.isSome,a.getD false))
      (.pop 0 (fun v _ => v) (.branch Prod.snd (.goto (fun _ => .skipHeader j field))
        (.goto (fun _ => if h : field.val<2 then .skipHeader j ⟨field.val+1,by omega⟩ else .readCount j))))
    | .readCount j => .peek 0 (fun _ a => (a.isSome,a.getD false))
      (.pop 0 (fun v _ => v) (.branch Prod.snd
        (.push 5 (fun _ => true) (.goto (fun _ => .readCount j))) (.goto (fun _ => .gate j))))
    | .gate j => .peek 5 (fun v a => (a.isSome,v.2))
      (.branch Prod.fst
        (.pop 5 (fun v _ => v) (.push 12 (fun _ => true) (.goto (fun _ => .tag j 0))))
        (.load (fun _ => (false,false)) (.goto (fun _ => if h : j.val+1<n then
          .skipHeader ⟨j.val+1,by omega⟩ 0 else .flagX))))
    | .tag j kind => .peek 0 (fun _ a => (a.isSome,a.getD false))
      (.pop 0 (fun v _ => v) (.branch Prod.snd
        (.push 13 (fun _ => true) (.goto (fun _ => .tag j (Fin.ofNat 4 (kind.val+1)))))
        (.push 13 (fun _ => false) (.goto (fun _ => .readAddress j kind 0)))))
    | .readAddress j kind a => .peek 0 (fun _ b => (b.isSome,b.getD false))
      (.pop 0 (fun v _ => v) (.branch Prod.snd
        (.push (addrKey a) (fun _ => true) (.goto (fun _ => .readAddress j kind a)))
        (.load (fun _ => (false,false)) (.goto (fun _ => if h : a.val+1<arity kind then
          .readAddress j kind ⟨a.val+1,by unfold arity at h; split_ifs at h <;> omega⟩
          else .compare (.body j kind 0))))))
    | .compare ctx => .peek 2 (fun v a => (a.isSome,v.2))
      (.peek (addrKey ctx.address) (fun v a => (v.1,a.isSome))
        (.branch Prod.fst
          (.branch Prod.snd
            (.pop 2 (fun v _ => v) (.pop (addrKey ctx.address) (fun v _ => v)
              (.push 9 (fun _ => true) (.push 10 (fun _ => true) (.goto (fun _ => .compare ctx))))))
            (.goto (fun _ => .restoreBound ctx true)))
          (.goto (fun _ => .restoreBound ctx false))))
    | .restoreBound ctx proof => .peek 9 (fun v a => (a.isSome,v.2))
      (.branch Prod.fst
        (.pop 9 (fun v _ => v) (.push 2 (fun _ => true) (.goto (fun _ => .restoreBound ctx proof))))
        (.load (fun _ => (false,false)) (.goto (fun _ => .sum (.address ctx proof) 0 0))))
    | .restoreAddress ctx => .peek 10 (fun v a => (a.isSome,v.2))
      (.branch Prod.fst
        (.pop 10 (fun v _ => v) (.push (addrKey ctx.address) (fun _ => true) (.goto (fun _ => .restoreAddress ctx))))
        (.load (fun _ => (false,false)) (.goto (fun _ => afterMapped n ctx))))
    | .sum task part counter => if h : part.val<3 then
      let part' : Fin 3 := ⟨part.val,h⟩
      if counter.val < task.copies part' then
        .load (fun _ => (false,false)) (.goto (fun _ => .copyUnary task part' counter false))
      else .load (fun _ => (false,false)) (.goto (fun _ => .sum task ⟨part.val+1,by omega⟩ 0))
      else Statement.pushMany task.dest.key (List.replicate task.literal true)
        (.load (fun _ => (false,false))
          (if task.delimiter then .push task.dest.key (fun _ => false) (.goto (fun _ => sumReturn n task))
            else .goto (fun _ => sumReturn n task)))
    | .copyUnary task part counter false => .peek (task.source part).key (fun v a => (a.isSome,v.2))
      (.branch Prod.fst
        (.pop (task.source part).key (fun v _ => v)
          (.push 11 (fun _ => true) (.push task.dest.key (fun _ => true)
            (.goto (fun _ => .copyUnary task part counter false)))))
        (.goto (fun _ => .copyUnary task part counter true)))
    | .copyUnary task part counter true => .peek 11 (fun v a => (a.isSome,v.2))
      (.branch Prod.fst
        (.pop 11 (fun v _ => v) (.push (task.source part).key (fun _ => true)
          (.goto (fun _ => .copyUnary task part counter true))))
        (.load (fun _ => (false,false)) (.goto (fun _ => .sum task part.castSucc
          (Fin.ofNat (n+2) (counter.val+1))))))
    | .clearSources ret j => .peek (addrKey j) (fun v a => (a.isSome,v.2))
      (.branch Prod.fst
        (.pop (addrKey j) (fun v _ => v) (.goto (fun _ => .clearSources ret j)))
        (.load (fun _ => (false,false)) (.goto (fun _ => if h : j.val<2 then
          .clearSources ret ⟨j.val+1,by omega⟩ else afterClear n ret))))
    | .flagX => .push 12 (fun _ => true) (.push 13 (fun _ => false)
      (.load (fun _ => (false,false)) (.goto (fun _ => .sum .flagX 0 0))))
    | .andFirst j => .push 12 (fun _ => true)
      (Statement.pushMany 13 (encNat 2).reverse
        (.load (fun _ => (false,false)) (.goto (fun _ => .sum (.andFirst j) 0 0))))
    | .cleanup j => .peek ⟨2+j.val,by have := j.isLt; omega⟩ (fun v a => (a.isSome,v.2))
      (.branch Prod.fst
        (.pop ⟨2+j.val,by have := j.isLt; omega⟩ (fun v _ => v) (.goto (fun _ => .cleanup j)))
        (.load (fun _ => (false,false)) (.goto (fun _ => if h : j.val<3 then
          .cleanup ⟨j.val+1,by omega⟩ else .finish 0))))
    | .finish j =>
      let key : Fin 15 := if j.val=0 then 13 else if j.val=1 then 12 else 1
      .peek key (fun _ a => (a.isSome,a.getD false))
        (.branch Prod.fst
          (.pop key (fun v _ => v) (.push 14 Prod.snd (.goto (fun _ => .finish j))))
          (if j.val=0 then .push 14 (fun _ => false) (.goto (fun _ => .finish 1))
            else if j.val=1 then .goto (fun _ => .finish 2)
            else .load (fun _ => (false,false)) .halt))

structure Data where
  input : Str := []
  header : Str := []
  bound : Str := []
  ancilla : Str := []
  oldOutput : Str := []
  gatesLeft : Str := []
  addresses : Fin 3 → Str := fun _ => []
  savedBound : Str := []
  savedAddress : Str := []
  temp : Str := []
  count : Str := []
  body : Str := []
  output : Str := []

def Data.stacks (d : Data) : Fin 15 → Str :=
  ![d.input,d.header,d.bound,d.ancilla,d.oldOutput,d.gatesLeft,d.addresses 0,d.addresses 1,
    d.addresses 2,d.savedBound,d.savedAddress,d.temp,d.count,d.body,d.output]

def cfg (n : ℕ) (l : Label n) (v : Bool × Bool) (d : Data) : (machine n).Cfg := ⟨some l,v,d.stacks⟩
abbrev transition (n : ℕ) : Option (machine n).Cfg → Option (machine n).Cfg := fun q => q.bind (machine n).step


namespace Data

def source (d : Data) : Source → Str
  | .bound => d.bound
  | .ancilla => d.ancilla
  | .address j => d.addresses j
  | .saved => d.savedAddress
  | .output => d.oldOutput

def setSource (d : Data) (source : Source) (xs : Str) : Data := match source with
  | .bound => {d with bound := xs}
  | .ancilla => {d with ancilla := xs}
  | .address j => {d with addresses := Function.update d.addresses j xs}
  | .saved => {d with savedAddress := xs}
  | .output => {d with oldOutput := xs}

def dest (d : Data) : Dest → Str
  | .header => d.header
  | .body => d.body
  | .address => d.addresses 0

def setDest (d : Data) (dest : Dest) (xs : Str) : Data := match dest with
  | .header => {d with header := xs}
  | .body => {d with body := xs}
  | .address => {d with addresses := Function.update d.addresses 0 xs}

@[simp] lemma stacks_source (d : Data) (s : Source) : d.stacks s.key = d.source s := by
  cases s with
  | address j => fin_cases j <;> rfl
  | bound => rfl
  | ancilla => rfl
  | saved => rfl
  | output => rfl

@[simp] lemma stacks_dest (d : Data) (dst : Dest) : d.stacks dst.key = d.dest dst := by cases dst <;> rfl

lemma setSource_stacks (d : Data) (s : Source) (xs : Str) :
    (d.setSource s xs).stacks = Function.update d.stacks s.key xs := by
  cases s with
  | address j =>
    fin_cases j <;> funext k <;> fin_cases k <;> simp [setSource,Data.stacks,Source.key,addrKey]
  | bound => funext k; fin_cases k <;> simp [setSource,Data.stacks,Source.key]
  | ancilla => funext k; fin_cases k <;> simp [setSource,Data.stacks,Source.key]
  | saved => funext k; fin_cases k <;> simp [setSource,Data.stacks,Source.key]
  | output => funext k; fin_cases k <;> simp [setSource,Data.stacks,Source.key]

lemma setDest_stacks (d : Data) (dst : Dest) (xs : Str) :
    (d.setDest dst xs).stacks = Function.update d.stacks dst.key xs := by
  cases dst <;> funext k <;> fin_cases k <;> simp [setDest,Data.stacks,Dest.key]

@[simp] lemma source_setSource (d : Data) (s : Source) (xs : Str) : (d.setSource s xs).source s = xs := by
  cases s <;> simp [source,setSource]

@[simp] lemma setSource_self (d : Data) (s : Source) : d.setSource s (d.source s) = d := by
  cases s <;> simp [source,setSource]

@[simp] lemma setSource_setSource (d : Data) (s : Source) (a b : Str) :
    (d.setSource s a).setSource s b = d.setSource s b := by
  cases s <;> simp [setSource]

@[simp] lemma dest_setDest (d : Data) (dst : Dest) (xs : Str) : (d.setDest dst xs).dest dst = xs := by
  cases dst <;> simp [dest,setDest]

@[simp] lemma setDest_self (d : Data) (dst : Dest) : d.setDest dst (d.dest dst) = d := by
  cases dst <;> simp [dest,setDest]

@[simp] lemma setDest_setDest (d : Data) (dst : Dest) (a b : Str) :
    (d.setDest dst a).setDest dst b = d.setDest dst b := by
  cases dst <;> simp [setDest]

end Data

lemma source_ne_header (s : Source) : s.key ≠ (1 : Fin 15) := by
  cases s <;> simp [Source.key,addrKey,Fin.ext_iff]
  omega

lemma source_ne_body (s : Source) : s.key ≠ (13 : Fin 15) := by
  cases s <;> simp [Source.key,addrKey,Fin.ext_iff]
  omega

lemma source_ne_temp (s : Source) : s.key ≠ (11 : Fin 15) := by
  cases s <;> simp [Source.key,addrKey,Fin.ext_iff]
  omega

lemma dest_ne_temp (dst : Dest) : dst.key ≠ (11 : Fin 15) := by cases dst <;> decide

lemma source_dest_ne {n : ℕ} (task : SumTask n) (part : Fin 3) :
    (task.source part).key ≠ task.dest.key := by
  cases task with
  | headerOutput => exact source_ne_header _
  | loadOutput j => fin_cases part <;> simp [SumTask.source,SumTask.dest,Source.key,Dest.key]
  | address ctx proof => exact source_ne_body _
  | flagX => exact source_ne_body _
  | andFirst j => exact source_ne_body _
  | andLast j => exact source_ne_body _

variable (n : ℕ)



namespace Data

def unstack (S : Fin 15 → Str) : Data :=
  {input := S 0,header := S 1,bound := S 2,ancilla := S 3,oldOutput := S 4,gatesLeft := S 5, addresses := fun j => S (addrKey j),savedBound := S 9,savedAddress := S 10,temp := S 11, count := S 12,body := S 13,output := S 14}

@[simp] lemma unstack_stacks (d : Data) : unstack d.stacks = d := by
  cases d
  simp only [unstack,Data.stacks]
  congr 1
  funext j
  fin_cases j <;> rfl

lemma stacks_injective : Function.Injective Data.stacks := by
  intro d e h
  simpa only [unstack_stacks] using congrArg unstack h

@[simp] lemma stacks_temp (d : Data) : d.stacks 11 = d.temp := rfl

lemma temp_stacks (d : Data) (xs : Str) :
    ({d with temp := xs} : Data).stacks = Function.update d.stacks 11 xs := by
  funext k
  fin_cases k <;> simp [Data.stacks]

lemma dest_setSource (d : Data) (s : Source) (dst : Dest) (xs : Str) (h : dst.key ≠ s.key) :
    (d.setSource s xs).dest dst = d.dest dst := by
  rw [← stacks_dest,setSource_stacks,Function.update_of_ne h,stacks_dest]

lemma source_setDest (d : Data) (s : Source) (dst : Dest) (xs : Str) (h : s.key ≠ dst.key) :
    (d.setDest dst xs).source s = d.source s := by
  rw [← stacks_source,setDest_stacks,Function.update_of_ne h,stacks_source]

lemma setDest_setSource (d : Data) (s : Source) (dst : Dest) (xs ys : Str) (h : s.key ≠ dst.key) :
    (d.setDest dst ys).setSource s xs = (d.setSource s xs).setDest dst ys := by
  apply stacks_injective
  simp only [setSource_stacks,setDest_stacks]
  exact (Function.update_comm h xs ys d.stacks).symm

lemma temp_setSource (d : Data) (s : Source) (xs ys : Str) :
    ({d with temp := ys} : Data).setSource s xs = {d.setSource s xs with temp := ys} := by
  apply stacks_injective
  simp only [setSource_stacks,temp_stacks]
  exact (Function.update_comm (source_ne_temp s) xs ys d.stacks).symm

lemma setDest_temp (d : Data) (dst : Dest) (xs ys : Str) :
    {d.setDest dst ys with temp := xs} = ({d with temp := xs} : Data).setDest dst ys := by
  apply stacks_injective
  simp only [setDest_stacks,temp_stacks]
  exact Function.update_comm (dest_ne_temp dst) ys xs d.stacks

@[simp] lemma source_temp (d : Data) (s : Source) (xs : Str) :
    ({d with temp := xs} : Data).source s = d.source s := by
  rw [← stacks_source,temp_stacks,Function.update_of_ne (source_ne_temp s),stacks_source]



@[simp] lemma temp_setSource_value (d : Data) (s : Source) (xs : Str) : (d.setSource s xs).temp = d.temp := by
  cases s <;> rfl

@[simp] lemma temp_setDest_value (d : Data) (dst : Dest) (xs : Str) : (d.setDest dst xs).temp = d.temp := by
  cases dst <;> rfl

end Data

lemma copy_scan_cons (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) (xs : Str) :
    (machine n).step (cfg n (.copyUnary task part counter false) v
      (d.setSource (task.source part) (true::xs))) =
      some (cfg n (.copyUnary task part counter false) (true,v.2)
        (({d.setSource (task.source part) xs with temp := true::d.temp} : Data).setDest task.dest (true::d.dest task.dest))) := by
  have hST := source_ne_temp (task.source part)
  have hDT := dest_ne_temp task.dest
  have hSD := source_dest_ne task part
  simp [FinTM2.step,TM2.step,machine,cfg,TM2.stepAux,Data.setSource_stacks,Data.setDest_stacks,
    Data.temp_stacks,Function.update_idem,hST,hST.symm,hDT,hDT.symm,hSD,hSD.symm]

lemma copy_scan_nil (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.copyUnary task part counter false) v (d.setSource (task.source part) [])) =
      some (cfg n (.copyUnary task part counter true) (false,v.2) (d.setSource (task.source part) [])) := by
  simp [FinTM2.step,TM2.step,machine,cfg,TM2.stepAux,Data.setSource_stacks]

lemma copy_restore_cons (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) (xs : Str) :
    (machine n).step (cfg n (.copyUnary task part counter true) v {d with temp := true::xs}) =
      some (cfg n (.copyUnary task part counter true) (true,v.2)
        (({d with temp := xs} : Data).setSource (task.source part) (true::d.source (task.source part)))) := by
  have hST := source_ne_temp (task.source part)
  simp [FinTM2.step,TM2.step,machine,cfg,TM2.stepAux,Data.setSource_stacks,Data.temp_stacks,hST,hST.symm]

lemma copy_restore_nil (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.copyUnary task part counter true) v {d with temp := []}) =
      some (cfg n (.sum task part.castSucc (Fin.ofNat (n+2) (counter.val+1))) (false,false) {d with temp := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,TM2.stepAux,Data.temp_stacks]


lemma compare_both_step (ctx : Context n) (v : Bool × Bool) (d : Data) (m w : Str) :
    (machine n).step (cfg n (.compare ctx) v
      {d with bound := true::m,addresses := Function.update d.addresses ctx.address (true::w)}) =
      some (cfg n (.compare ctx) (true,true)
        {d with bound := m,addresses := Function.update d.addresses ctx.address w, savedBound := true::d.savedBound,savedAddress := true::d.savedAddress}) := by
  cases ctx with
  | body j kind a =>
    fin_cases a <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,Context.address,addrKey,TM2.stepAux]
    all_goals funext k; fin_cases k <;> simp
  | output j =>
    simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,Context.address,addrKey,TM2.stepAux]
    funext k
    fin_cases k <;> simp

lemma compare_bound_zero (ctx : Context n) (v : Bool × Bool) (d : Data) (w : Str) :
    (machine n).step (cfg n (.compare ctx) v
      {d with bound := [],addresses := Function.update d.addresses ctx.address w}) =
      some (cfg n (.restoreBound ctx false) (false,w.head?.isSome)
        {d with bound := [],addresses := Function.update d.addresses ctx.address w}) := by
  cases ctx with
  | body j kind a =>
    fin_cases a <;> cases w <;>
      simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,Context.address,addrKey,TM2.stepAux]
  | output j => cases w <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,Context.address,addrKey,TM2.stepAux]

lemma compare_address_zero (ctx : Context n) (v : Bool × Bool) (d : Data) (m : Str) :
    (machine n).step (cfg n (.compare ctx) v
      {d with bound := true::m,addresses := Function.update d.addresses ctx.address []}) =
      some (cfg n (.restoreBound ctx true) (true,false)
        {d with bound := true::m,addresses := Function.update d.addresses ctx.address []}) := by
  cases ctx with
  | body j kind a => fin_cases a <;>
      simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,Context.address,addrKey,TM2.stepAux]
  | output j => simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,Context.address,addrKey,TM2.stepAux]

lemma restore_bound_cons (ctx : Context n) (proof : Bool) (v : Bool × Bool) (d : Data) (xs : Str) :
    (machine n).step (cfg n (.restoreBound ctx proof) v {d with savedBound := true::xs}) =
      some (cfg n (.restoreBound ctx proof) (true,v.2) {d with savedBound := xs,bound := true::d.bound}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma restore_bound_nil (ctx : Context n) (proof : Bool) (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.restoreBound ctx proof) v {d with savedBound := []}) =
      some (cfg n (.sum (.address ctx proof) 0 0) (false,false) {d with savedBound := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma restore_bound_run (ctx : Context n) (proof : Bool) (v : Bool × Bool) (d : Data) (k : ℕ) :
    (transition n)^[k+1] (some (cfg n (.restoreBound ctx proof) v {d with savedBound := List.replicate k true})) =
      some (cfg n (.sum (.address ctx proof) 0 0) (false,false)
        {d with savedBound := [],bound := List.replicate k true++d.bound}) := by
  induction k generalizing v d with
  | zero => simpa using restore_bound_nil n ctx proof v d
  | succ k ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[k+1]
      ((machine n).step (cfg n (.restoreBound ctx proof) v {d with savedBound := true::List.replicate k true})) = _
    rw [restore_bound_cons]
    have hr : List.replicate k true++true::d.bound = List.replicate (k+1) true++d.bound := by rw [List.replicate_add]; simp
    simpa only [hr] using ih (true,v.2) {d with bound := true::d.bound}

lemma compare_run (ctx : Context n) (m : ℕ) : ∀ (w : ℕ) (v : Bool × Bool) (d : Data),
    (transition n)^[min m w+1]
      (some (cfg n (.compare ctx) v {d with bound := List.replicate m true,addresses := Function.update d.addresses ctx.address (List.replicate w true)})) =
      some (cfg n (.restoreBound ctx (decide (w < m))) (decide (w < m),decide (m < w))
        {d with bound := List.replicate (m-w) true,addresses := Function.update d.addresses ctx.address (List.replicate (w-m) true), savedBound := List.replicate (min m w) true++d.savedBound,savedAddress := List.replicate (min m w) true++d.savedAddress}) := by
  induction m with
  | zero =>
    intro w v d
    change (machine n).step (cfg n (.compare ctx) v {d with bound := [],addresses := Function.update d.addresses ctx.address (List.replicate w true)}) = _
    have h := compare_bound_zero n ctx v d (List.replicate w true)
    cases w <;> simpa [List.replicate_succ] using h
  | succ m ih =>
    intro w v d
    cases w with
    | zero =>
      change (machine n).step (cfg n (.compare ctx) v {d with bound := true::List.replicate m true,addresses := Function.update d.addresses ctx.address []}) = _
      simpa [List.replicate_succ] using compare_address_zero n ctx v d (List.replicate m true)
    | succ w =>
      have hmin : min (m+1) (w+1) = min m w+1 := by omega
      rw [hmin,Nat.succ_add,Function.iterate_succ_apply]
      change (transition n)^[min m w+1]
        ((machine n).step (cfg n (.compare ctx) v {d with bound := true::List.replicate m true,addresses := Function.update d.addresses ctx.address (true::List.replicate w true)})) = _
      rw [compare_both_step]
      have hb : List.replicate (min m w) true++true::d.savedBound = List.replicate (min m w+1) true++d.savedBound := by rw [List.replicate_add]; simp
      have ha : List.replicate (min m w) true++true::d.savedAddress = List.replicate (min m w+1) true++d.savedAddress := by rw [List.replicate_add]; simp
      simpa only [Nat.add_sub_add_right,Nat.add_lt_add_iff_right,hmin,hb,ha] using
        ih w (true,true) {d with savedBound := true::d.savedBound,savedAddress := true::d.savedAddress}

lemma split_run (ctx : Context n) (m w : ℕ) (v : Bool × Bool) (d : Data)
    (hs : d.savedBound = []) (ht : d.savedAddress = []) :
    (transition n)^[2*min m w+2]
      (some (cfg n (.compare ctx) v {d with bound := List.replicate m true,addresses := Function.update d.addresses ctx.address (List.replicate w true)})) =
      some (cfg n (.sum (.address ctx (decide (w < m))) 0 0) (false,false)
        {d with bound := List.replicate m true,addresses := Function.update d.addresses ctx.address (List.replicate (w-m) true),savedBound := [],savedAddress := List.replicate (min m w) true}) := by
  rw [show 2*min m w+2 = (min m w+1)+(min m w+1) by omega,Function.iterate_add_apply,compare_run n ctx m w v d]
  simp only [hs,ht,List.append_nil]
  have h := restore_bound_run n ctx (decide (w < m)) (decide (w < m),decide (m < w))
    {d with bound := List.replicate (m-w) true,addresses := Function.update d.addresses ctx.address (List.replicate (w-m) true),savedAddress := List.replicate (min m w) true} (min m w)
  have hm : min m w+(m-w) = m := by omega
  simpa only [← List.replicate_add,hm] using h


lemma copy_scan_run (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) (w : ℕ) :
    (transition n)^[w+1]
      (some (cfg n (.copyUnary task part counter false) v (d.setSource (task.source part) (List.replicate w true)))) =
      some (cfg n (.copyUnary task part counter true) (false,v.2)
        (({d.setSource (task.source part) [] with temp := List.replicate w true++d.temp} : Data).setDest task.dest
          (List.replicate w true++d.dest task.dest))) := by
  have hSD := source_dest_ne task part
  induction w generalizing v d with
  | zero =>
    change (machine n).step (cfg n (.copyUnary task part counter false) v (d.setSource (task.source part) [])) = _
    have he : (({d.setSource (task.source part) [] with temp := d.temp} : Data).setDest task.dest (d.dest task.dest)) =
        d.setSource (task.source part) [] := by
      have ht : ({d.setSource (task.source part) [] with temp := d.temp} : Data) = d.setSource (task.source part) [] := by
        rw [← Data.temp_setSource_value d (task.source part) []]
      rw [ht,← Data.dest_setSource d (task.source part) task.dest [] hSD.symm,Data.setDest_self]
    simpa only [List.replicate_zero,List.nil_append,he] using copy_scan_nil n task part counter v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1]
      ((machine n).step (cfg n (.copyUnary task part counter false) v
        (d.setSource (task.source part) (true::List.replicate w true)))) = _
    rw [copy_scan_cons]
    let d' := ({d with temp := true::d.temp} : Data).setDest task.dest (true::d.dest task.dest)
    have h := ih (true,v.2) d'
    have hT : List.replicate w true++true::d.temp = List.replicate (w+1) true++d.temp := by rw [List.replicate_add]; simp
    have hD : List.replicate w true++true::d.dest task.dest = List.replicate (w+1) true++d.dest task.dest := by rw [List.replicate_add]; simp
    have hmove (xs : Str) : d'.setSource (task.source part) xs =
        (({d.setSource (task.source part) xs with temp := true::d.temp} : Data).setDest task.dest (true::d.dest task.dest)) := by
      dsimp only [d']
      rw [Data.setDest_setSource _ (task.source part) task.dest xs _ hSD,Data.temp_setSource]
    have htmp : d'.temp = true::d.temp := by dsimp only [d']; rw [Data.temp_setDest_value]
    have hdst : d'.dest task.dest = true::d.dest task.dest := by dsimp only [d']; rw [Data.dest_setDest]
    simpa only [hmove,htmp,hdst,Data.setDest_temp,Data.setDest_setDest,hT,hD] using h

lemma copy_restore_run (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) (w : ℕ) :
    (transition n)^[w+1]
      (some (cfg n (.copyUnary task part counter true) v {d with temp := List.replicate w true})) =
      some (cfg n (.sum task part.castSucc (Fin.ofNat (n+2) (counter.val+1))) (false,false)
        (({d with temp := []} : Data).setSource (task.source part)
          (List.replicate w true++d.source (task.source part)))) := by
  induction w generalizing v d with
  | zero =>
    change (machine n).step (cfg n (.copyUnary task part counter true) v {d with temp := []}) = _
    have he : (({d with temp := []} : Data).setSource (task.source part) (d.source (task.source part))) =
        {d with temp := []} := by
      rw [← Data.source_temp d (task.source part) [],Data.setSource_self]
    simpa only [List.replicate_zero,List.nil_append,he] using copy_restore_nil n task part counter v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1]
      ((machine n).step (cfg n (.copyUnary task part counter true) v {d with temp := true::List.replicate w true})) = _
    rw [copy_restore_cons]
    have h := ih (true,v.2) (d.setSource (task.source part) (true::d.source (task.source part)))
    have hr : List.replicate w true++true::d.source (task.source part) =
        List.replicate (w+1) true++d.source (task.source part) := by rw [List.replicate_add]; simp
    simpa only [Data.temp_setSource,Data.source_setSource,Data.setSource_setSource,hr] using h

/-- One unary counter is copied to the task's destination and fully restored. -/
lemma copy_unary_run (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) (w : ℕ)
    (hw : d.source (task.source part) = List.replicate w true) (ht : d.temp = []) :
    (transition n)^[2*w+2] (some (cfg n (.copyUnary task part counter false) v d)) =
      some (cfg n (.sum task part.castSucc (Fin.ofNat (n+2) (counter.val+1))) (false,false)
        (d.setDest task.dest (List.replicate w true++d.dest task.dest))) := by
  have hSD := source_dest_ne task part
  have hd : d.setSource (task.source part) (List.replicate w true) = d := by rw [← hw,Data.setSource_self]
  have hs := copy_scan_run n task part counter v d w
  rw [hd] at hs
  rw [show 2*w+2 = (w+1)+(w+1) by omega,Function.iterate_add_apply,hs]
  simp only [ht,List.append_nil]
  let d' := (d.setSource (task.source part) []).setDest task.dest (List.replicate w true++d.dest task.dest)
  have h := copy_restore_run n task part counter (false,v.2) d' w
  have htemp : ({d with temp := []} : Data) = d := by rw [← ht]
  have hinit : ({d' with temp := List.replicate w true} : Data) =
      (({d.setSource (task.source part) [] with temp := List.replicate w true} : Data).setDest task.dest
        (List.replicate w true++d.dest task.dest)) := by
    dsimp only [d']
    rw [Data.setDest_temp]
  have hsrc : d'.source (task.source part) = [] := by
    dsimp only [d']
    rw [Data.source_setDest _ (task.source part) task.dest _ hSD,Data.source_setSource]
  have hmid : d'.setSource (task.source part) (List.replicate w true) =
      d.setDest task.dest (List.replicate w true++d.dest task.dest) := by
    dsimp only [d']
    rw [Data.setDest_setSource _ (task.source part) task.dest _ _ hSD,Data.setSource_setSource,hd]
  have hout : (({d' with temp := []} : Data).setSource (task.source part) (List.replicate w true)) =
      d.setDest task.dest (List.replicate w true++d.dest task.dest) := by
    rw [Data.temp_setSource]
    simp only [hmid]
    rw [Data.setDest_temp,htemp]
  simpa only [hinit,hsrc,List.append_nil,hout] using h


lemma run_trans {k l : ℕ} {a b c : Option (machine n).Cfg}
    (hk : (transition n)^[k] a = b) (hl : (transition n)^[l] b = c) :
    (transition n)^[k+l] a = c := by rw [Nat.add_comm k l,Function.iterate_add_apply,hk,hl]

lemma copies_le (task : SumTask n) (part : Fin 3) : task.copies part ≤ n+1 := by
  cases task with
  | address ctx proof =>
    have h := ctx.index.isLt
    cases proof <;> fin_cases part <;> simp [SumTask.copies] <;> omega
  | loadOutput j => fin_cases part <;> simp [SumTask.copies] <;> omega
  | headerOutput => fin_cases part <;> simp [SumTask.copies]
  | flagX => fin_cases part <;> simp [SumTask.copies]
  | andFirst j => fin_cases part <;> simp [SumTask.copies]
  | andLast j => fin_cases part <;> simp [SumTask.copies]

lemma sum_copy_step (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) (hc : counter.val < task.copies part) :
    (machine n).step (cfg n (.sum task part.castSucc counter) v d) =
      some (cfg n (.copyUnary task part counter false) (false,false) d) := by
  simp [FinTM2.step,TM2.step,machine,cfg,TM2.stepAux,part.isLt,hc]

lemma sum_advance_step (task : SumTask n) (part : Fin 3) (counter : Fin (n+2))
    (v : Bool × Bool) (d : Data) (hc : ¬counter.val < task.copies part) :
    (machine n).step (cfg n (.sum task part.castSucc counter) v d) =
      some (cfg n (.sum task ⟨part.val+1,by have := part.isLt; omega⟩ 0) (false,false) d) := by
  simp [FinTM2.step,TM2.step,machine,cfg,TM2.stepAux,part.isLt,hc]

def finishWord (task : SumTask n) : Str :=
  if task.delimiter then encNat task.literal else List.replicate task.literal true

lemma sum_finish_step (task : SumTask n) (counter : Fin (n+2)) (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.sum task 3 counter) v d) =
      some (cfg n (sumReturn n task) (false,false)
        (d.setDest task.dest ((finishWord n task).reverse++d.dest task.dest))) := by
  cases hd : task.delimiter <;>
    simp [FinTM2.step,TM2.step,machine,cfg,TM2.stepAux,Statement.stepAux_pushMany,
      Data.setDest_stacks,finishWord,hd,encNat,List.reverse_append]

lemma sum_component_run (task : SumTask n) (part : Fin 3) (r : ℕ) :
    ∀ (counter : Fin (n+2)) (hr : counter.val+r = task.copies part)
      (v : Bool × Bool) (d : Data) (w : ℕ)
      (hw : d.source (task.source part) = List.replicate w true) (ht : d.temp = []),
    (transition n)^[r*(2*w+3)+1]
      (some (cfg n (.sum task part.castSucc counter) v d)) =
      some (cfg n (.sum task ⟨part.val+1,by have := part.isLt; omega⟩ 0) (false,false)
        (d.setDest task.dest (List.replicate (r*w) true++d.dest task.dest))) := by
  induction r with
  | zero =>
    intro counter hr v d w hw ht
    simp only [Nat.zero_mul,Nat.zero_add]
    change (machine n).step (cfg n (.sum task part.castSucc counter) v d) = _
    simpa only [Nat.zero_mul,List.replicate_zero,List.nil_append,Data.setDest_self] using
      sum_advance_step n task part counter v d (by omega)
  | succ r ih =>
    intro counter hr v d w hw ht
    have hmax := copies_le n task part
    have hn : (Fin.ofNat (n+2) (counter.val+1)).val = counter.val+1 := by
      rw [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega)]
    have h1 : (transition n)^[1] (some (cfg n (.sum task part.castSucc counter) v d)) =
        some (cfg n (.copyUnary task part counter false) (false,false) d) :=
      sum_copy_step n task part counter v d (by omega)
    have h2 := copy_unary_run n task part counter (false,false) d w hw ht
    have hs : (d.setDest task.dest (List.replicate w true++d.dest task.dest)).source (task.source part) = List.replicate w true := by
      rw [Data.source_setDest _ (task.source part) task.dest _ (source_dest_ne task part)]
      exact hw
    have h3 := ih (Fin.ofNat (n+2) (counter.val+1)) (by rw [hn]; omega) (false,false)
      (d.setDest task.dest (List.replicate w true++d.dest task.dest)) w hs (by simpa only [Data.temp_setDest_value] using ht)
    have h := run_trans n (run_trans n h1 h2) h3
    have hR : List.replicate (r*w) true++(List.replicate w true++d.dest task.dest) =
        List.replicate ((r+1)*w) true++d.dest task.dest := by
      rw [← List.append_assoc,← List.replicate_add,show r*w+w = (r+1)*w by ring]
    convert h using 1 <;> try simp only [Data.dest_setDest,Data.setDest_setDest,hR]
    all_goals congr 1 <;> ring


def sumSize (task : SumTask n) (a : Fin 3 → ℕ) : ℕ :=
  task.copies 0*a 0+task.copies 1*a 1+task.copies 2*a 2+task.literal

def sumWord (task : SumTask n) (a : Fin 3 → ℕ) : Str :=
  if task.delimiter then encNat (sumSize n task a) else List.replicate (sumSize n task a) true

def sumTime (task : SumTask n) (a : Fin 3 → ℕ) : ℕ :=
  (task.copies 0*(2*a 0+3)+1)+(task.copies 1*(2*a 1+3)+1)+
    (task.copies 2*(2*a 2+3)+1)+1

lemma unary_append (a b : ℕ) (xs : Str) :
    List.replicate a true++(List.replicate b true++xs) = List.replicate (a+b) true++xs := by
  rw [← List.append_assoc,← List.replicate_add]

lemma sum_word_append (task : SumTask n) (a : Fin 3 → ℕ) (xs : Str) :
    (finishWord n task).reverse++
      (List.replicate (task.copies 2*a 2) true++
        (List.replicate (task.copies 1*a 1) true++(List.replicate (task.copies 0*a 0) true++xs))) =
      (sumWord n task a).reverse++xs := by
  have he : task.literal+(task.copies 2*a 2+(task.copies 1*a 1+task.copies 0*a 0)) =
      task.copies 0*a 0+task.copies 1*a 1+task.copies 2*a 2+task.literal := by omega
  cases hd : task.delimiter <;>
    simp only [finishWord,sumWord,sumSize,hd,Bool.false_eq_true,ite_false,ite_true,encNat,
      List.reverse_append,List.reverse_singleton,List.reverse_replicate,List.singleton_append,
      List.cons_append,List.nil_append,unary_append,he]

/-- A task emits its complete unary sum word, preserving every source and all scratch. -/
lemma sum_run (task : SumTask n) (v : Bool × Bool) (d : Data) (a : Fin 3 → ℕ)
    (hw : ∀ part, d.source (task.source part) = List.replicate (a part) true) (ht : d.temp = []) :
    (transition n)^[sumTime n task a] (some (cfg n (.sum task 0 0) v d)) =
      some (cfg n (sumReturn n task) (false,false)
        (d.setDest task.dest ((sumWord n task a).reverse++d.dest task.dest))) := by
  have h0 := sum_component_run n task 0 (task.copies 0) 0 (by simp) v d (a 0) (hw 0) ht
  let d0 := d.setDest task.dest (List.replicate (task.copies 0*a 0) true++d.dest task.dest)
  have hs1 : d0.source (task.source 1) = List.replicate (a 1) true := by
    dsimp only [d0]
    rw [Data.source_setDest _ (task.source 1) task.dest _ (source_dest_ne task 1)]
    exact hw 1
  have ht0 : d0.temp = [] := by simpa only [d0,Data.temp_setDest_value] using ht
  have h1 := sum_component_run n task 1 (task.copies 1) 0 (by simp) (false,false) d0 (a 1) hs1 ht0
  let d1 := d0.setDest task.dest (List.replicate (task.copies 1*a 1) true++d0.dest task.dest)
  have hs2 : d1.source (task.source 2) = List.replicate (a 2) true := by
    dsimp only [d1,d0]
    rw [Data.source_setDest _ (task.source 2) task.dest _ (source_dest_ne task 2),
      Data.source_setDest _ (task.source 2) task.dest _ (source_dest_ne task 2)]
    exact hw 2
  have ht1 : d1.temp = [] := by simpa only [d1,d0,Data.temp_setDest_value] using ht
  have h2 := sum_component_run n task 2 (task.copies 2) 0 (by simp) (false,false) d1 (a 2) hs2 ht1
  let d2 := d1.setDest task.dest (List.replicate (task.copies 2*a 2) true++d1.dest task.dest)
  have hf := sum_finish_step n task 0 (false,false) d2
  change (transition n)^[1] (some (cfg n (.sum task 3 0) (false,false) d2)) = _ at hf
  have h := run_trans n (run_trans n (run_trans n h0 h1) h2) hf
  have hz : (0 : Fin 3).castSucc = (0 : Fin 4) := rfl
  simpa only [hz,sumTime,d2,d1,d0,Data.dest_setDest,Data.setDest_setDest,sum_word_append] using h



lemma restore_address_cons (ctx : Context n) (v : Bool × Bool) (d : Data) (xs : Str) :
    (machine n).step (cfg n (.restoreAddress ctx) v {d with savedAddress := true::xs}) =
      some (cfg n (.restoreAddress ctx) (true,v.2)
        {d with savedAddress := xs,addresses := Function.update d.addresses ctx.address (true::d.addresses ctx.address)}) := by
  cases ctx with
  | body j kind a =>
    fin_cases a <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,Context.address,addrKey,TM2.stepAux]
    all_goals funext k; fin_cases k <;> simp
  | output j =>
    simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,Context.address,addrKey,TM2.stepAux]
    funext k; fin_cases k <;> simp

lemma restore_address_nil (ctx : Context n) (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.restoreAddress ctx) v {d with savedAddress := []}) =
      some (cfg n (afterMapped n ctx) (false,false) {d with savedAddress := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma restore_address_run (ctx : Context n) (v : Bool × Bool) (d : Data) (k : ℕ) :
    (transition n)^[k+1]
      (some (cfg n (.restoreAddress ctx) v {d with savedAddress := List.replicate k true})) =
      some (cfg n (afterMapped n ctx) (false,false)
        {d with savedAddress := [],addresses := Function.update d.addresses ctx.address (List.replicate k true++d.addresses ctx.address)}) := by
  induction k generalizing v d with
  | zero => simpa using restore_address_nil n ctx v d
  | succ k ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[k+1]
      ((machine n).step (cfg n (.restoreAddress ctx) v
        {d with savedAddress := true::List.replicate k true})) = _
    rw [restore_address_cons]
    have hr : List.replicate k true++true::d.addresses ctx.address =
        List.replicate (k+1) true++d.addresses ctx.address := by rw [List.replicate_add]; simp
    simpa only [Function.update_self,Function.update_idem,hr] using
      ih (true,v.2) {d with addresses := Function.update d.addresses ctx.address (true::d.addresses ctx.address)}

def addressParts (m a w : ℕ) : Fin 3 → ℕ := ![m,a,if w < m then min m w else w-m]

def addressTime (ctx : Context n) (m a w : ℕ) : ℕ :=
  (2*min m w+2)+sumTime n (.address ctx (decide (w < m))) (addressParts m a w)+(min m w+1)

lemma mapped_address_run (ctx : Context n) (v : Bool × Bool) (d : Data) (m a w : ℕ)
    (hm : d.bound = List.replicate m true) (ha : d.ancilla = List.replicate a true)
    (hw : d.addresses ctx.address = List.replicate w true)
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []) :
    (transition n)^[addressTime n ctx m a w] (some (cfg n (.compare ctx) v d)) =
      some (cfg n (afterMapped n ctx) (false,false)
        {d with body := (encNat (Encoding.remapWire m a n ctx.index.val w)).reverse++d.body}) := by
  let ds : Data := {d with bound := List.replicate m true, addresses := Function.update d.addresses ctx.address (List.replicate (w-m) true), savedBound := [],savedAddress := List.replicate (min m w) true}
  have hd : {d with bound := List.replicate m true, addresses := Function.update d.addresses ctx.address (List.replicate w true)} = d := by
    rw [← hm,← hw,Function.update_eq_self]
  have h1 := split_run n ctx m w v d hs ht
  rw [hd] at h1
  change (transition n)^[2*min m w+2] (some (cfg n (.compare ctx) v d)) =
    some (cfg n (.sum (.address ctx (decide (w < m))) 0 0) (false,false) ds) at h1
  have hp : ∀ part, ds.source ((SumTask.address ctx (decide (w < m))).source part) =
      List.replicate (addressParts m a w part) true := by
    intro part
    fin_cases part <;> by_cases h : w < m <;> simp [ds,Data.source,SumTask.source,addressParts,ha,h]
  have h2 := sum_run n (.address ctx (decide (w < m))) (false,false) ds
    (addressParts m a w) hp hu
  have hword : sumWord n (.address ctx (decide (w < m))) (addressParts m a w) =
      encNat (Encoding.remapWire m a n ctx.index.val w) := by
    simp only [sumWord,SumTask.delimiter,ite_true,sumSize,SumTask.copies,SumTask.literal,addressParts]
    by_cases h : w < m
    · simp [h,Encoding.remapWire,Nat.min_eq_right (Nat.le_of_lt h),Nat.mul_comm,Nat.add_comm]
    · simp [h,Encoding.remapWire]
      congr 1
      ring
  rw [hword] at h2
  let de : Data := {ds with body := (encNat (Encoding.remapWire m a n ctx.index.val w)).reverse++ds.body}
  change (transition n)^[sumTime n (.address ctx (decide (w < m))) (addressParts m a w)]
    (some (cfg n (.sum (.address ctx (decide (w < m))) 0 0) (false,false) ds)) =
    some (cfg n (.restoreAddress ctx) (false,false) de) at h2
  have h3 := restore_address_run n ctx (false,false) de (min m w)
  have hin : {de with savedAddress := List.replicate (min m w) true} = de := rfl
  rw [hin] at h3
  have ho : {de with savedAddress := [],addresses := Function.update de.addresses ctx.address (List.replicate (min m w) true++de.addresses ctx.address)} =
      {d with body := (encNat (Encoding.remapWire m a n ctx.index.val w)).reverse++d.body} := by
    dsimp only [de,ds]
    simp only [Function.update_self,Function.update_idem,← List.replicate_add,
      show min m w+(w-m)=w by omega]
    rw [← hm,← hw,Function.update_eq_self]
    simp only [hs,ht]
  rw [ho] at h3
  exact run_trans n (run_trans n h1 h2) h3

lemma addressTime_le (ctx : Context n) (m a w : ℕ) :
    addressTime n ctx m a w ≤ 20*(n+1)*(m+a+w+1) := by
  have hj := ctx.index.isLt
  have hp0 := copies_le n (.address ctx (decide (w < m))) 0
  have hp1 := copies_le n (.address ctx (decide (w < m))) 1
  have hp2 := copies_le n (.address ctx (decide (w < m))) 2
  have hm : min m w ≤ m := Nat.min_le_left _ _
  have hw : min m w ≤ w := Nat.min_le_right _ _
  have hp : ∀ j, addressParts m a w j ≤ m+a+w := by
    intro j
    fin_cases j
    · change m ≤ m+a+w; omega
    · change a ≤ m+a+w; omega
    · change (if w < m then min m w else w-m) ≤ m+a+w
      split_ifs <;> omega
  have h0 := Nat.mul_le_mul hp0 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hp 0)) 3)
  have h1 := Nat.mul_le_mul hp1 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hp 1)) 3)
  have h2 := Nat.mul_le_mul hp2 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hp 2)) 3)
  unfold addressTime sumTime
  nlinarith



def nextRead (j : Fin (n+1)) (kind : Fin 4) (a : Fin 3) : Label n :=
  if h : a.val+1<arity kind then
    .readAddress j kind ⟨a.val+1,by unfold arity at h; split_ifs at h <;> omega⟩
  else .compare (.body j kind 0)

def nextClear (ret : AfterAddress n) (j : Fin 3) : Label n :=
  if h : j.val<2 then .clearSources ret ⟨j.val+1,by omega⟩ else afterClear n ret

lemma read_true_step (j : Fin (n+1)) (kind : Fin 4) (a : Fin 3)
    (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.readAddress j kind a) v {d with input := true::tail}) =
      some (cfg n (.readAddress j kind a) (true,true)
        {d with input := tail,addresses := Function.update d.addresses a (true::d.addresses a)}) := by
  fin_cases kind <;> fin_cases a <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux,arity]
  all_goals funext k; fin_cases k <;> simp

lemma read_false_step (j : Fin (n+1)) (kind : Fin 4) (a : Fin 3)
    (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.readAddress j kind a) v {d with input := false::tail}) =
      some (cfg n (nextRead n j kind a) (false,false) {d with input := tail}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux,nextRead]
  funext k; fin_cases k <;> simp

lemma read_run (j : Fin (n+1)) (kind : Fin 4) (a : Fin 3)
    (v : Bool × Bool) (d : Data) (w : ℕ) (tail : Str) :
    (transition n)^[w+1]
      (some (cfg n (.readAddress j kind a) v {d with input := encNat w++tail})) =
      some (cfg n (nextRead n j kind a) (false,false)
        {d with input := tail,addresses := Function.update d.addresses a (List.replicate w true++d.addresses a)}) := by
  induction w generalizing v d with
  | zero => simpa [encNat] using read_false_step n j kind a v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1]
      ((machine n).step (cfg n (.readAddress j kind a) v {d with input := true::(encNat w++tail)})) = _
    rw [read_true_step]
    have hrep : List.replicate w true++true::d.addresses a =
        List.replicate (w+1) true++d.addresses a := by rw [List.replicate_add]; simp
    simpa only [Function.update_self,Function.update_idem,hrep] using
      ih (true,true) {d with addresses := Function.update d.addresses a (true::d.addresses a)}

lemma clear_true_step (ret : AfterAddress n) (a : Fin 3) (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.clearSources ret a) v
      {d with addresses := Function.update d.addresses a (true::tail)}) =
      some (cfg n (.clearSources ret a) (true,v.2)
        {d with addresses := Function.update d.addresses a tail}) := by
  fin_cases a <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals funext k; fin_cases k <;> simp

lemma clear_nil_step (ret : AfterAddress n) (a : Fin 3) (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.clearSources ret a) v
      {d with addresses := Function.update d.addresses a []}) =
      some (cfg n (nextClear n ret a) (false,false)
        {d with addresses := Function.update d.addresses a []}) := by
  fin_cases a <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux,nextClear]

lemma clear_run (ret : AfterAddress n) (a : Fin 3) (v : Bool × Bool) (d : Data) (w : ℕ) :
    (transition n)^[w+1]
      (some (cfg n (.clearSources ret a) v
        {d with addresses := Function.update d.addresses a (List.replicate w true)})) =
      some (cfg n (nextClear n ret a) (false,false)
        {d with addresses := Function.update d.addresses a []}) := by
  induction w generalizing v with
  | zero => exact clear_nil_step n ret a v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1] ((machine n).step
      (cfg n (.clearSources ret a) v {d with addresses := Function.update d.addresses a (true::List.replicate w true)})) = _
    rw [clear_true_step,ih]

lemma clear_actual_run (ret : AfterAddress n) (a : Fin 3) (v : Bool × Bool) (d : Data) (w : ℕ)
    (hw : d.addresses a = List.replicate w true) :
    (transition n)^[w+1] (some (cfg n (.clearSources ret a) v d)) =
      some (cfg n (nextClear n ret a) (false,false)
        {d with addresses := Function.update d.addresses a []}) := by
  have hd : {d with addresses := Function.update d.addresses a (List.replicate w true)} = d := by
    rw [← hw,Function.update_eq_self]
  simpa only [hd] using clear_run n ret a v d w

lemma clear_sources_run (ret : AfterAddress n) (v : Bool × Bool) (d : Data) (a : Fin 3 → ℕ)
    (hw : ∀ j, d.addresses j = List.replicate (a j) true) :
    (transition n)^[a 0+a 1+a 2+3] (some (cfg n (.clearSources ret 0) v d)) =
      some (cfg n (afterClear n ret) (false,false) {d with addresses := fun _ => []}) := by
  have h0 := clear_actual_run n ret 0 v d (a 0) (hw 0)
  have h1 := clear_actual_run n ret 1 (false,false)
    {d with addresses := Function.update d.addresses 0 []} (a 1) (by simpa using hw 1)
  have h2 := clear_actual_run n ret 2 (false,false)
    {d with addresses := Function.update (Function.update d.addresses 0 []) 1 []} (a 2) (by simpa using hw 2)
  have hc0 : nextClear n ret 0 = .clearSources ret 1 := rfl
  have hc1 : nextClear n ret 1 = .clearSources ret 2 := rfl
  have hc2 : nextClear n ret 2 = afterClear n ret := rfl
  simp only [hc0,hc1,hc2] at h0 h1 h2
  have h := run_trans n (run_trans n h0 h1) h2
  have hz : Function.update (Function.update (Function.update d.addresses 0 []) 1 []) 2 [] = fun _ => [] := by
    funext i; fin_cases i <;> simp
  convert h using 1 <;> try simp only [hz]
  all_goals congr 1 <;> omega



def rawArgs (kind : Fin 4) (a : Fin 3 → ℕ) : List ℕ :=
  if kind = 0 then [a 0] else if kind = 2 then [a 0,a 1,a 2] else [a 0,a 1]

def sourceWires (kind : Fin 4) (a : Fin 3 → ℕ) : Str := (rawArgs kind a).flatMap encNat

def loadedAddresses (kind : Fin 4) (a : Fin 3 → ℕ) : Fin 3 → Str :=
  fun j => if j.val<arity kind then List.replicate (a j) true else []

def readTime (kind : Fin 4) (a : Fin 3 → ℕ) : ℕ :=
  if kind = 0 then a 0+1 else if kind = 2 then (a 0+1)+(a 1+1)+(a 2+1) else (a 0+1)+(a 1+1)

lemma read_sources_run (j : Fin (n+1)) (kind : Fin 4) (v : Bool × Bool) (d : Data)
    (a : Fin 3 → ℕ) (tail : Str) (hd : d.addresses = fun _ => []) :
    (transition n)^[readTime kind a]
      (some (cfg n (.readAddress j kind 0) v {d with input := sourceWires kind a++tail})) =
      some (cfg n (.compare (.body j kind 0)) (false,false)
        {d with input := tail,addresses := loadedAddresses kind a}) := by
  fin_cases kind
  ·
    change (transition n)^[readTime 0 a]
      (some (cfg n (.readAddress j 0 0) v {d with input := sourceWires 0 a++tail})) =
      some (cfg n (.compare (.body j 0 0)) (false,false)
        {d with input := tail,addresses := loadedAddresses 0 a})
    have h0 := read_run n j 0 0 v (d) (a 0) (tail)
    have hn0 : nextRead n j 0 0 = .compare (.body j 0 0) := rfl
    rw [hn0] at h0
    have h := h0
    have he : Function.update d.addresses 0 (List.replicate (a 0) true++d.addresses 0) = loadedAddresses 0 a := by
      funext i; fin_cases i <;> simp [hd,loadedAddresses,arity]
    simpa only [readTime,sourceWires,rawArgs,show (0 : Fin 4) = 0 from rfl,
      ite_true,ite_false,show ¬(2 : Fin 4)=0 by decide,show ¬(1 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=0 by decide,
      show ¬(1 : Fin 4)=2 by decide,show ¬(3 : Fin 4)=2 by decide,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,he] using h
  ·
    change (transition n)^[readTime 1 a]
      (some (cfg n (.readAddress j 1 0) v {d with input := sourceWires 1 a++tail})) =
      some (cfg n (.compare (.body j 1 0)) (false,false)
        {d with input := tail,addresses := loadedAddresses 1 a})
    have h0 := read_run n j 1 0 v (d) (a 0) (encNat (a 1)++tail)
    have hn0 : nextRead n j 1 0 = .readAddress j 1 1 := rfl
    rw [hn0] at h0
    have h1 := read_run n j 1 1 (false,false) ({d with addresses := Function.update d.addresses 0 (List.replicate (a 0) true++d.addresses 0)}) (a 1) (tail)
    have hn1 : nextRead n j 1 1 = .compare (.body j 1 0) := rfl
    rw [hn1] at h1
    try simp only [List.append_assoc] at h0
    simp only [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)] at h1
    have h := run_trans n h0 h1
    have he : Function.update (Function.update d.addresses 0 (List.replicate (a 0) true++d.addresses 0)) 1 (List.replicate (a 1) true++d.addresses 1) = loadedAddresses 1 a := by
      funext i; fin_cases i <;> simp [hd,loadedAddresses,arity]
    simpa only [readTime,sourceWires,rawArgs,show (1 : Fin 4) = 1 from rfl,
      ite_true,ite_false,show ¬(2 : Fin 4)=0 by decide,show ¬(1 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=0 by decide,
      show ¬(1 : Fin 4)=2 by decide,show ¬(3 : Fin 4)=2 by decide,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,he] using h
  ·
    change (transition n)^[readTime 2 a]
      (some (cfg n (.readAddress j 2 0) v {d with input := sourceWires 2 a++tail})) =
      some (cfg n (.compare (.body j 2 0)) (false,false)
        {d with input := tail,addresses := loadedAddresses 2 a})
    have h0 := read_run n j 2 0 v (d) (a 0) (encNat (a 1)++encNat (a 2)++tail)
    have hn0 : nextRead n j 2 0 = .readAddress j 2 1 := rfl
    rw [hn0] at h0
    have h1 := read_run n j 2 1 (false,false) ({d with addresses := Function.update d.addresses 0 (List.replicate (a 0) true++d.addresses 0)}) (a 1) (encNat (a 2)++tail)
    have hn1 : nextRead n j 2 1 = .readAddress j 2 2 := rfl
    rw [hn1] at h1
    have h2 := read_run n j 2 2 (false,false) ({d with addresses := Function.update (Function.update d.addresses 0 (List.replicate (a 0) true++d.addresses 0)) 1 (List.replicate (a 1) true++d.addresses 1)}) (a 2) (tail)
    have hn2 : nextRead n j 2 2 = .compare (.body j 2 0) := rfl
    rw [hn2] at h2
    simp only [List.append_assoc] at h0 h1
    simp only [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)] at h1
    simp only [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0),
      Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1)] at h2
    have h := run_trans n (run_trans n h0 h1) h2
    have he : Function.update (Function.update (Function.update d.addresses 0 (List.replicate (a 0) true++d.addresses 0)) 1 (List.replicate (a 1) true++d.addresses 1)) 2 (List.replicate (a 2) true++d.addresses 2) = loadedAddresses 2 a := by
      funext i; fin_cases i <;> simp [hd,loadedAddresses,arity]
    simpa only [readTime,sourceWires,rawArgs,show (2 : Fin 4) = 2 from rfl,
      ite_true,ite_false,show ¬(2 : Fin 4)=0 by decide,show ¬(1 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=0 by decide,
      show ¬(1 : Fin 4)=2 by decide,show ¬(3 : Fin 4)=2 by decide,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,he] using h
  ·
    change (transition n)^[readTime 3 a]
      (some (cfg n (.readAddress j 3 0) v {d with input := sourceWires 3 a++tail})) =
      some (cfg n (.compare (.body j 3 0)) (false,false)
        {d with input := tail,addresses := loadedAddresses 3 a})
    have h0 := read_run n j 3 0 v (d) (a 0) (encNat (a 1)++tail)
    have hn0 : nextRead n j 3 0 = .readAddress j 3 1 := rfl
    rw [hn0] at h0
    have h1 := read_run n j 3 1 (false,false) ({d with addresses := Function.update d.addresses 0 (List.replicate (a 0) true++d.addresses 0)}) (a 1) (tail)
    have hn1 : nextRead n j 3 1 = .compare (.body j 3 0) := rfl
    rw [hn1] at h1
    try simp only [List.append_assoc] at h0
    simp only [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)] at h1
    have h := run_trans n h0 h1
    have he : Function.update (Function.update d.addresses 0 (List.replicate (a 0) true++d.addresses 0)) 1 (List.replicate (a 1) true++d.addresses 1) = loadedAddresses 3 a := by
      funext i; fin_cases i <;> simp [hd,loadedAddresses,arity]
    simpa only [readTime,sourceWires,rawArgs,show (3 : Fin 4) = 3 from rfl,
      ite_true,ite_false,show ¬(2 : Fin 4)=0 by decide,show ¬(1 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=0 by decide,
      show ¬(1 : Fin 4)=2 by decide,show ¬(3 : Fin 4)=2 by decide,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,he] using h



def loadedValues (kind : Fin 4) (a : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun j => if j.val<arity kind then a j else 0

def mappedWires (kind : Fin 4) (a : Fin 3 → ℕ) (m b n j : ℕ) : Str :=
  (rawArgs kind a).flatMap (fun w => encNat (Encoding.remapWire m b n j w))

def mappingTime (j : Fin (n+1)) (kind : Fin 4) (a : Fin 3 → ℕ) (m b : ℕ) : ℕ :=
  (if kind = 0 then addressTime n (.body j kind 0) m b (a 0)
    else if kind = 2 then addressTime n (.body j kind 0) m b (a 0)+
      addressTime n (.body j kind 1) m b (a 1)+addressTime n (.body j kind 2) m b (a 2)
    else addressTime n (.body j kind 0) m b (a 0)+addressTime n (.body j kind 1) m b (a 1))+
    (loadedValues kind a 0+loadedValues kind a 1+loadedValues kind a 2+3)

lemma map_sources_run (j : Fin (n+1)) (kind : Fin 4) (v : Bool × Bool) (d : Data)
    (a : Fin 3 → ℕ) (m b : ℕ)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (hd : d.addresses = loadedAddresses kind a)
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []) :
    (transition n)^[mappingTime n j kind a m b]
      (some (cfg n (.compare (.body j kind 0)) v d)) =
      some (cfg n (.gate j) (false,false)
        {d with addresses := fun _ => [],body := (mappedWires kind a m b n j.val).reverse++d.body}) := by
  have hw (i : Fin 3) : d.addresses i = List.replicate (loadedValues kind a i) true := by
    rw [hd]
    unfold loadedAddresses loadedValues
    split_ifs <;> rfl
  fin_cases kind
  ·
    change (transition n)^[mappingTime n j 0 a m b]
      (some (cfg n (.compare (.body j 0 0)) v d)) =
      some (cfg n (.gate j) (false,false)
        {d with addresses := fun _ => [],body := (mappedWires 0 a m b n j.val).reverse++d.body})
    have h0 := mapped_address_run n (.body j 0 0) v d m b (a 0) hm hb
      (by simpa [loadedValues,arity,Context.address] using hw 0) hs ht hu
    have hn0 : afterMapped n (.body j 0 0) = .clearSources (.body j) 0 := rfl
    rw [hn0] at h0
    let d0 : Data := {d with body := (encNat (Encoding.remapWire m b n j.val (a 0))).reverse++d.body}
    have hc := clear_sources_run n (.body j) (false,false) d0 (loadedValues 0 a) (by
      intro i
      exact hw i)
    have h := run_trans n h0 hc
    simpa only [mappingTime,mappedWires,rawArgs,afterClear,Context.index,
      show ¬(2 : Fin 4)=0 by decide,show ¬(1 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=0 by decide,
      show ¬(1 : Fin 4)=2 by decide,show ¬(3 : Fin 4)=2 by decide,
      ite_true,ite_false,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.reverse_append,List.append_assoc,d0] using h
  ·
    change (transition n)^[mappingTime n j 1 a m b]
      (some (cfg n (.compare (.body j 1 0)) v d)) =
      some (cfg n (.gate j) (false,false)
        {d with addresses := fun _ => [],body := (mappedWires 1 a m b n j.val).reverse++d.body})
    have h0 := mapped_address_run n (.body j 1 0) v d m b (a 0) hm hb
      (by simpa [loadedValues,arity,Context.address] using hw 0) hs ht hu
    have hn0 : afterMapped n (.body j 1 0) = .compare (.body j 1 1) := rfl
    rw [hn0] at h0
    let d0 : Data := {d with body := (encNat (Encoding.remapWire m b n j.val (a 0))).reverse++d.body}
    have h1 := mapped_address_run n (.body j 1 1) (false,false) d0 m b (a 1) hm hb
      (by simpa [loadedValues,arity,Context.address] using hw 1) hs ht hu
    have hn1 : afterMapped n (.body j 1 1) = .clearSources (.body j) 0 := rfl
    rw [hn1] at h1
    let d1 : Data := {d0 with body := (encNat (Encoding.remapWire m b n j.val (a 1))).reverse++d0.body}
    have hc := clear_sources_run n (.body j) (false,false) d1 (loadedValues 1 a) (by
      intro i
      exact hw i)
    have h := run_trans n (run_trans n h0 h1) hc
    simpa only [mappingTime,mappedWires,rawArgs,afterClear,Context.index,
      show ¬(2 : Fin 4)=0 by decide,show ¬(1 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=0 by decide,
      show ¬(1 : Fin 4)=2 by decide,show ¬(3 : Fin 4)=2 by decide,
      ite_true,ite_false,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.reverse_append,List.append_assoc,d0,d1] using h
  ·
    change (transition n)^[mappingTime n j 2 a m b]
      (some (cfg n (.compare (.body j 2 0)) v d)) =
      some (cfg n (.gate j) (false,false)
        {d with addresses := fun _ => [],body := (mappedWires 2 a m b n j.val).reverse++d.body})
    have h0 := mapped_address_run n (.body j 2 0) v d m b (a 0) hm hb
      (by simpa [loadedValues,arity,Context.address] using hw 0) hs ht hu
    have hn0 : afterMapped n (.body j 2 0) = .compare (.body j 2 1) := rfl
    rw [hn0] at h0
    let d0 : Data := {d with body := (encNat (Encoding.remapWire m b n j.val (a 0))).reverse++d.body}
    have h1 := mapped_address_run n (.body j 2 1) (false,false) d0 m b (a 1) hm hb
      (by simpa [loadedValues,arity,Context.address] using hw 1) hs ht hu
    have hn1 : afterMapped n (.body j 2 1) = .compare (.body j 2 2) := rfl
    rw [hn1] at h1
    let d1 : Data := {d0 with body := (encNat (Encoding.remapWire m b n j.val (a 1))).reverse++d0.body}
    have h2 := mapped_address_run n (.body j 2 2) (false,false) d1 m b (a 2) hm hb
      (by simpa [loadedValues,arity,Context.address] using hw 2) hs ht hu
    have hn2 : afterMapped n (.body j 2 2) = .clearSources (.body j) 0 := rfl
    rw [hn2] at h2
    let d2 : Data := {d1 with body := (encNat (Encoding.remapWire m b n j.val (a 2))).reverse++d1.body}
    have hc := clear_sources_run n (.body j) (false,false) d2 (loadedValues 2 a) (by
      intro i
      exact hw i)
    have h := run_trans n (run_trans n (run_trans n h0 h1) h2) hc
    simpa only [mappingTime,mappedWires,rawArgs,afterClear,Context.index,
      show ¬(2 : Fin 4)=0 by decide,show ¬(1 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=0 by decide,
      show ¬(1 : Fin 4)=2 by decide,show ¬(3 : Fin 4)=2 by decide,
      ite_true,ite_false,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.reverse_append,List.append_assoc,d0,d1,d2] using h
  ·
    change (transition n)^[mappingTime n j 3 a m b]
      (some (cfg n (.compare (.body j 3 0)) v d)) =
      some (cfg n (.gate j) (false,false)
        {d with addresses := fun _ => [],body := (mappedWires 3 a m b n j.val).reverse++d.body})
    have h0 := mapped_address_run n (.body j 3 0) v d m b (a 0) hm hb
      (by simpa [loadedValues,arity,Context.address] using hw 0) hs ht hu
    have hn0 : afterMapped n (.body j 3 0) = .compare (.body j 3 1) := rfl
    rw [hn0] at h0
    let d0 : Data := {d with body := (encNat (Encoding.remapWire m b n j.val (a 0))).reverse++d.body}
    have h1 := mapped_address_run n (.body j 3 1) (false,false) d0 m b (a 1) hm hb
      (by simpa [loadedValues,arity,Context.address] using hw 1) hs ht hu
    have hn1 : afterMapped n (.body j 3 1) = .clearSources (.body j) 0 := rfl
    rw [hn1] at h1
    let d1 : Data := {d0 with body := (encNat (Encoding.remapWire m b n j.val (a 1))).reverse++d0.body}
    have hc := clear_sources_run n (.body j) (false,false) d1 (loadedValues 3 a) (by
      intro i
      exact hw i)
    have h := run_trans n (run_trans n h0 h1) hc
    simpa only [mappingTime,mappedWires,rawArgs,afterClear,Context.index,
      show ¬(2 : Fin 4)=0 by decide,show ¬(1 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=0 by decide,
      show ¬(1 : Fin 4)=2 by decide,show ¬(3 : Fin 4)=2 by decide,
      ite_true,ite_false,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.reverse_append,List.append_assoc,d0,d1] using h



lemma tag_run (j : Fin (n+1)) (kind : Fin 4) (v : Bool × Bool) (d : Data) (tail : Str) :
    (transition n)^[kind.val+1]
      (some (cfg n (.tag j 0) v {d with input := encNat kind.val++tail})) =
      some (cfg n (.readAddress j kind 0) (true,false)
        {d with input := tail,body := (encNat kind.val).reverse++d.body}) := by
  fin_cases kind <;>
    simp [Function.iterate_succ_apply,Function.iterate_zero,transition,FinTM2.step,TM2.step,
      machine,cfg,Data.stacks,encNat,TM2.stepAux]
  all_goals funext k; fin_cases k <;> simp

lemma gate_start_step (j : Fin (n+1)) (v : Bool × Bool) (d : Data) (gs : Str) :
    (machine n).step (cfg n (.gate j) v {d with gatesLeft := true::gs}) =
      some (cfg n (.tag j 0) (true,v.2) {d with gatesLeft := gs,count := true::d.count}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k; fin_cases k <;> simp

lemma gate_end_step (j : Fin (n+1)) (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.gate j) v {d with gatesLeft := []}) =
      some (cfg n (if h : j.val+1<n then .skipHeader ⟨j.val+1,by omega⟩ 0 else .flagX)
        (false,false) {d with gatesLeft := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

def gateTime (j : Fin (n+1)) (kind : Fin 4) (a : Fin 3 → ℕ) (m b : ℕ) : ℕ :=
  1+(kind.val+1)+readTime kind a+mappingTime n j kind a m b

def instructionCode (kind : Fin 4) (a : Fin 3 → ℕ) : Str :=
  encNat kind.val++sourceWires kind a

def mappedCode (kind : Fin 4) (a : Fin 3 → ℕ) (m b n j : ℕ) : Str :=
  encNat kind.val++mappedWires kind a m b n j

lemma gate_run (j : Fin (n+1)) (kind : Fin 4) (v : Bool × Bool) (d : Data)
    (a : Fin 3 → ℕ) (m b : ℕ) (tail gs : Str)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (hd : d.addresses = fun _ => [])
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []) :
    (transition n)^[gateTime n j kind a m b]
      (some (cfg n (.gate j) v
        {d with input := instructionCode kind a++tail,gatesLeft := true::gs})) =
      some (cfg n (.gate j) (false,false)
        {d with input := tail,gatesLeft := gs,count := true::d.count, addresses := fun _ => [],body := (mappedCode kind a m b n j.val).reverse++d.body}) := by
  let d0 : Data := {d with input := instructionCode kind a++tail,gatesLeft := gs,count := true::d.count}
  have h0 := gate_start_step n j v {d with input := instructionCode kind a++tail} gs
  change (transition n)^[1]
    (some (cfg n (.gate j) v {d with input := instructionCode kind a++tail,gatesLeft := true::gs})) =
    some (cfg n (.tag j 0) (true,v.2) d0) at h0
  have h1 := tag_run n j kind (true,v.2) {d with gatesLeft := gs,count := true::d.count}
    (sourceWires kind a++tail)
  let d1 : Data := {d with input := sourceWires kind a++tail,gatesLeft := gs,count := true::d.count, body := (encNat kind.val).reverse++d.body}
  have h1' : (transition n)^[kind.val+1] (some (cfg n (.tag j 0) (true,v.2) d0)) =
      some (cfg n (.readAddress j kind 0) (true,false) d1) := by
    simpa only [d0,d1,instructionCode,List.append_assoc] using h1
  have h2 := read_sources_run n j kind (true,false)
    {d with gatesLeft := gs,count := true::d.count,body := (encNat kind.val).reverse++d.body} a tail hd
  let d2 : Data := {d with input := tail,gatesLeft := gs,count := true::d.count, body := (encNat kind.val).reverse++d.body,addresses := loadedAddresses kind a}
  change (transition n)^[readTime kind a] (some (cfg n (.readAddress j kind 0) (true,false) d1)) =
    some (cfg n (.compare (.body j kind 0)) (false,false) d2) at h2
  have h3 := map_sources_run n j kind (false,false) d2 a m b hm hb rfl hs ht hu
  have h := run_trans n (run_trans n (run_trans n h0 h1') h2) h3
  simpa only [gateTime,d2,mappedCode,List.reverse_append,List.append_assoc] using h



abbrev Recipe := Fin 4 × (Fin 3 → ℕ)

def sourceBody (rs : List Recipe) : Str := rs.flatMap (fun r => instructionCode r.1 r.2)
def copyBody (m b n j : ℕ) (rs : List Recipe) : Str := rs.flatMap (fun r => mappedCode r.1 r.2 m b n j)
def bodyTime (j : Fin (n+1)) (m b : ℕ) (rs : List Recipe) : ℕ :=
  (rs.map (fun r => gateTime n j r.1 r.2 m b)).sum

lemma body_run (j : Fin (n+1)) (rs : List Recipe) (v : Bool × Bool) (d : Data)
    (m b : ℕ) (tail : Str)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (hd : d.addresses = fun _ => [])
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []) :
    (transition n)^[bodyTime n j m b rs]
      (some (cfg n (.gate j) v
        {d with input := sourceBody rs++tail,gatesLeft := List.replicate rs.length true++d.gatesLeft})) =
      some (cfg n (.gate j) (if rs=[] then v else (false,false))
        {d with input := tail,count := List.replicate rs.length true++d.count, addresses := fun _ => [],body := (copyBody m b n j.val rs).reverse++d.body}) := by
  induction rs generalizing v d with
  | nil => simp only [bodyTime,List.map_nil,List.sum_nil,Function.iterate_zero,sourceBody,
      copyBody,List.flatMap_nil,List.length_nil,List.replicate_zero,List.nil_append,
      List.reverse_nil,ite_true,hd,id_eq]
  | cons r rs ih =>
    have h0 := gate_run n j r.1 v d r.2 m b (sourceBody rs++tail)
      (List.replicate rs.length true++d.gatesLeft) hm hb hd hs ht hu
    let d1 : Data := {d with count := true::d.count, body := (mappedCode r.1 r.2 m b n j.val).reverse++d.body}
    have h1 := ih (false,false) d1 hm hb hd hs ht hu
    simp only [hd] at h0
    simp only [d1,hd] at h1
    have h2 := run_trans n h0 h1
    have hc : List.replicate rs.length true++true::d.count =
        List.replicate (rs.length+1) true++d.count := by rw [List.replicate_add]; simp
    have hv : (if rs=[] then (false,false) else (false,false)) = (false,false) := by split <;> rfl
    simpa only [bodyTime,sourceBody,copyBody,List.flatMap_cons,List.map_cons,List.sum_cons,
      List.length_cons,List.replicate_succ,List.cons_append,List.append_assoc,
      List.cons_ne_nil,ite_false,List.reverse_append,d1,hc,hv,hd] using h2


lemma first0_true (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.firstHeader 0) v {d with input := true::tail}) =
      some (cfg n (.firstHeader 0) (true,true) {d with input := tail,bound := true::d.bound,header := List.replicate n true++d.header}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
  funext k; fin_cases k <;> simp

lemma first0_run (v : Bool × Bool) (d : Data) (w : ℕ) (tail : Str) :
    (transition n)^[w+1] (some (cfg n (.firstHeader 0) v {d with input := encNat w++tail})) =
      some (cfg n (.firstHeader 1) (true,false) {d with input := tail,bound := List.replicate w true++d.bound,header := List.replicate (n+1) true++false::(List.replicate (n*w) true++d.header)}) := by
  induction w generalizing v d with
  | zero =>
    simp [transition,Function.iterate_succ_apply,encNat,FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
    funext k; fin_cases k <;> simp
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1] ((machine n).step (cfg n (.firstHeader 0) v {d with input := true::(encNat w++tail)})) = _
    rw [first0_true]
    have hf : List.replicate w true++true::d.bound = List.replicate (w+1) true++d.bound := by
      rw [List.replicate_add]; simp
    have hh : List.replicate (n*w) true++(List.replicate n true++d.header) =
        List.replicate (n*(w+1)) true++d.header := by
      rw [unary_append,show n*w+n=n*(w+1) by ring]
    simpa only [hf,hh] using ih (true,true) {d with bound := true::d.bound,header := List.replicate n true++d.header}

lemma first1_true (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.firstHeader 1) v {d with input := true::tail}) =
      some (cfg n (.firstHeader 1) (true,true) {d with input := tail,ancilla := true::d.ancilla,header := List.replicate n true++d.header}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
  funext k; fin_cases k <;> simp

lemma first1_run (v : Bool × Bool) (d : Data) (w : ℕ) (tail : Str) :
    (transition n)^[w+1] (some (cfg n (.firstHeader 1) v {d with input := encNat w++tail})) =
      some (cfg n (.firstHeader 2) (true,false) {d with input := tail,ancilla := List.replicate w true++d.ancilla,header := false::(List.replicate (n*w) true++d.header)}) := by
  induction w generalizing v d with
  | zero =>
    simp [transition,Function.iterate_succ_apply,encNat,FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
    funext k; fin_cases k <;> simp
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1] ((machine n).step (cfg n (.firstHeader 1) v {d with input := true::(encNat w++tail)})) = _
    rw [first1_true]
    have hf : List.replicate w true++true::d.ancilla = List.replicate (w+1) true++d.ancilla := by
      rw [List.replicate_add]; simp
    have hh : List.replicate (n*w) true++(List.replicate n true++d.header) =
        List.replicate (n*(w+1)) true++d.header := by
      rw [unary_append,show n*w+n=n*(w+1) by ring]
    simpa only [hf,hh] using ih (true,true) {d with ancilla := true::d.ancilla,header := List.replicate n true++d.header}

lemma first2_true (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.firstHeader 2) v {d with input := true::tail}) =
      some (cfg n (.firstHeader 2) (true,true) {d with input := tail,oldOutput := true::d.oldOutput,header := d.header}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
  funext k; fin_cases k <;> simp

lemma first2_run (v : Bool × Bool) (d : Data) (w : ℕ) (tail : Str) :
    (transition n)^[w+1] (some (cfg n (.firstHeader 2) v {d with input := encNat w++tail})) =
      some (cfg n (.sum .headerOutput 0 0) (false,false) {d with input := tail,oldOutput := List.replicate w true++d.oldOutput,header := d.header}) := by
  induction w generalizing v d with
  | zero =>
    simp [transition,Function.iterate_succ_apply,encNat,FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
    funext k; fin_cases k <;> simp
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1] ((machine n).step (cfg n (.firstHeader 2) v {d with input := true::(encNat w++tail)})) = _
    rw [first2_true]
    have hf : List.replicate w true++true::d.oldOutput = List.replicate (w+1) true++d.oldOutput := by
      rw [List.replicate_add]; simp
    simpa only [hf] using ih (true,true) {d with oldOutput := true::d.oldOutput,header := d.header}


lemma finish_body_cons (v : Bool × Bool) (d : Data) (b : Bool) (s : Str) :
    (machine n).step (cfg n (.finish 0) v {d with body := b::s}) =
      some (cfg n (.finish 0) (true,b) {d with body := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_body_nil (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.finish 0) v {d with body := []}) =
      some (cfg n (.finish 1) (false,false) {d with body := [],output := false::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_count_cons (v : Bool × Bool) (d : Data) (b : Bool) (s : Str) :
    (machine n).step (cfg n (.finish 1) v {d with count := b::s}) =
      some (cfg n (.finish 1) (true,b) {d with count := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_count_nil (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.finish 1) v {d with count := []}) =
      some (cfg n (.finish 2) (false,false) {d with count := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma finish_header_cons (v : Bool × Bool) (d : Data) (b : Bool) (s : Str) :
    (machine n).step (cfg n (.finish 2) v {d with header := b::s}) =
      some (cfg n (.finish 2) (true,b) {d with header := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_header_nil (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.finish 2) v {d with header := []}) =
      some (⟨none,(false,false),({d with header := []} : Data).stacks⟩ : (machine n).Cfg) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma finish_body_run (v : Bool × Bool) (d : Data) (s : Str) :
    (fun o : Option (machine n).Cfg => o.bind (machine n).step)^[s.length+1]
      (some (cfg n (.finish 0) v {d with body := s})) =
      some (cfg n (.finish 1) (false,false) {d with body := [],output := false::(s.reverse++d.output)}) := by
  induction s generalizing v d with
  | nil => simpa using finish_body_nil n v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine n).Cfg => o.bind (machine n).step)^[s.length+1]
      ((machine n).step (cfg n (.finish 0) v {d with body := b::s})) = _
    rw [finish_body_cons n]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (true,b) {d with output := b::d.output}

lemma finish_count_run (v : Bool × Bool) (d : Data) (s : Str) :
    (fun o : Option (machine n).Cfg => o.bind (machine n).step)^[s.length+1]
      (some (cfg n (.finish 1) v {d with count := s})) =
      some (cfg n (.finish 2) (false,false) {d with count := [],output := s.reverse++d.output}) := by
  induction s generalizing v d with
  | nil => simpa using finish_count_nil n v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine n).Cfg => o.bind (machine n).step)^[s.length+1]
      ((machine n).step (cfg n (.finish 1) v {d with count := b::s})) = _
    rw [finish_count_cons n]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (true,b) {d with output := b::d.output}

lemma finish_header_run (v : Bool × Bool) (d : Data) (s : Str) :
    (fun o : Option (machine n).Cfg => o.bind (machine n).step)^[s.length+1]
      (some (cfg n (.finish 2) v {d with header := s})) =
      some (⟨none,(false,false),({d with header := [],output := s.reverse++d.output} : Data).stacks⟩ : (machine n).Cfg) := by
  induction s generalizing v d with
  | nil => simpa using finish_header_nil n v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine n).Cfg => o.bind (machine n).step)^[s.length+1]
      ((machine n).step (cfg n (.finish 2) v {d with header := b::s})) = _
    rw [finish_header_cons n]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (true,b) {d with output := b::d.output}
lemma finish_all_run (H B : Str) (N : ℕ) (v : Bool × Bool) :
    (fun q : Option (machine n).Cfg => q.bind (machine n).step)^[B.length+N+H.length+3]
      (some (cfg n (.finish 0) v {header := H.reverse,count := List.replicate N true,body := B.reverse})) =
      some (haltList (machine n) (H++encNat N++B)) := by
  rw [show B.length+N+H.length+3 = (H.reverse.length+1)+
      (((List.replicate N true).length+1)+(B.reverse.length+1)) by simp; omega,
    Function.iterate_add_apply _ (H.reverse.length+1) _,
    Function.iterate_add_apply _ ((List.replicate N true).length+1) _]
  rw [finish_body_run n v {header := H.reverse,count := List.replicate N true} B.reverse]
  simp only [List.reverse_reverse,List.append_nil]
  rw [finish_count_run n (false,false) {header := H.reverse,output := false::B} (List.replicate N true)]
  simp only [List.reverse_replicate]
  rw [finish_header_run n (false,false) {output := List.replicate N true++false::B} H.reverse]
  simp only [List.reverse_reverse,encNat,List.append_assoc,List.singleton_append]
  simp only [haltList,machine]
  congr 2
  funext k
  fin_cases k <;> rfl



def afterSkip (j : Fin (n+1)) (field : Fin 3) : Label n :=
  if h : field.val<2 then .skipHeader j ⟨field.val+1,by omega⟩ else .readCount j

lemma skip_true_step (j : Fin (n+1)) (field : Fin 3) (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.skipHeader j field) v {d with input := true::tail}) =
      some (cfg n (.skipHeader j field) (true,true) {d with input := tail}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k; fin_cases k <;> simp

lemma skip_false_step (j : Fin (n+1)) (field : Fin 3) (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.skipHeader j field) v {d with input := false::tail}) =
      some (cfg n (afterSkip n j field) (true,false) {d with input := tail}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,afterSkip]
  funext k; fin_cases k <;> simp

lemma skip_run (j : Fin (n+1)) (field : Fin 3) (v : Bool × Bool) (d : Data) (w : ℕ) (tail : Str) :
    (transition n)^[w+1]
      (some (cfg n (.skipHeader j field) v {d with input := encNat w++tail})) =
      some (cfg n (afterSkip n j field) (true,false) {d with input := tail}) := by
  induction w generalizing v d with
  | zero => simpa [encNat] using skip_false_step n j field v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1]
      ((machine n).step (cfg n (.skipHeader j field) v {d with input := true::(encNat w++tail)})) = _
    rw [skip_true_step]
    exact ih (true,true) d

lemma skip_all_run (j : Fin (n+1)) (v : Bool × Bool) (d : Data) (m b o : ℕ) (tail : Str) :
    (transition n)^[m+b+o+3]
      (some (cfg n (.skipHeader j 0) v {d with input := encNat m++encNat b++encNat o++tail})) =
      some (cfg n (.readCount j) (true,false) {d with input := tail}) := by
  have h0 := skip_run n j 0 v d m (encNat b++encNat o++tail)
  have h1 := skip_run n j 1 (true,false) d b (encNat o++tail)
  have h2 := skip_run n j 2 (true,false) d o tail
  have hs0 : afterSkip n j 0 = .skipHeader j 1 := rfl
  have hs1 : afterSkip n j 1 = .skipHeader j 2 := rfl
  have hs2 : afterSkip n j 2 = .readCount j := rfl
  simp only [hs0,hs1,hs2,List.append_assoc] at h0 h1 h2
  have h := run_trans n (run_trans n h0 h1) h2
  simpa only [List.append_assoc,show m+b+o+3=(m+1)+(b+1)+(o+1) by omega] using h

lemma count_true_step (j : Fin (n+1)) (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.readCount j) v {d with input := true::tail}) =
      some (cfg n (.readCount j) (true,true) {d with input := tail,gatesLeft := true::d.gatesLeft}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k; fin_cases k <;> simp

lemma count_false_step (j : Fin (n+1)) (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.readCount j) v {d with input := false::tail}) =
      some (cfg n (.gate j) (true,false) {d with input := tail}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k; fin_cases k <;> simp

lemma count_run (j : Fin (n+1)) (v : Bool × Bool) (d : Data) (w : ℕ) (tail : Str) :
    (transition n)^[w+1]
      (some (cfg n (.readCount j) v {d with input := encNat w++tail})) =
      some (cfg n (.gate j) (true,false)
        {d with input := tail,gatesLeft := List.replicate w true++d.gatesLeft}) := by
  induction w generalizing v d with
  | zero => simpa [encNat] using count_false_step n j v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1]
      ((machine n).step (cfg n (.readCount j) v {d with input := true::(encNat w++tail)})) = _
    rw [count_true_step]
    have hr : List.replicate w true++true::d.gatesLeft =
        List.replicate (w+1) true++d.gatesLeft := by rw [List.replicate_add]; simp
    simpa only [hr] using ih (true,true) {d with gatesLeft := true::d.gatesLeft}



def sourceHeader (m b o : ℕ) : Str := encNat m++encNat b++encNat o

def sourceCode (m b o : ℕ) (rs : List Recipe) : Str :=
  sourceHeader m b o++encNat rs.length++sourceBody rs

def targetHeader (m b n : ℕ) : Str :=
  encNat (n*m)++encNat (n*b+(n+1))++encNat (n*m+n*b+n)

def headerTime (m b o : ℕ) : ℕ := (m+1)+(b+1)+(o+1)+sumTime n .headerOutput ![m,b,b]

lemma encNat_reverse (k : ℕ) : (encNat k).reverse = false::List.replicate k true := by
  simp [encNat]

lemma header_all_run (m b o : ℕ) (tail : Str) :
    (transition n)^[headerTime n m b o]
      (some (cfg n (.firstHeader 0) (false,false) {input := sourceHeader m b o++tail})) =
      some (cfg n (.readCount 0) (false,false)
        {input := tail,bound := List.replicate m true,ancilla := List.replicate b true, oldOutput := List.replicate o true,header := (targetHeader m b n).reverse}) := by
  have h0 := first0_run n (false,false) ({} : Data) m (encNat b++encNat o++tail)
  let d0 : Data := {bound := List.replicate m true, header := List.replicate (n+1) true++false::List.replicate (n*m) true}
  have h1 := first1_run n (true,false) d0 b (encNat o++tail)
  let d1 : Data := {bound := List.replicate m true,ancilla := List.replicate b true, header := false::(List.replicate (n*b) true++d0.header)}
  have h2 := first2_run n (true,false) d1 o tail
  let d2 : Data := {input := tail,bound := List.replicate m true,ancilla := List.replicate b true, oldOutput := List.replicate o true,header := d1.header}
  have hp : ∀ part, d2.source ((SumTask.headerOutput : SumTask n).source part) =
      List.replicate (![m,b,b] part) true := by
    intro part; fin_cases part <;> rfl
  have h3 := sum_run n .headerOutput (false,false) d2 ![m,b,b] hp rfl
  have he : sumWord n .headerOutput ![m,b,b] = encNat (n*m+n*b+n) := by
    simp [sumWord,sumSize,SumTask.copies,SumTask.literal,SumTask.delimiter]
  rw [he] at h3
  simp only [d0,d1,List.append_nil,List.nil_append,List.append_assoc] at h0 h1 h2
  have h := run_trans n (run_trans n (run_trans n h0 h1) h2) h3
  have hh : (encNat (n*m+n*b+n)).reverse++d2.header = (targetHeader m b n).reverse := by
    simp only [targetHeader,d2,d1,d0,List.reverse_append,encNat_reverse,
      List.append_assoc,List.cons_append]
    rw [List.replicate_add (n*b) (n+1)]
    simp only [List.append_assoc]
  simpa only [headerTime,sourceHeader,d2,sumReturn,Data.setDest,SumTask.dest,Data.dest,hh,
    List.append_assoc] using h

def nextPacket (j : Fin (n+1)) : Label n :=
  if h : j.val+1<n then .skipHeader ⟨j.val+1,by omega⟩ 0 else .flagX

def packetTime (j : Fin (n+1)) (m b : ℕ) (rs : List Recipe) : ℕ :=
  (rs.length+1)+bodyTime n j m b rs+1

lemma packet_run (j : Fin (n+1)) (v : Bool × Bool) (d : Data)
    (m b : ℕ) (rs : List Recipe) (tail : Str)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (hg : d.gatesLeft = []) (hd : d.addresses = fun _ => [])
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []) :
    (transition n)^[packetTime n j m b rs]
      (some (cfg n (.readCount j) v {d with input := encNat rs.length++sourceBody rs++tail})) =
      some (cfg n (nextPacket n j) (false,false)
        {d with input := tail,gatesLeft := [],count := List.replicate rs.length true++d.count, addresses := fun _ => [],body := (copyBody m b n j.val rs).reverse++d.body}) := by
  have h0 := count_run n j v d rs.length (sourceBody rs++tail)
  have h1 := body_run n j rs (true,false) d m b tail hm hb hd hs ht hu
  let de : Data := {d with input := tail,count := List.replicate rs.length true++d.count, addresses := fun _ => [],body := (copyBody m b n j.val rs).reverse++d.body}
  have h2 := gate_end_step n j (if rs=[] then (true,false) else (false,false)) de
  change (transition n)^[1] (some (cfg n (.gate j)
    (if rs=[] then (true,false) else (false,false)) {de with gatesLeft := []})) = _ at h2
  simp only [hg] at h0 h1
  have h := run_trans n (run_trans n h0 h1) h2
  simpa only [packetTime,de,nextPacket,List.append_assoc,hg] using h

lemma skipped_packet_run (j : Fin (n+1)) (v : Bool × Bool) (d : Data)
    (m b o : ℕ) (rs : List Recipe) (tail : Str)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (hg : d.gatesLeft = []) (hd : d.addresses = fun _ => [])
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []) :
    (transition n)^[(m+b+o+3)+packetTime n j m b rs]
      (some (cfg n (.skipHeader j 0) v {d with input := sourceCode m b o rs++tail})) =
      some (cfg n (nextPacket n j) (false,false)
        {d with input := tail,gatesLeft := [],count := List.replicate rs.length true++d.count, addresses := fun _ => [],body := (copyBody m b n j.val rs).reverse++d.body}) := by
  have h0 := skip_all_run n j v d m b o (encNat rs.length++sourceBody rs++tail)
  have h1 := packet_run n j (true,false) d m b rs tail hm hb hg hd hs ht hu
  simpa only [sourceCode,sourceHeader,List.append_assoc] using run_trans n h0 h1



lemma static_parts (d : Data) (task : SumTask n) (m b o : ℕ)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (ho : d.oldOutput = List.replicate o true)
    (h : ∀ ctx proof, task ≠ .address ctx proof) :
    ∀ part, d.source (task.source part) =
      List.replicate ((if ∃ j, task = .loadOutput j then ![o,b,b] else ![m,b,b]) part) true := by
  intro part
  cases task <;> fin_cases part <;>
    simp_all [SumTask.source,Data.source]

lemma flag_start_step (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n .flagX v d) =
      some (cfg n (.sum .flagX 0 0) (false,false)
        {d with count := true::d.count,body := false::d.body}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k; fin_cases k <;> simp

lemma and_start_step (j : Fin (n+1)) (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.andFirst j) v d) =
      some (cfg n (.sum (.andFirst j) 0 0) (false,false)
        {d with count := true::d.count,body := (encNat 2).reverse++d.body}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
  funext k; fin_cases k <;> simp

def andCode (m b n j o : ℕ) : Str :=
  encNat 2++encNat (n*m+n*b+j)++encNat (Encoding.remapWire m b n j o)++encNat (n*m+n*b+(j+1))

def andTime (j : Fin (n+1)) (m b o : ℕ) : ℕ :=
  1+sumTime n (.andFirst j) ![m,b,b]+sumTime n (.loadOutput j) ![o,b,b]+
    addressTime n (.output j) m b o+(o+3)+sumTime n (.andLast j) ![m,b,b]

lemma and_run (j : Fin (n+1)) (v : Bool × Bool) (d : Data) (m b o : ℕ)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (ho : d.oldOutput = List.replicate o true) (hd : d.addresses = fun _ => [])
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []) :
    (transition n)^[andTime n j m b o] (some (cfg n (.andFirst j) v d)) =
      some (cfg n (sumReturn n (.andLast j)) (false,false)
        {d with count := true::d.count,addresses := fun _ => [], body := (andCode m b n j.val o).reverse++d.body}) := by
  let d0 : Data := {d with count := true::d.count,body := (encNat 2).reverse++d.body}
  have h0 := and_start_step n j v d
  change (transition n)^[1] (some (cfg n (.andFirst j) v d)) =
    some (cfg n (.sum (.andFirst j) 0 0) (false,false) d0) at h0
  have hp (task : SumTask n) (h : ∀ ctx proof, task ≠ .address ctx proof) :=
    static_parts n d task m b o hm hb ho h
  have h1 := sum_run n (.andFirst j) (false,false) d0 ![m,b,b]
    (by intro part; fin_cases part <;> simp [d0,SumTask.source,Data.source,hm,hb,ho]) hu
  have hf : sumWord n (.andFirst j) ![m,b,b] = encNat (n*m+n*b+j.val) := by
    simp [sumWord,sumSize,SumTask.copies,SumTask.literal,SumTask.delimiter]
  rw [hf] at h1
  let d1 : Data := {d0 with body := (encNat (n*m+n*b+j.val)).reverse++d0.body}
  change (transition n)^[sumTime n (.andFirst j) ![m,b,b]]
    (some (cfg n (.sum (.andFirst j) 0 0) (false,false) d0)) =
    some (cfg n (.sum (.loadOutput j) 0 0) (false,false) d1) at h1
  have h2 := sum_run n (.loadOutput j) (false,false) d1 ![o,b,b]
    (by intro part; fin_cases part <;> simp [d1,d0,SumTask.source,Data.source,hm,hb,ho]) hu
  have hl : sumWord n (.loadOutput j) ![o,b,b] = List.replicate o true := by
    simp [sumWord,sumSize,SumTask.copies,SumTask.literal,SumTask.delimiter]
  rw [hl] at h2
  let d2 : Data := {d1 with addresses := Function.update d.addresses 0 (List.replicate o true)}
  have h2' : (transition n)^[sumTime n (.loadOutput j) ![o,b,b]]
      (some (cfg n (.sum (.loadOutput j) 0 0) (false,false) d1)) =
      some (cfg n (.compare (.output j)) (false,false) d2) := by
    simpa only [sumReturn,SumTask.dest,Data.setDest,Data.dest,d2,d1,d0,hd,
      List.reverse_replicate,List.append_nil] using h2
  have h3 := mapped_address_run n (.output j) (false,false) d2 m b o hm hb
    (by simp [d2,Context.address]) hs ht hu
  let d3 : Data := {d2 with body := (encNat (Encoding.remapWire m b n j.val o)).reverse++d2.body}
  have h3' : (transition n)^[addressTime n (.output j) m b o]
      (some (cfg n (.compare (.output j)) (false,false) d2)) =
      some (cfg n (.clearSources (.output j) 0) (false,false) d3) := h3
  have h4 := clear_sources_run n (.output j) (false,false) d3 ![o,0,0] (by
    intro part; fin_cases part <;> simp [d3,d2,d1,d0,hd])
  change (transition n)^[o+3] (some (cfg n (.clearSources (.output j) 0) (false,false) d3)) = _ at h4
  let d4 : Data := {d3 with addresses := fun _ => []}
  have h5 := sum_run n (.andLast j) (false,false) d4 ![m,b,b]
    (by intro part; fin_cases part <;> simp [d4,d3,d2,d1,d0,SumTask.source,Data.source,hm,hb,ho]) hu
  have hh : sumWord n (.andLast j) ![m,b,b] = encNat (n*m+n*b+(j.val+1)) := by
    simp [sumWord,sumSize,SumTask.copies,SumTask.literal,SumTask.delimiter]
  rw [hh] at h5
  have h := run_trans n (run_trans n (run_trans n (run_trans n (run_trans n h0 h1) h2') h3') h4) h5
  simpa only [andTime,andCode,d4,d3,d2,d1,d0,afterClear,Data.setDest,Data.dest,
    SumTask.dest,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Nat.add_zero,
    Context.index,List.reverse_append,List.append_assoc] using h



def copiesLabel (j r : ℕ) : Label n :=
  if r=0 then .flagX else .skipHeader (Fin.ofNat (n+1) j) 0

def copiesBody (m b n : ℕ) (rs : List Recipe) : ℕ → ℕ → Str
  | _,0 => []
  | j,r+1 => copyBody m b n j rs++copiesBody m b n rs (j+1) r

def copiesTime (m b o : ℕ) (rs : List Recipe) : ℕ → ℕ → ℕ
  | _,0 => 0
  | j,r+1 => ((m+b+o+3)+packetTime n (Fin.ofNat (n+1) j) m b rs)+copiesTime m b o rs (j+1) r

lemma copies_run (rs : List Recipe) (r : ℕ) : ∀ (j : ℕ) (hjn : j+r=n)
    (v : Bool × Bool) (d : Data) (m b o : ℕ) (tail : Str)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (hg : d.gatesLeft = []) (hd : d.addresses = fun _ => [])
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []),
    (transition n)^[copiesTime n m b o rs j r]
      (some (cfg n (copiesLabel n j r) v
        {d with input := (List.replicate r (sourceCode m b o rs)).flatten++tail})) =
      some (cfg n .flagX (if r=0 then v else (false,false))
        {d with input := tail,gatesLeft := [],count := List.replicate (r*rs.length) true++d.count, addresses := fun _ => [],body := (copiesBody m b n rs j r).reverse++d.body}) := by
  induction r with
  | zero =>
    intro j hjn v d m b o tail hm hb hg hd hs ht hu
    simp only [copiesTime,copiesLabel,ite_true,List.replicate_zero,List.flatten_nil,
      List.nil_append,Nat.zero_mul,copiesBody,List.reverse_nil,Function.iterate_zero,id_eq,hg,hd]
  | succ r ih =>
    intro j hjn v d m b o tail hm hb hg hd hs ht hu
    have hj : j<n+1 := by omega
    have hv : (Fin.ofNat (n+1) j).val=j := by rw [Fin.val_ofNat,Nat.mod_eq_of_lt hj]
    let rest := (List.replicate r (sourceCode m b o rs)).flatten++tail
    have h0 := skipped_packet_run n (Fin.ofNat (n+1) j) v d m b o rs rest hm hb hg hd hs ht hu
    have hn : nextPacket n (Fin.ofNat (n+1) j) = copiesLabel n (j+1) r := by
      by_cases hr : r=0
      · have hnot : ¬(Fin.ofNat (n+1) j).val+1<n := by rw [hv]; omega
        simp only [nextPacket,copiesLabel,if_pos hr,dif_neg hnot]
      · have hlt : (Fin.ofNat (n+1) j).val+1<n := by rw [hv]; omega
        simp only [nextPacket,copiesLabel,if_neg hr,dif_pos hlt]
        congr 2
        simp only [hv,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : j+1<n+1)]
    rw [hn] at h0
    let d1 : Data := {d with gatesLeft := [],count := List.replicate rs.length true++d.count, addresses := fun _ => [],body := (copyBody m b n j rs).reverse++d.body}
    have h1 := ih (j+1) (by omega) (false,false) d1 m b o tail hm hb rfl rfl hs ht hu
    have h0' : (transition n)^[(m+b+o+3)+packetTime n (Fin.ofNat (n+1) j) m b rs]
        (some (cfg n (.skipHeader (Fin.ofNat (n+1) j) 0) v
          {d with input := sourceCode m b o rs++rest})) =
        some (cfg n (copiesLabel n (j+1) r) (false,false) {d1 with input := rest}) := by
      simpa only [hv,d1] using h0
    have h := run_trans n h0' h1
    have hc : List.replicate (r*rs.length) true++(List.replicate rs.length true++d.count) =
        List.replicate ((r+1)*rs.length) true++d.count := by
      rw [unary_append,show r*rs.length+rs.length=(r+1)*rs.length by ring]
    have hi : (if r=0 then (false,false) else (false,false)) = (false,false) := by split <;> rfl
    simpa only [copiesTime,copiesLabel,Nat.succ_ne_zero,ite_false,List.replicate_succ,
      List.flatten_cons,List.append_assoc,rest,d1,copiesBody,List.reverse_append,hc,hi] using h

def andLabel (j r : ℕ) : Label n :=
  if r=0 then .cleanup 0 else .andFirst (Fin.ofNat (n+1) j)

def andBody (m b n o : ℕ) : ℕ → ℕ → Str
  | _,0 => []
  | j,r+1 => andCode m b n j o++andBody m b n o (j+1) r

def andSeriesTime (m b o : ℕ) : ℕ → ℕ → ℕ
  | _,0 => 0
  | j,r+1 => andTime n (Fin.ofNat (n+1) j) m b o+andSeriesTime m b o (j+1) r

lemma and_series_run (r : ℕ) : ∀ (j : ℕ) (hjn : j+r=n)
    (v : Bool × Bool) (d : Data) (m b o : ℕ)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (ho : d.oldOutput = List.replicate o true) (hd : d.addresses = fun _ => [])
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []),
    (transition n)^[andSeriesTime n m b o j r]
      (some (cfg n (andLabel n j r) v d)) =
      some (cfg n (.cleanup 0) (if r=0 then v else (false,false))
        {d with count := List.replicate r true++d.count,addresses := fun _ => [], body := (andBody m b n o j r).reverse++d.body}) := by
  induction r with
  | zero =>
    intro j hjn v d m b o hm hb ho hd hs ht hu
    simp only [andSeriesTime,andLabel,ite_true,List.replicate_zero,List.nil_append,
      andBody,List.reverse_nil,Function.iterate_zero,id_eq,hd]
    rw [← hd]
  | succ r ih =>
    intro j hjn v d m b o hm hb ho hd hs ht hu
    have hj : j<n+1 := by omega
    have hv : (Fin.ofNat (n+1) j).val=j := by rw [Fin.val_ofNat,Nat.mod_eq_of_lt hj]
    have h0 := and_run n (Fin.ofNat (n+1) j) v d m b o hm hb ho hd hs ht hu
    have hn : sumReturn n (.andLast (Fin.ofNat (n+1) j)) = andLabel n (j+1) r := by
      by_cases hr : r=0
      · have hnot : ¬(Fin.ofNat (n+1) j).val+1<n := by rw [hv]; omega
        simp only [sumReturn,andLabel,if_pos hr,dif_neg hnot]
      · have hlt : (Fin.ofNat (n+1) j).val+1<n := by rw [hv]; omega
        simp only [sumReturn,andLabel,if_neg hr,dif_pos hlt]
        congr 2
        simp only [hv,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : j+1<n+1)]
    rw [hn] at h0
    let d1 : Data := {d with count := true::d.count,addresses := fun _ => [], body := (andCode m b n j o).reverse++d.body}
    have h1 := ih (j+1) (by omega) (false,false) d1 m b o hm hb ho rfl hs ht hu
    have h0' : (transition n)^[andTime n (Fin.ofNat (n+1) j) m b o]
        (some (cfg n (.andFirst (Fin.ofNat (n+1) j)) v d)) =
        some (cfg n (andLabel n (j+1) r) (false,false) d1) := by
      simpa only [hv,d1] using h0
    have h := run_trans n h0' h1
    have hc : List.replicate r true++true::d.count = List.replicate (r+1) true++d.count := by
      rw [List.replicate_add]; simp
    have hi : (if r=0 then (false,false) else (false,false)) = (false,false) := by split <;> rfl
    simpa only [andSeriesTime,andLabel,Nat.succ_ne_zero,ite_false,d1,andBody,
      List.reverse_append,List.append_assoc,hc,hi] using h





def setCleanup (d : Data) (j : Fin 4) (xs : Str) : Data :=
  if j=0 then {d with bound := xs} else if j=1 then {d with ancilla := xs} else
    if j=2 then {d with oldOutput := xs} else {d with gatesLeft := xs}

def afterCleanup (j : Fin 4) : Label n :=
  if h : j.val<3 then .cleanup ⟨j.val+1,by omega⟩ else .finish 0

lemma cleanup_true_step (j : Fin 4) (v : Bool × Bool) (d : Data) (tail : Str) :
    (machine n).step (cfg n (.cleanup j) v (setCleanup d j (true::tail))) =
      some (cfg n (.cleanup j) (true,v.2) (setCleanup d j tail)) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,setCleanup]
  all_goals funext k; fin_cases k <;> simp

lemma cleanup_nil_step (j : Fin 4) (v : Bool × Bool) (d : Data) :
    (machine n).step (cfg n (.cleanup j) v (setCleanup d j [])) =
      some (cfg n (afterCleanup n j) (false,false) (setCleanup d j [])) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,setCleanup,afterCleanup]

lemma cleanup_run (j : Fin 4) (v : Bool × Bool) (d : Data) (w : ℕ) :
    (transition n)^[w+1] (some (cfg n (.cleanup j) v (setCleanup d j (List.replicate w true)))) =
      some (cfg n (afterCleanup n j) (false,false) (setCleanup d j [])) := by
  induction w generalizing v with
  | zero => exact cleanup_nil_step n j v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (transition n)^[w+1] ((machine n).step
      (cfg n (.cleanup j) v (setCleanup d j (true::List.replicate w true)))) = _
    rw [cleanup_true_step,ih]

lemma cleanup_all_run (v : Bool × Bool) (d : Data) (m b o : ℕ)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (ho : d.oldOutput = List.replicate o true) (hg : d.gatesLeft = []) :
    (transition n)^[m+b+o+4] (some (cfg n (.cleanup 0) v d)) =
      some (cfg n (.finish 0) (false,false)
        {d with bound := [],ancilla := [],oldOutput := [],gatesLeft := []}) := by
  have h0 := cleanup_run n 0 v d m
  have h1 := cleanup_run n 1 (false,false) {d with bound := []} b
  have h2 := cleanup_run n 2 (false,false) {d with bound := [],ancilla := []} o
  have h3 := cleanup_run n 3 (false,false) {d with bound := [],ancilla := [],oldOutput := []} 0
  have hn0 : afterCleanup n 0 = .cleanup 1 := rfl
  have hn1 : afterCleanup n 1 = .cleanup 2 := rfl
  have hn2 : afterCleanup n 2 = .cleanup 3 := rfl
  have hn3 : afterCleanup n 3 = .finish 0 := rfl
  simp only [hn0,hn1,hn2,hn3,setCleanup,ite_true,
    show ¬(1 : Fin 4)=0 by decide,show ¬(2 : Fin 4)=0 by decide,show ¬(2 : Fin 4)=1 by decide,
    show ¬(3 : Fin 4)=0 by decide,show ¬(3 : Fin 4)=1 by decide,show ¬(3 : Fin 4)=2 by decide,
    ite_false,List.replicate_zero,← hm,← hb,← ho] at h0 h1 h2 h3
  have h0' : (transition n)^[m+1] (some (cfg n (.cleanup 0) v d)) =
      some (cfg n (.cleanup 1) (false,false) {d with bound := []}) := by simpa using h0
  have h3' : (transition n)^[1] (some (cfg n (.cleanup 3) (false,false)
      {d with bound := [],ancilla := [],oldOutput := []})) =
      some (cfg n (.finish 0) (false,false)
        {d with bound := [],ancilla := [],oldOutput := [],gatesLeft := []}) := by simpa only [hg] using h3
  have h := run_trans n (run_trans n (run_trans n h0' h1) h2) h3'
  simpa only [show m+b+o+4=(m+1)+(b+1)+(o+1)+1 by omega] using h

def flagCode (m b n : ℕ) : Str := encNat 0++encNat (n*m+n*b)
def finalBody (m b n o : ℕ) (rs : List Recipe) : Str :=
  copiesBody m b n rs 0 n++flagCode m b n++andBody m b n o 0 n

def suffixTime (m b o : ℕ) : ℕ :=
  1+sumTime n .flagX ![m,b,b]+andSeriesTime n m b o 0 n

lemma suffix_run (hn : 0<n) (v : Bool × Bool) (d : Data) (m b o : ℕ)
    (hm : d.bound = List.replicate m true) (hb : d.ancilla = List.replicate b true)
    (ho : d.oldOutput = List.replicate o true) (hd : d.addresses = fun _ => [])
    (hs : d.savedBound = []) (ht : d.savedAddress = []) (hu : d.temp = []) :
    (transition n)^[suffixTime n m b o] (some (cfg n .flagX v d)) =
      some (cfg n (.cleanup 0) (false,false)
        {d with count := List.replicate (n+1) true++d.count,addresses := fun _ => [], body := (flagCode m b n++andBody m b n o 0 n).reverse++d.body}) := by
  have h0 := flag_start_step n v d
  change (transition n)^[1] (some (cfg n .flagX v d)) = _ at h0
  let d0 : Data := {d with count := true::d.count,body := false::d.body}
  have h1 := sum_run n .flagX (false,false) d0 ![m,b,b]
    (by intro part; fin_cases part <;> simp [d0,SumTask.source,Data.source,hm,hb]) hu
  have hw : sumWord n .flagX ![m,b,b] = encNat (n*m+n*b) := by
    simp [sumWord,sumSize,SumTask.copies,SumTask.literal,SumTask.delimiter]
  rw [hw] at h1
  let d1 : Data := {d0 with body := (encNat (n*m+n*b)).reverse++d0.body}
  change (transition n)^[sumTime n .flagX ![m,b,b]]
    (some (cfg n (.sum .flagX 0 0) (false,false) d0)) =
      some (cfg n (.andFirst 0) (false,false) d1) at h1
  have h2 := and_series_run n n 0 (by omega) (false,false) d1 m b o hm hb ho hd hs ht hu
  have hl : andLabel n 0 n = .andFirst 0 := by simp [andLabel,Nat.ne_of_gt hn]
  rw [hl] at h2
  have h := run_trans n (run_trans n h0 h1) h2
  have hc : List.replicate n true++true::d.count = List.replicate (n+1) true++d.count := by
    rw [List.replicate_add]; simp
  simp only [if_neg (Nat.ne_of_gt hn)] at h
  have he : {d1 with count := List.replicate n true++d1.count,addresses := fun _ => [], body := (andBody m b n o 0 n).reverse++d1.body} =
      {d with count := List.replicate (n+1) true++d.count,addresses := fun _ => [], body := (flagCode m b n++andBody m b n o 0 n).reverse++d.body} := by
    dsimp only [d1,d0]
    rw [hc]
    simp only [flagCode,List.reverse_append,show (encNat 0).reverse=[false] from rfl,
      List.append_assoc,List.singleton_append]
  change (transition n)^[suffixTime n m b o] (some (cfg n .flagX v d)) =
    some (cfg n (.cleanup 0) (false,false)
      {d1 with count := List.replicate n true++d1.count,addresses := fun _ => [], body := (andBody m b n o 0 n).reverse++d1.body}) at h
  rw [he] at h
  exact h



def targetCount (n : ℕ) (rs : List Recipe) : ℕ := n*rs.length+n+1

def targetCode (m b n o : ℕ) (rs : List Recipe) : Str :=
  targetHeader m b n++encNat (targetCount n rs)++finalBody m b n o rs

def fullTime (m b o : ℕ) (rs : List Recipe) : ℕ :=
  headerTime n m b o+packetTime n 0 m b rs+copiesTime n m b o rs 1 (n-1)+
    suffixTime n m b o+(m+b+o+4)+
      ((finalBody m b n o rs).length+targetCount n rs+(targetHeader m b n).length+3)

lemma full_run (hn : 0<n) (m b o : ℕ) (rs : List Recipe) :
    (transition n)^[fullTime n m b o rs]
      (some (initList (machine n) (List.replicate n (sourceCode m b o rs)).flatten)) =
      some (haltList (machine n) (targetCode m b n o rs)) := by
  let rest := (List.replicate (n-1) (sourceCode m b o rs)).flatten
  let H := targetHeader m b n
  let B := finalBody m b n o rs
  let N := targetCount n rs
  let dh : Data := {header := H.reverse,bound := List.replicate m true, ancilla := List.replicate b true,oldOutput := List.replicate o true}
  have h0 := header_all_run n m b o (encNat rs.length++sourceBody rs++rest)
  have h1 := packet_run n 0 (false,false) dh m b rs rest rfl rfl rfl rfl rfl rfl rfl
  let dc : Data := {dh with count := List.replicate rs.length true, body := (copyBody m b n 0 rs).reverse}
  have hl : nextPacket n 0 = copiesLabel n 1 (n-1) := by
    by_cases he : n-1=0
    · have hlt : ¬(0 : Fin (n+1)).val+1<n := by simp only [Fin.val_zero]; omega
      simp only [nextPacket,copiesLabel,if_pos he,dif_neg hlt]
    · have hlt : (0 : Fin (n+1)).val+1<n := by simp only [Fin.val_zero]; omega
      simp only [nextPacket,copiesLabel,if_neg he,dif_pos hlt]
      congr 2
      simp only [Fin.val_zero,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<n+1)]
  rw [hl] at h1
  have h2 := copies_run n rs (n-1) 1 (by omega) (false,false) dc m b o [] rfl rfl rfl rfl rfl rfl rfl
  have h2v : (if n-1=0 then (false,false) else (false,false))=(false,false) := by split <;> rfl
  simp only [h2v,List.append_nil] at h2
  have hc : List.replicate ((n-1)*rs.length) true++List.replicate rs.length true =
      List.replicate (n*rs.length) true := by
    rw [← List.replicate_add,show (n-1)*rs.length+rs.length=n*rs.length by
      have he : n=(n-1)+1 := by omega
      conv_rhs => rw [he]
      ring]
  have hb : copyBody m b n 0 rs++copiesBody m b n rs 1 (n-1) = copiesBody m b n rs 0 n := by
    have he : n=(n-1)+1 := by omega
    simpa only [copiesBody,Nat.zero_add] using (congrArg (copiesBody m b n rs 0) he).symm
  let da : Data := {dh with count := List.replicate (n*rs.length) true, body := (copiesBody m b n rs 0 n).reverse}
  have h2' : (transition n)^[copiesTime n m b o rs 1 (n-1)]
      (some (cfg n (copiesLabel n 1 (n-1)) (false,false) {dc with input := rest})) =
      some (cfg n .flagX (false,false) da) := by
    simpa only [dc,da,dh,rest,List.append_nil,hc,← List.reverse_append,hb] using h2
  have h3 := suffix_run n hn (false,false) da m b o rfl rfl rfl rfl rfl rfl rfl
  have hnc : List.replicate (n+1) true++List.replicate (n*rs.length) true = List.replicate N true := by
    rw [← List.replicate_add]
    congr 1
    dsimp only [N,targetCount]
    omega
  let ds : Data := {dh with count := List.replicate N true,body := B.reverse}
  have h3' : (transition n)^[suffixTime n m b o] (some (cfg n .flagX (false,false) da)) =
      some (cfg n (.cleanup 0) (false,false) ds) := by
    simpa only [da,ds,B,finalBody,List.append_nil,← List.reverse_append,List.append_assoc,hnc] using h3
  have h4 := cleanup_all_run n (false,false) ds m b o rfl rfl rfl rfl
  have h5 := finish_all_run n H B N (false,false)
  have h1' : (transition n)^[packetTime n 0 m b rs]
      (some (cfg n (.readCount 0) (false,false) {dh with input := encNat rs.length++sourceBody rs++rest})) =
      some (cfg n (copiesLabel n 1 (n-1)) (false,false) {dc with input := rest}) := by
    simpa only [dc,dh,H,Fin.val_zero,List.append_nil,List.nil_append] using h1
  have h0' : (transition n)^[headerTime n m b o]
      (some (initList (machine n) (List.replicate n (sourceCode m b o rs)).flatten)) =
      some (cfg n (.readCount 0) (false,false) {dh with input := encNat rs.length++sourceBody rs++rest}) := by
    have hi : initList (machine n) (List.replicate n (sourceCode m b o rs)).flatten =
        cfg n (.firstHeader 0) (false,false)
          {input := sourceHeader m b o++(encNat rs.length++sourceBody rs++rest)} := by
      have he : (List.replicate n (sourceCode m b o rs)).flatten =
          sourceHeader m b o++(encNat rs.length++sourceBody rs++rest) := by
        conv_lhs => rw [show n=(n-1)+1 by omega,List.replicate_succ,List.flatten_cons]
        simp only [sourceCode,List.append_assoc,rest]
      rw [he]
      simp only [initList,cfg,machine,Data.stacks]
      congr 1
      funext k; fin_cases k <;> rfl
    rw [hi]
    simpa only [dh,H] using h0
  have h4' : (transition n)^[m+b+o+4] (some (cfg n (.cleanup 0) (false,false) ds)) =
      some (cfg n (.finish 0) (false,false) {header := H.reverse,count := List.replicate N true,body := B.reverse}) := by
    simpa only [ds,dh] using h4
  have h := run_trans n (run_trans n (run_trans n (run_trans n (run_trans n h0' h1') h2') h3') h4') h5
  simpa only [fullTime,targetCode,H,B,N] using h

end QMAPerfectCompleteness.Main.Repetition.CompilerTM


