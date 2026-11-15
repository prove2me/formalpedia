-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompilerTM
-- name    : QMAPerfectCompleteness_Proof_DyadicCompilerTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:56:18.072775+00:00
-- url     : https://prove2.me/theorems/fbf12ea3-a2c8-487a-877c-e84869978e5c
-- title:
--   Finite-machine implementation of the real-simulation compiler
-- statement:
--   Constructs a finite unary-stream transducer for the HP-to-G₂ compiler. Its labels parse headers and gate addresses, emit the exact fixed expansion of each gate, recount emitted gates, and clean its stacks. Checked runs on valid verifier encodings produce the compiled bytes within an explicit quadratic time polynomial. This runtime witness is auxiliary formalization infrastructure.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/DyadicCompilerTM.lean, lines 12–1041.

/- Generated from Solutions.DyadicCompilerTM by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QAlgorithms_ClassicalStringComputability
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



/-! Explicit unary-stream machine for the HP-to-G₂ real-simulation compiler. -/
set_option backward.isDefEq.respectTransparency false
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.DyadicCompiler.TM
open QAlgorithms.Complexity (Str encNat)
open Uniformity

inductive Token where
  | bit : Bool → Token
  | addr : Fin 3 → Token
  | count : Token
  deriving DecidableEq, Fintype

def onePlan : List Token :=
  [.count,.bit true,.bit true,.bit true,.bit false,.bit true,.addr 0,.bit true,.addr 2]
def phasePlan : List Token :=
  [.count,.bit true,.bit true,.bit true,.bit false,.bit false,.bit true,.addr 2]
def toffoliPlan : List Token :=
  [.count,.bit true,.bit true,.bit false,.bit true,.addr 0,.bit true,.addr 1,.bit false]
def plan (kind : Bool) : List Token :=
  if kind then phasePlan++toffoliPlan++phasePlan++toffoliPlan else onePlan
lemma plan_bound (kind : Bool) : (plan kind).length < 128 := by cases kind <;> decide

inductive Label where
  | headerStart : Fin 3 → Label
  | header : Fin 3 → Label
  | discardCount : Label
  | gate : Label
  | read : Bool → Fin 3 → Label
  | emit : Bool → Fin 128 → Label
  | copy : Bool → Fin 128 → Fin 3 → Bool → Label
  | clear : Fin 3 → Label
  | finish : Fin 3 → Label
  deriving DecidableEq, Fintype

def addrKey (j : Fin 3) : Fin 9 := ⟨j.val+2,by have := j.isLt; omega⟩
def nextRead (kind : Bool) (j : Fin 3) : Label :=
  if kind && decide (j.val < 1) then .read kind (Fin.ofNat 3 (j.val+1)) else .emit kind 0

def nextEmit (i : Fin 128) : Fin 128 := Fin.ofNat 128 (i.val+1)

abbrev machine : FinTM2 where
  K := Fin 9
  k₀ := 0
  k₁ := 8
  Γ _ := Bool
  Λ := Label
  main := .headerStart 0
  σ := Option Bool
  initialState := none
  m l := match l with
    | .headerStart j => .push 1 (fun _ => true) (.goto (fun _ => .header j))
    | .header j => .peek 0 (fun _ a => a)
      (.pop 0 (fun v _ => v) (.push 1 (fun v => v.getD false)
        (.branch (fun v => v.getD false)
          (if j.val < 2 then .push (addrKey 2) (fun _ => true) (.goto (fun _ => .header j))
            else .goto (fun _ => .header j))
          (.goto (fun _ => if j.val < 2 then .headerStart (Fin.ofNat 3 (j.val+1)) else .discardCount)))))
    | .discardCount => .peek 0 (fun _ a => a)
      (.pop 0 (fun v _ => v) (.branch (fun v => v.getD false)
        (.goto (fun _ => .discardCount)) (.goto (fun _ => .gate))))
    | .gate => .peek 0 (fun _ a => a)
      (.branch Option.isSome
        (.branch (fun v => v.getD false)
          (.pop 0 (fun v _ => v) (.pop 0 (fun v _ => v) (.goto (fun _ => .read true 0))))
          (.pop 0 (fun v _ => v) (.goto (fun _ => .read false 0))))
        (.goto (fun _ => .clear 2)))
    | .read kind j => .peek 0 (fun _ a => a)
      (.pop 0 (fun v _ => v) (.branch (fun v => v.getD false)
        (.push (addrKey j) (fun _ => true) (.goto (fun _ => .read kind j)))
        (.goto (fun _ => nextRead kind j))))
    | .emit kind i => match (plan kind)[i.val]? with
      | none => .load (fun _ => none) (.goto (fun _ => .clear 0))
      | some (.bit b) => .load (fun _ => none) (.push 7 (fun _ => b) (.goto (fun _ => .emit kind (nextEmit i))))
      | some .count => .load (fun _ => none) (.push 6 (fun _ => true) (.goto (fun _ => .emit kind (nextEmit i))))
      | some (.addr j) => .load (fun _ => none) (.goto (fun _ => .copy kind i j false))
    | .copy kind i j false => .peek (addrKey j) (fun _ a => a)
      (.branch Option.isSome
        (.pop (addrKey j) (fun v _ => v) (.push 5 (fun _ => true)
          (.push 7 (fun _ => true) (.goto (fun _ => .copy kind i j false)))))
        (.push 7 (fun _ => false) (.goto (fun _ => .copy kind i j true))))
    | .copy kind i j true => .peek 5 (fun _ a => a)
      (.branch Option.isSome
        (.pop 5 (fun v _ => v) (.push (addrKey j) (fun _ => true)
          (.goto (fun _ => .copy kind i j true))))
        (.goto (fun _ => .emit kind (nextEmit i))))
    | .clear j => .peek (addrKey j) (fun _ a => a)
      (.branch Option.isSome
        (.pop (addrKey j) (fun v _ => v) (.goto (fun _ => .clear j)))
        (.goto (fun _ => if j.val = 0 then .clear 1 else if j.val = 1 then .gate else .finish 0)))
    | .finish j =>
      let key := if j.val = 0 then (7 : Fin 9) else if j.val = 1 then 6 else 1
      .peek key (fun _ a => a)
        (.branch Option.isSome
          (.pop key (fun v _ => v) (.push 8 (fun v => v.getD false) (.goto (fun _ => .finish j))))
          (if j.val = 0 then .push 8 (fun _ => false) (.goto (fun _ => .finish 1))
            else if j.val = 1 then .goto (fun _ => .finish 2)
            else .load (fun _ => none) .halt))

structure Data where
  input : Str := []
  header : Str := []
  wires : Fin 3 → Str := fun _ => []
  tmp : Str := []
  count : Str := []
  body : Str := []
  output : Str := []

def Data.stacks (d : Data) : Fin 9 → Str :=
  ![d.input,d.header,d.wires 0,d.wires 1,d.wires 2,d.tmp,d.count,d.body,d.output]

def cfg (l : Label) (v : Option Bool) (d : Data) : machine.Cfg := ⟨some l,v,d.stacks⟩



lemma read_true_step (kind : Bool) (j : Fin 3) (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg (.read kind j) v {d with input := true::s}) =
      some (cfg (.read kind j) (some true)
        {d with input := s,wires := Function.update d.wires j (true::d.wires j)}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals
    funext k
    fin_cases k <;> simp

lemma read_false_step (kind : Bool) (j : Fin 3) (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg (.read kind j) v {d with input := false::s}) =
      some (cfg (nextRead kind j) (some false) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma read_run (kind : Bool) (j : Fin 3) (v : Option Bool) (d : Data) (w : ℕ) (tail : Str) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (some (cfg (.read kind j) v {d with input := encNat w++tail})) =
      some (cfg (nextRead kind j) (some false)
        {d with input := tail,wires := Function.update d.wires j (List.replicate w true++d.wires j)}) := by
  induction w generalizing v d with
  | zero =>
    simpa [encNat] using read_false_step kind j v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (machine.step (cfg (.read kind j) v {d with input := true::(encNat w++tail)})) = _
    rw [read_true_step]
    have hrep : List.replicate w true ++ true::d.wires j =
        List.replicate (w+1) true ++ d.wires j := by
      rw [List.replicate_add]
      simp
    simpa only [Function.update_self,Function.update_idem,hrep] using
      ih (some true) {d with wires := Function.update d.wires j (true::d.wires j)}


lemma copy_scan_true_step (kind : Bool) (i : Fin 128) (j : Fin 3) (v : Option Bool)
    (d : Data) (s : Str) :
    machine.step (cfg (.copy kind i j false) v
      {d with wires := Function.update d.wires j (true::s)}) =
      some (cfg (.copy kind i j false) (some true)
        {d with wires := Function.update d.wires j s,tmp := true::d.tmp,body := true::d.body}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals
    funext k
    fin_cases k <;> simp

lemma copy_scan_nil_step (kind : Bool) (i : Fin 128) (j : Fin 3) (v : Option Bool) (d : Data) :
    machine.step (cfg (.copy kind i j false) v {d with wires := Function.update d.wires j []}) =
      some (cfg (.copy kind i j true) none
        {d with wires := Function.update d.wires j [],body := false::d.body}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals
    funext k
    fin_cases k <;> simp

lemma copy_restore_true_step (kind : Bool) (i : Fin 128) (j : Fin 3) (v : Option Bool)
    (d : Data) (s : Str) :
    machine.step (cfg (.copy kind i j true) v {d with tmp := true::s}) =
      some (cfg (.copy kind i j true) (some true)
        {d with tmp := s,wires := Function.update d.wires j (true::d.wires j)}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals
    funext k
    fin_cases k <;> simp

lemma copy_restore_nil_step (kind : Bool) (i : Fin 128) (j : Fin 3) (v : Option Bool) (d : Data) :
    machine.step (cfg (.copy kind i j true) v {d with tmp := []}) =
      some (cfg (.emit kind (nextEmit i)) none {d with tmp := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]

lemma copy_scan_run (kind : Bool) (i : Fin 128) (j : Fin 3) (v : Option Bool)
    (d : Data) (w : ℕ) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (some (cfg (.copy kind i j false) v {d with wires := Function.update d.wires j (List.replicate w true)})) =
      some (cfg (.copy kind i j true) none
        {d with wires := Function.update d.wires j [],tmp := List.replicate w true++d.tmp,body := false::(List.replicate w true++d.body)}) := by
  induction w generalizing v d with
  | zero => simpa using copy_scan_nil_step kind i j v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (machine.step (cfg (.copy kind i j false) v
        {d with wires := Function.update d.wires j (true::List.replicate w true)})) = _
    rw [copy_scan_true_step]
    have ht : List.replicate w true ++ true::d.tmp = List.replicate (w+1) true++d.tmp := by
      rw [List.replicate_add]; simp
    have hb : List.replicate w true ++ true::d.body = List.replicate (w+1) true++d.body := by
      rw [List.replicate_add]; simp
    simpa only [Function.update_idem,ht,hb] using ih (some true)
      {d with tmp := true::d.tmp,body := true::d.body}

lemma copy_restore_run (kind : Bool) (i : Fin 128) (j : Fin 3) (v : Option Bool)
    (d : Data) (w : ℕ) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (some (cfg (.copy kind i j true) v {d with tmp := List.replicate w true})) =
      some (cfg (.emit kind (nextEmit i)) none
        {d with tmp := [],wires := Function.update d.wires j (List.replicate w true++d.wires j)}) := by
  induction w generalizing v d with
  | zero => simpa using copy_restore_nil_step kind i j v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (machine.step (cfg (.copy kind i j true) v {d with tmp := true::List.replicate w true})) = _
    rw [copy_restore_true_step]
    have hr : List.replicate w true ++ true::d.wires j = List.replicate (w+1) true++d.wires j := by
      rw [List.replicate_add]; simp
    simpa only [Function.update_self,Function.update_idem,hr] using ih (some true)
      {d with wires := Function.update d.wires j (true::d.wires j)}

/-- Copy one unary wire address to the reverse output buffer while restoring its source stack. -/
lemma copy_address_run (kind : Bool) (i : Fin 128) (j : Fin 3) (v : Option Bool)
    (d : Data) (w : ℕ) (hw : d.wires j = List.replicate w true) (htmp : d.tmp = []) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[2*w+2]
      (some (cfg (.copy kind i j false) v d)) =
      some (cfg (.emit kind (nextEmit i)) none {d with body := (encNat w).reverse++d.body}) := by
  have hd : {d with wires := Function.update d.wires j (List.replicate w true)} = d := by
    rw [← hw,Function.update_eq_self]
  have hs := copy_scan_run kind i j v d w
  rw [hd] at hs
  rw [show 2*w+2 = (w+1)+(w+1) by omega,Function.iterate_add_apply,hs]
  simp only [htmp,List.append_nil]
  have hr := copy_restore_run kind i j none
    {d with wires := Function.update d.wires j [],body := false::(List.replicate w true++d.body)} w
  have hu : Function.update d.wires j (List.replicate w true) = d.wires := by
    rw [← hw,Function.update_eq_self]
  simpa only [Function.update_self,Function.update_idem,List.nil_append,List.append_nil,hu,
    encNat,List.reverse_append,List.reverse_singleton,List.reverse_replicate,
    List.singleton_append,List.cons_append,htmp] using hr


def nextClear (j : Fin 3) : Label :=
  if j.val = 0 then .clear 1 else if j.val = 1 then .gate else .finish 0

lemma discard_true_step (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg .discardCount v {d with input := true::s}) =
      some (cfg .discardCount (some true) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma discard_false_step (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg .discardCount v {d with input := false::s}) =
      some (cfg .gate (some false) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma discard_run (v : Option Bool) (d : Data) (w : ℕ) (tail : Str) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (some (cfg .discardCount v {d with input := encNat w++tail})) =
      some (cfg .gate (some false) {d with input := tail}) := by
  induction w generalizing v d with
  | zero => simpa [encNat] using discard_false_step v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (machine.step (cfg .discardCount v {d with input := true::(encNat w++tail)})) = _
    rw [discard_true_step]
    exact ih (some true) d

lemma gate_H_step (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg .gate v {d with input := false::s}) =
      some (cfg (.read false 0) (some false) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma gate_Toffoli_step (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg .gate v {d with input := true::false::s}) =
      some (cfg (.read true 0) (some true) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma gate_nil_step (v : Option Bool) (d : Data) :
    machine.step (cfg .gate v {d with input := []}) = some (cfg (.clear 2) none {d with input := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma clear_true_step (j : Fin 3) (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg (.clear j) v {d with wires := Function.update d.wires j (true::s)}) =
      some (cfg (.clear j) (some true) {d with wires := Function.update d.wires j s}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,addrKey]
  all_goals
    funext k
    fin_cases k <;> simp

lemma clear_nil_step (j : Fin 3) (v : Option Bool) (d : Data) :
    machine.step (cfg (.clear j) v {d with wires := Function.update d.wires j []}) =
      some (cfg (nextClear j) none {d with wires := Function.update d.wires j []}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,addrKey,nextClear]

lemma clear_run (j : Fin 3) (v : Option Bool) (d : Data) (w : ℕ) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (some (cfg (.clear j) v {d with wires := Function.update d.wires j (List.replicate w true)})) =
      some (cfg (nextClear j) none {d with wires := Function.update d.wires j []}) := by
  induction w generalizing v d with
  | zero => simpa using clear_nil_step j v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (machine.step (cfg (.clear j) v {d with wires := Function.update d.wires j (true::List.replicate w true)})) = _
    rw [clear_true_step]
    exact ih (some true) d


def tokenBits (a : Fin 3 → ℕ) : Token → Str
  | .bit b => [b]
  | .addr j => encNat (a j)
  | .count => []

def tokenCount : Token → ℕ
  | .count => 1
  | _ => 0

def tokenCost (a : Fin 3 → ℕ) : Token → ℕ
  | .addr j => 2*a j+3
  | _ => 1

def execToken (a : Fin 3 → ℕ) (t : Token) (d : Data) : Data :=
  {d with body := (tokenBits a t).reverse++d.body,count := List.replicate (tokenCount t) true++d.count}

def execTokens (a : Fin 3 → ℕ) : List Token → Data → Data
  | [],d => d
  | t::ts,d => execTokens a ts (execToken a t d)




lemma emit_bit_step (kind : Bool) (i : Fin 128) (b : Bool) (h : (plan kind)[i.val]? = some (.bit b))
    (v : Option Bool) (d : Data) :
    machine.step (cfg (.emit kind i) v d) =
      some (cfg (.emit kind (nextEmit i)) none {d with body := b::d.body}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,h]
  funext k
  fin_cases k <;> simp

lemma emit_count_step (kind : Bool) (i : Fin 128) (h : (plan kind)[i.val]? = some .count)
    (v : Option Bool) (d : Data) :
    machine.step (cfg (.emit kind i) v d) =
      some (cfg (.emit kind (nextEmit i)) none {d with count := true::d.count}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,h]
  funext k
  fin_cases k <;> simp

lemma emit_addr_step (kind : Bool) (i : Fin 128) (j : Fin 3) (h : (plan kind)[i.val]? = some (.addr j))
    (v : Option Bool) (d : Data) :
    machine.step (cfg (.emit kind i) v d) = some (cfg (.copy kind i j false) none d) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,h]

lemma emit_none_step (kind : Bool) (i : Fin 128) (h : (plan kind)[i.val]? = none)
    (v : Option Bool) (d : Data) :
    machine.step (cfg (.emit kind i) v d) = some (cfg (.clear 0) none d) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,h]

lemma emit_token_run (kind : Bool) (i : Fin 128) (t : Token) (h : (plan kind)[i.val]? = some t)
    (v : Option Bool) (d : Data) (a : Fin 3 → ℕ)
    (hw : ∀ j, d.wires j = List.replicate (a j) true) (htmp : d.tmp = []) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[tokenCost a t]
      (some (cfg (.emit kind i) v d)) =
      some (cfg (.emit kind (nextEmit i)) none (execToken a t d)) := by
  cases t with
  | bit b =>
    change machine.step (cfg (.emit kind i) v d) = _
    simpa only [execToken,tokenBits,tokenCount,List.reverse_singleton,List.singleton_append,
      List.replicate_zero,List.nil_append] using emit_bit_step kind i b h v d
  | count =>
    change machine.step (cfg (.emit kind i) v d) = _
    simpa only [execToken,tokenBits,tokenCount,List.reverse_nil,List.nil_append,
      List.replicate_one,List.singleton_append] using emit_count_step kind i h v d
  | addr j =>
    change (fun o : Option machine.Cfg => o.bind machine.step)^[2*a j+3] _ = _
    rw [show 2*a j+3 = (2*a j+2)+1 by omega,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[2*a j+2]
      (machine.step (cfg (.emit kind i) v d)) = _
    rw [emit_addr_step kind i j h,copy_address_run kind i j none d (a j) (hw j) htmp]
    rfl


lemma emit_suffix_run (kind : Bool) (ts : List Token) :
    ∀ (pre : List Token) (hp : plan kind = pre++ts) (i : Fin 128) (hi : i.val = pre.length)
      (v : Option Bool) (d : Data) (a : Fin 3 → ℕ)
      (hw : ∀ j, d.wires j = List.replicate (a j) true) (htmp : d.tmp = []),
    (fun o : Option machine.Cfg => o.bind machine.step)^[(ts.map (tokenCost a)).sum+1]
      (some (cfg (.emit kind i) v d)) =
      some (cfg (.clear 0) none (execTokens a ts d)) := by
  induction ts with
  | nil =>
    intro pre hp i hi v d a hw htmp
    change machine.step (cfg (.emit kind i) v d) = _
    apply emit_none_step
    rw [hi,show plan kind = pre by simpa using hp]
    simp
  | cons t ts ih =>
    intro pre hp i hi v d a hw htmp
    have hget : (plan kind)[i.val]? = some t := by
      rw [hi,hp,List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hn : (nextEmit i).val = (pre++[t]).length := by
      have hb := plan_bound kind
      rw [hp,List.length_append,List.length_cons] at hb
      simp only [nextEmit,Fin.val_ofNat,List.length_append,List.length_singleton]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [List.map_cons,List.sum_cons]
    rw [show tokenCost a t+(ts.map (tokenCost a)).sum+1 =
        ((ts.map (tokenCost a)).sum+1)+tokenCost a t by omega,
      Function.iterate_add_apply,emit_token_run kind i t hget v d a hw htmp]
    exact ih (pre++[t]) (by simpa only [List.append_assoc,List.singleton_append] using hp)
      (nextEmit i) hn none (execToken a t d) a hw htmp

lemma emit_plan_run (kind : Bool) (v : Option Bool) (d : Data) (a : Fin 3 → ℕ)
    (hw : ∀ j, d.wires j = List.replicate (a j) true) (htmp : d.tmp = []) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[((plan kind).map (tokenCost a)).sum+1]
      (some (cfg (.emit kind 0) v d)) =
      some (cfg (.clear 0) none (execTokens a (plan kind) d)) :=
  emit_suffix_run kind (plan kind) [] rfl 0 rfl v d a hw htmp

lemma execTokens_effect (a : Fin 3 → ℕ) (ts : List Token) (d : Data) :
    execTokens a ts d =
      {d with body := (ts.flatMap (tokenBits a)).reverse++d.body,count :=         List.replicate ((ts.map tokenCount).sum) true++d.count} := by
  induction ts generalizing d with
  | nil => simp [execTokens]
  | cons t ts ih =>
    rw [execTokens,ih]
    simp only [execToken,List.flatMap_cons,List.reverse_append,List.append_assoc,
      List.map_cons,List.sum_cons]
    have hc : List.replicate ((ts.map tokenCount).sum) true ++
        (List.replicate (tokenCount t) true++d.count) =
        List.replicate (tokenCount t+(ts.map tokenCount).sum) true++d.count := by
      rw [← List.append_assoc,← List.replicate_add,Nat.add_comm]
    rw [hc]


lemma clear_actual_run (j : Fin 3) (v : Option Bool) (d : Data) (w : ℕ)
    (hw : d.wires j = List.replicate w true) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[w+1]
      (some (cfg (.clear j) v d)) =
      some (cfg (nextClear j) none {d with wires := Function.update d.wires j []}) := by
  have hd : {d with wires := Function.update d.wires j (List.replicate w true)} = d := by
    rw [← hw,Function.update_eq_self]
  have h := clear_run j v d w
  rwa [hd] at h

lemma finish_body_cons (v : Option Bool) (d : Data) (b : Bool) (s : Str) :
    machine.step (cfg (.finish 0) v {d with body := b::s}) =
      some (cfg (.finish 0) (some b) {d with body := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_body_nil (v : Option Bool) (d : Data) :
    machine.step (cfg (.finish 0) v {d with body := []}) =
      some (cfg (.finish 1) none {d with body := [],output := false::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_count_cons (v : Option Bool) (d : Data) (b : Bool) (s : Str) :
    machine.step (cfg (.finish 1) v {d with count := b::s}) =
      some (cfg (.finish 1) (some b) {d with count := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_count_nil (v : Option Bool) (d : Data) :
    machine.step (cfg (.finish 1) v {d with count := []}) =
      some (cfg (.finish 2) none {d with count := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma finish_header_cons (v : Option Bool) (d : Data) (b : Bool) (s : Str) :
    machine.step (cfg (.finish 2) v {d with header := b::s}) =
      some (cfg (.finish 2) (some b) {d with header := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_header_nil (v : Option Bool) (d : Data) :
    machine.step (cfg (.finish 2) v {d with header := []}) =
      some (⟨none,none,({d with header := []} : Data).stacks⟩ : machine.Cfg) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma finish_body_run (v : Option Bool) (d : Data) (s : Str) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[s.length+1]
      (some (cfg (.finish 0) v {d with body := s})) =
      some (cfg (.finish 1) none {d with body := [],output := false::(s.reverse++d.output)}) := by
  induction s generalizing v d with
  | nil => simpa using finish_body_nil v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[s.length+1]
      (machine.step (cfg (.finish 0) v {d with body := b::s})) = _
    rw [finish_body_cons]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (some b) {d with output := b::d.output}

lemma finish_count_run (v : Option Bool) (d : Data) (s : Str) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[s.length+1]
      (some (cfg (.finish 1) v {d with count := s})) =
      some (cfg (.finish 2) none {d with count := [],output := s.reverse++d.output}) := by
  induction s generalizing v d with
  | nil => simpa using finish_count_nil v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[s.length+1]
      (machine.step (cfg (.finish 1) v {d with count := b::s})) = _
    rw [finish_count_cons]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (some b) {d with output := b::d.output}

lemma finish_header_run (v : Option Bool) (d : Data) (s : Str) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[s.length+1]
      (some (cfg (.finish 2) v {d with header := s})) =
      some (⟨none,none,({d with header := [],output := s.reverse++d.output} : Data).stacks⟩ : machine.Cfg) := by
  induction s generalizing v d with
  | nil => simpa using finish_header_nil v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option machine.Cfg => o.bind machine.step)^[s.length+1]
      (machine.step (cfg (.finish 2) v {d with header := b::s})) = _
    rw [finish_header_cons]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (some b) {d with output := b::d.output}




def nextHeader (j : Fin 3) : Label :=
  if j.val < 2 then .headerStart (Fin.ofNat 3 (j.val+1)) else .discardCount

def capture (j : Fin 3) (w : ℕ) (u : Fin 3 → Str) : Fin 3 → Str :=
  if j.val < 2 then Function.update u 2 (List.replicate w true++u 2) else u

@[simp] lemma capture_zero (j : Fin 3) (u : Fin 3 → Str) : capture j 0 u = u := by
  simp [capture]

lemma replicate_cons (w : ℕ) (s : Str) :
    List.replicate w true++true::s = List.replicate (w+1) true++s := by
  rw [List.replicate_add]
  simp

lemma capture_succ (j : Fin 3) (w : ℕ) (u : Fin 3 → Str) :
    capture j w (capture j 1 u) = capture j (w+1) u := by
  by_cases hj : j.val < 2
  · simp [capture,hj,Function.update_idem,replicate_cons]
  · simp [capture,hj]

lemma header_start_step (j : Fin 3) (v : Option Bool) (d : Data) :
    machine.step (cfg (.headerStart j) v d) =
      some (cfg (.header j) v {d with header := true::d.header}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma header_true_step (j : Fin 3) (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg (.header j) v {d with input := true::s}) =
      some (cfg (.header j) (some true)
        {d with input := s,header := true::d.header,wires := capture j 1 d.wires}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,capture,addrKey]
  all_goals
    funext k
    fin_cases k <;> simp

lemma header_false_step (j : Fin 3) (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg (.header j) v {d with input := false::s}) =
      some (cfg (nextHeader j) (some false) {d with input := s,header := false::d.header}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,nextHeader]
  funext k
  fin_cases k <;> simp

lemma header_run (j : Fin 3) (v : Option Bool) (d : Data) (w : ℕ) (tail : Str) :
    (fun q : Option machine.Cfg => q.bind machine.step)^[w+1]
      (some (cfg (.header j) v {d with input := encNat w++tail})) =
      some (cfg (nextHeader j) (some false)
        {d with input := tail,header := (encNat w).reverse++d.header,wires := capture j w d.wires}) := by
  induction w generalizing v d with
  | zero =>
    change machine.step (cfg (.header j) v {d with input := encNat 0++tail}) = _
    simpa only [encNat,List.replicate_zero,List.nil_append,List.reverse_singleton,
      List.singleton_append,capture_zero] using header_false_step j v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun q : Option machine.Cfg => q.bind machine.step)^[w+1]
      (machine.step (cfg (.header j) v {d with input := true::(encNat w++tail)})) = _
    rw [header_true_step]
    have hr : (encNat w).reverse++true::d.header = (encNat (w+1)).reverse++d.header := by
      simpa only [encNat,List.reverse_append,List.reverse_singleton,List.reverse_replicate,
        List.singleton_append,List.cons_append,List.nil_append] using congrArg (List.cons false) (replicate_cons w d.header)
    simpa only [hr,capture_succ] using ih (some true)
      {d with header := true::d.header,wires := capture j 1 d.wires}

lemma header_offset_run (j : Fin 3) (v : Option Bool) (d : Data) (w : ℕ) (tail : Str) :
    (fun q : Option machine.Cfg => q.bind machine.step)^[w+2]
      (some (cfg (.headerStart j) v {d with input := encNat w++tail})) =
      some (cfg (nextHeader j) (some false)
        {d with input := tail,header := (encNat (w+1)).reverse++d.header,wires := capture j w d.wires}) := by
  rw [show w+2 = (w+1)+1 by omega,Function.iterate_succ_apply]
  change (fun q : Option machine.Cfg => q.bind machine.step)^[w+1]
    (machine.step (cfg (.headerStart j) v {d with input := encNat w++tail})) = _
  rw [header_start_step]
  have h := header_run j v {d with header := true::d.header} w tail
  simpa only [encNat,List.reverse_append,List.reverse_singleton,List.reverse_replicate,
    List.singleton_append,List.cons_append,List.nil_append,replicate_cons] using h


def baseWires (N : ℕ) : Fin 3 → Str := fun j => if j = 2 then List.replicate N true else []

def rawInstr (kind : Bool) (a : Fin 3 → ℕ) : RawEncoding.Instruction :=
  if kind then ⟨1,[a 0,a 1]⟩ else ⟨0,[a 0]⟩

def bodyCode (kind : Bool) (a : Fin 3 → ℕ) : Str :=
  (rawCompileInstr (a 2) (rawInstr kind a)).flatMap RawEncoding.Instruction.encode

lemma plan_bits (kind : Bool) (a : Fin 3 → ℕ) :
    (plan kind).flatMap (tokenBits a) = bodyCode kind a := by
  cases kind <;> simp [plan,onePlan,phasePlan,toffoliPlan,tokenBits,bodyCode,rawInstr,
    rawCompileInstr,compileTags,fromTags,RawEncoding.Instruction.encode,List.append_assoc,encNat,List.replicate_succ]

lemma plan_count (kind : Bool) : ((plan kind).map tokenCount).sum = if kind then 4 else 1 := by
  cases kind <;> decide

lemma plan_cost_bound (kind : Bool) (a : Fin 3 → ℕ) :
    ((plan kind).map (tokenCost a)).sum ≤ 100*(a 0+a 1+a 2+1) := by
  cases kind <;> simp [plan,onePlan,phasePlan,toffoliPlan,tokenCost] <;> omega

lemma exec_plan_effect (kind : Bool) (a : Fin 3 → ℕ) (d : Data) :
    execTokens a (plan kind) d =
      {d with body := (bodyCode kind a).reverse++d.body,count := List.replicate (if kind then 4 else 1) true++d.count} := by
  rw [execTokens_effect,plan_bits,plan_count]

lemma clear_sources_run (a : Fin 3 → ℕ) (v : Option Bool) (d : Data)
    (hw : ∀ j, d.wires j = List.replicate (a j) true) :
    (fun q : Option machine.Cfg => q.bind machine.step)^[a 0+a 1+2]
      (some (cfg (.clear 0) v d)) =
      some (cfg .gate none {d with wires := baseWires (a 2)}) := by
  rw [show a 0+a 1+2 = (a 1+1)+(a 0+1) by omega,Function.iterate_add_apply,
    clear_actual_run 0 v d (a 0) (hw 0)]
  change (fun q : Option machine.Cfg => q.bind machine.step)^[a 1+1]
    (some (cfg (.clear 1) none {d with wires := Function.update d.wires 0 []})) = _
  rw [clear_actual_run 1 none _ (a 1) (by simpa using hw 1)]
  congr 1
  congr 2
  funext j
  fin_cases j <;> simp [baseWires,hw]

lemma rawInstr_H_encode (w N : ℕ) (tail : Str) :
    (rawInstr false ![w,0,N]).encode++tail = false::(encNat w++tail) := by
  simp [rawInstr,RawEncoding.Instruction.encode,encNat,List.append_assoc]

lemma rawInstr_CP_encode (a : Fin 3 → ℕ) (tail : Str) :
    (rawInstr true a).encode++tail = true::false::(encNat (a 0)++(encNat (a 1)++tail)) := by
  simp [rawInstr,RawEncoding.Instruction.encode,encNat,List.append_assoc]

lemma parse_H_run (v : Option Bool) (d : Data) (w N : ℕ) (tail : Str)
    (hc : d.wires = baseWires N) :
    (fun q : Option machine.Cfg => q.bind machine.step)^[w+2]
      (some (cfg .gate v {d with input := (rawInstr false ![w,0,N]).encode++tail})) =
      some (cfg (.emit false 0) (some false)
        {d with input := tail,wires := fun j => List.replicate (![w,0,N] j) true}) := by
  rw [rawInstr_H_encode,show w+2 = (w+1)+1 by omega,Function.iterate_succ_apply]
  change (fun q : Option machine.Cfg => q.bind machine.step)^[w+1]
    (machine.step (cfg .gate v {d with input := false::(encNat w++tail)})) = _
  rw [gate_H_step,read_run false 0 (some false) d w tail]
  congr 1
  congr 2
  funext j
  fin_cases j <;> simp [hc,baseWires]

lemma parse_CP_run (v : Option Bool) (d : Data) (a : Fin 3 → ℕ) (tail : Str)
    (hc : d.wires = baseWires (a 2)) :
    (fun q : Option machine.Cfg => q.bind machine.step)^[a 0+a 1+3]
      (some (cfg .gate v {d with input := (rawInstr true a).encode++tail})) =
      some (cfg (.emit true 0) (some false)
        {d with input := tail,wires := fun j => List.replicate (a j) true}) := by
  rw [rawInstr_CP_encode,show a 0+a 1+3 = (a 1+1)+((a 0+1)+1) by omega,
    Function.iterate_add_apply _ (a 1+1) ((a 0+1)+1),Function.iterate_add_apply _ (a 0+1) 1]
  change (fun q : Option machine.Cfg => q.bind machine.step)^[a 1+1]
    ((fun q : Option machine.Cfg => q.bind machine.step)^[a 0+1]
      (machine.step (cfg .gate v {d with input := true::false::(encNat (a 0)++(encNat (a 1)++tail))}))) = _
  rw [gate_Toffoli_step,read_run true 0 (some true) d (a 0) _]
  change (fun q : Option machine.Cfg => q.bind machine.step)^[a 1+1]
    (some (cfg (.read true 1) (some false)
      {d with input := encNat (a 1)++tail,wires := Function.update d.wires 0 (List.replicate (a 0) true++d.wires 0)})) = _
  rw [read_run true 1 (some false) {d with wires := Function.update d.wires 0 (List.replicate (a 0) true++d.wires 0)} (a 1) tail]
  congr 1
  congr 2
  funext j
  fin_cases j <;> simp [hc,baseWires]

def parseTime (kind : Bool) (a : Fin 3 → ℕ) : ℕ :=
  if kind then a 0+a 1+3 else a 0+2

def gateTime (kind : Bool) (a : Fin 3 → ℕ) : ℕ :=
  parseTime kind a+(((plan kind).map (tokenCost a)).sum+1)+(a 0+a 1+2)

lemma parse_gate_run (kind : Bool) (v : Option Bool) (d : Data) (a : Fin 3 → ℕ) (tail : Str)
    (hc : d.wires = baseWires (a 2)) (hz : kind = false → a 1 = 0) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[parseTime kind a]
      (some (cfg .gate v {d with input := (rawInstr kind a).encode++tail})) =
      some (cfg (.emit kind 0) (some false)
        {d with input := tail,wires := fun j => List.replicate (a j) true}) := by
  cases kind with
  | false =>
    have h1 := hz rfl
    have ha : a = ![a 0,0,a 2] := by funext j; fin_cases j <;> simp [h1]
    rw [ha]
    exact parse_H_run v d (a 0) (a 2) tail hc
  | true => exact parse_CP_run v d a tail hc

/-- One complete gate translation: consume its code, emit its exact expansion, clean addresses. -/
lemma gate_run (kind : Bool) (v : Option Bool) (d : Data) (a : Fin 3 → ℕ) (tail : Str)
    (hc : d.wires = baseWires (a 2)) (htmp : d.tmp = [])
    (hz : kind = false → a 1 = 0) :
    (fun o : Option machine.Cfg => o.bind machine.step)^[gateTime kind a]
      (some (cfg .gate v {d with input := (rawInstr kind a).encode++tail})) =
      some (cfg .gate none {d with input := tail,         body := (bodyCode kind a).reverse++d.body,count := List.replicate (if kind then 4 else 1) true++d.count}) := by
  rw [gateTime,show parseTime kind a+(((plan kind).map (tokenCost a)).sum+1)+(a 0+a 1+2) =
      (a 0+a 1+2)+((((plan kind).map (tokenCost a)).sum+1)+parseTime kind a) by omega,
    Function.iterate_add_apply _ (a 0+a 1+2) _,
    Function.iterate_add_apply _ (((plan kind).map (tokenCost a)).sum+1) _,
    parse_gate_run kind v d a tail hc hz]
  rw [emit_plan_run kind (some false) {d with input := tail,wires := fun j => List.replicate (a j) true}
    a (fun _ => rfl) htmp,exec_plan_effect]
  simpa only [hc] using clear_sources_run a none
    {d with input := tail,wires := fun j => List.replicate (a j) true,body := (bodyCode kind a).reverse++d.body,count := List.replicate (if kind then 4 else 1) true++d.count}
    (fun _ => rfl)


abbrev Recipe := Bool × (Fin 3 → ℕ)
def Recipe.Valid (r : Recipe) : Prop := r.1 = false → r.2 1 = 0

def sourceBody (rs : List Recipe) : Str := rs.flatMap (fun r => (rawInstr r.1 r.2).encode)
def targetBody (rs : List Recipe) : Str := rs.flatMap (fun r => bodyCode r.1 r.2)
def targetCount (rs : List Recipe) : ℕ := (rs.map (fun r => if r.1 then 4 else 1)).sum
def bodyTime (rs : List Recipe) : ℕ := (rs.map (fun r => gateTime r.1 r.2)).sum

lemma body_run (N : ℕ) (rs : List Recipe) : ∀ (v : Option Bool) (d : Data) (tail : Str)
    (hc : d.wires = baseWires N) (htmp : d.tmp = []) (hv : ∀ r ∈ rs, r.Valid ∧ r.2 2 = N),
    (fun q : Option machine.Cfg => q.bind machine.step)^[bodyTime rs]
      (some (cfg .gate v {d with input := sourceBody rs++tail})) =
      some (cfg .gate (if rs = [] then v else none)
        {d with input := tail,body := (targetBody rs).reverse++d.body,count := List.replicate (targetCount rs) true++d.count}) := by
  induction rs with
  | nil =>
    intro v d tail hc htmp hv
    simp [bodyTime,sourceBody,targetBody,targetCount]
  | cons r rs ih =>
    intro v d tail hc htmp hv
    simp only [bodyTime,List.map_cons,List.sum_cons,sourceBody,List.flatMap_cons,List.append_assoc]
    rw [Nat.add_comm (gateTime r.1 r.2),Function.iterate_add_apply]
    have hg := gate_run r.1 v d r.2 (sourceBody rs++tail)
      (by rw [(hv r (by simp)).2]; exact hc) htmp (hv r (by simp)).1
    simp only [sourceBody] at hg
    rw [hg]
    have htail := ih none
      {d with body := (bodyCode r.1 r.2).reverse++d.body,count := List.replicate (if r.1 then 4 else 1) true++d.count}
      tail hc htmp (fun q hq => hv q (by simp [hq]))
    simp only [bodyTime,sourceBody] at htail
    rw [htail]
    simp only [targetBody,List.flatMap_cons,List.reverse_append,List.append_assoc,
      targetCount,List.map_cons,List.sum_cons,List.cons_ne_nil,if_false,ite_self]
    have hcnt : List.replicate ((rs.map (fun q => if q.1 then 4 else 1)).sum) true++
        (List.replicate (if r.1 then 4 else 1) true++d.count) =
        List.replicate ((if r.1 then 4 else 1)+(rs.map (fun q => if q.1 then 4 else 1)).sum) true++d.count := by
      rw [← List.append_assoc,← List.replicate_add,Nat.add_comm]
    rw [hcnt]

lemma rawInstr_length (kind : Bool) (a : Fin 3 → ℕ) :
    (rawInstr kind a).encode.length = if kind then a 0+a 1+4 else a 0+2 := by
  cases kind <;> simp [rawInstr,RawEncoding.Instruction.encode,Encoding.encNat_length] <;> omega

lemma gateTime_bound (kind : Bool) (a : Fin 3 → ℕ) (hz : kind = false → a 1 = 0) :
    gateTime kind a ≤ 1000*((rawInstr kind a).encode.length+a 2+1) := by
  have hp := plan_cost_bound kind a
  rw [rawInstr_length]
  unfold gateTime parseTime
  cases kind with
  | false => have h1 := hz rfl; simp only [Bool.false_eq_true,if_false,h1] at hp ⊢; omega
  | true => simp only [if_true] at hp ⊢; omega

lemma tokenBits_length_le (a : Fin 3 → ℕ) (t : Token) :
    (tokenBits a t).length ≤ tokenCost a t := by
  cases t <;> simp [tokenBits,tokenCost,Encoding.encNat_length] <;> omega

lemma bodyCode_length_bound (kind : Bool) (a : Fin 3 → ℕ) (hz : kind = false → a 1 = 0) :
    (bodyCode kind a).length ≤ 200*((rawInstr kind a).encode.length+a 2+1) := by
  have hp := plan_cost_bound kind a
  rw [← plan_bits,List.length_flatMap]
  have hb : ((plan kind).map (fun t => (tokenBits a t).length)).sum ≤
      ((plan kind).map (tokenCost a)).sum := List.sum_le_sum (fun t _ => tokenBits_length_le a t)
  rw [rawInstr_length]
  cases kind with
  | false => have h1 := hz rfl; simp only [Bool.false_eq_true,if_false,h1] at hp ⊢; omega
  | true => simp only [if_true] at hp ⊢; omega

lemma bodyTime_bound (N : ℕ) (rs : List Recipe) (hv : ∀ r ∈ rs, r.Valid ∧ r.2 2 = N) :
    bodyTime rs ≤ 1000*((sourceBody rs).length+rs.length*(N+1)) := by
  induction rs with
  | nil => simp [bodyTime,sourceBody]
  | cons r rs ih =>
    have hg := gateTime_bound r.1 r.2 (hv r (by simp)).1
    rw [(hv r (by simp)).2] at hg
    have hi := ih (fun q hq => hv q (by simp [hq]))
    simp only [bodyTime,List.map_cons,List.sum_cons,sourceBody,List.flatMap_cons,List.length_append,
      List.length_cons] at *
    have hm : (rs.length+1)*(N+1) = rs.length*(N+1)+(N+1) := by ring
    rw [hm]
    omega

lemma targetBody_length_bound (N : ℕ) (rs : List Recipe) (hv : ∀ r ∈ rs, r.Valid ∧ r.2 2 = N) :
    (targetBody rs).length ≤ 200*((sourceBody rs).length+rs.length*(N+1)) := by
  induction rs with
  | nil => simp [targetBody,sourceBody]
  | cons r rs ih =>
    have hg := bodyCode_length_bound r.1 r.2 (hv r (by simp)).1
    rw [(hv r (by simp)).2] at hg
    have hi := ih (fun q hq => hv q (by simp [hq]))
    simp only [targetBody,sourceBody,List.flatMap_cons,List.length_append,List.length_cons] at *
    have hm : (rs.length+1)*(N+1) = rs.length*(N+1)+(N+1) := by ring
    rw [hm]
    omega

lemma targetCount_bound (rs : List Recipe) : targetCount rs ≤ 4*rs.length := by
  induction rs with
  | nil => simp [targetCount]
  | cons r rs ih =>
    simp only [targetCount,List.map_cons,List.sum_cons,List.length_cons] at *
    split_ifs <;> omega


def sourceHeader (m a o : ℕ) : Str := encNat m++encNat a++encNat o
def targetHeader (m a o : ℕ) : Str := sourceHeader (m+1) (a+1) (o+1)
def sourceCode (m a o : ℕ) (rs : List Recipe) : Str := sourceHeader m a o++encNat rs.length++sourceBody rs
def targetCode (m a o : ℕ) (rs : List Recipe) : Str :=
  targetHeader m a o++encNat (targetCount rs)++targetBody rs

def fullTime (m a o : ℕ) (rs : List Recipe) : ℕ :=
  2*(sourceHeader m a o).length+rs.length+bodyTime rs+(targetBody rs).length+targetCount rs+(m+a)+12

lemma sourceHeader_length (m a o : ℕ) : (sourceHeader m a o).length = m+a+o+3 := by
  simp [sourceHeader,Encoding.encNat_length]
  omega

lemma targetHeader_length (m a o : ℕ) : (targetHeader m a o).length = (sourceHeader m a o).length+3 := by
  simp only [targetHeader,sourceHeader_length]
  omega

lemma capture_first (m : ℕ) : capture 0 m (fun _ => []) = baseWires m := by
  funext j
  fin_cases j <;> simp [capture,baseWires]

lemma capture_second (m a : ℕ) : capture 1 a (baseWires m) = baseWires (m+a) := by
  funext j
  fin_cases j <;> simp [capture,baseWires]
  all_goals simpa only [Nat.add_comm] using (List.replicate_add (a := true) a m).symm

lemma capture_third (N o : ℕ) : capture 2 o (baseWires N) = baseWires N := by simp [capture]

lemma header_all_run (m a o : ℕ) (tail : Str) :
    (fun q : Option machine.Cfg => q.bind machine.step)^[(sourceHeader m a o).length+3]
      (some (cfg (.headerStart 0) none {input := sourceHeader m a o++tail})) =
      some (cfg .discardCount (some false)
        {input := tail,header := (targetHeader m a o).reverse,wires := baseWires (m+a)}) := by
  rw [show (sourceHeader m a o).length+3 = (o+2)+((a+2)+(m+2)) by rw [sourceHeader_length]; omega,
    Function.iterate_add_apply _ (o+2) ((a+2)+(m+2)),Function.iterate_add_apply _ (a+2) (m+2)]
  simp only [sourceHeader,List.append_assoc]
  rw [header_offset_run 0 none {} m (encNat a++(encNat o++tail))]
  simp only [capture_first,List.append_nil]
  change (fun q : Option machine.Cfg => q.bind machine.step)^[o+2]
    ((fun q : Option machine.Cfg => q.bind machine.step)^[a+2]
      (some (cfg (.headerStart 1) (some false)
        {input := encNat a++(encNat o++tail),header := (encNat (m+1)).reverse,wires := baseWires m}))) = _
  rw [header_offset_run 1 (some false) {header := (encNat (m+1)).reverse,wires := baseWires m} a (encNat o++tail)]
  simp only [capture_second]
  change (fun q : Option machine.Cfg => q.bind machine.step)^[o+2]
    (some (cfg (.headerStart 2) (some false)
      {input := encNat o++tail,header := (encNat (a+1)).reverse++(encNat (m+1)).reverse,wires := baseWires (m+a)})) = _
  rw [header_offset_run 2 (some false)
    {header := (encNat (a+1)).reverse++(encNat (m+1)).reverse,wires := baseWires (m+a)} o tail]
  simp only [capture_third,targetHeader,sourceHeader,List.reverse_append,List.append_assoc]
  rfl

lemma finish_all_run (H B : Str) (N : ℕ) (v : Option Bool) :
    (fun q : Option machine.Cfg => q.bind machine.step)^[B.length+N+H.length+3]
      (some (cfg (.finish 0) v {header := H.reverse,count := List.replicate N true,body := B.reverse})) =
      some (haltList machine (H++encNat N++B)) := by
  rw [show B.length+N+H.length+3 = (H.reverse.length+1)+
      (((List.replicate N true).length+1)+(B.reverse.length+1)) by simp; omega,
    Function.iterate_add_apply _ (H.reverse.length+1) _,
    Function.iterate_add_apply _ ((List.replicate N true).length+1) _]
  rw [finish_body_run v {header := H.reverse,count := List.replicate N true} B.reverse]
  simp only [List.reverse_reverse,List.append_nil]
  rw [finish_count_run none {header := H.reverse,output := false::B} (List.replicate N true)]
  simp only [List.reverse_replicate]
  rw [finish_header_run none {output := List.replicate N true++false::B} H.reverse]
  simp only [List.reverse_reverse,encNat,List.append_assoc,List.singleton_append]
  simp only [haltList,machine]
  congr 2
  funext k
  fin_cases k <;> rfl

abbrev transition : Option machine.Cfg → Option machine.Cfg := fun q => q.bind machine.step

lemma run_trans {n m : ℕ} {a b c : Option machine.Cfg}
    (hn : transition^[n] a = b) (hm : transition^[m] b = c) : transition^[n+m] a = c := by
  rw [Nat.add_comm n m,Function.iterate_add_apply,hn,hm]

lemma full_run (m a o : ℕ) (rs : List Recipe)
    (hv : ∀ r ∈ rs, r.Valid ∧ r.2 2 = m+a) :
    transition^[fullTime m a o rs] (some (initList machine (sourceCode m a o rs))) =
      some (haltList machine (targetCode m a o rs)) := by
  have hi : initList machine (sourceCode m a o rs) = cfg (.headerStart 0) none {input := sourceCode m a o rs} := by
    simp only [initList,cfg,machine,Data.stacks]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hh := header_all_run m a o (encNat rs.length++sourceBody rs)
  have hd := discard_run (some false) {header := (targetHeader m a o).reverse,wires := baseWires (m+a)} rs.length (sourceBody rs)
  have hb := body_run (m+a) rs (some false) {header := (targetHeader m a o).reverse,wires := baseWires (m+a)} [] rfl rfl hv
  simp only [List.append_nil,List.nil_append] at hh hd hb
  have he := gate_nil_step (if rs = [] then some false else none)
    {header := (targetHeader m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount rs) true,body := (targetBody rs).reverse}
  change transition^[1] (some (cfg .gate (if rs = [] then some false else none)
    {header := (targetHeader m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount rs) true,body := (targetBody rs).reverse})) = _ at he
  have hc := clear_actual_run 2 none
    {header := (targetHeader m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount rs) true,body := (targetBody rs).reverse}
    (m+a) (by simp [baseWires])
  have hz : Function.update (baseWires (m+a)) 2 [] = fun _ => [] := by
    funext j
    fin_cases j <;> simp [baseWires]
  simp only [hz,nextClear,Fin.isValue,Fin.reduceFinMk,Fin.reduceEq,ite_false] at hc
  have hf := finish_all_run (targetHeader m a o) (targetBody rs) (targetCount rs) none
  have h := run_trans (run_trans (run_trans (run_trans (run_trans hh hd) hb) he) hc) hf
  rw [hi]
  convert h using 1 <;> simp only [fullTime,sourceCode,targetCode,List.append_assoc,targetHeader_length] <;> congr 1 <;> omega

lemma fullTime_bound (m a o : ℕ) (rs : List Recipe)
    (hv : ∀ r ∈ rs, r.Valid ∧ r.2 2 = m+a) :
    fullTime m a o rs ≤ 10000*((sourceCode m a o rs).length+1)^2 := by
  let L := (sourceCode m a o rs).length
  have hL : L = (sourceHeader m a o).length+(rs.length+1)+(sourceBody rs).length := by
    simp [L,sourceCode,Encoding.encNat_length]
    omega
  have hH : (sourceHeader m a o).length ≤ L := by omega
  have hN : m+a ≤ L := by rw [sourceHeader_length] at hH; omega
  have hn : rs.length ≤ L := by omega
  have hB : (sourceBody rs).length ≤ L := by omega
  have hp := Nat.mul_le_mul hn (Nat.add_le_add_right hN 1)
  have ht := bodyTime_bound (m+a) rs hv
  have hb := targetBody_length_bound (m+a) rs hv
  have hc := targetCount_bound rs
  change fullTime m a o rs ≤ 10000*(L+1)^2
  unfold fullTime
  nlinarith


noncomputable def instrRecipe {n : ℕ} (N : ℕ) (i : Instr gatesHP n) : Recipe :=
  (decide (i.gate.val = 1),fun j => if j = 2 then N else ((RawEncoding.eraseInstr i).wires[j.val]?).getD 0)

lemma instrRecipe_valid {n : ℕ} (N : ℕ) (i : Instr gatesHP n) :
    (instrRecipe N i).Valid ∧ (instrRecipe N i).2 2 = N := by
  rcases i with ⟨g,t⟩
  fin_cases g <;> simp [instrRecipe,Recipe.Valid,RawEncoding.eraseInstr,List.ofFn_succ]

lemma rawInstr_instrRecipe {n : ℕ} (N : ℕ) (i : Instr gatesHP n) :
    rawInstr (instrRecipe N i).1 (instrRecipe N i).2 = RawEncoding.eraseInstr i := by
  rcases i with ⟨g,t⟩
  fin_cases g <;> rfl

lemma compileRawInstr_length (kind : Bool) (a : Fin 3 → ℕ) :
    (rawCompileInstr (a 2) (rawInstr kind a)).length = if kind then 4 else 1 := by
  cases kind <;> rfl

lemma instrRecipe_count {n : ℕ} (N : ℕ) (i : Instr gatesHP n) :
    (if (instrRecipe N i).1 then 4 else 1) = (rawCompileInstr N (RawEncoding.eraseInstr i)).length := by
  rw [← compileRawInstr_length (instrRecipe N i).1 (instrRecipe N i).2,
    (instrRecipe_valid N i).2,rawInstr_instrRecipe]

lemma instrRecipe_bodyCode {n : ℕ} (N : ℕ) (i : Instr gatesHP n) :
    bodyCode (instrRecipe N i).1 (instrRecipe N i).2 =
      (rawCompileInstr N (RawEncoding.eraseInstr i)).flatMap RawEncoding.Instruction.encode := by
  rw [bodyCode,(instrRecipe_valid N i).2,rawInstr_instrRecipe]

lemma sourceCode_verifier (V : Verifier gatesHP) :
    sourceCode V.proofQubits V.ancillaQubits V.output.val
      (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits))) = V.encode := by
  simp only [sourceCode,sourceHeader,sourceBody,List.flatMap_map,Function.comp_def,
    rawInstr_instrRecipe,RawEncoding.eraseInstr_encode,List.length_map]
  simp only [Verifier.encode,encodeGates,List.append_assoc]

lemma targetCode_verifier (V : Verifier gatesHP) :
    targetCode V.proofQubits V.ancillaQubits V.output.val
      (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits))) = (compileVerifier V).encode := by
  calc
    _ = (rawCompile (RawEncoding.eraseVerifier V)).encode := by
      simp only [targetCode,targetHeader,sourceHeader,targetCount,targetBody,List.map_map,
        List.flatMap_map,Function.comp_def,instrRecipe_count,instrRecipe_bodyCode,
        rawCompile,RawEncoding.eraseVerifier,RawEncoding.Circuit.encode,List.length_flatMap,
        List.flatMap_assoc,List.append_assoc]
    _ = _ := by rw [rawCompile_erase,RawEncoding.eraseVerifier_encode]

noncomputable def timePolynomial : Polynomial ℕ := 10000*(Polynomial.X+1)^2

noncomputable def outputs_verifier (V : Verifier gatesHP) :
    TM2OutputsInTime machine V.encode (some (executableCompile V.encode)) (timePolynomial.eval V.encode.length) where
  steps := fullTime V.proofQubits V.ancillaQubits V.output.val
    (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits)))
  evals_in_steps := by
    rw [executableCompile_encode,← targetCode_verifier V,← sourceCode_verifier V]
    exact full_run _ _ _ _ (by
      intro r hr
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
      exact instrRecipe_valid _ i)
  steps_le_m := by
    have h := fullTime_bound V.proofQubits V.ancillaQubits V.output.val
      (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits)))
      (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr; exact instrRecipe_valid _ i)
    simpa only [sourceCode_verifier,timePolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using h



end QMAPerfectCompleteness.Main.DyadicCompiler.TM


