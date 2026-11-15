-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
-- name    : QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:56:32.786218+00:00
-- url     : https://prove2.me/theorems/3857e9e0-a727-4139-aecc-b1b55a0f9d3f
-- title:
--   A finite-plan unary gate compiler
-- statement:
--   Defines a finite machine for four source gate kinds, three source address fields and a captured total-wire counter. Literal output plans may emit bits, copied unary addresses and gate-count increments; the retained execution lemmas establish complete valid-code compilation and polynomial runtime.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/FinitePlanCompilerTM.lean, retained declaration span lines 11–1078.

/- Generated from Solutions.FinitePlanCompilerTM by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
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



/-! Parametric finite-plan unary gate compiler with four source kinds, three source address
slots, and a captured global wire-count slot. -/
set_option backward.isDefEq.respectTransparency false
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.FinitePlanCompiler
open QAlgorithms.Complexity (Str encNat)

inductive Token where
  | bit : Bool → Token
  | addr : Fin 4 → Token
  | count : Token
  deriving DecidableEq, Fintype

structure Config where
  plan : Fin 4 → List Token
  headerOffset : Fin 3 → ℕ
  plan_bound : ∀ kind, (plan kind).length < 2048

open Fin.NatCast in
@[simp high] lemma fin4_natCast_one : (Nat.cast 1 : Fin 4) = 1 := by decide
@[simp high] lemma fin4_ofNat_one : Fin.ofNat 4 1 = 1 := by decide
@[simp high] lemma fin4_ofNat_two : Fin.ofNat 4 2 = 2 := by decide

inductive Label where
  | headerStart : Fin 3 → Label
  | header : Fin 3 → Label
  | discardCount : Label
  | gate : Label
  | tag : Fin 4 → Label
  | read : Fin 4 → Fin 4 → Label
  | emit : Fin 4 → Fin 2048 → Label
  | copy : Fin 4 → Fin 2048 → Fin 4 → Bool → Label
  | clear : Fin 4 → Label
  | finish : Fin 3 → Label
  deriving DecidableEq, Fintype

def addrKey (j : Fin 4) : Fin 10 := ⟨j.val+2,by have := j.isLt; omega⟩
def arity (kind : Fin 4) : ℕ := if kind = 0 then 1 else if kind = 2 then 3 else 2

def nextRead (kind : Fin 4) (j : Fin 4) : Label :=
  if j.val+1 < arity kind then .read kind (Fin.ofNat 4 (j.val+1)) else .emit kind 0

def nextEmit (i : Fin 2048) : Fin 2048 := Fin.ofNat 2048 (i.val+1)

abbrev machine (C : Config) : FinTM2 where
  K := Fin 10
  k₀ := 0
  k₁ := 9
  Γ _ := Bool
  Λ := Label
  main := .headerStart 0
  σ := Option Bool
  initialState := none
  m l := match l with
    | .headerStart j => Statement.pushMany 1 (List.replicate (C.headerOffset j) true) (.goto (fun _ => .header j))
    | .header j => .peek 0 (fun _ a => a)
      (.pop 0 (fun v _ => v) (.push 1 (fun v => v.getD false)
        (.branch (fun v => v.getD false)
          (if j.val < 2 then .push (addrKey 3) (fun _ => true) (.goto (fun _ => .header j))
            else .goto (fun _ => .header j))
          (.goto (fun _ => if j.val < 2 then .headerStart (Fin.ofNat 3 (j.val+1)) else .discardCount)))))
    | .discardCount => .peek 0 (fun _ a => a)
      (.pop 0 (fun v _ => v) (.branch (fun v => v.getD false)
        (.goto (fun _ => .discardCount)) (.goto (fun _ => .gate))))
    | .gate => .peek 0 (fun _ a => a)
      (.branch Option.isSome (.goto (fun _ => .tag 0)) (.goto (fun _ => .clear 3)))
    | .tag kind => .peek 0 (fun _ a => a)
      (.pop 0 (fun v _ => v) (.branch (fun v => v.getD false)
        (.goto (fun _ => .tag (Fin.ofNat 4 (kind.val+1))))
        (.goto (fun _ => .read kind 0))))
    | .read kind j => .peek 0 (fun _ a => a)
      (.pop 0 (fun v _ => v) (.branch (fun v => v.getD false)
        (.push (addrKey j) (fun _ => true) (.goto (fun _ => .read kind j)))
        (.goto (fun _ => nextRead kind j))))
    | .emit kind i => match (C.plan kind)[i.val]? with
      | none => .load (fun _ => none) (.goto (fun _ => .clear 0))
      | some (.bit b) => .load (fun _ => none) (.push 8 (fun _ => b) (.goto (fun _ => .emit kind (nextEmit i))))
      | some .count => .load (fun _ => none) (.push 7 (fun _ => true) (.goto (fun _ => .emit kind (nextEmit i))))
      | some (.addr j) => .load (fun _ => none) (.goto (fun _ => .copy kind i j false))
    | .copy kind i j false => .peek (addrKey j) (fun _ a => a)
      (.branch Option.isSome
        (.pop (addrKey j) (fun v _ => v) (.push 6 (fun _ => true)
          (.push 8 (fun _ => true) (.goto (fun _ => .copy kind i j false)))))
        (.push 8 (fun _ => false) (.goto (fun _ => .copy kind i j true))))
    | .copy kind i j true => .peek 6 (fun _ a => a)
      (.branch Option.isSome
        (.pop 6 (fun v _ => v) (.push (addrKey j) (fun _ => true)
          (.goto (fun _ => .copy kind i j true))))
        (.goto (fun _ => .emit kind (nextEmit i))))
    | .clear j => .peek (addrKey j) (fun _ a => a)
      (.branch Option.isSome
        (.pop (addrKey j) (fun v _ => v) (.goto (fun _ => .clear j)))
        (.goto (fun _ => if j.val < 2 then .clear (Fin.ofNat 4 (j.val+1)) else if j.val = 2 then .gate else .finish 0)))
    | .finish j =>
      let key := if j.val = 0 then (8 : Fin 10) else if j.val = 1 then 7 else 1
      .peek key (fun _ a => a)
        (.branch Option.isSome
          (.pop key (fun v _ => v) (.push 9 (fun v => v.getD false) (.goto (fun _ => .finish j))))
          (if j.val = 0 then .push 9 (fun _ => false) (.goto (fun _ => .finish 1))
            else if j.val = 1 then .goto (fun _ => .finish 2)
            else .load (fun _ => none) .halt))

structure Data where
  input : Str := []
  header : Str := []
  wires : Fin 4 → Str := fun _ => []
  tmp : Str := []
  count : Str := []
  body : Str := []
  output : Str := []

def Data.stacks (d : Data) : Fin 10 → Str :=
  ![d.input,d.header,d.wires 0,d.wires 1,d.wires 2,d.wires 3,d.tmp,d.count,d.body,d.output]

variable (C : Config)

def cfg (C : Config) (l : Label) (v : Option Bool) (d : Data) : (machine C).Cfg := ⟨some l,v,d.stacks⟩



lemma read_true_step (kind : Fin 4) (j : Fin 4) (v : Option Bool) (d : Data) (s : Str) :
    (machine C).step (cfg C (.read kind j) v {d with input := true::s}) =
      some (cfg C (.read kind j) (some true)
        {d with input := s,wires := Function.update d.wires j (true::d.wires j)}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals
    funext k
    fin_cases k <;> simp

lemma read_false_step (kind : Fin 4) (j : Fin 4) (v : Option Bool) (d : Data) (s : Str) :
    (machine C).step (cfg C (.read kind j) v {d with input := false::s}) =
      some (cfg C (nextRead kind j) (some false) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma read_run (kind : Fin 4) (j : Fin 4) (v : Option Bool) (d : Data) (w : ℕ) (tail : Str) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      (some (cfg C (.read kind j) v {d with input := encNat w++tail})) =
      some (cfg C (nextRead kind j) (some false)
        {d with input := tail,wires := Function.update d.wires j (List.replicate w true++d.wires j)}) := by
  induction w generalizing v d with
  | zero =>
    simpa [encNat] using read_false_step C kind j v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      ((machine C).step (cfg C (.read kind j) v {d with input := true::(encNat w++tail)})) = _
    rw [read_true_step C]
    have hrep : List.replicate w true ++ true::d.wires j =
        List.replicate (w+1) true ++ d.wires j := by
      rw [List.replicate_add]
      simp
    simpa only [Function.update_self,Function.update_idem,hrep] using
      ih (some true) {d with wires := Function.update d.wires j (true::d.wires j)}


lemma copy_scan_true_step (kind : Fin 4) (i : Fin 2048) (j : Fin 4) (v : Option Bool)
    (d : Data) (s : Str) :
    (machine C).step (cfg C (.copy kind i j false) v
      {d with wires := Function.update d.wires j (true::s)}) =
      some (cfg C (.copy kind i j false) (some true)
        {d with wires := Function.update d.wires j s,tmp := true::d.tmp,body := true::d.body}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals
    funext k
    fin_cases k <;> simp

lemma copy_scan_nil_step (kind : Fin 4) (i : Fin 2048) (j : Fin 4) (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.copy kind i j false) v {d with wires := Function.update d.wires j []}) =
      some (cfg C (.copy kind i j true) none
        {d with wires := Function.update d.wires j [],body := false::d.body}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals
    funext k
    fin_cases k <;> simp

lemma copy_restore_true_step (kind : Fin 4) (i : Fin 2048) (j : Fin 4) (v : Option Bool)
    (d : Data) (s : Str) :
    (machine C).step (cfg C (.copy kind i j true) v {d with tmp := true::s}) =
      some (cfg C (.copy kind i j true) (some true)
        {d with tmp := s,wires := Function.update d.wires j (true::d.wires j)}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]
  all_goals
    funext k
    fin_cases k <;> simp

lemma copy_restore_nil_step (kind : Fin 4) (i : Fin 2048) (j : Fin 4) (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.copy kind i j true) v {d with tmp := []}) =
      some (cfg C (.emit kind (nextEmit i)) none {d with tmp := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,addrKey,TM2.stepAux]

lemma copy_scan_run (kind : Fin 4) (i : Fin 2048) (j : Fin 4) (v : Option Bool)
    (d : Data) (w : ℕ) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      (some (cfg C (.copy kind i j false) v {d with wires := Function.update d.wires j (List.replicate w true)})) =
      some (cfg C (.copy kind i j true) none
        {d with wires := Function.update d.wires j [],tmp := List.replicate w true++d.tmp,body := false::(List.replicate w true++d.body)}) := by
  induction w generalizing v d with
  | zero => simpa using copy_scan_nil_step C kind i j v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      ((machine C).step (cfg C (.copy kind i j false) v
        {d with wires := Function.update d.wires j (true::List.replicate w true)})) = _
    rw [copy_scan_true_step C]
    have ht : List.replicate w true ++ true::d.tmp = List.replicate (w+1) true++d.tmp := by
      rw [List.replicate_add]; simp
    have hb : List.replicate w true ++ true::d.body = List.replicate (w+1) true++d.body := by
      rw [List.replicate_add]; simp
    simpa only [Function.update_idem,ht,hb] using ih (some true)
      {d with tmp := true::d.tmp,body := true::d.body}

lemma copy_restore_run (kind : Fin 4) (i : Fin 2048) (j : Fin 4) (v : Option Bool)
    (d : Data) (w : ℕ) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      (some (cfg C (.copy kind i j true) v {d with tmp := List.replicate w true})) =
      some (cfg C (.emit kind (nextEmit i)) none
        {d with tmp := [],wires := Function.update d.wires j (List.replicate w true++d.wires j)}) := by
  induction w generalizing v d with
  | zero => simpa using copy_restore_nil_step C kind i j v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      ((machine C).step (cfg C (.copy kind i j true) v {d with tmp := true::List.replicate w true})) = _
    rw [copy_restore_true_step C]
    have hr : List.replicate w true ++ true::d.wires j = List.replicate (w+1) true++d.wires j := by
      rw [List.replicate_add]; simp
    simpa only [Function.update_self,Function.update_idem,hr] using ih (some true)
      {d with wires := Function.update d.wires j (true::d.wires j)}

/-- Copy one unary wire address to the reverse output buffer while restoring its source stack. -/
lemma copy_address_run (kind : Fin 4) (i : Fin 2048) (j : Fin 4) (v : Option Bool)
    (d : Data) (w : ℕ) (hw : d.wires j = List.replicate w true) (htmp : d.tmp = []) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[2*w+2]
      (some (cfg C (.copy kind i j false) v d)) =
      some (cfg C (.emit kind (nextEmit i)) none {d with body := (encNat w).reverse++d.body}) := by
  have hd : {d with wires := Function.update d.wires j (List.replicate w true)} = d := by
    rw [← hw,Function.update_eq_self]
  have hs := copy_scan_run C kind i j v d w
  rw [hd] at hs
  rw [show 2*w+2 = (w+1)+(w+1) by omega,Function.iterate_add_apply,hs]
  simp only [htmp,List.append_nil]
  have hr := copy_restore_run C kind i j none
    {d with wires := Function.update d.wires j [],body := false::(List.replicate w true++d.body)} w
  have hu : Function.update d.wires j (List.replicate w true) = d.wires := by
    rw [← hw,Function.update_eq_self]
  simpa only [Function.update_self,Function.update_idem,List.nil_append,List.append_nil,hu,
    encNat,List.reverse_append,List.reverse_singleton,List.reverse_replicate,
    List.singleton_append,List.cons_append,htmp] using hr



def nextClear (j : Fin 4) : Label :=
  if j.val < 2 then .clear (Fin.ofNat 4 (j.val+1)) else if j.val = 2 then .gate else .finish 0

lemma discard_true_step (v : Option Bool) (d : Data) (s : Str) :
    (machine C).step (cfg C .discardCount v {d with input := true::s}) =
      some (cfg C .discardCount (some true) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma discard_false_step (v : Option Bool) (d : Data) (s : Str) :
    (machine C).step (cfg C .discardCount v {d with input := false::s}) =
      some (cfg C .gate (some false) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma discard_run (v : Option Bool) (d : Data) (w : ℕ) (tail : Str) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      (some (cfg C .discardCount v {d with input := encNat w++tail})) =
      some (cfg C .gate (some false) {d with input := tail}) := by
  induction w generalizing v d with
  | zero => simpa [encNat] using discard_false_step C v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      ((machine C).step (cfg C .discardCount v {d with input := true::(encNat w++tail)})) = _
    rw [discard_true_step C]
    exact ih (some true) d

lemma clear_true_step (j : Fin 4) (v : Option Bool) (d : Data) (s : Str) :
    (machine C).step (cfg C (.clear j) v {d with wires := Function.update d.wires j (true::s)}) =
      some (cfg C (.clear j) (some true) {d with wires := Function.update d.wires j s}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,addrKey]
  all_goals
    funext k
    fin_cases k <;> simp

lemma clear_nil_step (j : Fin 4) (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.clear j) v {d with wires := Function.update d.wires j []}) =
      some (cfg C (nextClear j) none {d with wires := Function.update d.wires j []}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,addrKey,nextClear]

lemma clear_run (j : Fin 4) (v : Option Bool) (d : Data) (w : ℕ) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      (some (cfg C (.clear j) v {d with wires := Function.update d.wires j (List.replicate w true)})) =
      some (cfg C (nextClear j) none {d with wires := Function.update d.wires j []}) := by
  induction w generalizing v d with
  | zero => simpa using clear_nil_step C j v d
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      ((machine C).step (cfg C (.clear j) v {d with wires := Function.update d.wires j (true::List.replicate w true)})) = _
    rw [clear_true_step C]
    exact ih (some true) d


def tokenBits (a : Fin 4 → ℕ) : Token → Str
  | .bit b => [b]
  | .addr j => encNat (a j)
  | .count => []

def tokenCount : Token → ℕ
  | .count => 1
  | _ => 0

def tokenCost (a : Fin 4 → ℕ) : Token → ℕ
  | .addr j => 2*a j+3
  | _ => 1

def execToken (a : Fin 4 → ℕ) (t : Token) (d : Data) : Data :=
  {d with body := (tokenBits a t).reverse++d.body,count := List.replicate (tokenCount t) true++d.count}

def execTokens (a : Fin 4 → ℕ) : List Token → Data → Data
  | [],d => d
  | t::ts,d => execTokens a ts (execToken a t d)




lemma emit_bit_step (kind : Fin 4) (i : Fin 2048) (b : Bool) (h : (C.plan kind)[i.val]? = some (.bit b))
    (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.emit kind i) v d) =
      some (cfg C (.emit kind (nextEmit i)) none {d with body := b::d.body}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,h]
  funext k
  fin_cases k <;> simp

lemma emit_count_step (kind : Fin 4) (i : Fin 2048) (h : (C.plan kind)[i.val]? = some .count)
    (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.emit kind i) v d) =
      some (cfg C (.emit kind (nextEmit i)) none {d with count := true::d.count}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,h]
  funext k
  fin_cases k <;> simp

lemma emit_addr_step (kind : Fin 4) (i : Fin 2048) (j : Fin 4) (h : (C.plan kind)[i.val]? = some (.addr j))
    (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.emit kind i) v d) = some (cfg C (.copy kind i j false) none d) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,h]

lemma emit_none_step (kind : Fin 4) (i : Fin 2048) (h : (C.plan kind)[i.val]? = none)
    (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.emit kind i) v d) = some (cfg C (.clear 0) none d) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,h]

lemma emit_token_run (kind : Fin 4) (i : Fin 2048) (t : Token) (h : (C.plan kind)[i.val]? = some t)
    (v : Option Bool) (d : Data) (a : Fin 4 → ℕ)
    (hw : ∀ j, d.wires j = List.replicate (a j) true) (htmp : d.tmp = []) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[tokenCost a t]
      (some (cfg C (.emit kind i) v d)) =
      some (cfg C (.emit kind (nextEmit i)) none (execToken a t d)) := by
  cases t with
  | bit b =>
    change (machine C).step (cfg C (.emit kind i) v d) = _
    simpa only [execToken,tokenBits,tokenCount,List.reverse_singleton,List.singleton_append,
      List.replicate_zero,List.nil_append] using emit_bit_step C kind i b h v d
  | count =>
    change (machine C).step (cfg C (.emit kind i) v d) = _
    simpa only [execToken,tokenBits,tokenCount,List.reverse_nil,List.nil_append,
      List.replicate_one,List.singleton_append] using emit_count_step C kind i h v d
  | addr j =>
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[2*a j+3] _ = _
    rw [show 2*a j+3 = (2*a j+2)+1 by omega,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[2*a j+2]
      ((machine C).step (cfg C (.emit kind i) v d)) = _
    rw [emit_addr_step C kind i j h,copy_address_run C kind i j none d (a j) (hw j) htmp]
    rfl


lemma emit_suffix_run (kind : Fin 4) (ts : List Token) :
    ∀ (pre : List Token) (hp : C.plan kind = pre++ts) (i : Fin 2048) (hi : i.val = pre.length)
      (v : Option Bool) (d : Data) (a : Fin 4 → ℕ)
      (hw : ∀ j, d.wires j = List.replicate (a j) true) (htmp : d.tmp = []),
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[(ts.map (tokenCost a)).sum+1]
      (some (cfg C (.emit kind i) v d)) =
      some (cfg C (.clear 0) none (execTokens a ts d)) := by
  induction ts with
  | nil =>
    intro pre hp i hi v d a hw htmp
    change (machine C).step (cfg C (.emit kind i) v d) = _
    apply emit_none_step C
    rw [hi,show C.plan kind = pre by simpa using hp]
    simp
  | cons t ts ih =>
    intro pre hp i hi v d a hw htmp
    have hget : (C.plan kind)[i.val]? = some t := by
      rw [hi,hp,List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hn : (nextEmit i).val = (pre++[t]).length := by
      have hb := C.plan_bound kind
      rw [hp,List.length_append,List.length_cons] at hb
      simp only [nextEmit,Fin.val_ofNat,List.length_append,List.length_singleton]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [List.map_cons,List.sum_cons]
    rw [show tokenCost a t+(ts.map (tokenCost a)).sum+1 =
        ((ts.map (tokenCost a)).sum+1)+tokenCost a t by omega,
      Function.iterate_add_apply,emit_token_run C kind i t hget v d a hw htmp]
    exact ih (pre++[t]) (by simpa only [List.append_assoc,List.singleton_append] using hp)
      (nextEmit i) hn none (execToken a t d) a hw htmp

lemma emit_plan_run (kind : Fin 4) (v : Option Bool) (d : Data) (a : Fin 4 → ℕ)
    (hw : ∀ j, d.wires j = List.replicate (a j) true) (htmp : d.tmp = []) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[((C.plan kind).map (tokenCost a)).sum+1]
      (some (cfg C (.emit kind 0) v d)) =
      some (cfg C (.clear 0) none (execTokens a (C.plan kind) d)) :=
  emit_suffix_run C kind (C.plan kind) [] rfl 0 rfl v d a hw htmp

lemma execTokens_effect (a : Fin 4 → ℕ) (ts : List Token) (d : Data) :
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


lemma clear_actual_run (j : Fin 4) (v : Option Bool) (d : Data) (w : ℕ)
    (hw : d.wires j = List.replicate w true) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[w+1]
      (some (cfg C (.clear j) v d)) =
      some (cfg C (nextClear j) none {d with wires := Function.update d.wires j []}) := by
  have hd : {d with wires := Function.update d.wires j (List.replicate w true)} = d := by
    rw [← hw,Function.update_eq_self]
  have h := clear_run C j v d w
  rwa [hd] at h

lemma finish_body_cons (v : Option Bool) (d : Data) (b : Bool) (s : Str) :
    (machine C).step (cfg C (.finish 0) v {d with body := b::s}) =
      some (cfg C (.finish 0) (some b) {d with body := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_body_nil (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.finish 0) v {d with body := []}) =
      some (cfg C (.finish 1) none {d with body := [],output := false::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_count_cons (v : Option Bool) (d : Data) (b : Bool) (s : Str) :
    (machine C).step (cfg C (.finish 1) v {d with count := b::s}) =
      some (cfg C (.finish 1) (some b) {d with count := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_count_nil (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.finish 1) v {d with count := []}) =
      some (cfg C (.finish 2) none {d with count := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma finish_header_cons (v : Option Bool) (d : Data) (b : Bool) (s : Str) :
    (machine C).step (cfg C (.finish 2) v {d with header := b::s}) =
      some (cfg C (.finish 2) (some b) {d with header := s,output := b::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma finish_header_nil (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.finish 2) v {d with header := []}) =
      some (⟨none,none,({d with header := []} : Data).stacks⟩ : (machine C).Cfg) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma finish_body_run (v : Option Bool) (d : Data) (s : Str) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[s.length+1]
      (some (cfg C (.finish 0) v {d with body := s})) =
      some (cfg C (.finish 1) none {d with body := [],output := false::(s.reverse++d.output)}) := by
  induction s generalizing v d with
  | nil => simpa using finish_body_nil C v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[s.length+1]
      ((machine C).step (cfg C (.finish 0) v {d with body := b::s})) = _
    rw [finish_body_cons C]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (some b) {d with output := b::d.output}

lemma finish_count_run (v : Option Bool) (d : Data) (s : Str) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[s.length+1]
      (some (cfg C (.finish 1) v {d with count := s})) =
      some (cfg C (.finish 2) none {d with count := [],output := s.reverse++d.output}) := by
  induction s generalizing v d with
  | nil => simpa using finish_count_nil C v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[s.length+1]
      ((machine C).step (cfg C (.finish 1) v {d with count := b::s})) = _
    rw [finish_count_cons C]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (some b) {d with output := b::d.output}

lemma finish_header_run (v : Option Bool) (d : Data) (s : Str) :
    (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[s.length+1]
      (some (cfg C (.finish 2) v {d with header := s})) =
      some (⟨none,none,({d with header := [],output := s.reverse++d.output} : Data).stacks⟩ : (machine C).Cfg) := by
  induction s generalizing v d with
  | nil => simpa using finish_header_nil C v d
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine C).Cfg => o.bind (machine C).step)^[s.length+1]
      ((machine C).step (cfg C (.finish 2) v {d with header := b::s})) = _
    rw [finish_header_cons C]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (some b) {d with output := b::d.output}





def nextHeader (j : Fin 3) : Label :=
  if j.val < 2 then .headerStart (Fin.ofNat 3 (j.val+1)) else .discardCount

def capture (j : Fin 3) (w : ℕ) (u : Fin 4 → Str) : Fin 4 → Str :=
  if j.val < 2 then Function.update u 3 (List.replicate w true++u 3) else u

@[simp] lemma capture_zero (j : Fin 3) (u : Fin 4 → Str) : capture j 0 u = u := by
  simp [capture]

lemma replicate_cons (w : ℕ) (s : Str) :
    List.replicate w true++true::s = List.replicate (w+1) true++s := by
  rw [List.replicate_add]
  simp

lemma capture_succ (j : Fin 3) (w : ℕ) (u : Fin 4 → Str) :
    capture j w (capture j 1 u) = capture j (w+1) u := by
  by_cases hj : j.val < 2
  · simp [capture,hj,Function.update_idem,replicate_cons]
  · simp [capture,hj]

lemma header_start_step (j : Fin 3) (v : Option Bool) (d : Data) :
    (machine C).step (cfg C (.headerStart j) v d) =
      some (cfg C (.header j) v {d with header := List.replicate (C.headerOffset j) true++d.header}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
  funext k
  fin_cases k <;> simp

lemma header_true_step (j : Fin 3) (v : Option Bool) (d : Data) (s : Str) :
    (machine C).step (cfg C (.header j) v {d with input := true::s}) =
      some (cfg C (.header j) (some true)
        {d with input := s,header := true::d.header,wires := capture j 1 d.wires}) := by
  fin_cases j <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,capture,addrKey]
  all_goals
    funext k
    fin_cases k <;> simp

lemma header_false_step (j : Fin 3) (v : Option Bool) (d : Data) (s : Str) :
    (machine C).step (cfg C (.header j) v {d with input := false::s}) =
      some (cfg C (nextHeader j) (some false) {d with input := s,header := false::d.header}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,nextHeader]
  funext k
  fin_cases k <;> simp

lemma header_run (j : Fin 3) (v : Option Bool) (d : Data) (w : ℕ) (tail : Str) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[w+1]
      (some (cfg C (.header j) v {d with input := encNat w++tail})) =
      some (cfg C (nextHeader j) (some false)
        {d with input := tail,header := (encNat w).reverse++d.header,wires := capture j w d.wires}) := by
  induction w generalizing v d with
  | zero =>
    change (machine C).step (cfg C (.header j) v {d with input := encNat 0++tail}) = _
    simpa only [encNat,List.replicate_zero,List.nil_append,List.reverse_singleton,
      List.singleton_append,capture_zero] using header_false_step C j v d tail
  | succ w ih =>
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[w+1]
      ((machine C).step (cfg C (.header j) v {d with input := true::(encNat w++tail)})) = _
    rw [header_true_step C]
    have hr : (encNat w).reverse++true::d.header = (encNat (w+1)).reverse++d.header := by
      simpa only [encNat,List.reverse_append,List.reverse_singleton,List.reverse_replicate,
        List.singleton_append,List.cons_append,List.nil_append] using congrArg (List.cons false) (replicate_cons w d.header)
    simpa only [hr,capture_succ] using ih (some true)
      {d with header := true::d.header,wires := capture j 1 d.wires}

lemma header_offset_run (j : Fin 3) (v : Option Bool) (d : Data) (w : ℕ) (tail : Str) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[w+2]
      (some (cfg C (.headerStart j) v {d with input := encNat w++tail})) =
      some (cfg C (nextHeader j) (some false)
        {d with input := tail,header := (encNat (w+C.headerOffset j)).reverse++d.header,wires := capture j w d.wires}) := by
  rw [show w+2 = (w+1)+1 by omega,Function.iterate_succ_apply]
  change (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[w+1]
    ((machine C).step (cfg C (.headerStart j) v {d with input := encNat w++tail})) = _
  rw [header_start_step C]
  have h := header_run C j v {d with header := List.replicate (C.headerOffset j) true++d.header} w tail
  simpa only [encNat,List.reverse_append,List.reverse_singleton,List.reverse_replicate,
    List.singleton_append,List.cons_append,List.nil_append,← List.append_assoc,← List.replicate_add] using h




lemma gate_nil_step (v : Option Bool) (d : Data) :
    (machine C).step (cfg C .gate v {d with input := []}) =
      some (cfg C (.clear 3) none {d with input := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma gate_start_step (v : Option Bool) (d : Data) (xs : Str) (hxs : xs ≠ []) :
    (machine C).step (cfg C .gate v {d with input := xs}) =
      some (cfg C (.tag 0) xs.head? {d with input := xs}) := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons b xs => simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma tag_true_step (kind : Fin 4) (v : Option Bool) (d : Data) (tail : Str) :
    (machine C).step (cfg C (.tag kind) v {d with input := true::tail}) =
      some (cfg C (.tag (Fin.ofNat 4 (kind.val+1))) (some true) {d with input := tail}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma tag_false_step (kind : Fin 4) (v : Option Bool) (d : Data) (tail : Str) :
    (machine C).step (cfg C (.tag kind) v {d with input := false::tail}) =
      some (cfg C (.read kind 0) (some false) {d with input := tail}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  funext k
  fin_cases k <;> simp

lemma tag_unary_run (w : ℕ) : ∀ (kind : Fin 4) (hk : kind.val+w < 4)
    (v : Option Bool) (d : Data) (tail : Str),
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[w+1]
      (some (cfg C (.tag kind) v {d with input := encNat w++tail})) =
      some (cfg C (.read ⟨kind.val+w,hk⟩ 0) (some false) {d with input := tail}) := by
  induction w with
  | zero =>
    intro kind hk v d tail
    change (machine C).step (cfg C (.tag kind) v {d with input := false::tail}) = _
    simpa only [Nat.add_zero] using tag_false_step C kind v d tail
  | succ w ih =>
    intro kind hk v d tail
    rw [Nat.succ_add,Function.iterate_succ_apply]
    change (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[w+1]
      ((machine C).step (cfg C (.tag kind) v {d with input := true::(encNat w++tail)})) = _
    rw [tag_true_step C]
    have hn : (Fin.ofNat 4 (kind.val+1)).val = kind.val+1 := by
      rw [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega)]
    have h := ih (Fin.ofNat 4 (kind.val+1)) (by rw [hn]; omega) (some true) d tail
    have heq : (⟨kind.val+(w+1),hk⟩ : Fin 4) =
        ⟨(Fin.ofNat 4 (kind.val+1)).val+w,by rw [hn]; omega⟩ := by
      apply Fin.ext
      simp only [hn]
      omega
    simpa only [heq] using h

lemma tag_dispatch_run (kind : Fin 4) (v : Option Bool) (d : Data) (tail : Str) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[kind.val+2]
      (some (cfg C .gate v {d with input := encNat kind.val++tail})) =
      some (cfg C (.read kind 0) (some false) {d with input := tail}) := by
  rw [show kind.val+2 = (kind.val+1)+1 by omega,Function.iterate_succ_apply]
  change (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[kind.val+1]
    ((machine C).step (cfg C .gate v {d with input := encNat kind.val++tail})) = _
  rw [gate_start_step C v d _ (by
    intro h
    have := congrArg List.length h
    simp [encNat] at this)]
  simpa only [Fin.val_zero,Nat.zero_add] using tag_unary_run C kind.val 0 (by simpa using kind.isLt)
    (encNat kind.val++tail).head? d tail


def baseWires (N : ℕ) : Fin 4 → Str := fun j => if j = 3 then List.replicate N true else []

def rawInstr (kind : Fin 4) (a : Fin 4 → ℕ) : Main.RawEncoding.Instruction :=
  ⟨kind.val,if kind = 0 then [a 0] else if kind = 2 then [a 0,a 1,a 2] else [a 0,a 1]⟩

def sourceWires (kind : Fin 4) (a : Fin 4 → ℕ) : Str :=
  (rawInstr kind a).wires.flatMap encNat

def Valid (kind : Fin 4) (a : Fin 4 → ℕ) : Prop :=
  if kind = 0 then a 1 = 0 ∧ a 2 = 0 else if kind = 2 then True else a 2 = 0

def readTime (kind : Fin 4) (a : Fin 4 → ℕ) : ℕ :=
  if kind = 0 then a 0+1 else if kind = 2 then a 0+a 1+a 2+3 else a 0+a 1+2

def parseTime (kind : Fin 4) (a : Fin 4 → ℕ) : ℕ := readTime kind a+(kind.val+2)

lemma read_one_run (kind : Fin 4) (hk : arity kind = 1) (v : Option Bool)
    (d : Data) (a : Fin 4 → ℕ) (tail : Str) (hc : d.wires = baseWires (a 3))
    (h1 : a 1 = 0) (h2 : a 2 = 0) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[a 0+1]
      (some (cfg C (.read kind 0) v {d with input := encNat (a 0)++tail})) =
      some (cfg C (.emit kind 0) (some false)
        {d with input := tail,wires := fun j => List.replicate (a j) true}) := by
  rw [read_run C kind 0 v d (a 0) tail]
  simp only [nextRead,hk,Fin.val_zero,Nat.zero_add,lt_self_iff_false,ite_false]
  congr 1
  congr 2
  funext j
  fin_cases j <;> simp [hc,baseWires,h1,h2]

lemma read_two_run (kind : Fin 4) (hk : arity kind = 2) (v : Option Bool)
    (d : Data) (a : Fin 4 → ℕ) (tail : Str) (hc : d.wires = baseWires (a 3))
    (h2 : a 2 = 0) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[a 0+a 1+2]
      (some (cfg C (.read kind 0) v {d with input := encNat (a 0)++(encNat (a 1)++tail)})) =
      some (cfg C (.emit kind 0) (some false)
        {d with input := tail,wires := fun j => List.replicate (a j) true}) := by
  rw [show a 0+a 1+2 = (a 1+1)+(a 0+1) by omega,Function.iterate_add_apply,
    read_run C kind 0 v d (a 0) (encNat (a 1)++tail)]
  have hn : nextRead kind 0 = .read kind 1 := by simp [nextRead,hk]
  rw [hn,read_run C kind 1 (some false)
    {d with wires := Function.update d.wires 0 (List.replicate (a 0) true++d.wires 0)} (a 1) tail]
  simp only [nextRead,hk,Fin.val_one,lt_self_iff_false,ite_false]
  congr 1
  congr 2
  funext j
  fin_cases j <;> simp [hc,baseWires,h2]

lemma read_three_run (kind : Fin 4) (hk : arity kind = 3) (v : Option Bool)
    (d : Data) (a : Fin 4 → ℕ) (tail : Str) (hc : d.wires = baseWires (a 3)) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[a 0+a 1+a 2+3]
      (some (cfg C (.read kind 0) v {d with input := encNat (a 0)++(encNat (a 1)++(encNat (a 2)++tail))})) =
      some (cfg C (.emit kind 0) (some false)
        {d with input := tail,wires := fun j => List.replicate (a j) true}) := by
  rw [show a 0+a 1+a 2+3 = (a 2+1)+((a 1+1)+(a 0+1)) by omega,
    Function.iterate_add_apply _ (a 2+1) ((a 1+1)+(a 0+1)),Function.iterate_add_apply _ (a 1+1) (a 0+1),
    read_run C kind 0 v d (a 0) _]
  have hn0 : nextRead kind 0 = .read kind 1 := by simp [nextRead,hk]
  have hn1 : nextRead kind 1 = .read kind 2 := by simp [nextRead,hk]
  rw [hn0,read_run C kind 1 (some false)
    {d with wires := Function.update d.wires 0 (List.replicate (a 0) true++d.wires 0)} (a 1) _]
  rw [hn1,read_run C kind 2 (some false)
    {d with wires := Function.update (Function.update d.wires 0 (List.replicate (a 0) true++d.wires 0)) 1       (List.replicate (a 1) true++(Function.update d.wires 0 (List.replicate (a 0) true++d.wires 0)) 1)} (a 2) tail]
  have hn2 : nextRead kind 2 = .emit kind 0 := by simp [nextRead,hk]
  rw [hn2]
  congr 1
  congr 2
  funext j
  fin_cases j <;> simp [hc,baseWires]

lemma parse_gate_run (kind : Fin 4) (v : Option Bool) (d : Data) (a : Fin 4 → ℕ) (tail : Str)
    (hc : d.wires = baseWires (a 3)) (hz : Valid kind a) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[parseTime kind a]
      (some (cfg C .gate v {d with input := (rawInstr kind a).encode++tail})) =
      some (cfg C (.emit kind 0) (some false)
        {d with input := tail,wires := fun j => List.replicate (a j) true}) := by
  rw [parseTime,Function.iterate_add_apply]
  have he : (rawInstr kind a).encode++tail = encNat kind.val++(sourceWires kind a++tail) := by
    simp [Main.RawEncoding.Instruction.encode,sourceWires,rawInstr,List.append_assoc]
  rw [he,tag_dispatch_run C kind v d (sourceWires kind a++tail)]
  fin_cases kind
  · simpa [sourceWires,rawInstr,readTime,List.append_assoc] using read_one_run C 0 rfl (some false) d a tail hc hz.1 hz.2
  · simpa [sourceWires,rawInstr,readTime,List.append_assoc] using read_two_run C 1 rfl (some false) d a tail hc hz
  · simpa [sourceWires,rawInstr,readTime,List.append_assoc] using read_three_run C 2 rfl (some false) d a tail hc
  · simpa [sourceWires,rawInstr,readTime,List.append_assoc] using read_two_run C 3 rfl (some false) d a tail hc hz


def bodyCode (kind : Fin 4) (a : Fin 4 → ℕ) : Str := (C.plan kind).flatMap (tokenBits a)
def gateCount (kind : Fin 4) : ℕ := ((C.plan kind).map tokenCount).sum
def gateTime (kind : Fin 4) (a : Fin 4 → ℕ) : ℕ :=
  parseTime kind a+(((C.plan kind).map (tokenCost a)).sum+1)+(a 0+a 1+a 2+3)

lemma exec_plan_effect (kind : Fin 4) (a : Fin 4 → ℕ) (d : Data) :
    execTokens a (C.plan kind) d =
      {d with body := (bodyCode C kind a).reverse++d.body,count := List.replicate (gateCount C kind) true++d.count} := by
  rw [execTokens_effect]
  rfl

lemma clear_sources_run (a : Fin 4 → ℕ) (v : Option Bool) (d : Data)
    (hw : ∀ j, d.wires j = List.replicate (a j) true) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[a 0+a 1+a 2+3]
      (some (cfg C (.clear 0) v d)) =
      some (cfg C .gate none {d with wires := baseWires (a 3)}) := by
  rw [show a 0+a 1+a 2+3 = (a 2+1)+((a 1+1)+(a 0+1)) by omega,
    Function.iterate_add_apply _ (a 2+1) ((a 1+1)+(a 0+1)),
    Function.iterate_add_apply _ (a 1+1) (a 0+1),clear_actual_run C 0 v d (a 0) (hw 0)]
  change (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[a 2+1]
    ((fun q : Option (machine C).Cfg => q.bind (machine C).step)^[a 1+1]
      (some (cfg C (.clear 1) none {d with wires := Function.update d.wires 0 []}))) = _
  rw [clear_actual_run C 1 none _ (a 1) (by simpa using hw 1)]
  change (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[a 2+1]
    (some (cfg C (.clear 2) none {d with wires := Function.update (Function.update d.wires 0 []) 1 []})) = _
  rw [clear_actual_run C 2 none _ (a 2) (by simpa using hw 2)]
  congr 1
  congr 2
  funext j
  fin_cases j <;> simp [baseWires,hw]

lemma gate_run (kind : Fin 4) (v : Option Bool) (d : Data) (a : Fin 4 → ℕ) (tail : Str)
    (hc : d.wires = baseWires (a 3)) (htmp : d.tmp = []) (hz : Valid kind a) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[gateTime C kind a]
      (some (cfg C .gate v {d with input := (rawInstr kind a).encode++tail})) =
      some (cfg C .gate none {d with input := tail,body := (bodyCode C kind a).reverse++d.body,count := List.replicate (gateCount C kind) true++d.count}) := by
  rw [gateTime,show parseTime kind a+(((C.plan kind).map (tokenCost a)).sum+1)+(a 0+a 1+a 2+3) =
      (a 0+a 1+a 2+3)+((((C.plan kind).map (tokenCost a)).sum+1)+parseTime kind a) by omega,
    Function.iterate_add_apply _ (a 0+a 1+a 2+3) _,
    Function.iterate_add_apply _ (((C.plan kind).map (tokenCost a)).sum+1) _,
    parse_gate_run C kind v d a tail hc hz]
  rw [emit_plan_run C kind (some false) {d with input := tail,wires := fun j => List.replicate (a j) true}
    a (fun _ => rfl) htmp,exec_plan_effect C]
  simpa only [hc] using clear_sources_run C a none
    {d with input := tail,wires := fun j => List.replicate (a j) true,body := (bodyCode C kind a).reverse++d.body,count := List.replicate (gateCount C kind) true++d.count}
    (fun _ => rfl)

abbrev Recipe := Fin 4 × (Fin 4 → ℕ)
def Recipe.Valid (r : Recipe) : Prop := QMAPerfectCompleteness.Uniformity.FinitePlanCompiler.Valid r.1 r.2

def sourceBody (rs : List Recipe) : Str := rs.flatMap (fun r => (rawInstr r.1 r.2).encode)
def targetBody (rs : List Recipe) : Str := rs.flatMap (fun r => bodyCode C r.1 r.2)
def targetCount (rs : List Recipe) : ℕ := (rs.map (fun r => gateCount C r.1)).sum
def bodyTime (rs : List Recipe) : ℕ := (rs.map (fun r => gateTime C r.1 r.2)).sum

lemma body_run (N : ℕ) (rs : List Recipe) : ∀ (v : Option Bool) (d : Data) (tail : Str)
    (hc : d.wires = baseWires N) (htmp : d.tmp = []) (hv : ∀ r ∈ rs, r.Valid ∧ r.2 3 = N),
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[bodyTime C rs]
      (some (cfg C .gate v {d with input := sourceBody rs++tail})) =
      some (cfg C .gate (if rs = [] then v else none)
        {d with input := tail,body := (targetBody C rs).reverse++d.body,count := List.replicate (targetCount C rs) true++d.count}) := by
  induction rs with
  | nil => intro v d tail hc htmp hv; simp [bodyTime,sourceBody,targetBody,targetCount]
  | cons r rs ih =>
    intro v d tail hc htmp hv
    simp only [bodyTime,List.map_cons,List.sum_cons,sourceBody,List.flatMap_cons,List.append_assoc]
    rw [Nat.add_comm (gateTime C r.1 r.2),Function.iterate_add_apply]
    have hg := gate_run C r.1 v d r.2 (sourceBody rs++tail)
      (by rw [(hv r (by simp)).2]; exact hc) htmp (hv r (by simp)).1
    simp only [sourceBody] at hg
    rw [hg]
    have htail := ih none
      {d with body := (bodyCode C r.1 r.2).reverse++d.body,count := List.replicate (gateCount C r.1) true++d.count}
      tail hc htmp (fun q hq => hv q (by simp [hq]))
    simp only [bodyTime,sourceBody] at htail
    rw [htail]
    simp only [targetBody,List.flatMap_cons,List.reverse_append,List.append_assoc,
      targetCount,List.map_cons,List.sum_cons,List.cons_ne_nil,if_false,ite_self]
    have hcnt : List.replicate ((rs.map (fun q => gateCount C q.1)).sum) true++
        (List.replicate (gateCount C r.1) true++d.count) =
        List.replicate (gateCount C r.1+(rs.map (fun q => gateCount C q.1)).sum) true++d.count := by
      rw [← List.append_assoc,← List.replicate_add,Nat.add_comm]
    rw [hcnt]

lemma rawInstr_args_le (kind : Fin 4) (a : Fin 4 → ℕ) (hz : Valid kind a) :
    a 0+a 1+a 2 ≤ (rawInstr kind a).encode.length := by
  fin_cases kind <;> simp [Valid] at hz <;>
    simp [rawInstr,Main.RawEncoding.Instruction.encode,Main.Encoding.encNat_length] <;> omega

lemma parseTime_length (kind : Fin 4) (a : Fin 4 → ℕ) :
    parseTime kind a = (rawInstr kind a).encode.length+1 := by
  fin_cases kind <;> simp [parseTime,readTime,rawInstr,Main.RawEncoding.Instruction.encode,Main.Encoding.encNat_length] <;> omega

lemma arg_le (a : Fin 4 → ℕ) (j : Fin 4) : a j ≤ a 0+a 1+a 2+a 3 := by
  fin_cases j
  · change a 0 ≤ a 0+a 1+a 2+a 3; omega
  · change a 1 ≤ a 0+a 1+a 2+a 3; omega
  · change a 2 ≤ a 0+a 1+a 2+a 3; omega
  · change a 3 ≤ a 0+a 1+a 2+a 3; omega

lemma tokenCost_bound (a : Fin 4 → ℕ) (t : Token) :
    tokenCost a t ≤ 2*(a 0+a 1+a 2+a 3)+3 := by
  cases t with
  | addr j => have h := arg_le a j; simp only [tokenCost]; omega
  | bit b => simp only [tokenCost]; omega
  | count => simp only [tokenCost]; omega

lemma sum_map_le (ts : List Token) (f : Token → ℕ) (B : ℕ) (hf : ∀ t ∈ ts, f t ≤ B) :
    (ts.map f).sum ≤ ts.length*B := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht := hf t (by simp)
    have hi := ih (fun q hq => hf q (by simp [hq]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma plan_cost_bound (kind : Fin 4) (a : Fin 4 → ℕ) :
    ((C.plan kind).map (tokenCost a)).sum ≤ 2048*(2*(a 0+a 1+a 2+a 3)+3) := by
  exact (sum_map_le (C.plan kind) _ _ (fun t _ => tokenCost_bound a t)).trans
    (Nat.mul_le_mul_right _ (Nat.le_of_lt (C.plan_bound kind)))

lemma gateTime_bound (kind : Fin 4) (a : Fin 4 → ℕ) (hz : Valid kind a) :
    gateTime C kind a ≤ 10000*((rawInstr kind a).encode.length+a 3+1) := by
  have hp := plan_cost_bound C kind a
  have ha := rawInstr_args_le kind a hz
  rw [gateTime,parseTime_length]
  omega

lemma tokenBits_length_le (a : Fin 4 → ℕ) (t : Token) :
    (tokenBits a t).length ≤ tokenCost a t := by
  cases t <;> simp [tokenBits,tokenCost,Main.Encoding.encNat_length] <;> omega

lemma bodyCode_length_bound (kind : Fin 4) (a : Fin 4 → ℕ) (hz : Valid kind a) :
    (bodyCode C kind a).length ≤ 10000*((rawInstr kind a).encode.length+a 3+1) := by
  have hp := plan_cost_bound C kind a
  have ha := rawInstr_args_le kind a hz
  rw [bodyCode,List.length_flatMap]
  have hb : ((C.plan kind).map (fun t => (tokenBits a t).length)).sum ≤
      ((C.plan kind).map (tokenCost a)).sum := List.sum_le_sum (fun t _ => tokenBits_length_le a t)
  omega

lemma gateCount_bound (kind : Fin 4) : gateCount C kind ≤ 2048 := by
  have h := sum_map_le (C.plan kind) tokenCount 1 (fun t _ => by cases t <;> simp [tokenCount])
  simp only [Nat.mul_one] at h
  exact h.trans (Nat.le_of_lt (C.plan_bound kind))

lemma bodyTime_bound (N : ℕ) (rs : List Recipe) (hv : ∀ r ∈ rs, r.Valid ∧ r.2 3 = N) :
    bodyTime C rs ≤ 10000*((sourceBody rs).length+rs.length*(N+1)) := by
  induction rs with
  | nil => simp [bodyTime,sourceBody]
  | cons r rs ih =>
    have hg := gateTime_bound C r.1 r.2 (hv r (by simp)).1
    rw [(hv r (by simp)).2] at hg
    have hi := ih (fun q hq => hv q (by simp [hq]))
    simp only [bodyTime,List.map_cons,List.sum_cons,sourceBody,List.flatMap_cons,List.length_append,List.length_cons] at *
    have hm : (rs.length+1)*(N+1) = rs.length*(N+1)+(N+1) := by ring
    rw [hm]
    omega

lemma targetBody_length_bound (N : ℕ) (rs : List Recipe) (hv : ∀ r ∈ rs, r.Valid ∧ r.2 3 = N) :
    (targetBody C rs).length ≤ 10000*((sourceBody rs).length+rs.length*(N+1)) := by
  induction rs with
  | nil => simp [targetBody,sourceBody]
  | cons r rs ih =>
    have hg := bodyCode_length_bound C r.1 r.2 (hv r (by simp)).1
    rw [(hv r (by simp)).2] at hg
    have hi := ih (fun q hq => hv q (by simp [hq]))
    simp only [targetBody,sourceBody,List.flatMap_cons,List.length_append,List.length_cons] at *
    have hm : (rs.length+1)*(N+1) = rs.length*(N+1)+(N+1) := by ring
    rw [hm]
    omega

lemma targetCount_bound (rs : List Recipe) : targetCount C rs ≤ 2048*rs.length := by
  induction rs with
  | nil => simp [targetCount]
  | cons r rs ih =>
    have h := gateCount_bound C r.1
    simp only [targetCount,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

def sourceHeader (m a o : ℕ) : Str := encNat m++encNat a++encNat o
def headerDelta : ℕ := C.headerOffset 0+C.headerOffset 1+C.headerOffset 2
def targetHeader (m a o : ℕ) : Str :=
  sourceHeader (m+C.headerOffset 0) (a+C.headerOffset 1) (o+C.headerOffset 2)
def sourceCode (m a o : ℕ) (rs : List Recipe) : Str := sourceHeader m a o++encNat rs.length++sourceBody rs
def targetCode (m a o : ℕ) (rs : List Recipe) : Str :=
  targetHeader C m a o++encNat (targetCount C rs)++targetBody C rs

def fullTime (m a o : ℕ) (rs : List Recipe) : ℕ :=
  2*(sourceHeader m a o).length+rs.length+bodyTime C rs+(targetBody C rs).length+targetCount C rs+(m+a)+headerDelta C+9

lemma sourceHeader_length (m a o : ℕ) : (sourceHeader m a o).length = m+a+o+3 := by
  simp [sourceHeader,Main.Encoding.encNat_length]
  omega

lemma targetHeader_length (m a o : ℕ) : (targetHeader C m a o).length = (sourceHeader m a o).length+headerDelta C := by
  simp only [targetHeader,sourceHeader_length,headerDelta]
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
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[(sourceHeader m a o).length+3]
      (some (cfg C (.headerStart 0) none {input := sourceHeader m a o++tail})) =
      some (cfg C .discardCount (some false)
        {input := tail,header := (targetHeader C m a o).reverse,wires := baseWires (m+a)}) := by
  rw [show (sourceHeader m a o).length+3 = (o+2)+((a+2)+(m+2)) by rw [sourceHeader_length]; omega,
    Function.iterate_add_apply _ (o+2) ((a+2)+(m+2)),Function.iterate_add_apply _ (a+2) (m+2)]
  simp only [sourceHeader,List.append_assoc]
  rw [header_offset_run C 0 none {} m (encNat a++(encNat o++tail))]
  simp only [capture_first,List.append_nil]
  change (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[o+2]
    ((fun q : Option (machine C).Cfg => q.bind (machine C).step)^[a+2]
      (some (cfg C (.headerStart 1) (some false)
        {input := encNat a++(encNat o++tail),header := (encNat (m+C.headerOffset 0)).reverse,wires := baseWires m}))) = _
  rw [header_offset_run C 1 (some false) {header := (encNat (m+C.headerOffset 0)).reverse,wires := baseWires m} a (encNat o++tail)]
  simp only [capture_second]
  change (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[o+2]
    (some (cfg C (.headerStart 2) (some false)
      {input := encNat o++tail,header := (encNat (a+C.headerOffset 1)).reverse++(encNat (m+C.headerOffset 0)).reverse,wires := baseWires (m+a)})) = _
  rw [header_offset_run C 2 (some false)
    {header := (encNat (a+C.headerOffset 1)).reverse++(encNat (m+C.headerOffset 0)).reverse,wires := baseWires (m+a)} o tail]
  simp only [capture_third,targetHeader,sourceHeader,List.reverse_append,List.append_assoc]
  rfl

lemma finish_all_run (H B : Str) (N : ℕ) (v : Option Bool) :
    (fun q : Option (machine C).Cfg => q.bind (machine C).step)^[B.length+N+H.length+3]
      (some (cfg C (.finish 0) v {header := H.reverse,count := List.replicate N true,body := B.reverse})) =
      some (haltList (machine C) (H++encNat N++B)) := by
  rw [show B.length+N+H.length+3 = (H.reverse.length+1)+
      (((List.replicate N true).length+1)+(B.reverse.length+1)) by simp; omega,
    Function.iterate_add_apply _ (H.reverse.length+1) _,
    Function.iterate_add_apply _ ((List.replicate N true).length+1) _]
  rw [finish_body_run C v {header := H.reverse,count := List.replicate N true} B.reverse]
  simp only [List.reverse_reverse,List.append_nil]
  rw [finish_count_run C none {header := H.reverse,output := false::B} (List.replicate N true)]
  simp only [List.reverse_replicate]
  rw [finish_header_run C none {output := List.replicate N true++false::B} H.reverse]
  simp only [List.reverse_reverse,encNat,List.append_assoc,List.singleton_append]
  simp only [haltList,machine]
  congr 2
  funext k
  fin_cases k <;> rfl

abbrev transition : Option (machine C).Cfg → Option (machine C).Cfg := fun q => q.bind (machine C).step

lemma run_trans {n m : ℕ} {a b c : Option (machine C).Cfg}
    (hn : (transition C)^[n] a = b) (hm : (transition C)^[m] b = c) : (transition C)^[n+m] a = c := by
  rw [Nat.add_comm n m,Function.iterate_add_apply,hn,hm]

lemma full_run (m a o : ℕ) (rs : List Recipe)
    (hv : ∀ r ∈ rs, r.Valid ∧ r.2 3 = m+a) :
    (transition C)^[fullTime C m a o rs] (some (initList (machine C) (sourceCode m a o rs))) =
      some (haltList (machine C) (targetCode C m a o rs)) := by
  have hi : initList (machine C) (sourceCode m a o rs) = cfg C (.headerStart 0) none {input := sourceCode m a o rs} := by
    simp only [initList,cfg,machine,Data.stacks]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hh := header_all_run C m a o (encNat rs.length++sourceBody rs)
  have hd := discard_run C (some false) {header := (targetHeader C m a o).reverse,wires := baseWires (m+a)} rs.length (sourceBody rs)
  have hb := body_run C (m+a) rs (some false) {header := (targetHeader C m a o).reverse,wires := baseWires (m+a)} [] rfl rfl hv
  simp only [List.append_nil,List.nil_append] at hh hd hb
  have he := gate_nil_step C (if rs = [] then some false else none)
    {header := (targetHeader C m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount C rs) true,body := (targetBody C rs).reverse}
  change (transition C)^[1] (some (cfg C .gate (if rs = [] then some false else none)
    {header := (targetHeader C m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount C rs) true,body := (targetBody C rs).reverse})) = _ at he
  have hc := clear_actual_run C 3 none
    {header := (targetHeader C m a o).reverse,wires := baseWires (m+a),count := List.replicate (targetCount C rs) true,body := (targetBody C rs).reverse}
    (m+a) (by simp [baseWires])
  have hz : Function.update (baseWires (m+a)) 3 [] = fun _ => [] := by
    funext j
    fin_cases j <;> simp [baseWires]
  simp only [hz,nextClear,Fin.isValue,Fin.reduceFinMk,Fin.reduceEq,ite_false] at hc
  have hf := finish_all_run C (targetHeader C m a o) (targetBody C rs) (targetCount C rs) none
  have h := run_trans C (run_trans C (run_trans C (run_trans C (run_trans C hh hd) hb) he) hc) hf
  rw [hi]
  convert h using 1 <;> simp only [fullTime,sourceCode,targetCode,List.append_assoc,targetHeader_length C] <;> congr 1 <;> omega

lemma fullTime_bound (m a o : ℕ) (rs : List Recipe)
    (hv : ∀ r ∈ rs, r.Valid ∧ r.2 3 = m+a) :
    fullTime C m a o rs ≤ 100000*((sourceCode m a o rs).length+headerDelta C+1)^2 := by
  let L := (sourceCode m a o rs).length
  have hL : L = (sourceHeader m a o).length+(rs.length+1)+(sourceBody rs).length := by
    simp [L,sourceCode,Main.Encoding.encNat_length]
    omega
  have hH : (sourceHeader m a o).length ≤ L := by omega
  have hN : m+a ≤ L := by rw [sourceHeader_length] at hH; omega
  have hn : rs.length ≤ L := by omega
  have hB : (sourceBody rs).length ≤ L := by omega
  have hp := Nat.mul_le_mul hn (Nat.add_le_add_right hN 1)
  have ht := bodyTime_bound C (m+a) rs hv
  have hb := targetBody_length_bound C (m+a) rs hv
  have hc := targetCount_bound C rs
  change fullTime C m a o rs ≤ 100000*(L+headerDelta C+1)^2
  unfold fullTime
  nlinarith



end QMAPerfectCompleteness.Uniformity.FinitePlanCompiler


