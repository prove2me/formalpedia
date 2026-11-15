-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_FixedBlockCopy
-- name    : QMAPerfectCompleteness_Proof_FixedBlockCopy
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:53:43.498208+00:00
-- url     : https://prove2.me/theorems/d1626851-ac9d-4c9d-88bd-1485c194cbdf
-- title:
--   Fixed-count duplication of generated strings
-- statement:
--   Defines an explicit finite-machine continuation that duplicates a generated binary string a fixed number of times. The scan, copy and cleanup phases preserve word order, clear auxiliary stacks and supply a polynomial-time output-duplication construction.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/FixedBlockCopy.lean, retained declaration span lines 9–320.

/- Generated from Solutions.FixedBlockCopy by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
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



/-! Explicit fixed-count whole-block duplication, with a direct source-generator continuation. -/
set_option backward.isDefEq.respectTransparency false
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.BlockCopy
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

abbrev Keys (tm : FinTM2) := tm.K ⊕ Fin 2
abbrev Alphabet (tm : FinTM2) : Keys tm → Type := Sum.elim tm.Γ (fun _ => Bool)
abbrev Labels (tm : FinTM2) (n : ℕ) := tm.Λ ⊕ (Fin (n+1) × Bool)
abbrev Vars (tm : FinTM2) := tm.σ × Option Bool

/-- Lift a source statement into the combined machine, wiring each halt to the scan phase. -/
def liftStmt (tm : FinTM2) (n : ℕ) : TM2.Stmt tm.Γ tm.Λ tm.σ →
    TM2.Stmt (Alphabet tm) (Labels tm n) (Vars tm)
  | .push k f q => .push (.inl k) (fun v => f v.1) (liftStmt tm n q)
  | .peek k f q => .peek (.inl k) (fun v x => (f v.1 x,v.2)) (liftStmt tm n q)
  | .pop k f q => .pop (.inl k) (fun v x => (f v.1 x,v.2)) (liftStmt tm n q)
  | .load f q => .load (fun v => (f v.1,v.2)) (liftStmt tm n q)
  | .branch f q r => .branch (fun v => f v.1) (liftStmt tm n q) (liftStmt tm n r)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun _ => .inr (⟨n,by omega⟩,false))

abbrev machine (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ) : FinTM2 where
  K := Keys tm
  k₀ := .inl tm.k₀
  k₁ := .inr 1
  Γ := Alphabet tm
  Γk₀Fin := tm.Γk₀Fin
  Λ := Labels tm n
  main := .inl tm.main
  σ := Vars tm
  initialState := (tm.initialState,none)
  m l := match l with
    | .inl l => liftStmt tm n (tm.m l)
    | .inr (j,phase) => if j.val = 0 then
      .peek (.inl tm.k₁) (fun v x => (v.1,x.map e))
        (.branch (fun v => v.2.isSome)
          (.pop (.inl tm.k₁) (fun v _ => v) (.goto (fun _ => .inr (j,false))))
          (.load (fun _ => (tm.initialState,none)) .halt))
      else if phase then
      .peek (.inr 0) (fun v x => (v.1,x))
        (.branch (fun v => v.2.isSome)
          (.pop (.inr 0) (fun v _ => v)
            (.push (.inl tm.k₁) (fun v => e.symm (v.2.getD false))
              (.push (.inr 1) (fun v => v.2.getD false) (.goto (fun _ => .inr (j,true))))))
          (.goto (fun _ => .inr (⟨j.val-1,by omega⟩,false))))
      else
      .peek (.inl tm.k₁) (fun v x => (v.1,x.map e))
        (.branch (fun v => v.2.isSome)
          (.pop (.inl tm.k₁) (fun v _ => v)
            (.push (.inr 0) (fun v => v.2.getD false) (.goto (fun _ => .inr (j,false)))))
          (.goto (fun _ => .inr (j,true))))

/-- Source stacks are embedded with two empty fresh stacks. -/
def sourceStacks (tm : FinTM2) (S : ∀ k, List (tm.Γ k)) : ∀ k, List (Alphabet tm k)
  | .inl k => S k
  | .inr _ => []

def sourceCfg (tm : FinTM2) (n : ℕ) (c : tm.Cfg) :
    TM2.Cfg (Alphabet tm) (Labels tm n) (Vars tm) :=
  ⟨some (c.l.elim (.inr (⟨n,by omega⟩,false)) Sum.inl), (c.var,none), sourceStacks tm c.stk⟩

lemma sourceStacks_update (tm : FinTM2) (S : ∀ k, List (tm.Γ k)) (k : tm.K)
    (s : List (tm.Γ k)) :
    Function.update (sourceStacks tm S) (.inl k) s = sourceStacks tm (Function.update S k s) := by
  funext j
  cases j with
  | inl j =>
    by_cases hj : j = k
    · subst j
      simp only [Function.update_self,sourceStacks]
    · rw [Function.update_of_ne (by simpa using hj : (Sum.inl j : Keys tm) ≠ .inl k)]
      simp [sourceStacks,hj]
  | inr j => rw [Function.update_of_ne (by simp : (Sum.inr j : Keys tm) ≠ .inl k)]; rfl

lemma stepAux_liftStmt (tm : FinTM2) (n : ℕ) (q : TM2.Stmt tm.Γ tm.Λ tm.σ)
    (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    TM2.stepAux (liftStmt tm n q) (v,none) (sourceStacks tm S) =
      sourceCfg tm n (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftStmt, TM2.stepAux, sourceStacks]
    rw [sourceStacks_update]
    exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [liftStmt, TM2.stepAux, sourceStacks]
    rw [sourceStacks_update]
    exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    cases hf : f v <;> simp [liftStmt, TM2.stepAux, hf, ihq, ihr]
  | goto f => rfl
  | halt => rfl

lemma source_step (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (c c' : tm.Cfg) (hc : tm.step c = some c') :
    (machine tm e n).step (sourceCfg tm n c) = some (sourceCfg tm n c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [FinTM2.step, TM2.step] at hc
  | some l =>
    change some (TM2.stepAux (tm.m l) v S) = some c' at hc
    have heq := Option.some.inj hc
    subst c'
    change some (TM2.stepAux (liftStmt tm n (tm.m l)) (v,none) (sourceStacks tm S)) = _
    rw [stepAux_liftStmt]

lemma sourceCfg_init (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (s : List (tm.Γ tm.k₀)) :
    sourceCfg tm n (initList tm s) = initList (machine tm e n) s := by
  simp only [sourceCfg, initList]
  congr 1
  funext k
  cases k <;> simp [sourceStacks, machine]


def copyStacks (tm : FinTM2) (s : List (tm.Γ tm.k₁)) (tmp out : List Bool) :
    ∀ k, List (Alphabet tm k)
  | .inl k => (Function.update (fun _ => []) tm.k₁ s) k
  | .inr j => if j = 0 then tmp else out

def copyCfg (tm : FinTM2) (n : ℕ) (j : Fin (n+1)) (phase : Bool) (v : Option Bool)
    (s : List (tm.Γ tm.k₁)) (tmp out : List Bool) :
    TM2.Cfg (Alphabet tm) (Labels tm n) (Vars tm) :=
  ⟨some (.inr (j,phase)),(tm.initialState,v),copyStacks tm s tmp out⟩

lemma sourceCfg_halt (tm : FinTM2) (n : ℕ) (s : List (tm.Γ tm.k₁)) :
    sourceCfg tm n (haltList tm s) = copyCfg tm n ⟨n,by omega⟩ false none s [] [] := by
  simp only [sourceCfg,haltList,copyCfg]
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = tm.k₁
    · subst k; simp [sourceStacks,copyStacks]
    · simp [sourceStacks,copyStacks,hk]
  | inr k => fin_cases k <;> simp [sourceStacks,copyStacks]

lemma scan_step_cons (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (j : Fin (n+1)) (hj : j.val ≠ 0) (v : Option Bool)
    (b : tm.Γ tm.k₁) (s : List (tm.Γ tm.k₁)) (tmp out : List Bool) :
    (machine tm e n).step (copyCfg tm n j false v (b::s) tmp out) =
      some (copyCfg tm n j false (some (e b)) s (e b::tmp) out) := by
  simp [FinTM2.step,TM2.step,machine,copyCfg,copyStacks,TM2.stepAux,hj]
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = tm.k₁
    · subst k; simp [copyStacks]
    · simp [copyStacks,hk]
  | inr k => fin_cases k <;> simp [copyStacks]

lemma scan_step_nil (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (j : Fin (n+1)) (hj : j.val ≠ 0) (v : Option Bool) (tmp out : List Bool) :
    (machine tm e n).step (copyCfg tm n j false v [] tmp out) =
      some (copyCfg tm n j true none [] tmp out) := by
  simp [FinTM2.step,TM2.step,machine,copyCfg,copyStacks,TM2.stepAux,hj]

lemma copy_step_cons (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (j : Fin (n+1)) (hj : j.val ≠ 0) (v : Option Bool)
    (b : Bool) (s : List (tm.Γ tm.k₁)) (tmp out : List Bool) :
    (machine tm e n).step (copyCfg tm n j true v s (b::tmp) out) =
      some (copyCfg tm n j true (some b) (e.symm b::s) tmp (b::out)) := by
  simp [FinTM2.step,TM2.step,machine,copyCfg,copyStacks,TM2.stepAux,hj]
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = tm.k₁
    · subst k; simp [copyStacks]
    · simp [copyStacks,hk]
  | inr k => fin_cases k <;> simp [copyStacks]

lemma copy_step_nil (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (j : Fin (n+1)) (hj : j.val ≠ 0) (v : Option Bool)
    (s : List (tm.Γ tm.k₁)) (out : List Bool) :
    (machine tm e n).step (copyCfg tm n j true v s [] out) =
      some (copyCfg tm n ⟨j.val-1,by omega⟩ false none s [] out) := by
  simp [FinTM2.step,TM2.step,machine,copyCfg,copyStacks,TM2.stepAux,hj]

lemma erase_step_cons (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (v : Option Bool) (b : tm.Γ tm.k₁) (s : List (tm.Γ tm.k₁)) (out : List Bool) :
    (machine tm e n).step (copyCfg tm n 0 false v (b::s) [] out) =
      some (copyCfg tm n 0 false (some (e b)) s [] out) := by
  simp [FinTM2.step,TM2.step,machine,copyCfg,copyStacks,TM2.stepAux]
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = tm.k₁
    · subst k; simp [copyStacks]
    · simp [copyStacks,hk]
  | inr k => fin_cases k <;> simp [copyStacks]

lemma erase_step_nil (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (v : Option Bool) (out : List Bool) :
    (machine tm e n).step (copyCfg tm n 0 false v [] [] out) =
      some (haltList (machine tm e n) out) := by
  simp [FinTM2.step,TM2.step,machine,copyCfg,copyStacks,TM2.stepAux,haltList]
  funext k
  cases k with
  | inl k => simp [copyStacks]
  | inr k => fin_cases k <;> simp [copyStacks]


lemma scan_run (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (j : Fin (n+1)) (hj : j.val ≠ 0) (v : Option Bool)
    (s : List (tm.Γ tm.k₁)) (tmp out : List Bool) :
    (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[s.length+1]
      (some (copyCfg tm n j false v s tmp out)) =
      some (copyCfg tm n j true none [] ((s.map e).reverse++tmp) out) := by
  induction s generalizing v tmp with
  | nil => exact scan_step_nil tm e n j hj v tmp out
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[s.length+1]
      ((machine tm e n).step (copyCfg tm n j false v (b::s) tmp out)) = _
    rw [scan_step_cons tm e n j hj,ih]
    simp [List.reverse_cons,List.append_assoc]

lemma copy_run (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (j : Fin (n+1)) (hj : j.val ≠ 0) (v : Option Bool)
    (s : List (tm.Γ tm.k₁)) (tmp out : List Bool) :
    (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[tmp.length+1]
      (some (copyCfg tm n j true v s tmp out)) =
      some (copyCfg tm n ⟨j.val-1,by omega⟩ false none
        (tmp.reverse.map e.symm++s) [] (tmp.reverse++out)) := by
  induction tmp generalizing v s out with
  | nil => exact copy_step_nil tm e n j hj v s out
  | cons b tmp ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[tmp.length+1]
      ((machine tm e n).step (copyCfg tm n j true v s (b::tmp) out)) = _
    rw [copy_step_cons tm e n j hj,ih]
    simp [List.reverse_cons,List.map_append,List.append_assoc]

lemma erase_run (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (v : Option Bool) (s : List (tm.Γ tm.k₁)) (out : List Bool) :
    (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[s.length+1]
      (some (copyCfg tm n 0 false v s [] out)) = some (haltList (machine tm e n) out) := by
  induction s generalizing v with
  | nil => exact erase_step_nil tm e n v out
  | cons b s ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[s.length+1]
      ((machine tm e n).step (copyCfg tm n 0 false v (b::s) [] out)) = _
    rw [erase_step_cons,ih]

lemma cycle_run (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (j : Fin (n+1)) (hj : j.val ≠ 0) (v : Option Bool)
    (s : List (tm.Γ tm.k₁)) (out : List Bool) :
    (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[2*(s.length+1)]
      (some (copyCfg tm n j false v s [] out)) =
      some (copyCfg tm n ⟨j.val-1,by omega⟩ false none s [] (s.map e++out)) := by
  rw [show 2*(s.length+1) = ((s.map e).reverse.length+1)+(s.length+1) by simp; omega,
    Function.iterate_add_apply,scan_run tm e n j hj]
  simp only [List.append_nil]
  rw [copy_run tm e n j hj]
  simp

/-- Fixed-count block repetition; no work stack survives the final cleanup. -/
lemma repetition_run (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n j : ℕ) (hj : j ≤ n)
    (v : Option Bool) (s : List (tm.Γ tm.k₁)) (out : List Bool) :
    (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[(2*j+1)*(s.length+1)]
      (some (copyCfg tm n ⟨j,by omega⟩ false v s [] out)) =
      some (haltList (machine tm e n) ((List.replicate j (s.map e)).flatten++out)) := by
  induction j generalizing v out with
  | zero => simpa using erase_run tm e n v s out
  | succ j ih =>
    rw [show (2*(j+1)+1)*(s.length+1) = (2*j+1)*(s.length+1)+2*(s.length+1) by ring,
      Function.iterate_add_apply,cycle_run tm e n ⟨j+1,by omega⟩ (by simp)]
    simp only [Nat.add_sub_cancel]
    rw [ih (by omega)]
    rw [List.replicate_add,List.flatten_append]
    simp [List.append_assoc]


/-- Compose the source run with the explicit duplicate-and-clean phases. -/
def outputs_copy (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (n : ℕ)
    (s : List (tm.Γ tm.k₀)) (t : List (tm.Γ tm.k₁)) (m : ℕ)
    (hr : TM2OutputsInTime tm s (some t) m) :
    TM2OutputsInTime (machine tm e n) s (some ((List.replicate n (t.map e)).flatten))
      (m+(2*n+1)*(t.length+1)) where
  steps := hr.steps+(2*n+1)*(t.length+1)
  steps_le_m := by have hb := hr.steps_le_m; omega
  evals_in_steps := by
    have hs := successful_iterate_simulation tm.step (machine tm e n).step
      (sourceCfg tm n) (source_step tm e n) hr.steps (initList tm s) (haltList tm t) hr.evals_in_steps
    rw [sourceCfg_init tm e n] at hs
    change (fun o : Option (machine tm e n).Cfg => o.bind (machine tm e n).step)^[hr.steps+(2*n+1)*(t.length+1)]
      (some (initList (machine tm e n) s)) =
        some (haltList (machine tm e n) ((List.replicate n (t.map e)).flatten))
    rw [Nat.add_comm hr.steps,Function.iterate_add_apply,hs,sourceCfg_halt]
    simpa using repetition_run tm e n n le_rfl none t []

noncomputable def computableInPolyTime {f : List Bool → List Bool}
    (hf : TM2ComputableInPolyTime id id f) (n : ℕ) :
    TM2ComputableInPolyTime id id (fun s => (List.replicate n (f s)).flatten) where
  tm := machine hf.tm hf.outputAlphabet n
  inputAlphabet := hf.inputAlphabet
  outputAlphabet := Equiv.refl Bool
  time := hf.time + Polynomial.C (2*n+1)*
    (Polynomial.X+Polynomial.C (machinePushBound hf.tm)*hf.time+1)
  outputsFun s := by
    have hout := hf.outputsFun s
    change TM2OutputsInTime hf.tm (s.map hf.inputAlphabet.invFun)
      (some ((f s).map hf.outputAlphabet.invFun)) (hf.time.eval s.length) at hout
    have hc := outputs_copy hf.tm hf.outputAlphabet n _ _ _ hout
    simp [Function.comp_def] at hc
    change TM2OutputsInTime (machine hf.tm hf.outputAlphabet n) (s.map hf.inputAlphabet.invFun)
      (some (((List.replicate n (f s)).flatten).map (Equiv.refl Bool).invFun)) _
    simp only [Equiv.refl,List.map_id_fun]
    refine { steps := hc.steps, evals_in_steps := by simpa using hc.evals_in_steps, steps_le_m := ?_ }
    have hb := polytime_output_length_bound hf s
    have ht := hc.steps_le_m
    simp only [id_eq] at hb
    simp only [id_eq,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    exact ht.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (2*n+1) (Nat.add_le_add_right hb 1)) _)





end QMAPerfectCompleteness.Uniformity.BlockCopy


