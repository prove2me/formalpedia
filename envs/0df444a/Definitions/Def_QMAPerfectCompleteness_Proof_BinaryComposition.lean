-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
-- name    : QMAPerfectCompleteness_Proof_BinaryComposition
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:53:57.097275+00:00
-- url     : https://prove2.me/theorems/f8351e48-920a-498d-bc5c-37240bc6136a
-- title:
--   Finite-machine composition with a clean handoff
-- statement:
--   For finite stack machines with a binary interface, defines a combined machine with disjoint source and target registers and an order-preserving two-pass transfer. The construction supplies exact sequential computations and polynomial-time continuations on outputs actually produced by the first machine, with auxiliary stacks cleared at handoff and termination.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BinaryComposition.lean, lines 10–399.

/- Generated from Solutions.BinaryComposition by authoritative Stage-2 skeleton subtraction.
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



/-! Explicit sequential composition of binary TM2 generators, using disjoint stacks and a
clean two-pass transfer. This file does not invoke the upstream composition declaration. -/
set_option backward.isDefEq.respectTransparency false
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.BinaryComposition
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

abbrev Keys (S T : FinTM2) := S.K ⊕ (Fin 1 ⊕ T.K)
abbrev Alphabet (S T : FinTM2) : Keys S T → Type := Sum.elim S.Γ (Sum.elim (fun _ => Bool) T.Γ)
abbrev Labels (S T : FinTM2) := S.Λ ⊕ (Bool ⊕ T.Λ)
abbrev Vars (S T : FinTM2) := S.σ × T.σ × Option Bool
abbrev initial (S T : FinTM2) : Vars S T := (S.initialState,T.initialState,none)

def sourceStmt (S T : FinTM2) : TM2.Stmt S.Γ S.Λ S.σ →
    TM2.Stmt (Alphabet S T) (Labels S T) (Vars S T)
  | .push k f q => .push (.inl k) (fun v => f v.1) (sourceStmt S T q)
  | .peek k f q => .peek (.inl k) (fun v a => (f v.1 a,v.2)) (sourceStmt S T q)
  | .pop k f q => .pop (.inl k) (fun v a => (f v.1 a,v.2)) (sourceStmt S T q)
  | .load f q => .load (fun v => (f v.1,v.2)) (sourceStmt S T q)
  | .branch f q r => .branch (fun v => f v.1) (sourceStmt S T q) (sourceStmt S T r)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun _ => .inr (.inl false))

def targetStmt (S T : FinTM2) : TM2.Stmt T.Γ T.Λ T.σ →
    TM2.Stmt (Alphabet S T) (Labels S T) (Vars S T)
  | .push k f q => .push (.inr (.inr k)) (fun v => f v.2.1) (targetStmt S T q)
  | .peek k f q => .peek (.inr (.inr k)) (fun v a => (v.1,f v.2.1 a,v.2.2)) (targetStmt S T q)
  | .pop k f q => .pop (.inr (.inr k)) (fun v a => (v.1,f v.2.1 a,v.2.2)) (targetStmt S T q)
  | .load f q => .load (fun v => (v.1,f v.2.1,v.2.2)) (targetStmt S T q)
  | .branch f q r => .branch (fun v => f v.2.1) (targetStmt S T q) (targetStmt S T r)
  | .goto f => .goto (fun v => .inr (.inr (f v.2.1)))
  | .halt => .load (fun _ => initial S T) .halt

abbrev machine (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool) : FinTM2 where
  K := Keys S T
  k₀ := .inl S.k₀
  k₁ := .inr (.inr T.k₁)
  Γ := Alphabet S T
  Γk₀Fin := S.Γk₀Fin
  Λ := Labels S T
  main := .inl S.main
  σ := Vars S T
  initialState := initial S T
  m l := match l with
    | .inl l => sourceStmt S T (S.m l)
    | .inr (.inr l) => targetStmt S T (T.m l)
    | .inr (.inl false) =>
      .peek (.inl S.k₁) (fun v a => (v.1,v.2.1,a.map e))
        (.branch (fun v => v.2.2.isSome)
          (.pop (.inl S.k₁) (fun v _ => v)
            (.push (.inr (.inl 0)) (fun v => v.2.2.getD false)
              (.goto (fun _ => .inr (.inl false)))))
          (.goto (fun _ => .inr (.inl true))))
    | .inr (.inl true) =>
      .peek (.inr (.inl 0)) (fun v a => (v.1,v.2.1,a))
        (.branch (fun v => v.2.2.isSome)
          (.pop (.inr (.inl 0)) (fun v _ => v)
            (.push (.inr (.inr T.k₀)) (fun v => f.symm (v.2.2.getD false))
              (.goto (fun _ => .inr (.inl true)))))
          (.load (fun _ => initial S T) (.goto (fun _ => .inr (.inr T.main)))))

def sourceStacks (S T : FinTM2) (stk : ∀ k, List (S.Γ k)) : ∀ k, List (Alphabet S T k)
  | .inl k => stk k
  | .inr _ => []

def sourceCfg (S T : FinTM2) (c : S.Cfg) : TM2.Cfg (Alphabet S T) (Labels S T) (Vars S T) :=
  ⟨some (c.l.elim (.inr (.inl false)) Sum.inl), (c.var,T.initialState,none), sourceStacks S T c.stk⟩

lemma sourceStacks_update (S T : FinTM2) (stk : ∀ k, List (S.Γ k)) (k : S.K)
    (s : List (S.Γ k)) :
    Function.update (sourceStacks S T stk) (.inl k) s = sourceStacks S T (Function.update stk k s) := by
  funext j
  cases j with
  | inl j =>
    by_cases hj : j = k
    · subst j; simp only [Function.update_self,sourceStacks]
    · rw [Function.update_of_ne (by simpa using hj : (Sum.inl j : Keys S T) ≠ .inl k)]
      simp [sourceStacks,hj]
  | inr j => rw [Function.update_of_ne (by simp : (Sum.inr j : Keys S T) ≠ .inl k)]; rfl

lemma stepAux_sourceStmt (S T : FinTM2) (q : TM2.Stmt S.Γ S.Λ S.σ)
    (v : S.σ) (stk : ∀ k, List (S.Γ k)) :
    TM2.stepAux (sourceStmt S T q) (v,T.initialState,none) (sourceStacks S T stk) =
      sourceCfg S T (TM2.stepAux q v stk) := by
  induction q generalizing v stk with
  | push k f q ih =>
    simp only [sourceStmt,TM2.stepAux,sourceStacks]
    rw [sourceStacks_update]
    exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [sourceStmt,TM2.stepAux,sourceStacks]
    rw [sourceStacks_update]
    exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr => cases hf : f v <;> simp [sourceStmt,TM2.stepAux,hf,ihq,ihr]
  | goto f => rfl
  | halt => rfl

lemma source_step (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (c c' : S.Cfg) (hc : S.step c = some c') :
    (machine S T e f).step (sourceCfg S T c) = some (sourceCfg S T c') := by
  rcases c with ⟨l,v,stk⟩
  cases l with
  | none => simp [FinTM2.step,TM2.step] at hc
  | some l =>
    change some (TM2.stepAux (S.m l) v stk) = some c' at hc
    have heq := Option.some.inj hc
    subst c'
    change some (TM2.stepAux (sourceStmt S T (S.m l)) (v,T.initialState,none) (sourceStacks S T stk)) = _
    rw [stepAux_sourceStmt]

lemma sourceCfg_init (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (s : List (S.Γ S.k₀)) : sourceCfg S T (initList S s) = initList (machine S T e f) s := by
  simp only [sourceCfg,initList]
  congr 1
  funext k
  cases k <;> simp [sourceStacks,machine,initial]


def targetStacks (S T : FinTM2) (stk : ∀ k, List (T.Γ k)) : ∀ k, List (Alphabet S T k)
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr k) => stk k

def targetCfg (S T : FinTM2) (c : T.Cfg) : TM2.Cfg (Alphabet S T) (Labels S T) (Vars S T) :=
  ⟨c.l.map (fun l => .inr (.inr l)),
    if c.l.isNone then initial S T else (S.initialState,c.var,none), targetStacks S T c.stk⟩

lemma targetStacks_update (S T : FinTM2) (stk : ∀ k, List (T.Γ k)) (k : T.K)
    (s : List (T.Γ k)) :
    Function.update (targetStacks S T stk) (.inr (.inr k)) s =
      targetStacks S T (Function.update stk k s) := by
  funext j
  cases j with
  | inl j => rw [Function.update_of_ne (by simp : (Sum.inl j : Keys S T) ≠ .inr (.inr k))]; rfl
  | inr j =>
    cases j with
    | inl j => rw [Function.update_of_ne (by simp : (Sum.inr (.inl j) : Keys S T) ≠ .inr (.inr k))]; rfl
    | inr j =>
      by_cases hj : j = k
      · subst j; simp only [Function.update_self,targetStacks]
      · rw [Function.update_of_ne (by simpa using hj : (Sum.inr (.inr j) : Keys S T) ≠ .inr (.inr k))]
        simp [targetStacks,hj]

lemma stepAux_targetStmt (S T : FinTM2) (q : TM2.Stmt T.Γ T.Λ T.σ)
    (v : T.σ) (stk : ∀ k, List (T.Γ k)) :
    TM2.stepAux (targetStmt S T q) (S.initialState,v,none) (targetStacks S T stk) =
      targetCfg S T (TM2.stepAux q v stk) := by
  induction q generalizing v stk with
  | push k f q ih =>
    simp only [targetStmt,TM2.stepAux,targetStacks]
    rw [targetStacks_update]
    exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [targetStmt,TM2.stepAux,targetStacks]
    rw [targetStacks_update]
    exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr => cases hf : f v <;> simp [targetStmt,TM2.stepAux,hf,ihq,ihr]
  | goto f => rfl
  | halt => rfl

lemma target_step (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (c c' : T.Cfg) (hc : T.step c = some c') :
    (machine S T e f).step (targetCfg S T c) = some (targetCfg S T c') := by
  rcases c with ⟨l,v,stk⟩
  cases l with
  | none => simp [FinTM2.step,TM2.step] at hc
  | some l =>
    change some (TM2.stepAux (T.m l) v stk) = some c' at hc
    have heq := Option.some.inj hc
    subst c'
    change some (TM2.stepAux (targetStmt S T (T.m l)) (S.initialState,v,none) (targetStacks S T stk)) = _
    rw [stepAux_targetStmt]

lemma targetCfg_halt (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (out : List (T.Γ T.k₁)) :
    targetCfg S T (haltList T out) = haltList (machine S T e f) out := by
  simp only [targetCfg,haltList,Option.map_none,Option.isNone_none,ite_true]
  congr 1
  funext k
  cases k with
  | inl k => simp [targetStacks,machine]
  | inr k =>
    cases k with
    | inl k => simp [targetStacks,machine]
    | inr k => simp [targetStacks,machine]


def bridgeStacks (S T : FinTM2) (src : List (S.Γ S.k₁)) (tmp : List Bool)
    (dst : List (T.Γ T.k₀)) : ∀ k, List (Alphabet S T k)
  | .inl k => (Function.update (fun _ => []) S.k₁ src) k
  | .inr (.inl _) => tmp
  | .inr (.inr k) => (Function.update (fun _ => []) T.k₀ dst) k

def bridgeCfg (S T : FinTM2) (phase : Bool) (v : Option Bool)
    (src : List (S.Γ S.k₁)) (tmp : List Bool) (dst : List (T.Γ T.k₀)) :
    TM2.Cfg (Alphabet S T) (Labels S T) (Vars S T) :=
  ⟨some (.inr (.inl phase)),(S.initialState,T.initialState,v),bridgeStacks S T src tmp dst⟩

lemma sourceCfg_halt (S T : FinTM2) (src : List (S.Γ S.k₁)) :
    sourceCfg S T (haltList S src) = bridgeCfg S T false none src [] [] := by
  simp only [sourceCfg,haltList,bridgeCfg]
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = S.k₁
    · subst k; simp [sourceStacks,bridgeStacks]
    · simp [sourceStacks,bridgeStacks,hk]
  | inr k => cases k <;> simp [sourceStacks,bridgeStacks]

lemma bridge_scan_cons (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (v : Option Bool) (b : S.Γ S.k₁) (src : List (S.Γ S.k₁)) (tmp : List Bool) :
    (machine S T e f).step (bridgeCfg S T false v (b::src) tmp []) =
      some (bridgeCfg S T false (some (e b)) src (e b::tmp) []) := by
  simp [FinTM2.step,TM2.step,machine,bridgeCfg,bridgeStacks,TM2.stepAux]
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = S.k₁
    · subst k; simp [bridgeStacks]
    · simp [bridgeStacks,hk]
  | inr k =>
    cases k with
    | inl k => fin_cases k; simp [bridgeStacks]
    | inr k => simp [bridgeStacks]

lemma bridge_scan_nil (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (v : Option Bool) (tmp : List Bool) :
    (machine S T e f).step (bridgeCfg S T false v [] tmp []) =
      some (bridgeCfg S T true none [] tmp []) := by
  simp [FinTM2.step,TM2.step,machine,bridgeCfg,bridgeStacks,TM2.stepAux]

lemma bridge_write_cons (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (v : Option Bool) (b : Bool) (tmp : List Bool) (dst : List (T.Γ T.k₀)) :
    (machine S T e f).step (bridgeCfg S T true v [] (b::tmp) dst) =
      some (bridgeCfg S T true (some b) [] tmp (f.symm b::dst)) := by
  simp [FinTM2.step,TM2.step,machine,bridgeCfg,bridgeStacks,TM2.stepAux]
  funext k
  cases k with
  | inl k => simp [bridgeStacks]
  | inr k =>
    cases k with
    | inl k => fin_cases k; simp [bridgeStacks]
    | inr k =>
      by_cases hk : k = T.k₀
      · subst k; simp [bridgeStacks]
      · simp [bridgeStacks,hk]

lemma bridge_write_nil (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (v : Option Bool) (dst : List (T.Γ T.k₀)) :
    (machine S T e f).step (bridgeCfg S T true v [] [] dst) =
      some (targetCfg S T (initList T dst)) := by
  simp [FinTM2.step,TM2.step,machine,bridgeCfg,bridgeStacks,TM2.stepAux,targetCfg,initList,initial]
  funext k
  cases k with
  | inl k => simp [bridgeStacks,targetStacks]
  | inr k =>
    cases k with
    | inl k => simp [bridgeStacks,targetStacks]
    | inr k =>
      by_cases hk : k = T.k₀
      · subst k; simp [bridgeStacks,targetStacks]
      · simp [bridgeStacks,targetStacks,hk]


lemma bridge_scan_run (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (v : Option Bool) (src : List (S.Γ S.k₁)) (tmp : List Bool) :
    (fun o : Option (machine S T e f).Cfg => o.bind (machine S T e f).step)^[src.length+1]
      (some (bridgeCfg S T false v src tmp [])) =
      some (bridgeCfg S T true none [] ((src.map e).reverse++tmp) []) := by
  induction src generalizing v tmp with
  | nil => exact bridge_scan_nil S T e f v tmp
  | cons b src ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine S T e f).Cfg => o.bind (machine S T e f).step)^[src.length+1]
      ((machine S T e f).step (bridgeCfg S T false v (b::src) tmp [])) = _
    rw [bridge_scan_cons,ih]
    simp [List.reverse_cons,List.append_assoc]

lemma bridge_write_run (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (v : Option Bool) (tmp : List Bool) (dst : List (T.Γ T.k₀)) :
    (fun o : Option (machine S T e f).Cfg => o.bind (machine S T e f).step)^[tmp.length+1]
      (some (bridgeCfg S T true v [] tmp dst)) =
      some (targetCfg S T (initList T (tmp.reverse.map f.symm++dst))) := by
  induction tmp generalizing v dst with
  | nil => exact bridge_write_nil S T e f v dst
  | cons b tmp ih =>
    rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
    change (fun o : Option (machine S T e f).Cfg => o.bind (machine S T e f).step)^[tmp.length+1]
      ((machine S T e f).step (bridgeCfg S T true v [] (b::tmp) dst)) = _
    rw [bridge_write_cons,ih]
    simp [List.reverse_cons,List.map_append,List.append_assoc]

/-- Order-preserving conversion of the clean source output to the target input. -/
lemma bridge_run (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (src : List (S.Γ S.k₁)) :
    (fun o : Option (machine S T e f).Cfg => o.bind (machine S T e f).step)^[2*src.length+2]
      (some (sourceCfg S T (haltList S src))) =
      some (targetCfg S T (initList T ((src.map e).map f.symm))) := by
  rw [sourceCfg_halt,show 2*src.length+2 = ((src.map e).reverse.length+1)+(src.length+1) by simp; omega,
    Function.iterate_add_apply,bridge_scan_run]
  simp only [List.append_nil]
  rw [bridge_write_run]
  simp

/-- Exact combined computation; both machines' auxiliary stacks are empty at handoff and halt. -/
def outputs_comp (S T : FinTM2) (e : S.Γ S.k₁ ≃ Bool) (f : T.Γ T.k₀ ≃ Bool)
    (s : List (S.Γ S.k₀)) (t : List (S.Γ S.k₁)) (u : List (T.Γ T.k₁)) (m₁ m₂ : ℕ)
    (h₁ : TM2OutputsInTime S s (some t) m₁)
    (h₂ : TM2OutputsInTime T ((t.map e).map f.symm) (some u) m₂) :
    TM2OutputsInTime (machine S T e f) s (some u) (m₁+(2*t.length+2)+m₂) where
  steps := h₁.steps+(2*t.length+2)+h₂.steps
  steps_le_m := by have ha := h₁.steps_le_m; have hb := h₂.steps_le_m; omega
  evals_in_steps := by
    have hs := successful_iterate_simulation S.step (machine S T e f).step
      (sourceCfg S T) (source_step S T e f) h₁.steps (initList S s) (haltList S t) h₁.evals_in_steps
    rw [sourceCfg_init S T e f] at hs
    have ht := successful_iterate_simulation T.step (machine S T e f).step
      (targetCfg S T) (target_step S T e f) h₂.steps
      (initList T ((t.map e).map f.symm)) (haltList T u) h₂.evals_in_steps
    rw [targetCfg_halt S T e f] at ht
    change (fun o : Option (machine S T e f).Cfg => o.bind (machine S T e f).step)^[h₁.steps+(2*t.length+2)+h₂.steps]
      (some (initList (machine S T e f) s)) = some (haltList (machine S T e f) u)
    rw [show h₁.steps+(2*t.length+2)+h₂.steps = h₂.steps+((2*t.length+2)+h₁.steps) by omega,
      Function.iterate_add_apply,Function.iterate_add_apply,hs,bridge_run,ht]



/-- The target need only satisfy a timed specification on outputs actually produced by the source.
This supports verified code compilers without a runtime promise on malformed codes. -/
noncomputable def computableContinuation {f g : List Bool → List Bool}
    (h₁ : TM2ComputableInPolyTime id id f) (T : FinTM2)
    (inputAlphabet : T.Γ T.k₀ ≃ Bool) (outputAlphabet : T.Γ T.k₁ ≃ Bool)
    (q : Polynomial ℕ)
    (h₂ : ∀ s, TM2OutputsInTime T ((f s).map inputAlphabet.invFun)
      (some ((g (f s)).map outputAlphabet.invFun)) (q.eval (f s).length)) :
    TM2ComputableInPolyTime id id (g ∘ f) where
  tm := machine h₁.tm T h₁.outputAlphabet inputAlphabet
  inputAlphabet := h₁.inputAlphabet
  outputAlphabet := outputAlphabet
  time := h₁.time + 2*(Polynomial.X+Polynomial.C (machinePushBound h₁.tm)*h₁.time+1) +
    q.comp (Polynomial.X+Polynomial.C (machinePushBound h₁.tm)*h₁.time)
  outputsFun s := by
    have ha := h₁.outputsFun s
    have hb := h₂ s
    change TM2OutputsInTime h₁.tm (s.map h₁.inputAlphabet.invFun)
      (some ((f s).map h₁.outputAlphabet.invFun)) (h₁.time.eval s.length) at ha
    change TM2OutputsInTime T ((f s).map inputAlphabet.invFun)
      (some ((g (f s)).map outputAlphabet.invFun)) (q.eval (f s).length) at hb
    have hc := outputs_comp h₁.tm T h₁.outputAlphabet inputAlphabet _ _ _ _ _ ha
      (by simpa [Function.comp_def] using hb)
    simp only [List.length_map] at hc
    change TM2OutputsInTime (machine h₁.tm T h₁.outputAlphabet inputAlphabet)
      (s.map h₁.inputAlphabet.invFun) (some ((g (f s)).map outputAlphabet.invFun)) _
    refine {steps := hc.steps,evals_in_steps := hc.evals_in_steps,steps_le_m := ?_}
    have hlen := polytime_output_length_bound h₁ s
    simp only [id_eq] at hlen
    have hq : q.eval (f s).length ≤
        q.eval (s.length+machinePushBound h₁.tm*h₁.time.eval s.length) :=
      natPolynomial_eval_monotone q hlen
    have ht := hc.steps_le_m
    simp only [id_eq,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
    omega



end QMAPerfectCompleteness.Uniformity.BinaryComposition


