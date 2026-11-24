-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Recursion_StatefulRecursiveExchange
-- name    : CSL_Interchange_Framework_Recursion_StatefulRecursiveExchange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:00:15.844543+00:00
-- url     : https://prove2.me/theorems/2e3e434f-3b15-4c74-ab91-510662086000
-- title:
--   Coded sorting library: Interchange / Framework / Recursion / StatefulRecursiveExchange
-- statement:
--   Module `CodedSorting.Interchange.Framework.Recursion.StatefulRecursiveExchange` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Stateful execution of the real edge/pivot program. Recursive callbacks
--   return payloads and control state; their recovered child identifier determines
--   the scan performed after the recursive return.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Recursion.StatefulRecursiveExchange

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchange

/-! Stateful execution of the real edge/pivot program. Recursive callbacks
return payloads and control state; their recovered child identifier determines
the scan performed after the recursive return. -/

namespace CSL.StatefulRecursiveExchange

open RecursiveExchange Circuit CircuitProgram ProgramNetwork TensorLabels
open MatrixFactorization CodedSimulation Address
open scoped BigOperators
noncomputable section

variable {σ α ι : Type}

/-- A sequential evaluator, invoking the stateful callback once per list entry. -/
def sequence (step : α → ι → σ → α × σ) : List ι → α → σ → α × σ
  | [], value, state => (value,state)
  | i::is, value, state =>
      let next := step value i state
      sequence step is next.1 next.2

theorem sequence_projection (step : α → ι → σ → α × σ)
    (pureStep : α → ι → α) (Safe : σ → Prop)
    (hstep : ∀ value i state, Safe state →
      (step value i state).1 = pureStep value i ∧ Safe (step value i state).2)
    (is : List ι) (value : α) (state : σ) (hs : Safe state) :
    (sequence step is value state).1 = is.foldl pureStep value ∧
      Safe (sequence step is value state).2 := by
  induction is generalizing value state with
  | nil => exact ⟨rfl,hs⟩
  | cons i is ih =>
    obtain ⟨hv,hs'⟩ := hstep value i state hs
    obtain ⟨hrec,hsrec⟩ := ih (step value i state).1 (step value i state).2 hs'
    exact ⟨by simpa only [sequence,List.foldl_cons,hv] using hrec,hsrec⟩

variable {Prefix Gap Suffix : Type}

abbrev Stream (f : ℕ) := LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit

/-- A real recursive return includes the decoded continuation identity. -/
abbrev ChildAction (σ : Type) (f : ℕ) :=
  Child → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → σ →
    (Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f × Child) × σ

def shortStep (f : ℕ) (child : ChildAction (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) σ f)
    (F : Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) (c : Child) (state : σ) :=
  let result := child c (transport (shortBefore f (childRow c) (childCol c)) F) state
  -- The returned continuation, not the pre-call closure, chooses this scan.
  (transport (shortAfter f (childRow result.1.2) (childCol result.1.2)) result.1.1,result.2)

def sparseProgram (f : ℕ) (e : Edge)
    (child : ChildAction (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) σ f)
    (ps : List (EdgeChild e))
    (F : Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) (state : σ) :=
  sequence (fun stream p => shortStep f child stream ⟨e,p⟩) ps F state

def edgeProgram (f : ℕ) (e : Edge)
    (child : ChildAction (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) σ f)
    (F : Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) (state : σ) :=
  let result := sparseProgram f e child (edgePivots e)
    (transport (coordinatePermutation f e) F) state
  (transport (coordinatePermutation f e).symm result.1,result.2)

theorem edgeProgram_projection (f : ℕ) (e : Edge)
    (child : ChildAction (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) σ f)
    (pureChild : Child → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (Safe : σ → Prop)
    (hchild : ∀ c F state, Safe state →
      (child c F state).1 = (pureChild c F,c) ∧ Safe (child c F state).2)
    (F : Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) (state : σ) (hs : Safe state) :
    (edgeProgram f e child F state).1 =
      edgeStreamProgram f e (fun p => pureChild ⟨e,p⟩) F ∧
      Safe (edgeProgram f e child F state).2 := by
  have hstep : ∀ stream (p : EdgeChild e) s, Safe s →
      (shortStep f child stream ⟨e,p⟩ s).1 =
        shortStreamStep f e (fun p => pureChild ⟨e,p⟩) p stream ∧
      Safe (shortStep f child stream ⟨e,p⟩ s).2 := by
    intro stream p s hsafe
    obtain ⟨hc,hstate⟩ := hchild ⟨e,p⟩ (transport (shortBefore f (oneRow p) (oneCol p)) stream) s hsafe
    constructor
    · try dsimp only [shortStep,childRow,childCol]
      rw [hc]
      rfl
    · exact hstate
  obtain ⟨hstream,hstate⟩ := sequence_projection
    (fun stream p => shortStep f child stream ⟨e,p⟩)
    (fun stream p => shortStreamStep f e (fun p => pureChild ⟨e,p⟩) p stream)
    Safe hstep (edgePivots e) (transport (coordinatePermutation f e) F) state hs
  exact ⟨congrArg (transport (coordinatePermutation f e).symm) hstream,hstate⟩

section Tabulation

variable {Key Value : Type} [DecidableEq Key]

def tabulate (keys : List Key) (run : Key → σ → Value × σ)
    (initial : Key → Value) (state : σ) : (Key → Value) × σ :=
  sequence (fun table key s =>
    let out := run key s
    (Function.update table key out.1,out.2)) keys initial state

theorem fold_update_at (keys : List Key) (values initial : Key → Value) (key : Key) :
    (keys.foldl (fun table i => Function.update table i (values i)) initial) key =
      if key ∈ keys then values key else initial key := by
  induction keys generalizing initial with
  | nil => simp
  | cons i keys ih =>
    rw [List.foldl_cons,ih]
    by_cases hm : key ∈ keys
    · simp [hm]
    · by_cases he : key = i
      · subst key; simp [hm]
      · simp [hm,he,Function.update_of_ne he]

theorem tabulate_projection (keys : List Key) (run : Key → σ → Value × σ)
    (values initial : Key → Value) (Safe : σ → Prop)
    (hrun : ∀ key state, Safe state → (run key state).1 = values key ∧ Safe (run key state).2)
    (state : σ) (hs : Safe state) :
    (∀ key, (tabulate keys run initial state).1 key =
      if key ∈ keys then values key else initial key) ∧
      Safe (tabulate keys run initial state).2 := by
  have hstep : ∀ table key s, Safe s →
      (let out := run key s; (Function.update table key out.1,out.2)).1 =
        Function.update table key (values key) ∧
      Safe (let out := run key s; (Function.update table key out.1,out.2)).2 := by
    intro table key s hsafe
    obtain ⟨hv,hstate⟩ := hrun key s hsafe
    exact ⟨by dsimp only; rw [hv],hstate⟩
  obtain ⟨hv,hstate⟩ := sequence_projection _ _ Safe hstep keys initial state hs
  refine ⟨fun key => ?_,hstate⟩
  change (sequence _ keys initial state).1 key = _
  rw [hv,fold_update_at]

end Tabulation

def gateInput (f : ℕ)
    (input : Reg → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (stored : DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) (e : Edge) :
    Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f :=
  fun a => (actualCode Parameters.d).localMap ((actualNetwork Parameters.d).tail e)
    (fun port => match port with
      | .inl i => input i.val a
      | .inr incoming => stored incoming.val a) ⟨e,rfl⟩

def layer (f : ℕ)
    (input : Reg → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (stored : DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (move : Edge → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → σ →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f × σ)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) :=
  let out := tabulate (Finset.univ : Finset Reg).toList
    (fun r => move (t,r) (gateInput f input stored (t,r))) (fun _ _ => 0) state
  ((fun e : Edge => if e.1=t then out.1 e.2 else stored e),out.2)

theorem layer_projection (f : ℕ)
    (input : Reg → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (stored : DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (move : Edge → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → σ →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f × σ)
    (pureMove : Edge → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (Safe : σ → Prop)
    (hmove : ∀ e F state, Safe state →
      (move e F state).1 = pureMove e F ∧ Safe (move e F state).2)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) (hs : Safe state) :
    (layer f input stored move t state).1 =
      (fun e => if e.1.val=t.val then physicalWireWith f input stored pureMove e else stored e) ∧
      Safe (layer f input stored move t state).2 := by
  obtain ⟨hp,hstate⟩ := tabulate_projection (Finset.univ : Finset Reg).toList
    (fun r => move (t,r) (gateInput f input stored (t,r)))
    (fun r => pureMove (t,r) (gateInput f input stored (t,r))) (fun _ _ => 0)
    Safe (fun r s h => hmove (t,r) _ s h) state hs
  refine ⟨?_,hstate⟩
  funext e
  rcases e with ⟨i,r⟩
  by_cases hi : i=t
  · subst i
    first
    | exact hp r
    | (have h_sx := hp r; simp only [layer,if_pos rfl,Finset.mem_toList,Finset.mem_univ,ite_true,
      physicalWireWith,gateInput] at h_sx ⊢; exact h_sx)
    | (have h_sx := hp r; simp only [layer,if_pos rfl,Finset.mem_toList,Finset.mem_univ,ite_true,
      physicalWireWith,gateInput] at h_sx; exact h_sx)
    | (simp only [layer,if_pos rfl,Finset.mem_toList,Finset.mem_univ,ite_true,
      physicalWireWith,gateInput]; exact hp r)
  · have hn : i.val ≠ t.val := fun hv => hi (Fin.ext hv)
    simp only [layer,if_neg hi,if_neg hn]

def execute (f : ℕ)
    (input : Reg → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (move : Edge → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → σ →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f × σ) :
    ℕ → σ → DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f × σ
  | 0, state => (fun _ _ => 0,state)
  | t+1, state =>
      let previous := execute f input move t state
      if ht : t < (globalProgram Parameters.d).length+1 then
        layer f input previous.1 move ⟨t,ht⟩ previous.2
      else previous

theorem execute_projection (f : ℕ)
    (input : Reg → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (move : Edge → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → σ →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f × σ)
    (pureMove : Edge → Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      Stream (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (Safe : σ → Prop)
    (hmove : ∀ e F state, Safe state →
      (move e F state).1 = pureMove e F ∧ Safe (move e F state).2)
    (t : ℕ) (state : σ) (hs : Safe state) :
    (execute f input move t state).1 = executeLayersWith f input pureMove t ∧
      Safe (execute f input move t state).2 := by
  induction t with
  | zero => exact ⟨rfl,hs⟩
  | succ t ih =>
    obtain ⟨hp,hstate⟩ := ih
    by_cases ht : t < (globalProgram Parameters.d).length+1
    · obtain ⟨hl,hsl⟩ := layer_projection f input (execute f input move t state).1
        move pureMove Safe hmove ⟨t,ht⟩ (execute f input move t state).2 hstate
      constructor
      · simpa only [execute,dif_pos ht,hp,executeLayersWith] using hl
      · simpa only [execute,dif_pos ht] using hsl
    · constructor
      · rw [execute,dif_neg ht,hp]
        funext e
        have he : e.1.val ≠ t := by have hb := e.1.isLt; omega
        simp only [executeLayersWith,if_neg he]
      · simpa only [execute,dif_neg ht] using hstate

section WholeLevel

variable {Rows : ℕ}

def middle (f : ℕ)
    (child : ChildAction (Prefix := Fin Rows) (Gap := Gap) (Suffix := Suffix) σ f)
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) (state : σ) :=
  let out := execute f (splitInput f F) (fun e => edgeProgram f e child)
    ((globalProgram Parameters.d).length+1) state
  (gatherOutput f (fun i => out.1 (sinkWire (globalProgram Parameters.d) (globalSwap i))),out.2)

def full (f : ℕ)
    (child : ChildAction (Prefix := Fin Rows) (Gap := Gap) (Suffix := Suffix) σ f)
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) (state : σ) :=
  let out := middle f child (transport (mapPairEquiv lowerSubtractEquiv) F) state
  (transport (mapPairEquiv lowerReflectEquiv) out.1,out.2)

theorem full_projection (f : ℕ)
    (child : ChildAction (Prefix := Fin Rows) (Gap := Gap) (Suffix := Suffix) σ f)
    (pureChild : Child → Stream (Prefix := Fin Rows) (Gap := Gap) (Suffix := Suffix) f →
      Stream (Prefix := Fin Rows) (Gap := Gap) (Suffix := Suffix) f)
    (Safe : σ → Prop)
    (hchild : ∀ c F state, Safe state →
      (child c F state).1 = (pureChild c F,c) ∧ Safe (child c F state).2)
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit)
    (state : σ) (hs : Safe state) :
    (full f child F state).1 = factoredFullExchange f pureChild F ∧
      Safe (full f child F state).2 := by
  obtain ⟨he,hstate⟩ := execute_projection f
    (splitInput f (transport (mapPairEquiv lowerSubtractEquiv) F))
    (fun e => edgeProgram f e child) (fun e => edgeStreamProgram f e (fun p => pureChild ⟨e,p⟩))
    Safe (fun e stream s h => edgeProgram_projection f e child pureChild Safe hchild stream s h)
    ((globalProgram Parameters.d).length+1) state hs
  constructor
  · try dsimp only [full,middle]
    rw [he]
    rfl
  · exact hstate

end WholeLevel

section Repacking
variable {A B : Type}

def viaShape (e : A ≃ B) (op : (B → Bit) → σ → (B → Bit) × σ)
    (F : A → Bit) (state : σ) :=
  let out := op (fun b => F (e.symm b)) state
  ((fun a => out.1 (e a)),out.2)

theorem viaShape_projection (e : A ≃ B) (op : (B → Bit) → σ → (B → Bit) × σ)
    (pureOp : (B → Bit) → (B → Bit)) (Safe : σ → Prop)
    (hop : ∀ F state, Safe state → (op F state).1 = pureOp F ∧ Safe (op F state).2)
    (F : A → Bit) (state : σ) (hs : Safe state) :
    (viaShape e op F state).1 = RecursiveExchange.viaShape e pureOp F ∧
      Safe (viaShape e op F state).2 := by
  obtain ⟨hv,hstate⟩ := hop (fun b => F (e.symm b)) state hs
  refine ⟨?_,hstate⟩
  exact congrArg (fun output a => output (e a)) hv

end Repacking

/-- The invariant is logical only: the concrete state can be a disk stack.
The returned descriptor is subsequently used by `shortStep` to select its
post-recursion data permutation. -/
structure Control (State Descriptor : Type) where
  childOf : Descriptor → Child
  enter : Descriptor → State → State
  leave : State → Descriptor × State
  Valid : List Descriptor → State → Prop
  enter_valid : ∀ d stack state, Valid stack state → Valid (d::stack) (enter d state)
  leave_valid : ∀ d stack state, Valid (d::stack) state →
    (leave state).1 = d ∧ Valid stack (leave state).2

variable {Descriptor : Type}

def framedChild (control : Control σ Descriptor) (descriptor : Descriptor)
    (op : (α → Bit) → σ → (α → Bit) × σ) (F : α → Bit) (state : σ) :=
  let out := op F (control.enter descriptor state)
  let resumed := control.leave out.2
  ((out.1,control.childOf resumed.1),resumed.2)

theorem framedChild_projection (control : Control σ Descriptor) (descriptor : Descriptor)
    (op : (α → Bit) → σ → (α → Bit) × σ) (pureOp : (α → Bit) → α → Bit)
    (stack : List Descriptor)
    (hop : ∀ F state, control.Valid (descriptor::stack) state →
      (op F state).1 = pureOp F ∧ control.Valid (descriptor::stack) (op F state).2)
    (F : α → Bit) (state : σ) (hs : control.Valid stack state) :
    (framedChild control descriptor op F state).1 = (pureOp F,control.childOf descriptor) ∧
      control.Valid stack (framedChild control descriptor op F state).2 := by
  obtain ⟨hv,hstate⟩ := hop F (control.enter descriptor state)
    (control.enter_valid descriptor stack state hs)
  obtain ⟨hd,hpop⟩ := control.leave_valid descriptor stack _ hstate
  exact ⟨Prod.ext hv (congrArg control.childOf hd),hpop⟩

/-- The actual array computation carries the disk/control state through
gates, edges, scans and recursive calls. The child callback genuinely
performs enter → recursive payload execution → leave. -/
def run (control : Control σ Descriptor)
    (makeFrame : ℕ → ℕ → ℕ → Child → Descriptor) (baseWidth cutoff : ℕ) :
    (k rows : ℕ) → {Prefix Gap Suffix : Type} →
    [Fintype Prefix] → [Fintype Gap] → [Fintype Suffix] →
    (Prefix ≃ Fin (rows * Parameters.W ^ k)) →
    (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) → σ →
    (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) × σ
  | 0, _, _, _, _, _, _, _, _, F, state => (transport exchangeEquiv F,state)
  | k+1, rows, Prefix, Gap, Suffix, _, _, _, layout, F, state =>
      let V := Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ (k+1))) Gap Suffix)
      if V ≤ cutoff then (transport exchangeEquiv F,state)
      else
        let f := baseWidth * Parameters.m ^ k
        let child : ChildAction (Prefix := Fin (rows * Parameters.W^k)) (Gap := Gap) (Suffix := Suffix) σ f :=
          fun c => framedChild control (makeFrame (k+1) (baseWidth * Parameters.m^(k+1)) V c)
            (viaShape (childRepack f c)
              (run control makeFrame baseWidth cutoff k (rows * beforeCard f (childRow c))
                (childPrefixLayout baseWidth k rows c)))
        viaShape (addressShape (parentPrefixLayout k rows layout) (splitLongField baseWidth k)
          (Equiv.refl _) (Equiv.refl _)) (full f child) F state

theorem run_projection (control : Control σ Descriptor)
    (makeFrame : ℕ → ℕ → ℕ → Child → Descriptor)
    (hframe : ∀ depth width volume c, control.childOf (makeFrame depth width volume c) = c)
    (baseWidth cutoff k rows : ℕ) (baseCharge : ℕ → ℕ) (levelCharge : ℕ → ℕ → ℕ)
    {Prefix Gap Suffix : Type} [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k))
    (F : FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit)
    (stack : List Descriptor) (state : σ) (hs : control.Valid stack state) :
    (run control makeFrame baseWidth cutoff k rows layout F state).1 =
      (cutoffExchange baseWidth cutoff baseCharge levelCharge k rows layout).run F ∧
    control.Valid stack (run control makeFrame baseWidth cutoff k rows layout F state).2 := by
  induction k generalizing rows Prefix Gap Suffix stack state with
  | zero => exact ⟨rfl,hs⟩
  | succ k ih =>
    let V := Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ (k+1))) Gap Suffix)
    by_cases hfit : V ≤ cutoff
    · try dsimp only [V] at hfit
      simpa only [run,cutoffExchange,if_pos hfit] using
        (show transport exchangeEquiv F = transport exchangeEquiv F ∧ control.Valid stack state from ⟨rfl,hs⟩)
    · try dsimp only [V] at hfit
      let f := baseWidth * Parameters.m ^ k
      let child : ChildAction (Prefix := Fin (rows * Parameters.W^k)) (Gap := Gap) (Suffix := Suffix) σ f :=
        fun c => framedChild control (makeFrame (k+1) (baseWidth * Parameters.m^(k+1)) V c)
          (viaShape (childRepack f c)
            (run control makeFrame baseWidth cutoff k (rows * beforeCard f (childRow c))
              (childPrefixLayout baseWidth k rows c)))
      let pureChild : Child → Stream (Prefix := Fin (rows * Parameters.W^k)) (Gap := Gap) (Suffix := Suffix) f →
          Stream (Prefix := Fin (rows * Parameters.W^k)) (Gap := Gap) (Suffix := Suffix) f :=
        fun c => RecursiveExchange.viaShape (childRepack f c)
          (cutoffExchange baseWidth cutoff baseCharge levelCharge k
            (rows * beforeCard f (childRow c)) (childPrefixLayout baseWidth k rows c)).run
      have hc : ∀ c stream s, control.Valid stack s →
          (child c stream s).1 = (pureChild c stream,c) ∧ control.Valid stack (child c stream s).2 := by
        intro c stream s hvalid
        have hr := framedChild_projection control
          (makeFrame (k+1) (baseWidth * Parameters.m^(k+1)) V c)
          (viaShape (childRepack f c)
            (run control makeFrame baseWidth cutoff k (rows * beforeCard f (childRow c))
              (childPrefixLayout baseWidth k rows c)))
          (pureChild c) stack
          (fun input st hst => viaShape_projection (childRepack f c) _ _ _
            (fun data st' hst' => ih _ _ data _ st' hst') input st hst)
          stream s hvalid
        simpa only [hframe] using hr
      have hfull := viaShape_projection
        (addressShape (parentPrefixLayout k rows layout) (splitLongField baseWidth k)
          (Equiv.refl Gap) (Equiv.refl Suffix))
        (full f child) (factoredFullExchange f pureChild) (control.Valid stack)
        (fun data st hst => full_projection f child pureChild (control.Valid stack) hc data st hst)
        F state hs
      simpa only [run,cutoffExchange,if_neg hfit] using hfull

theorem run_correct (control : Control σ Descriptor)
    (makeFrame : ℕ → ℕ → ℕ → Child → Descriptor)
    (hframe : ∀ depth width volume c, control.childOf (makeFrame depth width volume c) = c)
    (baseWidth cutoff k rows : ℕ)
    {Prefix Gap Suffix : Type} [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k))
    (F : FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit)
    (stack : List Descriptor) (state : σ) (hs : control.Valid stack state) :
    (run control makeFrame baseWidth cutoff k rows layout F state).1 = transport exchangeEquiv F ∧
      control.Valid stack (run control makeFrame baseWidth cutoff k rows layout F state).2 := by
  obtain ⟨hv,hstate⟩ := run_projection control makeFrame hframe baseWidth cutoff k rows
    (fun _ => 0) (fun _ _ => 0) layout F stack state hs
  exact ⟨hv.trans (cutoffExchange_correct _ _ _ _ _ _ layout F),hstate⟩

/-- An observational bound for the real evaluator: changing the frame maker
outside these depth/width/volume ranges cannot change either its payload or
its control state. The proof descends through the actual calls, using their
proved complete-address volume V/W. -/
theorem run_congr_frames (control : Control σ Descriptor)
    (make₁ make₂ : ℕ → ℕ → ℕ → Child → Descriptor)
    (baseWidth cutoff k rows : ℕ)
    {Prefix Gap Suffix : Type} [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k))
    (hmake : ∀ depth width volume c, depth ≤ k → width ≤ baseWidth * Parameters.m^k →
      volume ≤ Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix) →
      make₁ depth width volume c = make₂ depth width volume c)
    (F : FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) (state : σ) :
    run control make₁ baseWidth cutoff k rows layout F state =
      run control make₂ baseWidth cutoff k rows layout F state := by
  induction k generalizing rows Prefix Gap Suffix state with
  | zero => rfl
  | succ k ih =>
    have hw : baseWidth * Parameters.m^k ≤ baseWidth * Parameters.m^(k+1) := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right (by norm_num [Parameters.m_value]) (Nat.le_succ k)
    have hsub (c : Child) :
        run control make₁ baseWidth cutoff k
          (rows * beforeCard (baseWidth * Parameters.m^k) (childRow c))
          (Gap := SingleCoordinate.ShortGap (Gap := Gap) (R := Scalar (baseWidth * Parameters.m^k))
            (childRow c) (childCol c))
          (Suffix := SingleCoordinate.ShortSuffix (Suffix := Suffix) (R := Scalar (baseWidth * Parameters.m^k))
            (childCol c))
          (childPrefixLayout baseWidth k rows c) =
        run control make₂ baseWidth cutoff k
          (rows * beforeCard (baseWidth * Parameters.m^k) (childRow c))
          (childPrefixLayout baseWidth k rows c) := by
      funext input st
      apply ih
      intro depth width volume child hd hwidth hvolume
      apply hmake depth width volume child (hd.trans (Nat.le_succ k)) (hwidth.trans hw)
      apply hvolume.trans
      rw [recursive_child_volume baseWidth k rows layout c]
      exact Nat.div_le_self _ _
    rw [run,run]
    split_ifs with hfit
    · rfl
    · have hchildren :
          (fun c => framedChild control
            (make₁ (k+1) (baseWidth * Parameters.m^(k+1))
              (Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m^(k+1))) Gap Suffix)) c)
            (viaShape (childRepack (Gap := Gap) (Suffix := Suffix) (baseWidth * Parameters.m^k) c)
              (run control make₁ baseWidth cutoff k
                (rows * beforeCard (baseWidth * Parameters.m^k) (childRow c))
                (childPrefixLayout baseWidth k rows c)))) =
          (fun c => framedChild control
            (make₂ (k+1) (baseWidth * Parameters.m^(k+1))
              (Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m^(k+1))) Gap Suffix)) c)
            (viaShape (childRepack (Gap := Gap) (Suffix := Suffix) (baseWidth * Parameters.m^k) c)
              (run control make₂ baseWidth cutoff k
                (rows * beforeCard (baseWidth * Parameters.m^k) (childRow c))
                (childPrefixLayout baseWidth k rows c)))) := by
          funext c
          rw [hmake _ _ _ c (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),hsub c]
      try dsimp only
      rw [hchildren]

def checkedFrames (bound : ℕ) (make fallback : ℕ → ℕ → ℕ → Child → Descriptor) :
    ℕ → ℕ → ℕ → Child → Descriptor :=
  fun depth width volume c => if depth ≤ bound ∧ width ≤ bound ∧ volume ≤ bound
    then make depth width volume c else fallback depth width volume c

/-- For a bounded root call, the totalizing fallback is observationally
unreachable in the actual stateful execution, including its external state. -/
theorem run_checked_frames (control : Control σ Descriptor) (bound : ℕ)
    (make fallback : ℕ → ℕ → ℕ → Child → Descriptor)
    (baseWidth cutoff k rows : ℕ)
    {Prefix Gap Suffix : Type} [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k))
    (hk : k ≤ bound) (hw : baseWidth * Parameters.m^k ≤ bound)
    (hv : Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix) ≤ bound)
    (F : FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) (state : σ) :
    run control (checkedFrames bound make fallback) baseWidth cutoff k rows layout F state =
      run control make baseWidth cutoff k rows layout F state := by
  apply run_congr_frames
  intro depth width volume c hd hwidth hvolume
  exact if_pos ⟨hd.trans hk,hwidth.trans hw,hvolume.trans hv⟩

end
end CSL.StatefulRecursiveExchange


