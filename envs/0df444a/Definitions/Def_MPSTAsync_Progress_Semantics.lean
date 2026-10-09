-- Prove2me | Definitions.Def_MPSTAsync_Progress_Semantics
-- name    : MPSTAsync_Progress_Semantics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:10:13.299322+00:00
-- url     : https://prove2.me/theorems/5599aa03-d80b-4828-a2bc-3fb7fa7d68e9
-- title:
--   Def. 2.1 and Figs. 2–3 — programs, congruence and reduction
-- statement:
--   **Structural congruence** identifies processes by the equations of Fig. 2, including alpha conversion, parallel rearrangement, scope laws and empty-queue removal. **Reduction** has the base communication and conditional rules of Fig. 3 and is closed under scope, parallel composition, declarations and congruence. A **program** has no queues or restricted session channels up to congruence, and has no free session channels or process variables.
--
--   $$P\longrightarrow Q\quad\text{and}\quad P\equiv Q$$
--
--   The module defines free and bound identifiers and substitution for received values and session parameters.
--
--   **Formalization Note** Substitution is partial at ill-sorted name subjects and requires freshness against bound names and channels in the reduction rules. Session linking uses a requester and exactly the accepts numbered $2$ through $n$ with one common channel vector. As printed in Fig. 3 and explained in Remark 2.2, [SREC] receives the channel vector $\widetilde t$ that is already the binder of $s?((\widetilde t));P$, without substitution; the binder is matched to the queued names by alpha conversion inside $\equiv$. Structural congruence includes $(\nu a)(\nu\widetilde s)P\equiv(\nu\widetilde s)(\nu a)P$, the mixed instance of $(\nu nn')P\equiv(\nu n'n)P$.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 7–9, Def. 2.1, Figs. 2–3, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Syntax

set_option autoImplicit false

namespace MPSTAsync.Progress

def Val.names : Val → Finset Name
  | .name a => {a}
  | .tt | .ff => ∅

def Expr.names : Expr → Finset Name
  | .val v => v.names
  | .and e f | .or e f => e.names ∪ f.names
  | .not e => e.names

def Msg.names : Msg → Finset Name
  | .vals vs => vs.foldl (fun a v => a ∪ v.names) ∅
  | .label _ | .chans _ => ∅

def Msg.freeChans : Msg → Finset Chan
  | .chans cs => cs.toFinset
  | .label _ | .vals _ => ∅

-- Free names, session channels, and process variables, plus bound identifiers.
mutual
def Proc.freeNamesFuel : ℕ → Proc → Finset Name
  | 0, _ => ∅
  | n+1, .request a _ _ P | n+1, .accept a _ _ P => insert a (P.freeNamesFuel n)
  | n+1, .send _ es P => es.foldl (fun a e => a ∪ e.names) (P.freeNamesFuel n)
  | n+1, .recv _ xs P => P.freeNamesFuel n \ xs.toFinset
  | n+1, .deleg _ _ P | n+1, .srecv _ _ P
  | n+1, .sel _ _ P | n+1, .resS _ P => P.freeNamesFuel n
  | n+1, .branch _ bs => bs.foldl (fun a x => a ∪ x.2.freeNamesFuel n) ∅
  | n+1, .ite e P Q => e.names ∪ P.freeNamesFuel n ∪ Q.freeNamesFuel n
  | n+1, .par P Q => P.freeNamesFuel n ∪ Q.freeNamesFuel n
  | _+1, .nil => ∅
  | n+1, .resN a P => (P.freeNamesFuel n).erase a
  | n+1, .defn D P => P.freeNamesFuel n ∪
      D.foldl (fun a d => a ∪ d.freeNamesFuel n) ∅
  | _+1, .call _ es _ => es.foldl (fun a e => a ∪ e.names) ∅
  | _+1, .queue _ h => h.foldl (fun a x => a ∪ x.names) ∅
def Decl.freeNamesFuel : ℕ → Decl → Finset Name
  | 0, _ => ∅
  | n+1, .mk _ xs _ P => P.freeNamesFuel n \ xs.toFinset
end

noncomputable def Proc.freeNames (P : Proc) : Finset Name :=
  P.freeNamesFuel (sizeOf P)
noncomputable def Decl.freeNames (D : Decl) : Finset Name :=
  D.freeNamesFuel (sizeOf D)

mutual
def Proc.freeChansFuel : ℕ → Proc → Finset Chan
  | 0, _ => ∅
  | n+1, .request _ _ s P | n+1, .accept _ _ s P => P.freeChansFuel n \ s.toFinset
  | n+1, .send c _ P | n+1, .recv c _ P | n+1, .sel c _ P =>
      insert c (P.freeChansFuel n)
  | n+1, .deleg c ts P => insert c (ts.toFinset ∪ P.freeChansFuel n)
  | n+1, .srecv c ts P => insert c (P.freeChansFuel n \ ts.toFinset)
  | n+1, .branch c bs =>
      insert c (bs.foldl (fun a x => a ∪ x.2.freeChansFuel n) ∅)
  | n+1, .ite _ P Q | n+1, .par P Q => P.freeChansFuel n ∪ Q.freeChansFuel n
  | _+1, .nil => ∅
  | n+1, .resN _ P => P.freeChansFuel n
  | n+1, .resS s P => P.freeChansFuel n \ s.toFinset
  | n+1, .defn D P => P.freeChansFuel n ∪
      D.foldl (fun a d => a ∪ d.freeChansFuel n) ∅
  | _+1, .call _ _ ss => ss.toFinset
  | _+1, .queue c h => insert c (h.foldl (fun a x => a ∪ x.freeChans) ∅)
def Decl.freeChansFuel : ℕ → Decl → Finset Chan
  | 0, _ => ∅
  | n+1, .mk _ _ ss P => P.freeChansFuel n \ ss.toFinset
end

noncomputable def Proc.freeChans (P : Proc) : Finset Chan :=
  P.freeChansFuel (sizeOf P)
noncomputable def Decl.freeChans (D : Decl) : Finset Chan :=
  D.freeChansFuel (sizeOf D)

mutual
def Proc.freePVarsFuel : ℕ → Proc → Finset PVar
  | 0, _ => ∅
  | n+1, .request _ _ _ P | n+1, .accept _ _ _ P
  | n+1, .send _ _ P | n+1, .recv _ _ P
  | n+1, .deleg _ _ P | n+1, .srecv _ _ P
  | n+1, .sel _ _ P | n+1, .resN _ P | n+1, .resS _ P => P.freePVarsFuel n
  | n+1, .branch _ bs => bs.foldl (fun a x => a ∪ x.2.freePVarsFuel n) ∅
  | n+1, .ite _ P Q | n+1, .par P Q => P.freePVarsFuel n ∪ Q.freePVarsFuel n
  | _+1, .nil | _+1, .queue _ _ => ∅
  | n+1, .defn D P => (P.freePVarsFuel n ∪ D.foldl (fun a d => a ∪ d.freePVarsFuel n) ∅) \
      D.foldl (fun a d => match d with | .mk X _ _ _ => insert X a) ∅
  | _+1, .call X _ _ => {X}
def Decl.freePVarsFuel : ℕ → Decl → Finset PVar
  | 0, _ => ∅
  | n+1, .mk _ _ _ P => P.freePVarsFuel n
end

noncomputable def Proc.freePVars (P : Proc) : Finset PVar :=
  P.freePVarsFuel (sizeOf P)
noncomputable def Decl.freePVars (D : Decl) : Finset PVar :=
  D.freePVarsFuel (sizeOf D)

mutual
def Proc.boundNamesFuel : ℕ → Proc → Finset Name
  | 0, _ => ∅
  | n+1, .request _ _ _ P | n+1, .accept _ _ _ P
  | n+1, .send _ _ P | n+1, .deleg _ _ P
  | n+1, .srecv _ _ P | n+1, .sel _ _ P | n+1, .resS _ P => P.boundNamesFuel n
  | n+1, .recv _ xs P => xs.toFinset ∪ P.boundNamesFuel n
  | n+1, .branch _ bs => bs.foldl (fun a x => a ∪ x.2.boundNamesFuel n) ∅
  | n+1, .ite _ P Q | n+1, .par P Q => P.boundNamesFuel n ∪ Q.boundNamesFuel n
  | _+1, .nil | _+1, .call _ _ _ | _+1, .queue _ _ => ∅
  | n+1, .resN a P => insert a (P.boundNamesFuel n)
  | n+1, .defn D P => P.boundNamesFuel n ∪
      D.foldl (fun a d => a ∪ d.boundNamesFuel n) ∅
def Decl.boundNamesFuel : ℕ → Decl → Finset Name
  | 0, _ => ∅
  | n+1, .mk _ xs _ P => xs.toFinset ∪ P.boundNamesFuel n
end

noncomputable def Proc.boundNames (P : Proc) : Finset Name :=
  P.boundNamesFuel (sizeOf P)
noncomputable def Decl.boundNames (D : Decl) : Finset Name :=
  D.boundNamesFuel (sizeOf D)

mutual
def Proc.boundChansFuel : ℕ → Proc → Finset Chan
  | 0, _ => ∅
  | n+1, .request _ _ s P | n+1, .accept _ _ s P => s.toFinset ∪ P.boundChansFuel n
  | n+1, .send _ _ P | n+1, .recv _ _ P
  | n+1, .deleg _ _ P | n+1, .sel _ _ P | n+1, .resN _ P => P.boundChansFuel n
  | n+1, .srecv _ ts P => ts.toFinset ∪ P.boundChansFuel n
  | n+1, .branch _ bs => bs.foldl (fun a x => a ∪ x.2.boundChansFuel n) ∅
  | n+1, .ite _ P Q | n+1, .par P Q => P.boundChansFuel n ∪ Q.boundChansFuel n
  | _+1, .nil | _+1, .call _ _ _ | _+1, .queue _ _ => ∅
  | n+1, .resS s P => s.toFinset ∪ P.boundChansFuel n
  | n+1, .defn D P => P.boundChansFuel n ∪
      D.foldl (fun a d => a ∪ d.boundChansFuel n) ∅
def Decl.boundChansFuel : ℕ → Decl → Finset Chan
  | 0, _ => ∅
  | n+1, .mk _ _ ss P => ss.toFinset ∪ P.boundChansFuel n
end

noncomputable def Proc.boundChans (P : Proc) : Finset Chan :=
  P.boundChansFuel (sizeOf P)
noncomputable def Decl.boundChans (D : Decl) : Finset Chan :=
  D.boundChansFuel (sizeOf D)

-- Value substitution is partial when a Boolean is put in a name-subject position.
def Val.subst (ρ : List (Name × Val)) : Val → Val
  | .name a => (ρ.lookup a).getD (.name a)
  | .tt => .tt
  | .ff => .ff

def Val.asName? : Val → Option Name
  | .name a => some a
  | .tt | .ff => none

def Expr.subst (ρ : List (Name × Val)) : Expr → Expr
  | .val v => .val (v.subst ρ)
  | .and e f => .and (e.subst ρ) (f.subst ρ)
  | .or e f => .or (e.subst ρ) (f.subst ρ)
  | .not e => .not (e.subst ρ)

def substChan (ρ : List (Chan × Chan)) (c : Chan) : Chan := (ρ.lookup c).getD c
def substName? (ρ : List (Name × Val)) (a : Name) : Option Name :=
  (Val.subst ρ (.name a)).asName?

mutual
def Proc.substFuel? : ℕ → List (Name × Val) → List (Chan × Chan) → Proc → Option Proc
  | 0, _, _, _ => none
  | fuel+1, ρ, κ, .request a n s P => do
      let b ← substName? ρ a
      let Q ← Proc.substFuel? fuel ρ (κ.filter (fun x => x.1 ∉ s)) P
      pure (.request b n s Q)
  | fuel+1, ρ, κ, .accept a p s P => do
      let b ← substName? ρ a
      let Q ← Proc.substFuel? fuel ρ (κ.filter (fun x => x.1 ∉ s)) P
      pure (.accept b p s Q)
  | fuel+1, ρ, κ, .send c es P => do
      let Q ← Proc.substFuel? fuel ρ κ P
      pure (.send (substChan κ c) (es.map (Expr.subst ρ)) Q)
  | fuel+1, ρ, κ, .recv c xs P => do
      let Q ← Proc.substFuel? fuel (ρ.filter (fun x => x.1 ∉ xs)) κ P
      pure (.recv (substChan κ c) xs Q)
  | fuel+1, ρ, κ, .deleg c ts P => do
      let Q ← Proc.substFuel? fuel ρ κ P
      pure (.deleg (substChan κ c) (ts.map (substChan κ)) Q)
  | fuel+1, ρ, κ, .srecv c ts P => do
      let Q ← Proc.substFuel? fuel ρ (κ.filter (fun x => x.1 ∉ ts)) P
      pure (.srecv (substChan κ c) ts Q)
  | fuel+1, ρ, κ, .sel c l P => do
      let Q ← Proc.substFuel? fuel ρ κ P
      pure (.sel (substChan κ c) l Q)
  | fuel+1, ρ, κ, .branch c bs => do
      let bs' ← bs.mapM (fun x => do let Q ← Proc.substFuel? fuel ρ κ x.2; pure (x.1,Q))
      pure (.branch (substChan κ c) bs')
  | fuel+1, ρ, κ, .ite e P Q => do
      let P' ← Proc.substFuel? fuel ρ κ P
      let Q' ← Proc.substFuel? fuel ρ κ Q
      pure (.ite (e.subst ρ) P' Q')
  | fuel+1, ρ, κ, .par P Q => do
      let P' ← Proc.substFuel? fuel ρ κ P
      let Q' ← Proc.substFuel? fuel ρ κ Q
      pure (.par P' Q')
  | _+1, _, _, .nil => some .nil
  | fuel+1, ρ, κ, .resN a P => do
      let Q ← Proc.substFuel? fuel (ρ.filter (fun x => x.1 ≠ a)) κ P
      pure (.resN a Q)
  | fuel+1, ρ, κ, .resS s P => do
      let Q ← Proc.substFuel? fuel ρ (κ.filter (fun x => x.1 ∉ s)) P
      pure (.resS s Q)
  | fuel+1, ρ, κ, .defn D P => do
      let D' ← D.mapM (Decl.substFuel? fuel ρ κ)
      let Q ← Proc.substFuel? fuel ρ κ P
      pure (.defn D' Q)
  | _+1, ρ, κ, .call X es ss => some (.call X (es.map (Expr.subst ρ)) (ss.map (substChan κ)))
  | _+1, ρ, κ, .queue c h => some (.queue (substChan κ c) (h.map fun m => match m with
      | .label l => .label l
      | .vals vs => .vals (vs.map (Val.subst ρ))
      | .chans cs => .chans (cs.map (substChan κ))))
def Decl.substFuel? : ℕ → List (Name × Val) → List (Chan × Chan) → Decl → Option Decl
  | 0, _, _, _ => none
  | fuel+1, ρ, κ, .mk X xs ss P => do
      let Q ← Proc.substFuel? fuel (ρ.filter (fun x => x.1 ∉ xs))
        (κ.filter (fun x => x.1 ∉ ss)) P
      pure (.mk X xs ss Q)
end

noncomputable def Proc.subst? (P : Proc) (ρ : List (Name × Val))
    (κ : List (Chan × Chan)) : Option Proc :=
  Proc.substFuel? (sizeOf P) ρ κ P

def CaptureFree (ρ : List (Name × Val)) (P : Proc) : Prop :=
  (ρ.foldl (fun s x => s ∪ x.2.names) ∅ : Finset Name) ∩ P.boundNames = ∅

def CaptureFreeChan (κ : List (Chan × Chan)) (P : Proc) : Prop :=
  (κ.map Prod.snd).toFinset ∩ P.boundChans = ∅

-- A simultaneous bijective change of bound identifiers witnesses alpha conversion.
def Val.rename (ν : Name → Name) : Val → Val
  | .name a => .name (ν a)
  | .tt => .tt
  | .ff => .ff
def Expr.rename (ν : Name → Name) : Expr → Expr
  | .val v => .val (v.rename ν)
  | .and e f => .and (e.rename ν) (f.rename ν)
  | .or e f => .or (e.rename ν) (f.rename ν)
  | .not e => .not (e.rename ν)
def Msg.rename (ν : Name → Name) (χ : Chan → Chan) : Msg → Msg
  | .label l => .label l
  | .vals vs => .vals (vs.map (Val.rename ν))
  | .chans cs => .chans (cs.map χ)

mutual
def Proc.renameFuel : ℕ → (Name → Name) → (Chan → Chan) → (PVar → PVar) → Proc → Proc
  | 0, _, _, _, P => P
  | n+1, ν, χ, ξ, .request a j s P =>
      .request (ν a) j (s.map χ) (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .accept a p s P =>
      .accept (ν a) p (s.map χ) (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .send c es P =>
      .send (χ c) (es.map (Expr.rename ν)) (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .recv c xs P =>
      .recv (χ c) (xs.map ν) (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .deleg c ts P =>
      .deleg (χ c) (ts.map χ) (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .srecv c ts P =>
      .srecv (χ c) (ts.map χ) (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .sel c l P => .sel (χ c) l (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .branch c bs =>
      .branch (χ c) (bs.map fun x => (x.1,Proc.renameFuel n ν χ ξ x.2))
  | n+1, ν, χ, ξ, .ite e P Q =>
      .ite (e.rename ν) (Proc.renameFuel n ν χ ξ P) (Proc.renameFuel n ν χ ξ Q)
  | n+1, ν, χ, ξ, .par P Q =>
      .par (Proc.renameFuel n ν χ ξ P) (Proc.renameFuel n ν χ ξ Q)
  | _+1, _, _, _, .nil => .nil
  | n+1, ν, χ, ξ, .resN a P => .resN (ν a) (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .resS s P => .resS (s.map χ) (Proc.renameFuel n ν χ ξ P)
  | n+1, ν, χ, ξ, .defn D P =>
      .defn (D.map (Decl.renameFuel n ν χ ξ)) (Proc.renameFuel n ν χ ξ P)
  | _+1, ν, χ, ξ, .call X es ss =>
      .call (ξ X) (es.map (Expr.rename ν)) (ss.map χ)
  | _+1, ν, χ, _, .queue c h => .queue (χ c) (h.map (Msg.rename ν χ))
def Decl.renameFuel : ℕ → (Name → Name) → (Chan → Chan) → (PVar → PVar) → Decl → Decl
  | 0, _, _, _, D => D
  | n+1, ν, χ, ξ, .mk X xs ss P =>
      .mk (ξ X) (xs.map ν) (ss.map χ) (Proc.renameFuel n ν χ ξ P)
end

noncomputable def Proc.rename (P : Proc) (ν : Name → Name)
    (χ : Chan → Chan) (ξ : PVar → PVar) : Proc :=
  Proc.renameFuel (sizeOf P) ν χ ξ P


def Alpha (P Q : Proc) : Prop :=
  ∃ ν χ ξ, Function.Bijective ν ∧ Function.Bijective χ ∧ Function.Bijective ξ ∧
    (∀ a ∈ P.freeNames, ν a = a) ∧ (∀ c ∈ P.freeChans, χ c = c) ∧
    (∀ X ∈ P.freePVars, ξ X = X) ∧ Q = P.rename ν χ ξ

-- Figure 2: symmetric transitive congruence generated by its eleven equations.
inductive Congr : Proc → Proc → Prop where
  | alpha (P Q : Proc) (h : Alpha P Q) : Congr P Q
  | refl (P : Proc) : Congr P P
  | symm (P Q : Proc) (h : Congr P Q) : Congr Q P
  | trans (P Q R : Proc) (h : Congr P Q) (h' : Congr Q R) : Congr P R
  | parNil (P : Proc) : Congr (.par P .nil) P
  | parComm (P Q : Proc) : Congr (.par P Q) (.par Q P)
  | parAssoc (P Q R : Proc) : Congr (.par (.par P Q) R) (.par P (.par Q R))
  | scopeN (a : Name) (P Q : Proc) (h : a ∉ Q.freeNames) :
      Congr (.par (.resN a P) Q) (.resN a (.par P Q))
  | scopeS (s : List Chan) (P Q : Proc) (h : ∀ c ∈ s, c ∉ Q.freeChans) :
      Congr (.par (.resS s P) Q) (.resS s (.par P Q))
  | resNN (a b : Name) (P : Proc) : Congr (.resN a (.resN b P)) (.resN b (.resN a P))
  | resSS (s t : List Chan) (P : Proc) : Congr (.resS s (.resS t P)) (.resS t (.resS s P))
  | resNS (a : Name) (s : List Chan) (P : Proc) :
      Congr (.resN a (.resS s P)) (.resS s (.resN a P))
  | resNilN (a : Name) : Congr (.resN a .nil) .nil
  | resNilS (s : List Chan) : Congr (.resS s .nil) .nil
  | emptyQueues (s : List Chan) : Congr (.resS s (Proc.queues s)) .nil
  | defNil (D : List Decl) : Congr (.defn D .nil) .nil
  | defResN (D : List Decl) (a : Name) (P : Proc) (h : ∀ d ∈ D, a ∉ d.freeNames) :
      Congr (.defn D (.resN a P)) (.resN a (.defn D P))
  | defResS (D : List Decl) (s : List Chan) (P : Proc)
      (h : ∀ d ∈ D, ∀ c ∈ s, c ∉ d.freeChans) :
      Congr (.defn D (.resS s P)) (.resS s (.defn D P))
  | defPar (D : List Decl) (P Q : Proc)
      (h : ∀ d ∈ D, ∀ X ∈ (match d with | .mk X _ _ _ => ({X} : Finset PVar)), X ∉ Q.freePVars) :
      Congr (.par (.defn D P) Q) (.defn D (.par P Q))
  | defMerge (D D' : List Decl) (P : Proc)
      (h : (D.map fun d => match d with | .mk X _ _ _ => X).toFinset ∩
           (D'.map fun d => match d with | .mk X _ _ _ => X).toFinset = ∅) :
      Congr (.defn D (.defn D' P)) (.defn (D ++ D') P)
  | request (a : Name) (n : ℕ) (s : List Chan) (P Q : Proc) (h : Congr P Q) :
      Congr (.request a n s P) (.request a n s Q)
  | accept (a : Name) (p : ℕ) (s : List Chan) (P Q : Proc) (h : Congr P Q) :
      Congr (.accept a p s P) (.accept a p s Q)
  | send (c : Chan) (es : List Expr) (P Q : Proc) (h : Congr P Q) :
      Congr (.send c es P) (.send c es Q)
  | recv (c : Chan) (xs : List Name) (P Q : Proc) (h : Congr P Q) :
      Congr (.recv c xs P) (.recv c xs Q)
  | deleg (c : Chan) (ts : List Chan) (P Q : Proc) (h : Congr P Q) :
      Congr (.deleg c ts P) (.deleg c ts Q)
  | srecv (c : Chan) (ts : List Chan) (P Q : Proc) (h : Congr P Q) :
      Congr (.srecv c ts P) (.srecv c ts Q)
  | sel (c : Chan) (l : Label) (P Q : Proc) (h : Congr P Q) :
      Congr (.sel c l P) (.sel c l Q)
  | branch (c : Chan) (bs bs' : List (Label × Proc))
      (hlabels : bs.map Prod.fst = bs'.map Prod.fst)
      (h : ∀ x ∈ bs, ∀ y ∈ bs', x.1 = y.1 → Congr x.2 y.2) :
      Congr (.branch c bs) (.branch c bs')
  | iteLeft (e : Expr) (P P' Q : Proc) (h : Congr P P') :
      Congr (.ite e P Q) (.ite e P' Q)
  | iteRight (e : Expr) (P Q Q' : Proc) (h : Congr Q Q') :
      Congr (.ite e P Q) (.ite e P Q')
  | parLeft (P P' Q : Proc) (h : Congr P P') : Congr (.par P Q) (.par P' Q)
  | parRight (P Q Q' : Proc) (h : Congr Q Q') : Congr (.par P Q) (.par P Q')
  | resN (a : Name) (P Q : Proc) (h : Congr P Q) : Congr (.resN a P) (.resN a Q)
  | resS (s : List Chan) (P Q : Proc) (h : Congr P Q) : Congr (.resS s P) (.resS s Q)
  | defn (D : List Decl) (P Q : Proc) (h : Congr P Q) :
      Congr (.defn D P) (.defn D Q)
  | defnBodies (n : ℕ)
      (X : Fin n → PVar) (xs : Fin n → List Name) (ss : Fin n → List Chan)
      (Ps Qs : Fin n → Proc) (P : Proc)
      (h : ∀ i, Congr (Ps i) (Qs i)) :
      Congr
        (.defn (List.ofFn fun i => .mk (X i) (xs i) (ss i) (Ps i)) P)
        (.defn (List.ofFn fun i => .mk (X i) (xs i) (ss i) (Qs i)) P)

-- Figure 3, with the shared-name and session-channel binders represented explicitly.
inductive Reduces : Proc → Proc → Prop where
  | LINK (a : Name) (n : ℕ) (s : List Chan) (P : Proc)
      (ps : Fin (n-1) → Proc) (hn : 2 ≤ n) (hs : s.Nodup) :
      Reduces
        (.par (.request a n s P)
          (Proc.parList (List.ofFn fun i : Fin (n-1) => .accept a (i.val+2) s (ps i))))
        (.resS s (Proc.par (Proc.parList (P :: List.ofFn ps)) (Proc.queues s)))
  | SEND (c : Chan) (es : List Expr) (vs : List Val) (P : Proc) (h : List Msg)
      (he : EvalList es vs) :
      Reduces (.par (.send c es P) (.queue c h))
        (.par P (.queue c (h ++ [.vals vs])))
  | DELEG (c : Chan) (ts : List Chan) (P : Proc) (h : List Msg) :
      Reduces (.par (.deleg c ts P) (.queue c h))
        (.par P (.queue c (h ++ [.chans ts])))
  | LABEL (c : Chan) (l : Label) (P : Proc) (h : List Msg) :
      Reduces (.par (.sel c l P) (.queue c h))
        (.par P (.queue c (h ++ [.label l])))
  | RECV (c : Chan) (xs : List Name) (P P' : Proc) (vs : List Val) (h : List Msg)
      (hlen : xs.length = vs.length)
      (hcap : CaptureFree (xs.zip vs) P)
      (hsub : P.subst? (xs.zip vs) [] = some P') :
      Reduces (.par (.recv c xs P) (.queue c (.vals vs :: h)))
        (.par P' (.queue c h))
  -- [SREC] uses the received channel names t̃ without substitution (Remark 2.2);
  -- the bound t̃ is matched to the queued t̃ by alpha conversion through [STR].
  | SREC (c : Chan) (ts : List Chan) (P : Proc) (h : List Msg) :
      Reduces (.par (.srecv c ts P) (.queue c (.chans ts :: h)))
        (.par P (.queue c h))
  | BRANCH (c : Chan) (bs : List (Label × Proc)) (l : Label) (P : Proc) (h : List Msg)
      (hin : (l,P) ∈ bs) :
      Reduces (.par (.branch c bs) (.queue c (.label l :: h)))
        (.par P (.queue c h))
  | IFT (e : Expr) (P Q : Proc) (he : Eval e .tt) : Reduces (.ite e P Q) P
  | IFF (e : Expr) (P Q : Proc) (he : Eval e .ff) : Reduces (.ite e P Q) Q
  | DEF (D : List Decl) (X : PVar) (es : List Expr) (ss : List Chan)
      (xs : List Name) (ts : List Chan) (B P' Q : Proc) (vs : List Val)
      (hmem : .mk X xs ts B ∈ D) (he : EvalList es vs)
      (hlen : xs.length = vs.length ∧ ts.length = ss.length)
      (hcap : CaptureFree (xs.zip vs) B)
      (hcapC : CaptureFreeChan (ts.zip ss) B)
      (hsub : B.subst? (xs.zip vs) (ts.zip ss) = some P') :
      Reduces (.defn D (.par (.call X es ss) Q)) (.defn D (.par P' Q))
  | SCOPN (a : Name) (P Q : Proc) (h : Reduces P Q) :
      Reduces (.resN a P) (.resN a Q)
  | SCOPS (s : List Chan) (P Q : Proc) (h : Reduces P Q) :
      Reduces (.resS s P) (.resS s Q)
  | PAR (P P' Q : Proc) (h : Reduces P P') :
      Reduces (.par P Q) (.par P' Q)
  | DEFIN (D : List Decl) (P Q : Proc) (h : Reduces P Q) :
      Reduces (.defn D P) (.defn D Q)
  | STR (P P' Q' Q : Proc) (h₁ : Congr P P') (h₂ : Reduces P' Q')
      (h₃ : Congr Q' Q) : Reduces P Q

def Proc.noQueuesFuel : ℕ → Proc → Prop
  | 0, _ => False
  | _+1, .queue _ _ => False
  | n+1, .request _ _ _ P | n+1, .accept _ _ _ P
  | n+1, .send _ _ P | n+1, .recv _ _ P
  | n+1, .deleg _ _ P | n+1, .srecv _ _ P
  | n+1, .sel _ _ P | n+1, .resN _ P | n+1, .resS _ P => P.noQueuesFuel n
  | n+1, .branch _ bs => ∀ x ∈ bs, x.2.noQueuesFuel n
  | n+1, .ite _ P Q | n+1, .par P Q => P.noQueuesFuel n ∧ Q.noQueuesFuel n
  | n+1, .defn D P => P.noQueuesFuel n ∧
      ∀ d ∈ D, match d with | .mk _ _ _ Q => Q.noQueuesFuel n
  | _+1, .nil | _+1, .call _ _ _ => True

noncomputable def Proc.noQueues (P : Proc) : Prop :=
  P.noQueuesFuel (sizeOf P)

def Proc.noResSFuel : ℕ → Proc → Prop
  | 0, _ => False
  | _+1, .resS _ _ => False
  | n+1, .request _ _ _ P | n+1, .accept _ _ _ P
  | n+1, .send _ _ P | n+1, .recv _ _ P
  | n+1, .deleg _ _ P | n+1, .srecv _ _ P
  | n+1, .sel _ _ P | n+1, .resN _ P => P.noResSFuel n
  | n+1, .branch _ bs => ∀ x ∈ bs, x.2.noResSFuel n
  | n+1, .ite _ P Q | n+1, .par P Q => P.noResSFuel n ∧ Q.noResSFuel n
  | n+1, .defn D P => P.noResSFuel n ∧
      ∀ d ∈ D, match d with | .mk _ _ _ Q => Q.noResSFuel n
  | _+1, .nil | _+1, .call _ _ _ | _+1, .queue _ _ => True

noncomputable def Proc.noResS (P : Proc) : Prop :=
  P.noResSFuel (sizeOf P)

def IsProgramPhrase (P : Proc) : Prop :=
  ∃ Q, Congr P Q ∧ Q.noQueues ∧ Q.noResS

def IsProgram (P : Proc) : Prop :=
  ∃ Q, Congr P Q ∧ Q.noQueues ∧ Q.noResS ∧ Q.freeChans = ∅ ∧ Q.freePVars = ∅

end MPSTAsync.Progress


