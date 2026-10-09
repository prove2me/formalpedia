-- Prove2me | Definitions.Def_MPSTAsync_Progress_Activity
-- name    : MPSTAsync_Progress_Activity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:16:21.495187+00:00
-- url     : https://prove2.me/theorems/aa584303-2600-4026-8e95-eabe02f7cc38
-- title:
--   pp. 34–37, Defs. 5.24–5.27 — activity, queue-fullness, simplicity and well-linkedness
-- statement:
--   A **reduction context** exposes one process position outside communication prefixes and conditional branches. An **active prefix** is a request, accept, send, receive, delegation or label action available at that position after any number of declaration unfoldings by [DEF]. A redex at channel $s$ contains such an active session prefix and the partners required by a reduction rule. A process is **queue-full** when its mentioned queue channels equal the channels in its session typing. It is **simple** when it admits a restricted runtime typing derivation; it is **well-linked** when every reduct's active shared-name prefix belongs to a redex.
--
--   $$\operatorname{WellLinked}(P)\iff\forall Q\,(P\longrightarrow^*Q\Rightarrow\text{each active shared-name prefix of }Q\text{ is in a redex}).$$
--
--   These predicates state the hypotheses of progress and its intermediate results.
--
--   **Formalization Note** The restriction in Def. 5.25 is applied to the Figure 7 rules of the runtime derivation; [SREC] and [DELEG] are absent, following Appendix B.8's correction of the printed [RCV] slip. In [CONC], each of $\Delta,\Delta'$ has at most one entry. Context occurrences count every free channel occurrence outside the hole. The redex predicates identify the rule that fires, and well-linkedness checks each exposed shared-name occurrence separately. Activity allows any finite number of [DEF] unfoldings.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 34–37, Defs. 5.24–5.27 and Appendix B.8, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Runtime

set_option autoImplicit false

namespace MPSTAsync.Progress

-- Reduction contexts from p. 34, with one hole.
inductive Ctx where
  | hole
  | parLeft (E : Ctx) (P : Proc)
  | parRight (P : Proc) (E : Ctx)
  | resN (a : Name) (E : Ctx)
  | resS (s : List Chan) (E : Ctx)
  | defn (D : List Decl) (E : Ctx)

def Ctx.fill (E : Ctx) (R : Proc) : Proc :=
  match E with
  | .hole => R
  | .parLeft C P => .par (C.fill R) P
  | .parRight P C => .par P (C.fill R)
  | .resN a C => .resN a (C.fill R)
  | .resS s C => .resS s (C.fill R)
  | .defn D C => .defn D (C.fill R)

-- Count free occurrences of c in process positions, including subjects,
-- delegated channels, calls, queue names, and channel messages.
mutual
def Proc.occFreeFuel : ℕ → Chan → Finset Chan → Proc → ℕ
  | 0, _, _, _ => 0
  | n+1, c, bound, .request _ _ s P | n+1, c, bound, .accept _ _ s P =>
      P.occFreeFuel n c (bound ∪ s.toFinset)
  | n+1, c, bound, .send d _ P | n+1, c, bound, .recv d _ P
  | n+1, c, bound, .sel d _ P =>
      (if d = c ∧ c ∉ bound then 1 else 0) + P.occFreeFuel n c bound
  | n+1, c, bound, .deleg d ts P =>
      (if d = c ∧ c ∉ bound then 1 else 0) +
      (ts.filter (· = c)).length * (if c ∈ bound then 0 else 1) + P.occFreeFuel n c bound
  | n+1, c, bound, .srecv d ts P =>
      (if d = c ∧ c ∉ bound then 1 else 0) + P.occFreeFuel n c (bound ∪ ts.toFinset)
  | n+1, c, bound, .branch d bs => (if d = c ∧ c ∉ bound then 1 else 0) +
      bs.foldl (fun m x => m + x.2.occFreeFuel n c bound) 0
  | n+1, c, bound, .ite _ P Q | n+1, c, bound, .par P Q =>
      P.occFreeFuel n c bound + Q.occFreeFuel n c bound
  | _+1, _, _, .nil => 0
  | n+1, c, bound, .resN _ P => P.occFreeFuel n c bound
  | n+1, c, bound, .resS s P => P.occFreeFuel n c (bound ∪ s.toFinset)
  | n+1, c, bound, .defn D P => P.occFreeFuel n c bound +
      D.foldl (fun m d => m + d.occFreeFuel n c bound) 0
  | _+1, c, bound, .call _ _ ss =>
      (ss.filter (· = c)).length * (if c ∈ bound then 0 else 1)
  | _+1, c, bound, .queue d h => (if d = c ∧ c ∉ bound then 1 else 0) +
      h.foldl (fun n m => n + match m with
        | .chans ss => (ss.filter (· = c)).length * (if c ∈ bound then 0 else 1)
        | _ => 0) 0
def Decl.occFreeFuel : ℕ → Chan → Finset Chan → Decl → ℕ
  | 0, _, _, _ => 0
  | n+1, c, bound, .mk _ _ ss P => P.occFreeFuel n c (bound ∪ ss.toFinset)
end

noncomputable def Proc.occFree (P : Proc) (c : Chan) (bound : Finset Chan) : ℕ :=
  P.occFreeFuel (sizeOf P) c bound
noncomputable def Decl.occFree (D : Decl) (c : Chan) (bound : Finset Chan) : ℕ :=
  D.occFreeFuel (sizeOf D) c bound

noncomputable def Ctx.occ (c : Chan) : Ctx → ℕ
  | .hole => 0
  | .parLeft E P => E.occ c + P.occFree c ∅
  | .parRight P E => P.occFree c ∅ + E.occ c
  | .resN _ E => E.occ c
  | .resS s E => if c ∈ s then 0 else E.occ c
  | .defn D E => E.occ c + D.foldl (fun n d => n + d.occFree c ∅) 0

inductive Subject where
  | shared (a : Name)
  | session (c : Chan)

inductive Direction where
  | emit | receive

-- Active prefixes are outside prefixes and conditional branches. A call in
-- scope is unfolded by its declaration; the index bounds the number of unfoldings.
inductive ActivePrefix : ℕ → List Decl → Proc → Subject → Direction → Prop where
  | request (fuel : ℕ) (D : List Decl) (a : Name) (n : ℕ) (s : List Chan) (P : Proc) :
      ActivePrefix fuel D (.request a n s P) (.shared a) .emit
  | accept (fuel : ℕ) (D : List Decl) (a : Name) (p : Role) (s : List Chan) (P : Proc) :
      ActivePrefix fuel D (.accept a p s P) (.shared a) .receive
  | send (fuel : ℕ) (D : List Decl) (c : Chan) (es : List Expr) (P : Proc) :
      ActivePrefix fuel D (.send c es P) (.session c) .emit
  | recv (fuel : ℕ) (D : List Decl) (c : Chan) (xs : List Name) (P : Proc) :
      ActivePrefix fuel D (.recv c xs P) (.session c) .receive
  | deleg (fuel : ℕ) (D : List Decl) (c : Chan) (ts : List Chan) (P : Proc) :
      ActivePrefix fuel D (.deleg c ts P) (.session c) .emit
  | srecv (fuel : ℕ) (D : List Decl) (c : Chan) (ts : List Chan) (P : Proc) :
      ActivePrefix fuel D (.srecv c ts P) (.session c) .receive
  | sel (fuel : ℕ) (D : List Decl) (c : Chan) (l : Label) (P : Proc) :
      ActivePrefix fuel D (.sel c l P) (.session c) .emit
  | branch (fuel : ℕ) (D : List Decl) (c : Chan) (bs : List (Label × Proc)) :
      ActivePrefix fuel D (.branch c bs) (.session c) .receive
  | parLeft (fuel : ℕ) (D : List Decl) (P Q : Proc) (s : Subject) (dir : Direction)
      (h : ActivePrefix fuel D P s dir) : ActivePrefix fuel D (.par P Q) s dir
  | parRight (fuel : ℕ) (D : List Decl) (P Q : Proc) (s : Subject) (dir : Direction)
      (h : ActivePrefix fuel D Q s dir) : ActivePrefix fuel D (.par P Q) s dir
  | resN (fuel : ℕ) (D : List Decl) (a : Name) (P : Proc) (s : Subject) (dir : Direction)
      (h : ActivePrefix fuel D P s dir) : ActivePrefix fuel D (.resN a P) s dir
  | resS (fuel : ℕ) (D : List Decl) (ss : List Chan) (P : Proc) (s : Subject) (dir : Direction)
      (h : ActivePrefix fuel D P s dir) : ActivePrefix fuel D (.resS ss P) s dir
  | defn (fuel : ℕ) (D D' : List Decl) (P : Proc) (s : Subject) (dir : Direction)
      (h : ActivePrefix fuel (D' ++ D) P s dir) :
      ActivePrefix fuel D (.defn D' P) s dir
  | call (fuel : ℕ) (D : List Decl) (X : PVar) (es : List Expr) (ss : List Chan)
      (xs : List Name) (ts : List Chan) (B Q : Proc) (vs : List Val)
      (s : Subject) (dir : Direction)
      (hdecl : .mk X xs ts B ∈ D) (he : EvalList es vs)
      (hlen : xs.length = vs.length ∧ ts.length = ss.length)
      (hcap : CaptureFree (xs.zip vs) B)
      (hcapC : CaptureFreeChan (ts.zip ss) B)
      (hsub : B.subst? (xs.zip vs) (ts.zip ss) = some Q)
      (h : ActivePrefix fuel D Q s dir) :
      ActivePrefix (fuel+1) D (.call X es ss) s dir

-- "after any unfoldings by [DEF]" (p. 35): any finite number of unfoldings.
def ActiveAt (P : Proc) (c : Chan) : Prop :=
  ∃ n d, ActivePrefix n [] P (.session c) d

def ActiveEmit (P : Proc) (c : Chan) : Prop :=
  ∃ n, ActivePrefix n [] P (.session c) .emit

def ActiveRecv (P : Proc) (c : Chan) : Prop :=
  ∃ n, ActivePrefix n [] P (.session c) .receive

def ActiveSharedPrefix (P : Proc) (a : Name) : Prop :=
  ∃ n d, ActivePrefix n [] P (.shared a) d

-- These are precisely the communication redexes of Fig. 3.  A reduction
-- elsewhere in a process does not make an unrelated active prefix a redex.
inductive SessionRedexAt : Proc → Chan → Prop where
  | SEND (c : Chan) (es : List Expr) (vs : List Val) (P : Proc) (h : List Msg)
      (he : EvalList es vs) :
      SessionRedexAt (.par (.send c es P) (.queue c h)) c
  | DELEG (c : Chan) (ts : List Chan) (P : Proc) (h : List Msg) :
      SessionRedexAt (.par (.deleg c ts P) (.queue c h)) c
  | LABEL (c : Chan) (l : Label) (P : Proc) (h : List Msg) :
      SessionRedexAt (.par (.sel c l P) (.queue c h)) c
  | RECV (c : Chan) (xs : List Name) (P P' : Proc) (vs : List Val) (h : List Msg)
      (hlen : xs.length = vs.length) (hcap : CaptureFree (xs.zip vs) P)
      (hsub : P.subst? (xs.zip vs) [] = some P') :
      SessionRedexAt (.par (.recv c xs P) (.queue c (.vals vs :: h))) c
  | SREC (c : Chan) (ts : List Chan) (P : Proc) (h : List Msg) :
      SessionRedexAt (.par (.srecv c ts P) (.queue c (.chans ts :: h))) c
  | BRANCH (c : Chan) (bs : List (Label × Proc)) (l : Label) (P : Proc)
      (h : List Msg) (hin : (l,P) ∈ bs) :
      SessionRedexAt (.par (.branch c bs) (.queue c (.label l :: h))) c

inductive SharedRedexAt : Proc → Name → Prop where
  | LINK (a : Name) (n : ℕ) (s : List Chan) (P : Proc)
      (ps : Fin (n-1) → Proc) (hn : 2 ≤ n) (hs : s.Nodup) :
      SharedRedexAt
        (.par (.request a n s P)
          (Proc.parList (List.ofFn fun i : Fin (n-1) =>
            .accept a (i.val+2) s (ps i)))) a

def HasRedexAt (P : Proc) (c : Chan) : Prop :=
  c ∈ P.freeChans ∧ ∃ (E : Ctx) (R : Proc),
    Congr P (E.fill R) ∧ SessionRedexAt R c

def ReceivingRedexPart (P R : Proc) (c : Chan) : Prop :=
  ActiveRecv R c ∧ ∃ (E : Ctx) (R' Q : Proc),
    Congr R R' ∧ Congr P (E.fill (.par R' Q)) ∧
    SessionRedexAt (.par R' Q) c

def PartOfRedex (P : Proc) (a : Name) : Prop :=
  ∃ (E : Ctx) (R : Proc), Congr P (E.fill R) ∧ SharedRedexAt R a

inductive SharedHead : Proc → Name → Prop where
  | request (a : Name) (n : ℕ) (s : List Chan) (P : Proc) :
      SharedHead (.request a n s P) a
  | accept (a : Name) (p : Role) (s : List Chan) (P : Proc) :
      SharedHead (.accept a p s P) a

-- The selected active occurrence, rather than just some prefix at the same
-- name, participates in this LINK redex.
def SharedRedexContains (R S : Proc) (a : Name) : Prop :=
  ∃ (n : ℕ) (s : List Chan) (P : Proc) (ps : Fin (n-1) → Proc),
    2 ≤ n ∧ s.Nodup ∧
    S = .par (.request a n s P)
      (Proc.parList (List.ofFn fun i : Fin (n-1) =>
        .accept a (i.val+2) s (ps i))) ∧
    (Congr R (.request a n s P) ∨
      ∃ i : Fin (n-1), Congr R (.accept a (i.val+2) s (ps i)))

def WellLinked (P : Proc) : Prop :=
  ∀ Q, Relation.ReflTransGen Reduces P Q →
    ∀ (E : Ctx) (R : Proc) (a : Name),
      Congr Q (E.fill R) → SharedHead R a →
      ∃ (E' : Ctx) (S : Proc),
        Congr Q (E'.fill S) ∧ SharedRedexContains R S a

def QueueFull (q : List Chan) (Δ : Typing) : Prop :=
  q.toFinset = Δ.chans

inductive RTypedSimple : Env → Proc → List Chan → Typing → Prop where
  | MCAST (Γ : Env) (a : Name) (n : ℕ) (s : List Chan) (P : Proc)
      (Δ Δ' : Typing) (G : GType) (T : EType)
      (ha : (a,.shared G) ∈ Γ.names) (hn : 2 ≤ n)
      (hfresh : s.Nodup)
      (hroles : G.pid = (Finset.range n).image (· + 1))
      (hsid : s.length = G.sid.card)
      (hproj : proj G 1 = some T)
      (hins : Typing.Insert Δ s [(.pure T,1)] Δ')
      (hempty : Δ = [])
      (hP : RTypedSimple Γ P [] Δ') : RTypedSimple Γ (.request a n s P) [] Δ
  | MACC (Γ : Env) (a : Name) (p : Role) (s : List Chan) (P : Proc)
      (Δ Δ' : Typing) (G : GType) (T : EType)
      (ha : (a,.shared G) ∈ Γ.names) (hp : p ∈ G.pid)
      (hfresh : s.Nodup)
      (hsid : s.length = G.sid.card) (hproj : proj G p = some T)
      (hins : Typing.Insert Δ s [(.pure T,p)] Δ')
      (hempty : Δ = [])
      (hP : RTypedSimple Γ P [] Δ') : RTypedSimple Γ (.accept a p s P) [] Δ
  | SEND (Γ : Env) (c : Chan) (es : List Expr) (Ss : List ValSort)
      (P : Proc) (Δ Δ' : Typing) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (hc : TypeAt s k c) (he : ExprsTyped Γ es Ss)
      (hrep : Typing.ReplaceOne Δ s p (.pure T) (.pure (.send k (.sorts Ss) T)) Δ')
      (hsingle : Δ.length ≤ 1 ∧ Δ'.length ≤ 1)
      (hP : RTypedSimple Γ P [] Δ) : RTypedSimple Γ (.send c es P) [] Δ'
  | RCV (Γ : Env) (c : Chan) (xs : List Name) (Ss : List ValSort)
      (P : Proc) (Δ Δ' : Typing) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (hc : TypeAt s k c) (hlen : xs.length = Ss.length) (hxs : xs.Nodup)
      (hfresh : ∀ x ∈ xs, x ∉ Γ.names.map Prod.fst)
      (hrep : Typing.ReplaceOne Δ s p (.pure T) (.pure (.recv k (.sorts Ss) T)) Δ')
      (hsingle : Δ.length ≤ 1 ∧ Δ'.length ≤ 1)
      (hP : RTypedSimple (Γ.addNames xs Ss) P [] Δ) :
      RTypedSimple Γ (.recv c xs P) [] Δ'
  | SEL (Γ : Env) (c : Chan) (l : Label) (P : Proc)
      (Δ Δ' : Typing) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (bs : List (Label × EType)) (hc : TypeAt s k c) (hin : (l,T) ∈ bs)
      (hrep : Typing.ReplaceOne Δ s p (.pure T) (.pure (.sel k bs)) Δ')
      (hsingle : Δ.length ≤ 1 ∧ Δ'.length ≤ 1)
      (hP : RTypedSimple Γ P [] Δ) : RTypedSimple Γ (.sel c l P) [] Δ'
  | BRANCH (Γ : Env) (c : Chan) (s : List Chan) (k : ℕ) (p : Role)
      (n : ℕ) (labels : Fin n → Label) (procs : Fin n → Proc)
      (Ts : Fin n → EType) (Δs : Fin n → Typing) (Δ : Typing)
      (hc : TypeAt s k c) (hn : 0 < n)
      (hlabels : (List.ofFn labels).Nodup)
      (hrep : ∀ i, Typing.ReplaceOne (Δs i) s p (.pure (Ts i))
          (.pure (.bra k (List.ofFn fun j => (labels j,Ts j)))) Δ)
      (hsingle : Δ.length ≤ 1)
      (hP : ∀ i, RTypedSimple Γ (procs i) [] (Δs i)) :
      RTypedSimple Γ (.branch c (List.ofFn fun i => (labels i,procs i))) [] Δ
  | IF (Γ : Env) (e : Expr) (P Q : Proc) (Δ : Typing)
      (he : ExprTyped Γ e .bool)
      (hsingle : Δ.length ≤ 1)
      (hP : RTypedSimple Γ P [] Δ) (hQ : RTypedSimple Γ Q [] Δ) :
      RTypedSimple Γ (.ite e P Q) [] Δ
  | CONC (Γ : Env) (P Q : Proc) (q r : List Chan) (Δ Ξ R : Typing)
      (hsingle : Δ.length ≤ 1 ∧ Ξ.length ≤ 1)
      (hqueue : Disjoint q.toFinset r.toFinset)
      (hcomp : TypingComp Δ Ξ R)
      (hP : RTypedSimple Γ P q Δ) (hQ : RTypedSimple Γ Q r Ξ) :
      RTypedSimple Γ (.par P Q) (q ++ r) R
  | INACT (Γ : Env) (Δ : Typing) (hend : Δ.EndOnly) (hsingle : Δ.length ≤ 1) :
      RTypedSimple Γ .nil [] Δ
  | NRES (Γ : Env) (a : Name) (G : GType) (P : Proc) (q : List Chan) (Δ : Typing)
      (hcoh : Coherent G) (hfresh : a ∉ Γ.names.map Prod.fst)
      (hsingle : Δ.length ≤ 1)
      (hP : RTypedSimple (Γ.addName a (.shared G)) P q Δ) :
      RTypedSimple Γ (.resN a P) q Δ
  | VAR (Γ : Env) (X : PVar) (es : List Expr) (ss : List Chan)
      (sig : PSig) (sss : List (List Chan)) (Δ : Typing)
      (hX : (X,sig) ∈ Γ.pvars) (he : ExprsTyped Γ es sig.1)
      (hsplit : SplitsAs ss sss sig.2)
      (hend : Δ.EndOnly) (hempty : Δ = []) (hwf : (Typing.ofSig sss sig.2 ++ Δ).WellFormed) :
      RTypedSimple Γ (.call X es ss) [] (Typing.ofSig sss sig.2 ++ Δ)
  | DEF (Γ : Env) (D : List Decl) (P : Proc) (q : List Chan) (Δ : Typing)
      (signatures : List (PVar × PSig))
      (hbind : D.map Decl.name = signatures.map Prod.fst)
      (hX : (signatures.map Prod.fst).Nodup ∧
        ∀ X ∈ signatures.map Prod.fst, X ∉ Γ.pvars.map Prod.fst)
      (hparams : ∀ d ∈ D, ∀ X xs ss Q, d = .mk X xs ss Q →
        ∀ sig, (X,sig) ∈ signatures →
          xs.length = sig.1.length ∧ xs.Nodup ∧ (∀ x ∈ xs, x ∉ Γ.names.map Prod.fst) ∧
          ∃ sss, SplitsAs ss sss sig.2 ∧ (Typing.ofSig sss sig.2).WellFormed)
      -- the split of the declared channels is unique, so ∀ here is the paper's premise
      (hdefs : ∀ d ∈ D, ∀ X xs ss Q, d = .mk X xs ss Q →
        ∀ sig, (X,sig) ∈ signatures → ∀ sss, SplitsAs ss sss sig.2 →
          RTypedSimple ((Γ.addPVars signatures).addNames xs sig.1) Q [] (Typing.ofSig sss sig.2))
      (hsingle : Δ.length ≤ 1)
      (hP : RTypedSimple (Γ.addPVars signatures) P q Δ) :
      RTypedSimple Γ (.defn D P) q Δ
  | QNIL (Γ : Env) (s : List Chan) (k : ℕ) (c : Chan)
      (roles : List Role) (Δ R : Typing) (hc : TypeAt s k c) (hr : roles.Nodup)
      (hend : Δ.EndOnly)
      (hcomp : TypingComp [(s,roles.map fun p => (.ctx .hole,p))] Δ R) :
      RTypedSimple Γ (.queue c []) [c] R
  | QVAL (Γ : Env) (c : Chan) (h : List Msg) (vs : List Val)
      (Ss : List ValSort) (s : List Chan) (k : ℕ) (p : Role)
      (C : TContext) (Δ Δ' : Typing)
      (hc : TypeAt s k c) (hv : ValsTyped Γ vs Ss)
      (hrep : Typing.Replace Δ s p (.ctx C)
        (.ctx (C.fill (.send k (.sorts Ss) .hole))) Δ')
      (hh : RTypedSimple Γ (.queue c h) [c] Δ) :
      RTypedSimple Γ (.queue c (h ++ [.vals vs])) [c] Δ'
  | QSESS (Γ : Env) (c : Chan) (h : List Msg) (ts : List Chan)
      (s : List Chan) (k : ℕ) (p p' : Role) (T' : EType)
      (C : TContext) (Δ Δ' Δ'' : Typing)
      (hc : TypeAt s k c)
      (hrep : Typing.Replace Δ s p (.ctx C)
        (.ctx (C.fill (.send k (.located T' p') .hole))) Δ')
      (hins : Typing.Insert Δ' ts [(.pure T',p')] Δ'')
      (hh : RTypedSimple Γ (.queue c h) [c] Δ) :
      RTypedSimple Γ (.queue c (h ++ [.chans ts])) [c] Δ''
  | QSEL (Γ : Env) (c : Chan) (h : List Msg) (l : Label)
      (s : List Chan) (k : ℕ) (p : Role) (C : TContext) (Δ Δ' : Typing)
      (hc : TypeAt s k c)
      (hrep : Typing.Replace Δ s p (.ctx C) (.ctx (C.fill (.sel k l .hole))) Δ')
      (hh : RTypedSimple Γ (.queue c h) [c] Δ) :
      RTypedSimple Γ (.queue c (h ++ [.label l])) [c] Δ'
  | CRES (Γ : Env) (s : List Chan) (P : Proc) (q : List Chan)
      (F : HFamily) (Δ Δ' : Typing)
      (hch : s.toFinset ⊆ q.toFinset)
      (hrem : Typing.Remove Δ s F Δ')
      (hcoh : HFamilyCoherent F)
      (hP : RTypedSimple Γ P q Δ) :
      RTypedSimple Γ (.resS s P) (q.filter fun c => c ∉ s) Δ'
  | SUBS (Γ : Env) (P : Proc) (q : List Chan) (Δ Δ' : Typing)
      (hsub : TypingSub Δ Δ') (hwf : Δ'.WellFormed)
      (hP : RTypedSimple Γ P q Δ) : RTypedSimple Γ P q Δ'
  | CONV (Γ : Env) (P : Proc) (q : List Chan) (Δ Δ' : Typing)
      (hiso : TypingEquiv Δ Δ') (hwf : Δ'.WellFormed)
      (hP : RTypedSimple Γ P q Δ) : RTypedSimple Γ P q Δ'


def Simple (P : Proc) : Prop :=
  ∃ Γ q Δ, Γ.WellFormed ∧ RTypedSimple Γ P q Δ

end MPSTAsync.Progress


