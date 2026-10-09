-- Prove2me | Definitions.Def_MPSTAsync_Progress_Runtime
-- name    : MPSTAsync_Progress_Runtime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:14:45.553418+00:00
-- url     : https://prove2.me/theorems/76609699-c3e1-400b-b800-f1dbca467c67
-- title:
--   Defs. 5.1–5.9, Fig. 8 and Appendix B — runtime typing and type reduction
-- statement:
--   A **type context** records outputs or selections already placed in a queue, with one hole for the participant's remaining endpoint type. Runtime typings combine endpoint types and type contexts through a partial operation $\circ$. The judgement $\Gamma\vdash P\triangleright_{\widetilde s}\Delta$ records exactly the queue channels $\widetilde s$ mentioned by a running process. The module includes all runtime process and queue rules, subtyping, permutation of independent outputs, full projection, coherent typings and labelled type reduction.
--
--   $$\Delta\xrightarrow{\ell}\Delta'. $$
--
--   These relations give the type-level counterpart to operational reduction.
--
--   **Formalization Note** The printed subtyping operator omits the reflexive $(\mathrm{end},\mathrm{end})$ case; it is supplied here. Channel indices remain one based. Type-context composition is partial, and queue rules keep the channel index attached to each queue judgement. As in the program system, prefix rules act on singleton entries $\widetilde s:T@p$, [VAR]/[DEF] carry one singleton entry per session vector, and [DELEG]/[SREC] place $\widetilde t:T'@p'$ in the conclusion/premise respectively. [QNIL] includes its weakening $\circ\,\Delta$ by an end-only $\Delta$, and the runtime [INACT] allows entries that are all `end` or all empty contexts.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 28–31, 54, Defs. 5.1–5.9, Fig. 8 and Appendix B, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Typing

set_option autoImplicit false

namespace MPSTAsync.Progress

inductive TContext where
  | hole
  | send (k : ℕ) (U : VType) (C : TContext)
  | sel (k : ℕ) (l : Label) (C : TContext)

def TContext.plug (C : TContext) (T : EType) : EType :=
  match C with
  | .hole => T
  | .send k U D => .send k U (D.plug T)
  | .sel k l D => .sel k [(l,D.plug T)]

def TContext.fill (C D : TContext) : TContext :=
  match C with
  | .hole => D
  | .send k U E => .send k U (E.fill D)
  | .sel k l E => .sel k l (E.fill D)

def TContext.sid : TContext → Finset ℕ
  | .hole => ∅
  | .send k _ C | .sel k _ C => insert k C.sid

inductive HType where
  | pure (T : EType)
  | ctx (C : TContext)

def HType.asType? : HType → Option EType
  | .pure T => some T
  | .ctx _ => none

-- Definition 5.4: composition is undefined on two completed types.
def HType.compose? : HType → HType → Option HType
  | .pure T, .ctx C | .ctx C, .pure T => some (.pure (C.plug T))
  | .ctx C, .ctx D =>
      if Disjoint C.sid D.sid then some (.ctx (C.fill D)) else none
  | .pure _, .pure _ => none

-- Definition 5.1 as a greatest post-fixed relation. The end/end clause is
-- the reflexivity case omitted from the printed operator F.
def SubStep (R : Set (EType × EType)) (T U : EType) : Prop :=
  match T, U with
  | .mu t A, B => (A.substE t (.mu t A),B) ∈ R
  | A, .mu t B => (A,B.substE t (.mu t B)) ∈ R
  | .send k V A, .send j W B => k = j ∧ V = W ∧ (A,B) ∈ R
  | .recv k V A, .recv j W B => k = j ∧ V = W ∧ (A,B) ∈ R
  | .sel k as, .sel j bs => k = j ∧
      (as.map Prod.fst).toFinset ⊆ (bs.map Prod.fst).toFinset ∧
      ∀ a ∈ as, ∀ b ∈ bs, a.1 = b.1 → (a.2,b.2) ∈ R
  | .bra k as, .bra j bs => k = j ∧
      (bs.map Prod.fst).toFinset ⊆ (as.map Prod.fst).toFinset ∧
      ∀ b ∈ bs, ∀ a ∈ as, a.1 = b.1 → (a.2,b.2) ∈ R
  | .var t, .var u => t = u
  | .stop, .stop => True
  | _, _ => False

def SubType (T U : EType) : Prop :=
  ∃ R : Set (EType × EType), (T,U) ∈ R ∧
    ∀ A B, (A,B) ∈ R → SubStep R A B

-- Definition 5.3. Independent outputs and selections may commute, as may
-- their occurrences below a type constructor.
inductive EIso : EType → EType → Prop where
  | eqv (T U : EType) (h : EEquiv T U) : EIso T U
  | symm (T U : EType) (h : EIso T U) : EIso U T
  | trans (T U V : EType) (h : EIso T U) (h' : EIso U V) : EIso T V
  | sendSend (k j : ℕ) (U V : VType) (T : EType) (h : k ≠ j) :
      EIso (.send k U (.send j V T)) (.send j V (.send k U T))
  | sendSel (k j : ℕ) (U : VType) (l : Label) (T : EType) (h : k ≠ j) :
      EIso (.send k U (.sel j [(l,T)])) (.sel j [(l,.send k U T)])
  | sendSelFamily (k j n : ℕ) (U : VType)
      (labels : Fin n → Label) (Ts : Fin n → EType)
      (h : k ≠ j) (hn : 0 < n) (hl : (List.ofFn labels).Nodup) :
      EIso (.send k U (.sel j (List.ofFn fun i => (labels i,Ts i))))
        (.sel j (List.ofFn fun i => (labels i,.send k U (Ts i))))
  | selSel (k j : ℕ) (l m : Label) (T : EType) (h : k ≠ j) :
      EIso (.sel k [(l,.sel j [(m,T)])]) (.sel j [(m,.sel k [(l,T)])])
  | selSelFamily (k j n m : ℕ) (li : Fin n → Label) (lj : Fin m → Label)
      (Ts : Fin n → Fin m → EType)
      (h : k ≠ j) (hn : 0 < n) (hm : 0 < m)
      (hni : (List.ofFn li).Nodup) (hnj : (List.ofFn lj).Nodup) :
      EIso
        (.sel k (List.ofFn fun i =>
          (li i,.sel j (List.ofFn fun z => (lj z,Ts i z)))))
        (.sel j (List.ofFn fun z =>
          (lj z,.sel k (List.ofFn fun i => (li i,Ts i z)))))
  | sendCongr (k : ℕ) (U : VType) (T T' : EType) (h : EIso T T') :
      EIso (.send k U T) (.send k U T')
  | recvCongr (k : ℕ) (U : VType) (T T' : EType) (h : EIso T T') :
      EIso (.recv k U T) (.recv k U T')
  | selCongr (k : ℕ) (bs cs : List (Label × EType))
      (hlabels : bs.map Prod.fst = cs.map Prod.fst)
      (h : ∀ x ∈ bs, ∀ y ∈ cs, x.1 = y.1 → EIso x.2 y.2) :
      EIso (.sel k bs) (.sel k cs)
  | braCongr (k : ℕ) (bs cs : List (Label × EType))
      (hlabels : bs.map Prod.fst = cs.map Prod.fst)
      (h : ∀ x ∈ bs, ∀ y ∈ cs, x.1 = y.1 → EIso x.2 y.2) :
      EIso (.bra k bs) (.bra k cs)
  | muCongr (t : TVar) (T U : EType) (h : EIso T U) :
      EIso (.mu t T) (.mu t U)

def HType.Iso : HType → HType → Prop
  | .pure T, .pure U => EIso T U
  | .ctx C, .ctx D => C = D
  | _, _ => False

abbrev HFamily := List (HType × Role)
abbrev Typing := List (List Chan × HFamily)

def HFamily.roles (F : HFamily) : Finset Role := (F.map Prod.snd).toFinset
def HFamily.WellFormed (F : HFamily) : Prop := (F.map Prod.snd).Nodup

def Typing.chans (Δ : Typing) : Finset Chan :=
  Δ.foldl (fun a x => a ∪ x.1.toFinset) ∅

def Typing.WellFormed (Δ : Typing) : Prop :=
  (Δ.map Prod.fst).Nodup ∧
  (∀ x ∈ Δ, x.1.Nodup ∧ x.2.WellFormed) ∧
  (∀ x ∈ Δ, ∀ y ∈ Δ, x ≠ y → Disjoint x.1.toFinset y.1.toFinset)

-- Runtime [INACT] (App. B): "Δ end only, Δ′ [ ] only", so each entry is
-- either all end or all empty contexts.
def Typing.EndOnly (Δ : Typing) : Prop :=
  Δ.WellFormed ∧ ∀ x ∈ Δ,
    (∀ y ∈ x.2, y.1 = .pure .stop) ∨ (∀ y ∈ x.2, y.1 = .ctx .hole)

def Typing.Replace (Δ : Typing) (s : List Chan) (p : Role)
    (T T' : HType) (Δ' : Typing) : Prop :=
  ∃ before after left right, Δ = before ++ (s,left ++ (T,p)::right)::after ∧
    Δ' = before ++ (s,left ++ (T',p)::right)::after ∧
    (∀ x ∈ left ++ right, x.2 ≠ p)

-- Notation 4.5: a prefix rule acts on a singleton entry s̃ : T@p.
def Typing.ReplaceOne (Δ : Typing) (s : List Chan) (p : Role)
    (T T' : HType) (Δ' : Typing) : Prop :=
  ∃ before after, Δ = before ++ (s,[(T,p)])::after ∧
    Δ' = before ++ (s,[(T',p)])::after

def Typing.ofSig (sss : List (List Chan)) (sig : List (ℕ × (EType × Role))) : Typing :=
  List.zipWith (fun s y => (s,[(.pure y.2.1,y.2.2)])) sss sig

def Typing.Insert (Δ : Typing) (s : List Chan) (F : HFamily) (Δ' : Typing) : Prop :=
  s ∉ Δ.map Prod.fst ∧ Δ' = (s,F)::Δ ∧ Disjoint s.toFinset Δ.chans

def Typing.Remove (Δ : Typing) (s : List Chan) (F : HFamily) (Δ' : Typing) : Prop :=
  Δ = (s,F)::Δ'

def HFamilyCoherent (F : HFamily) : Prop :=
  ∃ E : Family, FamilyCoherent E ∧
    F.roles = E.roles ∧
    ∀ x ∈ F, ∃ y ∈ E, x.2 = y.2 ∧ x.1 = .pure y.1

def TypingCoherent (Δ : Typing) : Prop :=
  Δ.WellFormed ∧ ∀ x ∈ Δ, HFamilyCoherent x.2

def HFamilyIso (F H : HFamily) : Prop :=
  F.roles = H.roles ∧
  ∀ x ∈ F, ∀ y ∈ H, x.2 = y.2 → HType.Iso x.1 y.1

def HFamilyEquiv (F H : HFamily) : Prop :=
  F.roles = H.roles ∧
  ∀ x ∈ F, ∀ y ∈ H, x.2 = y.2 →
    match x.1,y.1 with
    | .pure T,.pure U => EEquiv T U
    | .ctx C,.ctx D => C = D
    | _,_ => False

def TypingIso (Δ Δ' : Typing) : Prop :=
  (Δ.map Prod.fst).toFinset = (Δ'.map Prod.fst).toFinset ∧
  ∀ x ∈ Δ, ∀ y ∈ Δ', x.1 = y.1 → HFamilyIso x.2 y.2

def TypingEquiv (Δ Δ' : Typing) : Prop :=
  (Δ.map Prod.fst).toFinset = (Δ'.map Prod.fst).toFinset ∧
  ∀ x ∈ Δ, ∀ y ∈ Δ', x.1 = y.1 → HFamilyEquiv x.2 y.2

def HFamilySub (F H : HFamily) : Prop :=
  F.roles = H.roles ∧
  ∀ x ∈ F, ∀ y ∈ H, x.2 = y.2 →
    match x.1,y.1 with
    | .pure T,.pure U => SubType T U
    | .ctx C,.ctx D => C = D
    | _,_ => False

def TypingSub (Δ Δ' : Typing) : Prop :=
  (Δ.map Prod.fst).toFinset = (Δ'.map Prod.fst).toFinset ∧
  ∀ x ∈ Δ, ∀ y ∈ Δ', x.1 = y.1 → HFamilySub x.2 y.2

-- Pointwise composition on a common session and disjoint union otherwise.
def HFamilyComp (F H K : HFamily) : Prop :=
  F.WellFormed ∧ H.WellFormed ∧ K.WellFormed ∧
  K.roles = F.roles ∪ H.roles ∧
  ∀ x ∈ K,
    (∃ y ∈ F, x.2 = y.2 ∧ x.2 ∉ H.roles ∧ x.1 = y.1) ∨
    (∃ y ∈ H, x.2 = y.2 ∧ x.2 ∉ F.roles ∧ x.1 = y.1) ∨
    (∃ y ∈ F, ∃ z ∈ H, x.2 = y.2 ∧ x.2 = z.2 ∧
      HType.compose? y.1 z.1 = some x.1)

def TypingComp (Δ Ξ R : Typing) : Prop :=
  Δ.WellFormed ∧ Ξ.WellFormed ∧ R.WellFormed ∧
  (∀ x ∈ Δ, ∀ y ∈ Ξ, x.1 ≠ y.1 → Disjoint x.1.toFinset y.1.toFinset) ∧
  (∀ x ∈ R, (∃ y ∈ Δ, y.1 = x.1 ∧ x.1 ∉ Ξ.map Prod.fst ∧ x.2 = y.2) ∨
    (∃ y ∈ Ξ, y.1 = x.1 ∧ x.1 ∉ Δ.map Prod.fst ∧ x.2 = y.2) ∨
    (∃ y ∈ Δ, ∃ z ∈ Ξ, y.1 = x.1 ∧ z.1 = x.1 ∧ HFamilyComp y.2 z.2 x.2)) ∧
  (R.map Prod.fst).toFinset = (Δ.map Prod.fst).toFinset ∪ (Ξ.map Prod.fst).toFinset

def TypingCompatible (Δ Ξ : Typing) : Prop := ∃ R, TypingComp Δ Ξ R

def PartiallyCoherent (Δ : Typing) : Prop :=
  ∃ Ξ R, TypingCompatible Δ Ξ ∧ TypingComp Δ Ξ R ∧ TypingCoherent R

inductive TLabel where
  | value (p q : Role) (k : ℕ) (U : VType)
  | choice (p q : Role) (k : ℕ) (l : Label)
  | svalue (p q : Role) (s : List Chan) (k : ℕ) (U : VType)
  | schoice (p q : Role) (s : List Chan) (k : ℕ) (l : Label)

def TLabel.index : TLabel → ℕ
  | .value _ _ k _ | .choice _ _ k _ | .svalue _ _ _ k _ | .schoice _ _ _ k _ => k

inductive TRed : Typing → TLabel → Typing → Prop where
  | TR_COM (s : List Chan) (p q : Role) (k : ℕ) (U : VType)
      (P Q : EType) (Δ Δ₀ Δ' : Typing)
      (hp : Typing.Replace Δ s p (.pure (.send k U P)) (.pure P) Δ₀)
      (hq : Typing.Replace Δ₀ s q (.pure (.recv k U Q)) (.pure Q) Δ') :
      TRed Δ (.value p q k U) Δ'
  | TR_BRA (s : List Chan) (p q : Role) (k : ℕ) (l : Label)
      (bs cs : List (Label × EType)) (P Q : EType)
      (Δ Δ₀ Δ' : Typing)
      (hp : (l,P) ∈ bs) (hq : (l,Q) ∈ cs)
      (hsel : Typing.Replace Δ s p (.pure (.sel k bs)) (.pure P) Δ₀)
      (hbra : Typing.Replace Δ₀ s q (.pure (.bra k cs)) (.pure Q) Δ') :
      TRed Δ (.choice p q k l) Δ'
  | TR_CONTEXT_VAL (Δ Δ' : Typing) (s : List Chan) (p q : Role) (k : ℕ)
      (U : VType) (hk : 1 ≤ k ∧ k ≤ s.length)
      (h : TRed Δ (.value p q k U) Δ') :
      TRed Δ (.svalue p q s k U) Δ'
  | TR_CONTEXT_BRA (Δ Δ' : Typing) (s : List Chan) (p q : Role) (k : ℕ)
      (l : Label) (hk : 1 ≤ k ∧ k ≤ s.length)
      (h : TRed Δ (.choice p q k l) Δ') :
      TRed Δ (.schoice p q s k l) Δ'
  | TR_ISO (Δ Δ₀ Δ₀' Δ' : Typing) (l : TLabel)
      (h₁ : TypingIso Δ Δ₀) (h₂ : TRed Δ₀ l Δ₀') (h₃ : TypingIso Δ₀' Δ') :
      TRed Δ l Δ'

def ValsTyped (Γ : Env) (vs : List Val) (Ss : List ValSort) : Prop :=
  List.Forall₂ (fun v S => ExprTyped Γ (.val v) S) vs Ss

-- Figure 8 and Appendix B: the full runtime typing judgement.
inductive RTyped (subs : Bool) : Env → Proc → List Chan → Typing → Prop where
  | MCAST (Γ : Env) (a : Name) (n : ℕ) (s : List Chan) (P : Proc)
      (Δ Δ' : Typing) (G : GType) (T : EType)
      (ha : (a,.shared G) ∈ Γ.names) (hn : 2 ≤ n)
      (hfresh : s.Nodup)
      (hroles : G.pid = (Finset.range n).image (· + 1))
      (hsid : s.length = G.sid.card)
      (hproj : proj G 1 = some T)
      (hins : Typing.Insert Δ s [(.pure T,1)] Δ')
      (hP : RTyped subs Γ P [] Δ') : RTyped subs Γ (.request a n s P) [] Δ
  | MACC (Γ : Env) (a : Name) (p : Role) (s : List Chan) (P : Proc)
      (Δ Δ' : Typing) (G : GType) (T : EType)
      (ha : (a,.shared G) ∈ Γ.names) (hp : p ∈ G.pid)
      (hfresh : s.Nodup)
      (hsid : s.length = G.sid.card) (hproj : proj G p = some T)
      (hins : Typing.Insert Δ s [(.pure T,p)] Δ')
      (hP : RTyped subs Γ P [] Δ') : RTyped subs Γ (.accept a p s P) [] Δ
  | SEND (Γ : Env) (c : Chan) (es : List Expr) (Ss : List ValSort)
      (P : Proc) (Δ Δ' : Typing) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (hc : TypeAt s k c) (he : ExprsTyped Γ es Ss)
      (hrep : Typing.ReplaceOne Δ s p (.pure T) (.pure (.send k (.sorts Ss) T)) Δ')
      (hP : RTyped subs Γ P [] Δ) : RTyped subs Γ (.send c es P) [] Δ'
  | RCV (Γ : Env) (c : Chan) (xs : List Name) (Ss : List ValSort)
      (P : Proc) (Δ Δ' : Typing) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (hc : TypeAt s k c) (hlen : xs.length = Ss.length) (hxs : xs.Nodup)
      (hfresh : ∀ x ∈ xs, x ∉ Γ.names.map Prod.fst)
      (hrep : Typing.ReplaceOne Δ s p (.pure T) (.pure (.recv k (.sorts Ss) T)) Δ')
      (hP : RTyped subs (Γ.addNames xs Ss) P [] Δ) :
      RTyped subs Γ (.recv c xs P) [] Δ'
  | DELEG (Γ : Env) (c : Chan) (ts : List Chan) (P : Proc)
      (Δ Δ' Δ'' : Typing) (s : List Chan) (k : ℕ) (p p' : Role)
      (T T' : EType) (hc : TypeAt s k c)
      (hrep : Typing.ReplaceOne Δ s p (.pure T) (.pure (.send k (.located T' p') T)) Δ')
      (hins : Typing.Insert Δ' ts [(.pure T',p')] Δ'')
      (hP : RTyped subs Γ P [] Δ) : RTyped subs Γ (.deleg c ts P) [] Δ''
  | SREC (Γ : Env) (c : Chan) (ts : List Chan) (P : Proc)
      (Δ Δ' Δ'' : Typing) (s : List Chan) (k : ℕ) (p p' : Role)
      (T T' : EType) (hc : TypeAt s k c)
      (hrem : Typing.Remove Δ ts [(.pure T',p')] Δ')
      (hrep : Typing.ReplaceOne Δ' s p (.pure T) (.pure (.recv k (.located T' p') T)) Δ'')
      (hP : RTyped subs Γ P [] Δ) : RTyped subs Γ (.srecv c ts P) [] Δ''
  | SEL (Γ : Env) (c : Chan) (l : Label) (P : Proc)
      (Δ Δ' : Typing) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (bs : List (Label × EType)) (hc : TypeAt s k c) (hin : (l,T) ∈ bs)
      (hrep : Typing.ReplaceOne Δ s p (.pure T) (.pure (.sel k bs)) Δ')
      (hP : RTyped subs Γ P [] Δ) : RTyped subs Γ (.sel c l P) [] Δ'
  | BRANCH (Γ : Env) (c : Chan) (s : List Chan) (k : ℕ) (p : Role)
      (n : ℕ) (labels : Fin n → Label) (procs : Fin n → Proc)
      (Ts : Fin n → EType) (Δs : Fin n → Typing) (Δ : Typing)
      (hc : TypeAt s k c) (hn : 0 < n)
      (hlabels : (List.ofFn labels).Nodup)
      (hrep : ∀ i, Typing.ReplaceOne (Δs i) s p (.pure (Ts i))
          (.pure (.bra k (List.ofFn fun j => (labels j,Ts j)))) Δ)
      (hP : ∀ i, RTyped subs Γ (procs i) [] (Δs i)) :
      RTyped subs Γ (.branch c (List.ofFn fun i => (labels i,procs i))) [] Δ
  | IF (Γ : Env) (e : Expr) (P Q : Proc) (Δ : Typing)
      (he : ExprTyped Γ e .bool)
      (hP : RTyped subs Γ P [] Δ) (hQ : RTyped subs Γ Q [] Δ) :
      RTyped subs Γ (.ite e P Q) [] Δ
  | CONC (Γ : Env) (P Q : Proc) (q r : List Chan) (Δ Ξ R : Typing)
      (hqueue : Disjoint q.toFinset r.toFinset)
      (hcomp : TypingComp Δ Ξ R)
      (hP : RTyped subs Γ P q Δ) (hQ : RTyped subs Γ Q r Ξ) :
      RTyped subs Γ (.par P Q) (q ++ r) R
  | INACT (Γ : Env) (Δ : Typing) (hend : Δ.EndOnly) :
      RTyped subs Γ .nil [] Δ
  | NRES (Γ : Env) (a : Name) (G : GType) (P : Proc) (q : List Chan) (Δ : Typing)
      (hcoh : Coherent G) (hfresh : a ∉ Γ.names.map Prod.fst)
      (hP : RTyped subs (Γ.addName a (.shared G)) P q Δ) :
      RTyped subs Γ (.resN a P) q Δ
  | VAR (Γ : Env) (X : PVar) (es : List Expr) (ss : List Chan)
      (sig : PSig) (sss : List (List Chan)) (Δ : Typing)
      (hX : (X,sig) ∈ Γ.pvars) (he : ExprsTyped Γ es sig.1)
      (hsplit : SplitsAs ss sss sig.2)
      (hend : Δ.EndOnly) (hwf : (Typing.ofSig sss sig.2 ++ Δ).WellFormed) :
      RTyped subs Γ (.call X es ss) [] (Typing.ofSig sss sig.2 ++ Δ)
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
          RTyped subs ((Γ.addPVars signatures).addNames xs sig.1) Q [] (Typing.ofSig sss sig.2))
      (hP : RTyped subs (Γ.addPVars signatures) P q Δ) :
      RTyped subs Γ (.defn D P) q Δ
  | QNIL (Γ : Env) (s : List Chan) (k : ℕ) (c : Chan)
      (roles : List Role) (Δ R : Typing) (hc : TypeAt s k c) (hr : roles.Nodup)
      (hend : Δ.EndOnly)
      (hcomp : TypingComp [(s,roles.map fun p => (.ctx .hole,p))] Δ R) :
      RTyped subs Γ (.queue c []) [c] R
  | QVAL (Γ : Env) (c : Chan) (h : List Msg) (vs : List Val)
      (Ss : List ValSort) (s : List Chan) (k : ℕ) (p : Role)
      (C : TContext) (Δ Δ' : Typing)
      (hc : TypeAt s k c) (hv : ValsTyped Γ vs Ss)
      (hrep : Typing.Replace Δ s p (.ctx C)
        (.ctx (C.fill (.send k (.sorts Ss) .hole))) Δ')
      (hh : RTyped subs Γ (.queue c h) [c] Δ) :
      RTyped subs Γ (.queue c (h ++ [.vals vs])) [c] Δ'
  | QSESS (Γ : Env) (c : Chan) (h : List Msg) (ts : List Chan)
      (s : List Chan) (k : ℕ) (p p' : Role) (T' : EType)
      (C : TContext) (Δ Δ' Δ'' : Typing)
      (hc : TypeAt s k c)
      (hrep : Typing.Replace Δ s p (.ctx C)
        (.ctx (C.fill (.send k (.located T' p') .hole))) Δ')
      (hins : Typing.Insert Δ' ts [(.pure T',p')] Δ'')
      (hh : RTyped subs Γ (.queue c h) [c] Δ) :
      RTyped subs Γ (.queue c (h ++ [.chans ts])) [c] Δ''
  | QSEL (Γ : Env) (c : Chan) (h : List Msg) (l : Label)
      (s : List Chan) (k : ℕ) (p : Role) (C : TContext) (Δ Δ' : Typing)
      (hc : TypeAt s k c)
      (hrep : Typing.Replace Δ s p (.ctx C) (.ctx (C.fill (.sel k l .hole))) Δ')
      (hh : RTyped subs Γ (.queue c h) [c] Δ) :
      RTyped subs Γ (.queue c (h ++ [.label l])) [c] Δ'
  | CRES (Γ : Env) (s : List Chan) (P : Proc) (q : List Chan)
      (F : HFamily) (Δ Δ' : Typing)
      (hch : s.toFinset ⊆ q.toFinset)
      (hrem : Typing.Remove Δ s F Δ')
      (hcoh : HFamilyCoherent F)
      (hP : RTyped subs Γ P q Δ) :
      RTyped subs Γ (.resS s P) (q.filter fun c => c ∉ s) Δ'
  | SUBS (Γ : Env) (P : Proc) (q : List Chan) (Δ Δ' : Typing)
      (hsubs : subs = true) (hsub : TypingSub Δ Δ') (hwf : Δ'.WellFormed)
      (hP : RTyped subs Γ P q Δ) : RTyped subs Γ P q Δ'
  | CONV (Γ : Env) (P : Proc) (q : List Chan) (Δ Δ' : Typing)
      (hiso : TypingEquiv Δ Δ') (hwf : Δ'.WellFormed)
      (hP : RTyped subs Γ P q Δ) : RTyped subs Γ P q Δ'

end MPSTAsync.Progress


