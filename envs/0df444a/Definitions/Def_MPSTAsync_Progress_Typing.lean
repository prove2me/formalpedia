-- Prove2me | Definitions.Def_MPSTAsync_Progress_Typing
-- name    : MPSTAsync_Progress_Typing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:11:18.323843+00:00
-- url     : https://prove2.me/theorems/2e6fff19-831b-49a7-9f6f-1ad39aa35122
-- title:
--   Fig. 7 and Notation 4.5 — environments and program typing
-- statement:
--   A shared-name environment $\Gamma$ assigns sorts to names and parameter signatures to process variables. A **session typing** $\Delta$ assigns a family of located endpoint types to each channel vector. The judgement $\Gamma\vdash P\triangleright\Delta$ follows the expression and process rules of Fig. 7, including session initiation, all communication prefixes, parallel composition, conditionals, restrictions and recursive definitions.
--
--   $$\Gamma\vdash P\triangleright\Delta.$$
--
--   This program-level judgement is the basis for the runtime extension.
--
--   **Formalization Note** Environments and typings are finite association lists whose names, roles and session-channel domains must be distinct where the paper requires them; the extensions $\Gamma,\tilde x:\tilde S$ and $\Gamma,X:\tilde S\tilde T$ made by [RCV], [NRES] and [DEF] require fresh names, as $\Gamma$ is a finite map. The environment is well formed only when each mentioned global type is coherent. Following Notation 4.5, every prefix rule acts on a singleton entry $\widetilde s:T@p$. A process-variable signature records the value sorts and, for each session vector $\widetilde s_i$, its length and located type $T_i@p_i$; [VAR] and [DEF] split the channel arguments into $\widetilde s_1..\widetilde s_n$ accordingly, and [DEF] requires $|\tilde x|=|\tilde S|$. In [DELEG] the delegated $\widetilde t:T'@p'$ belongs to the conclusion, in [SREC] to the premise. A conversion rule accounts for equality of equi-recursive endpoint types, with a well-formed result.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 23–25, Fig. 7 and Notation 4.5, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Projection
import Definitions.Def_MPSTAsync_Progress_Semantics

set_option autoImplicit false

namespace MPSTAsync.Progress

-- A process-variable signature X : S̃ T̃ (§4.4): the sorts of the value
-- parameters and, for each session vector s̃ᵢ, its length and located type Tᵢ@pᵢ.
abbrev PSig := List ValSort × List (ℕ × (EType × Role))

structure Env where
  names : List (Name × ValSort)
  pvars : List (PVar × PSig)

def Env.addName (Γ : Env) (a : Name) (S : ValSort) : Env :=
  { Γ with names := (a,S)::Γ.names }

def Env.addNames (Γ : Env) (xs : List Name) (Ss : List ValSort) : Env :=
  { Γ with names := xs.zip Ss ++ Γ.names }

def Env.addPVars (Γ : Env) (xs : List (PVar × PSig)) : Env :=
  { Γ with pvars := xs ++ Γ.pvars }

def ValSort.WellFormed : ValSort → Prop
  | .bool => True
  | .shared G => Coherent G

def Env.WellFormed (Γ : Env) : Prop :=
  (Γ.names.map Prod.fst).Nodup ∧ (Γ.pvars.map Prod.fst).Nodup ∧
  (∀ x ∈ Γ.names, x.2.WellFormed) ∧
  (∀ x ∈ Γ.pvars, (∀ S ∈ x.2.1, S.WellFormed) ∧ ∀ y ∈ x.2.2, y.2.1.WellFormed)

def Decl.name : Decl → PVar
  | .mk X _ _ _ => X

-- The channel arguments s̃₁..s̃ₙ of a call or declaration, split as its signature says.
def SplitsAs (ss : List Chan) (sss : List (List Chan))
    (sig : List (ℕ × (EType × Role))) : Prop :=
  ss = sss.flatten ∧ sss.map List.length = sig.map Prod.fst

abbrev ProgTyping := List (List Chan × Family)

def ProgTyping.chans (Δ : ProgTyping) : Finset Chan :=
  Δ.foldl (fun a x => a ∪ x.1.toFinset) ∅

def ProgTyping.WellFormed (Δ : ProgTyping) : Prop :=
  (Δ.map Prod.fst).Nodup ∧
  (∀ x ∈ Δ, x.1.Nodup ∧ x.2.WellFormed) ∧
  (∀ x ∈ Δ, ∀ y ∈ Δ, x ≠ y → Disjoint x.1.toFinset y.1.toFinset)

def ProgTyping.EndOnly (Δ : ProgTyping) : Prop :=
  Δ.WellFormed ∧ ∀ x ∈ Δ, ∀ y ∈ x.2, EEquiv y.1 .stop

def ProgTypingEquiv (Δ Δ' : ProgTyping) : Prop :=
  (Δ.map Prod.fst).toFinset = (Δ'.map Prod.fst).toFinset ∧
  ∀ x ∈ Δ, ∀ y ∈ Δ', x.1 = y.1 →
    x.2.roles = y.2.roles ∧
    ∀ u ∈ x.2, ∀ v ∈ y.2, u.2 = v.2 → EEquiv u.1 v.1

def ProgTyping.Replace (Δ : ProgTyping) (s : List Chan) (p : Role)
    (T T' : EType) (Δ' : ProgTyping) : Prop :=
  ∃ before after left right, Δ = before ++ (s,left ++ (T,p)::right)::after ∧
    Δ' = before ++ (s,left ++ (T',p)::right)::after ∧
    (∀ x ∈ left ++ right, x.2 ≠ p)

-- Notation 4.5: a prefix rule acts on a singleton entry s̃ : T@p.
def ProgTyping.ReplaceOne (Δ : ProgTyping) (s : List Chan) (p : Role)
    (T T' : EType) (Δ' : ProgTyping) : Prop :=
  ∃ before after, Δ = before ++ (s,[(T,p)])::after ∧
    Δ' = before ++ (s,[(T',p)])::after

def ProgTyping.ofSig (sss : List (List Chan)) (sig : List (ℕ × (EType × Role))) :
    ProgTyping :=
  List.zipWith (fun s y => (s,[y.2])) sss sig

def ProgTyping.Insert (Δ : ProgTyping) (s : List Chan) (F : Family) (Δ' : ProgTyping) : Prop :=
  s ∉ Δ.map Prod.fst ∧ Δ' = (s,F)::Δ ∧ Disjoint s.toFinset Δ.chans

def ProgTyping.Remove (Δ : ProgTyping) (s : List Chan) (F : Family) (Δ' : ProgTyping) : Prop :=
  Δ = (s,F)::Δ'

def TypeAt (s : List Chan) (k : ℕ) (c : Chan) : Prop :=
  1 ≤ k ∧ s[k-1]? = some c

inductive ExprTyped : Env → Expr → ValSort → Prop where
  | NAME (Γ : Env) (a : Name) (S : ValSort) (h : (a,S) ∈ Γ.names) :
      ExprTyped Γ (.val (.name a)) S
  | BOOL_T (Γ : Env) : ExprTyped Γ (.val .tt) .bool
  | BOOL_F (Γ : Env) : ExprTyped Γ (.val .ff) .bool
  | AND (Γ : Env) (e f : Expr) (he : ExprTyped Γ e .bool) (hf : ExprTyped Γ f .bool) :
      ExprTyped Γ (.and e f) .bool
  | OR (Γ : Env) (e f : Expr) (he : ExprTyped Γ e .bool) (hf : ExprTyped Γ f .bool) :
      ExprTyped Γ (.or e f) .bool
  | NOT (Γ : Env) (e : Expr) (he : ExprTyped Γ e .bool) :
      ExprTyped Γ (.not e) .bool

def ExprsTyped (Γ : Env) (es : List Expr) (Ss : List ValSort) : Prop :=
  List.Forall₂ (ExprTyped Γ) es Ss

-- Figure 7. Every premise's session typing is retained explicitly.
inductive Typed : Env → Proc → ProgTyping → Prop where
  | MCAST (Γ : Env) (a : Name) (n : ℕ) (s : List Chan) (P : Proc)
      (Δ Δ' : ProgTyping) (G : GType) (T : EType)
      (ha : (a,.shared G) ∈ Γ.names) (hn : 2 ≤ n)
      (hfresh : s.Nodup)
      (hroles : G.pid = (Finset.range n).image (· + 1))
      (hsid : s.length = G.sid.card)
      (hproj : proj G 1 = some T)
      (hins : ProgTyping.Insert Δ s [(T,1)] Δ')
      (hP : Typed Γ P Δ') : Typed Γ (.request a n s P) Δ
  | MACC (Γ : Env) (a : Name) (p : Role) (s : List Chan) (P : Proc)
      (Δ Δ' : ProgTyping) (G : GType) (T : EType)
      (ha : (a,.shared G) ∈ Γ.names) (hp : p ∈ G.pid)
      (hfresh : s.Nodup)
      (hsid : s.length = G.sid.card) (hproj : proj G p = some T)
      (hins : ProgTyping.Insert Δ s [(T,p)] Δ') (hP : Typed Γ P Δ') :
      Typed Γ (.accept a p s P) Δ
  | SEND (Γ : Env) (c : Chan) (es : List Expr) (Ss : List ValSort)
      (P : Proc) (Δ Δ' : ProgTyping) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (hc : TypeAt s k c) (he : ExprsTyped Γ es Ss)
      (hrep : ProgTyping.ReplaceOne Δ s p T (.send k (.sorts Ss) T) Δ')
      (hP : Typed Γ P Δ) : Typed Γ (.send c es P) Δ'
  | RCV (Γ : Env) (c : Chan) (xs : List Name) (Ss : List ValSort)
      (P : Proc) (Δ Δ' : ProgTyping) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (hc : TypeAt s k c) (hlen : xs.length = Ss.length) (hxs : xs.Nodup)
      (hfresh : ∀ x ∈ xs, x ∉ Γ.names.map Prod.fst)
      (hrep : ProgTyping.ReplaceOne Δ s p T (.recv k (.sorts Ss) T) Δ')
      (hP : Typed (Γ.addNames xs Ss) P Δ) : Typed Γ (.recv c xs P) Δ'
  | DELEG (Γ : Env) (c : Chan) (ts : List Chan) (P : Proc)
      (Δ Δ' Δ'' : ProgTyping) (s : List Chan) (k : ℕ) (p p' : Role)
      (T T' : EType) (hc : TypeAt s k c)
      (hrep : ProgTyping.ReplaceOne Δ s p T (.send k (.located T' p') T) Δ')
      (hins : ProgTyping.Insert Δ' ts [(T',p')] Δ'')
      (hP : Typed Γ P Δ) : Typed Γ (.deleg c ts P) Δ''
  | SREC (Γ : Env) (c : Chan) (ts : List Chan) (P : Proc)
      (Δ Δ' Δ'' : ProgTyping) (s : List Chan) (k : ℕ) (p p' : Role)
      (T T' : EType) (hc : TypeAt s k c)
      (hrem : ProgTyping.Remove Δ ts [(T',p')] Δ')
      (hrep : ProgTyping.ReplaceOne Δ' s p T (.recv k (.located T' p') T) Δ'')
      (hP : Typed Γ P Δ) : Typed Γ (.srecv c ts P) Δ''
  | SEL (Γ : Env) (c : Chan) (l : Label) (P : Proc)
      (Δ Δ' : ProgTyping) (s : List Chan) (k : ℕ) (p : Role) (T : EType)
      (bs : List (Label × EType)) (hc : TypeAt s k c) (hin : (l,T) ∈ bs)
      (hrep : ProgTyping.ReplaceOne Δ s p T (.sel k bs) Δ')
      (hP : Typed Γ P Δ) : Typed Γ (.sel c l P) Δ'
  | BRANCH (Γ : Env) (c : Chan) (s : List Chan) (k : ℕ) (p : Role)
      (n : ℕ) (labels : Fin n → Label) (procs : Fin n → Proc)
      (Ts : Fin n → EType) (Δs : Fin n → ProgTyping) (Δ : ProgTyping)
      (hc : TypeAt s k c) (hn : 0 < n)
      (hlabels : (List.ofFn labels).Nodup)
      (hrep : ∀ i, ProgTyping.ReplaceOne (Δs i) s p (Ts i)
          (.bra k (List.ofFn fun j => (labels j,Ts j))) Δ)
      (hP : ∀ i, Typed Γ (procs i) (Δs i)) :
      Typed Γ (.branch c (List.ofFn fun i => (labels i,procs i))) Δ
  | CONC (Γ : Env) (P Q : Proc) (Δ Δ' : ProgTyping)
      (hdisj : Disjoint Δ.chans Δ'.chans)
      (hP : Typed Γ P Δ) (hQ : Typed Γ Q Δ') :
      Typed Γ (.par P Q) (Δ ++ Δ')
  | IF (Γ : Env) (e : Expr) (P Q : Proc) (Δ : ProgTyping)
      (he : ExprTyped Γ e .bool) (hP : Typed Γ P Δ) (hQ : Typed Γ Q Δ) :
      Typed Γ (.ite e P Q) Δ
  | INACT (Γ : Env) (Δ : ProgTyping) (hend : Δ.EndOnly) : Typed Γ .nil Δ
  | NRES (Γ : Env) (a : Name) (G : GType) (P : Proc) (Δ : ProgTyping)
      (hcoh : Coherent G) (hfresh : a ∉ Γ.names.map Prod.fst)
      (hP : Typed (Γ.addName a (.shared G)) P Δ) :
      Typed Γ (.resN a P) Δ
  | VAR (Γ : Env) (X : PVar) (es : List Expr) (ss : List Chan)
      (sig : PSig) (sss : List (List Chan)) (Δ : ProgTyping)
      (hX : (X,sig) ∈ Γ.pvars) (he : ExprsTyped Γ es sig.1)
      (hsplit : SplitsAs ss sss sig.2)
      (hend : Δ.EndOnly) (hwf : (ProgTyping.ofSig sss sig.2 ++ Δ).WellFormed) :
      Typed Γ (.call X es ss) (ProgTyping.ofSig sss sig.2 ++ Δ)
  | DEF (Γ : Env) (D : List Decl) (P : Proc) (Δ : ProgTyping)
      (signatures : List (PVar × PSig))
      (hbind : D.map Decl.name = signatures.map Prod.fst)
      (hX : (signatures.map Prod.fst).Nodup ∧
        ∀ X ∈ signatures.map Prod.fst, X ∉ Γ.pvars.map Prod.fst)
      (hparams : ∀ d ∈ D, ∀ X xs ss Q, d = .mk X xs ss Q →
        ∀ sig, (X,sig) ∈ signatures →
          xs.length = sig.1.length ∧ xs.Nodup ∧ (∀ x ∈ xs, x ∉ Γ.names.map Prod.fst) ∧
          ∃ sss, SplitsAs ss sss sig.2 ∧ (ProgTyping.ofSig sss sig.2).WellFormed)
      -- the split of the declared channels is unique, so ∀ here is the paper's premise
      (hdefs : ∀ d ∈ D, ∀ X xs ss Q, d = .mk X xs ss Q →
        ∀ sig, (X,sig) ∈ signatures → ∀ sss, SplitsAs ss sss sig.2 →
          Typed ((Γ.addPVars signatures).addNames xs sig.1) Q (ProgTyping.ofSig sss sig.2))
      (hP : Typed (Γ.addPVars signatures) P Δ) :
      Typed Γ (.defn D P) Δ
  | CONV (Γ : Env) (P : Proc) (Δ Δ' : ProgTyping)
      (hequiv : ProgTypingEquiv Δ Δ') (hwf : Δ'.WellFormed) (hP : Typed Γ P Δ) :
      Typed Γ P Δ'

end MPSTAsync.Progress


