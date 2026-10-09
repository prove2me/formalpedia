-- Prove2me | Definitions.Def_MPSTAsync_Progress_Syntax
-- name    : MPSTAsync_Progress_Syntax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:57.575214+00:00
-- url     : https://prove2.me/theorems/e8c4d137-6011-4070-8fc5-85b48228bdf6
-- title:
--   Fig. 1, p. 6 — processes, declarations, expressions and messages
-- statement:
--   The **process calculus** has multiparty session requests and accepts, value and channel passing, labels, branching, conditionals, parallel composition, restrictions, recursive declarations, calls and FIFO queues. Expressions contain values and Boolean connectives; queue messages are labels, vectors of values or vectors of channels.
--
--   $$P ::= \overline a[2..n](\widetilde s).P\mid a[p](\widetilde s).P\mid s!\langle\widetilde e\rangle;P\mid s?(\widetilde x);P\mid\cdots\mid s::\widetilde h.$$
--
--   The syntax is the common carrier for operational semantics and typing.
--
--   **Formalization Note** The paper leaves expression evaluation unspecified; this module pins the displayed Boolean operations to their ordinary truth tables. The `or` connective is included because Fig. 7 has an [OR] typing rule although Fig. 1 abbreviates its expression grammar.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 6–7, Fig. 1, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_GlobalTypes

set_option autoImplicit false

namespace MPSTAsync.Progress

inductive Val where
  | name (a : Name) | tt | ff
  deriving DecidableEq, Repr

inductive Expr where
  | val (v : Val)
  | and (e e' : Expr)
  | or (e e' : Expr)
  | not (e : Expr)
  deriving DecidableEq, Repr

inductive Msg where
  | label (l : Label)
  | vals (vs : List Val)
  | chans (ts : List Chan)
  deriving DecidableEq, Repr

mutual
inductive Proc where
  | request (a : Name) (n : ℕ) (s : List Chan) (P : Proc)
  | accept (a : Name) (p : ℕ) (s : List Chan) (P : Proc)
  | send (c : Chan) (es : List Expr) (P : Proc)
  | recv (c : Chan) (xs : List Name) (P : Proc)
  | deleg (c : Chan) (ts : List Chan) (P : Proc)
  | srecv (c : Chan) (ts : List Chan) (P : Proc)
  | sel (c : Chan) (l : Label) (P : Proc)
  | branch (c : Chan) (bs : List (Label × Proc))
  | ite (e : Expr) (P Q : Proc)
  | par (P Q : Proc)
  | nil
  | resN (a : Name) (P : Proc)
  | resS (s : List Chan) (P : Proc)
  | defn (D : List Decl) (P : Proc)
  | call (X : PVar) (es : List Expr) (ss : List Chan)
  | queue (c : Chan) (h : List Msg)
inductive Decl where
  | mk (X : PVar) (xs : List Name) (ss : List Chan) (P : Proc)
end

inductive Eval : Expr → Val → Prop where
  | value (v : Val) : Eval (.val v) v
  | andTT (e f : Expr) (he : Eval e .tt) (hf : Eval f .tt) : Eval (.and e f) .tt
  | andTF (e f : Expr) (he : Eval e .tt) (hf : Eval f .ff) : Eval (.and e f) .ff
  | andFT (e f : Expr) (he : Eval e .ff) (hf : Eval f .tt) : Eval (.and e f) .ff
  | andFF (e f : Expr) (he : Eval e .ff) (hf : Eval f .ff) : Eval (.and e f) .ff
  | orTT (e f : Expr) (he : Eval e .tt) (hf : Eval f .tt) : Eval (.or e f) .tt
  | orTF (e f : Expr) (he : Eval e .tt) (hf : Eval f .ff) : Eval (.or e f) .tt
  | orFT (e f : Expr) (he : Eval e .ff) (hf : Eval f .tt) : Eval (.or e f) .tt
  | orFF (e f : Expr) (he : Eval e .ff) (hf : Eval f .ff) : Eval (.or e f) .ff
  | notT (e : Expr) (he : Eval e .tt) : Eval (.not e) .ff
  | notF (e : Expr) (he : Eval e .ff) : Eval (.not e) .tt

def EvalList (es : List Expr) (vs : List Val) : Prop := List.Forall₂ Eval es vs

def Proc.parList (ps : List Proc) : Proc := ps.foldr Proc.par Proc.nil
def Proc.queues (s : List Chan) : Proc := Proc.parList (s.map (fun c => Proc.queue c []))

-- The paper's process grammar uses nonempty, pairwise-distinct branch labels.
def Proc.wfBranchesFuel : ℕ → Proc → Prop
  | 0, _ => False
  | n+1, .branch _ bs =>
      bs ≠ [] ∧ (bs.map Prod.fst).Nodup ∧ ∀ x ∈ bs, x.2.wfBranchesFuel n
  | n+1, .request _ _ _ P | n+1, .accept _ _ _ P
  | n+1, .send _ _ P | n+1, .recv _ _ P
  | n+1, .deleg _ _ P | n+1, .srecv _ _ P
  | n+1, .sel _ _ P | n+1, .resN _ P | n+1, .resS _ P => P.wfBranchesFuel n
  | n+1, .ite _ P Q | n+1, .par P Q =>
      P.wfBranchesFuel n ∧ Q.wfBranchesFuel n
  | n+1, .defn D P => P.wfBranchesFuel n ∧
      ∀ d ∈ D, match d with | .mk _ _ _ Q => Q.wfBranchesFuel n
  | _+1, .call _ _ _ | _+1, .queue _ _ | _+1, .nil => True

noncomputable def Proc.WellFormedBranches (P : Proc) : Prop :=
  P.wfBranchesFuel (sizeOf P)

end MPSTAsync.Progress


