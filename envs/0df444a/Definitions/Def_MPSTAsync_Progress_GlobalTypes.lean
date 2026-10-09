-- Prove2me | Definitions.Def_MPSTAsync_Progress_GlobalTypes
-- name    : MPSTAsync_Progress_GlobalTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:13.706207+00:00
-- url     : https://prove2.me/theorems/26643e80-6f25-49e7-98e2-d41ce83db9e7
-- title:
--   Figs. 4 and 6, Def. 3.2, Notation A.1 — global and endpoint types
-- statement:
--   A **global type** records communications between numbered roles over numbered session channels. A communication carries either a vector of value sorts or a located endpoint type; a branch offers a finite labelled family. Global types also have parallel composition, guarded recursion, variables and termination. **Endpoint types** record the local send, receive, select and branch actions. The module defines participant and channel-index sets, substitution, finite recursion unfoldings, and the labelled transition relation $G\xrightarrow{\ell}G'$.
--
--   $$G ::= p\to q:k\langle U\rangle.G\mid p\to q:k\{l_i:G_i\}_{i\in I}\mid G\mid G\mid\mu t.G\mid t\mid\mathrm{end}. $$
--
--   These declarations are shared by the projection, typing and progress statements.
--
--   **Formalization Note** Roles and identifiers are natural numbers; channel indices start at one. The printed Boolean and shared-name sorts are represented. The global transition relation includes the paper's equi-recursive unfolding convention and treats parallel composition with `end` as a unit.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 12–14, 21, 52, Figs. 4 and 6, Def. 3.2, Notation A.1, https://doi.org/10.1145/2827695

import Mathlib

set_option autoImplicit false

namespace MPSTAsync.Progress

abbrev Name := ℕ
abbrev Chan := ℕ
abbrev Label := ℕ
abbrev PVar := ℕ
abbrev Role := ℕ
abbrev TVar := ℕ

mutual
inductive GType where
  | comm (p q : Role) (k : ℕ) (U : VType) (G : GType)
  | branch (p q : Role) (k : ℕ) (bs : List (Label × GType))
  | par (G H : GType)
  | mu (t : TVar) (G : GType)
  | var (t : TVar)
  | stop
  deriving BEq
inductive VType where
  | sorts (Ss : List ValSort)
  | located (T : EType) (p : Role)
  deriving BEq
inductive ValSort where
  | bool
  | shared (G : GType)
  deriving BEq
inductive EType where
  | send (k : ℕ) (U : VType) (T : EType)
  | recv (k : ℕ) (U : VType) (T : EType)
  | sel (k : ℕ) (bs : List (Label × EType))
  | bra (k : ℕ) (bs : List (Label × EType))
  | mu (t : TVar) (T : EType)
  | var (t : TVar)
  | stop
  deriving BEq
end

-- A size-based recursion budget makes the mutual syntax traversals total.
-- Every recursive call descends one constructor of the original syntax.
mutual
def GType.substFuel : ℕ → TVar → GType → GType → GType
  | 0, _, _, G => G
  | n+1, t, R, .comm p q k U G =>
      .comm p q k (VType.substFuel n t R U) (GType.substFuel n t R G)
  | n+1, t, R, .branch p q k bs =>
      .branch p q k (bs.map fun x => (x.1,GType.substFuel n t R x.2))
  | n+1, t, R, .par G H => .par (GType.substFuel n t R G) (GType.substFuel n t R H)
  | n+1, t, R, .mu u G =>
      if t = u then .mu u G else .mu u (GType.substFuel n t R G)
  | _+1, t, R, .var u => if t = u then R else .var u
  | _+1, _, _, .stop => .stop
def VType.substFuel : ℕ → TVar → GType → VType → VType
  | 0, _, _, U => U
  | n+1, t, R, .sorts Ss => .sorts (Ss.map (ValSort.substFuel n t R))
  | n+1, t, R, .located T p => .located (EType.substFuel n t R T) p
def ValSort.substFuel : ℕ → TVar → GType → ValSort → ValSort
  | 0, _, _, S => S
  | _+1, _, _, .bool => .bool
  | n+1, t, R, .shared G => .shared (GType.substFuel n t R G)
def EType.substFuel : ℕ → TVar → GType → EType → EType
  | 0, _, _, T => T
  | n+1, t, R, .send k U T => .send k (VType.substFuel n t R U) (EType.substFuel n t R T)
  | n+1, t, R, .recv k U T => .recv k (VType.substFuel n t R U) (EType.substFuel n t R T)
  | n+1, t, R, .sel k bs => .sel k (bs.map fun x => (x.1,EType.substFuel n t R x.2))
  | n+1, t, R, .bra k bs => .bra k (bs.map fun x => (x.1,EType.substFuel n t R x.2))
  | n+1, t, R, .mu u T => .mu u (EType.substFuel n t R T)
  | _+1, _, _, .var u => .var u
  | _+1, _, _, .stop => .stop
end

noncomputable def GType.subst (G : GType) (t : TVar) (R : GType) : GType :=
  GType.substFuel (sizeOf G) t R G

-- Notation A.1: only continuation structure is unfolded, never carried types.
noncomputable def GType.unfoldFuel : ℕ → ℕ → GType → GType
  | _, 0, G => G
  | 0, fuel+1, .mu t G =>
      (GType.unfoldFuel 0 fuel G).subst t .stop
  | n+1, fuel+1, .mu t G =>
      (GType.unfoldFuel (n+1) fuel G).subst t
        (GType.unfoldFuel n (sizeOf (GType.mu t G)) (GType.mu t G))
  | n, fuel+1, .comm p q k U G => .comm p q k U (GType.unfoldFuel n fuel G)
  | n, fuel+1, .branch p q k bs =>
      .branch p q k (bs.map fun x => (x.1,GType.unfoldFuel n fuel x.2))
  | n, fuel+1, .par G H => .par (GType.unfoldFuel n fuel G) (GType.unfoldFuel n fuel H)
  | _, _+1, .var t => .var t
  | _, _+1, .stop => .stop
termination_by n fuel G => (n,fuel)

noncomputable def GType.unfold (n : ℕ) (G : GType) : GType :=
  GType.unfoldFuel n (sizeOf G) G

def GType.pidFuel : ℕ → GType → Finset Role
  | 0, _ => ∅
  | n+1, .comm p q _ _ G => insert p (insert q (GType.pidFuel n G))
  | n+1, .branch p q _ bs =>
      insert p (insert q (bs.foldl (fun a b => a ∪ GType.pidFuel n b.2) ∅))
  | n+1, .par G H => GType.pidFuel n G ∪ GType.pidFuel n H
  | n+1, .mu _ G => GType.pidFuel n G
  | _+1, .var _ | _+1, .stop => ∅

noncomputable def GType.pid (G : GType) : Finset Role := GType.pidFuel (sizeOf G) G

def GType.sidFuel : ℕ → GType → Finset ℕ
  | 0, _ => ∅
  | n+1, .comm _ _ k _ G => insert k (GType.sidFuel n G)
  | n+1, .branch _ _ k bs =>
      insert k (bs.foldl (fun a b => a ∪ GType.sidFuel n b.2) ∅)
  | n+1, .par G H => GType.sidFuel n G ∪ GType.sidFuel n H
  | n+1, .mu _ G => GType.sidFuel n G
  | _+1, .var _ | _+1, .stop => ∅

noncomputable def GType.sid (G : GType) : Finset ℕ := GType.sidFuel (sizeOf G) G

inductive GLabel where
  | value (p q : Role) (k : ℕ) (U : VType)
  | choice (p q : Role) (k : ℕ) (l : Label)

def GLabel.avoids (q : Role) : GLabel → Prop
  | .value p r _ _ | .choice p r _ _ => q ≠ p ∧ q ≠ r

-- Definition 3.2, including unfolding and the unit law for end in parallel.
inductive GStep : GType → GLabel → GType → Prop where
  | GR1 (p q : Role) (k : ℕ) (U : VType) (G : GType) : GStep (.comm p q k U G) (.value p q k U) G
  | GR2 (p q : Role) (k : ℕ) (l : Label) (bs : List (Label × GType)) (G : GType) (h : (l,G) ∈ bs) :
      GStep (.branch p q k bs) (.choice p q k l) G
  | GR3 (p q : Role) (k : ℕ) (U : VType) (G G' : GType) (l : GLabel) (h : GStep G l G')
      (hp : l.avoids q) :
      GStep (.comm p q k U G) l (.comm p q k U G')
  | GR4 (p q : Role) (k : ℕ) (bs bs' : List (Label × GType)) (l : GLabel)
      (hlabels : bs.map Prod.fst = bs'.map Prod.fst)
      (h : ∀ x ∈ bs, ∀ y ∈ bs', x.1 = y.1 → GStep x.2 l y.2)
      (hp : l.avoids q) :
      GStep (.branch p q k bs) l (.branch p q k bs')
  | GR5L (G H G' : GType) (l : GLabel) (h : GStep G l G') :
      GStep (.par G H) l (.par G' H)
  | GR5R (G H H' : GType) (l : GLabel) (h : GStep H l H') :
      GStep (.par G H) l (.par G H')
  | REC (t : TVar) (G G' : GType) (l : GLabel)
      (h : GStep (G.subst t (.mu t G)) l G') : GStep (.mu t G) l G'
  | PAR_END_L (G G' : GType) (l : GLabel) (h : GStep G l G') :
      GStep (.par .stop G) l G'
  | PAR_END_R (G G' : GType) (l : GLabel) (h : GStep G l G') :
      GStep (.par G .stop) l G'

end MPSTAsync.Progress


