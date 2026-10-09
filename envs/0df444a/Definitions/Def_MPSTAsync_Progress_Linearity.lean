-- Prove2me | Definitions.Def_MPSTAsync_Progress_Linearity
-- name    : MPSTAsync_Progress_Linearity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:06:03.069334+00:00
-- url     : https://prove2.me/theorems/2aa8c390-f169-4f49-bcad-afa392beeb1f
-- title:
--   Defs. 3.3, 3.7, 3.11–3.12 — node order, dependencies and linearity
-- statement:
--   A **node** is an interaction at a position in a finite unfolding of a global type. The order $n\prec m$ places an action before a later action within the same continuation, branch or parallel component. The input and output dependency relations follow the sender and receiver matching rules of the paper.
--
--   $$\operatorname{Linear}(G)\iff\forall n\prec m\text{ on the same channel},\quad n\prec_{\mathrm{in}}m\ \land\ n\prec_{\mathrm{out}}m.$$
--
--   The module also checks finite branch families, closed recursion and guard conditions. It supplies the causal side of global-type coherence.
--
--   **Formalization Note** Recursive types are tested on every finite unfolding. Input dependencies have at least one step, resolving the impossible printed $n=0$ case in Def. 3.11. Carried global types are checked recursively.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 15–20, Defs. 3.3, 3.7, 3.11–3.12, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_GlobalTypes

set_option autoImplicit false

namespace MPSTAsync.Progress

-- A position is a root-to-node path in the finite syntax tree of an unfolding.
abbrev Pos := List ℕ

inductive NodeAt : GType → Pos → Role → Role → ℕ → Prop where
  | commRoot (p q : Role) (k : ℕ) (U : VType) (G : GType) :
      NodeAt (.comm p q k U G) [] p q k
  | branchRoot (p q : Role) (k : ℕ) (bs : List (Label × GType)) :
      NodeAt (.branch p q k bs) [] p q k
  | commBelow (p q : Role) (k : ℕ) (U : VType) (G : GType)
      (path : Pos) (a b : Role) (j : ℕ) (h : NodeAt G path a b j) :
      NodeAt (.comm p q k U G) (0::path) a b j
  | branchBelow (p q : Role) (k i : ℕ) (bs : List (Label × GType))
      (l : Label) (G : GType) (path : Pos) (a b : Role) (j : ℕ)
      (hget : bs[i]? = some (l,G)) (h : NodeAt G path a b j) :
      NodeAt (.branch p q k bs) (i::path) a b j
  | parLeft (G H : GType) (path : Pos) (a b : Role) (j : ℕ)
      (h : NodeAt G path a b j) : NodeAt (.par G H) (0::path) a b j
  | parRight (G H : GType) (path : Pos) (a b : Role) (j : ℕ)
      (h : NodeAt H path a b j) : NodeAt (.par G H) (1::path) a b j

-- The five cases of Definition 3.7 are represented by root order under a
-- communication or branching and order propagated inside one component.
inductive PrecStep : GType → Pos → Pos → Prop where
  | commRoot (p q : Role) (k : ℕ) (U : VType) (G : GType)
      (m : Pos) (a b : Role) (j : ℕ) (h : NodeAt G m a b j) :
      PrecStep (.comm p q k U G) [] (0::m)
  | branchRoot (p q : Role) (k i : ℕ) (bs : List (Label × GType))
      (l : Label) (G : GType) (m : Pos) (a b : Role) (j : ℕ)
      (hget : bs[i]? = some (l,G)) (h : NodeAt G m a b j) :
      PrecStep (.branch p q k bs) [] (i::m)
  | commLift (p q : Role) (k : ℕ) (U : VType) (G : GType)
      (n m : Pos) (h : PrecStep G n m) :
      PrecStep (.comm p q k U G) (0::n) (0::m)
  | branchLift (p q : Role) (k i : ℕ) (bs : List (Label × GType))
      (l : Label) (G : GType) (n m : Pos)
      (hget : bs[i]? = some (l,G)) (h : PrecStep G n m) :
      PrecStep (.branch p q k bs) (i::n) (i::m)
  | parLeft (G H : GType) (n m : Pos) (h : PrecStep G n m) :
      PrecStep (.par G H) (0::n) (0::m)
  | parRight (G H : GType) (n m : Pos) (h : PrecStep H n m) :
      PrecStep (.par G H) (1::n) (1::m)

def Precedes (G : GType) (n m : Pos) : Prop :=
  Relation.TransGen (PrecStep G) n m

def DepII (G : GType) (n m : Pos) : Prop :=
  Precedes G n m ∧ ∃ p q r k j, NodeAt G n p q k ∧ NodeAt G m r q j

def DepIO (G : GType) (n m : Pos) : Prop :=
  Precedes G n m ∧ ∃ p q r k j, NodeAt G n p q k ∧ NodeAt G m q r j

def DepOO (G : GType) (n m : Pos) : Prop :=
  Precedes G n m ∧ ∃ p q r k, NodeAt G n p q k ∧ NodeAt G m p r k

def InputDep (G : GType) (n m : Pos) : Prop :=
  ∃ u, Relation.ReflTransGen (DepIO G) n u ∧ DepII G u m

def OutputDep (G : GType) (n m : Pos) : Prop :=
  Relation.TransGen (fun a b => DepOO G a b ∨ DepIO G a b) n m

def CoreLinear (G : GType) : Prop :=
  ∀ n m p q r s k, NodeAt G n p q k → NodeAt G m r s k →
    Precedes G n m → InputDep G n m ∧ OutputDep G n m

mutual
def GType.allCarriedFuel : ℕ → GType → List GType
  | 0, _ => []
  | n+1, .comm _ _ _ U G => U.allCarriedFuel n ++ G.allCarriedFuel n
  | n+1, .branch _ _ _ bs => bs.flatMap (fun x => x.2.allCarriedFuel n)
  | n+1, .par G H => G.allCarriedFuel n ++ H.allCarriedFuel n
  | n+1, .mu _ G => G.allCarriedFuel n
  | _+1, .var _ | _+1, .stop => []
def VType.allCarriedFuel : ℕ → VType → List GType
  | 0, _ => []
  | n+1, .sorts Ss => Ss.flatMap (ValSort.allCarriedFuel n)
  | n+1, .located T _ => T.allCarriedFuel n
def ValSort.allCarriedFuel : ℕ → ValSort → List GType
  | 0, _ => []
  | _+1, .bool => []
  | n+1, .shared G => G :: G.allCarriedFuel n
def EType.allCarriedFuel : ℕ → EType → List GType
  | 0, _ => []
  | n+1, .send _ U T | n+1, .recv _ U T => U.allCarriedFuel n ++ T.allCarriedFuel n
  | n+1, .sel _ bs | n+1, .bra _ bs => bs.flatMap (fun x => x.2.allCarriedFuel n)
  | n+1, .mu _ T => T.allCarriedFuel n
  | _+1, .var _ | _+1, .stop => []
end

noncomputable def GType.allCarried (G : GType) : List GType :=
  G.allCarriedFuel (sizeOf G)

def IsLinear (G : GType) : Prop :=
  (∀ n, CoreLinear (G.unfold n)) ∧
  (∀ H ∈ G.allCarried, ∀ n, CoreLinear (H.unfold n))

-- The finite tree is closed and guarded, and every choice has a genuine label family.
mutual
def GType.wfFuel : ℕ → Finset TVar → Bool → GType → Prop
  | 0, _, _, _ => False
  | n+1, bound, _, .comm p q k U G =>
      p ≠ q ∧ 1 ≤ k ∧ U.wfFuel n ∧ G.wfFuel n bound true
  | n+1, bound, _, .branch p q k bs =>
      p ≠ q ∧ 1 ≤ k ∧ bs ≠ [] ∧ (bs.map Prod.fst).Nodup ∧
        ∀ x ∈ bs, x.2.wfFuel n bound true
  | n+1, bound, guarded, .par G H =>
      G.wfFuel n bound guarded ∧ H.wfFuel n bound guarded
  | n+1, bound, _, .mu t G => G.wfFuel n (insert t bound) false
  | _+1, bound, guarded, .var t => t ∈ bound ∧ guarded
  | _+1, _, _, .stop => True
def VType.wfFuel : ℕ → VType → Prop
  | 0, _ => False
  | n+1, .sorts Ss => ∀ S ∈ Ss, S.wfFuel n
  | n+1, .located T _ => T.wfFuel n ∅ false
def ValSort.wfFuel : ℕ → ValSort → Prop
  | 0, _ => False
  | _+1, .bool => True
  | n+1, .shared G => G.wfFuel n ∅ false
def EType.wfFuel : ℕ → Finset TVar → Bool → EType → Prop
  | 0, _, _, _ => False
  | n+1, bound, _, .send k U T | n+1, bound, _, .recv k U T =>
      1 ≤ k ∧ U.wfFuel n ∧ T.wfFuel n bound true
  | n+1, bound, _, .sel k bs | n+1, bound, _, .bra k bs =>
      1 ≤ k ∧ bs ≠ [] ∧ (bs.map Prod.fst).Nodup ∧
        ∀ x ∈ bs, x.2.wfFuel n bound true
  | n+1, bound, _, .mu t T => T.wfFuel n (insert t bound) false
  | _+1, bound, guarded, .var t => t ∈ bound ∧ guarded
  | _+1, _, _, .stop => True
end

noncomputable def GType.WellFormed (G : GType) : Prop :=
  G.wfFuel (sizeOf G) ∅ false
noncomputable def EType.WellFormed (T : EType) : Prop :=
  T.wfFuel (sizeOf T) ∅ false

end MPSTAsync.Progress


