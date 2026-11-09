-- Prove2me | Definitions.Def_ProportionalTSP_Exact_Trees
-- name    : ProportionalTSP_Exact_Trees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:24.0589+00:00
-- url     : https://prove2.me/theorems/aa4b16da-e6dc-4ecf-84b9-12e295997ba5
-- title:
--   Neighboring-load trees, normalized prices, and compatible-set enumeration
-- statement:
--   For a load $d$, let $p$ be its first positive index, $L_p=\{p,\ldots,m\}$, $u=d-e_p$, and $d^{(j)}=u+e_j$. The definitions compute
--   $$T_S(u)=\bigcup_{j\in S}A_{u+e_j},\qquad a_j^{(d)}=w(A_d)-w(A_{d^{(j)}}).$$
--   The restricted tree has vertex type $S\sqcup R$; isolated vertices outside $S$ are not included. Parent relations use an adjacent vertex one step nearer the root. The coloring forest is the undirected relation of equation (3.1), on all of $L$, including isolated vertices.
--
--   A compatible set satisfies $r\in U\iff A(r)\in U$. The enumeration lists balanced feasible loads and proper Boolean colorings of their computed forests and outputs their compatible subsets, preserving multiplicity. The count is $N_{m,k}=\sum_d2^{b(d)}$, where $b(d)=p(d)+|\{l>p(d):d_l=2\}|$. Fin indexing is compensated by adding one in $b(d)$. Every finite enumeration has an explicit numeric rank order.
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), §2.3, equation (2.1), Definition 3.1, equation (3.1), PDF p. 5–9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Assignments

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

/-- Cross graphs on the actual restricted carrier S ⊔ R. -/
def crossGraph {m k : ℕ} (S : Finset (Fin m)) (e : Fin m → Fin k → Prop) :
    SimpleGraph (S ⊕ Fin k) where
  Adj x y := match x, y with
    | .inl l, .inr r => e l.val r
    | .inr r, .inl l => e l.val r
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def unitLoad {m : ℕ} (j : Fin m) : Load m := fun l => if l = j then 1 else 0

def plusUnit {m : ℕ} (u : Load m) (j : Fin m) : Load m := fun l => u l + unitLoad j l

def firstPositive {m : ℕ} [NeZero m] (d : Load m) : Fin m :=
  ((List.finRange m).find? (fun l => decide (0 < d l))).getD
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

def tailSet {m : ℕ} [NeZero m] (d : Load m) : Finset (Fin m) :=
  Finset.univ.filter (fun l => firstPositive d ≤ l)

def removeFirst {m : ℕ} [NeZero m] (d : Load m) : Load m :=
  fun l => d l - unitLoad (firstPositive d) l

def neighboringTree {m k : ℕ} [NeZero m] (w : Fin m → Fin k → ℝ)
    (S : Finset (Fin m)) (u : Load m) : SimpleGraph (S ⊕ Fin k) :=
  crossGraph S (fun l r => ∃ j ∈ S, canonical w (plusUnit u j) r = l)

def normalizedPrices {m k : ℕ} [NeZero m]
    (w : Fin m → Fin k → ℝ) (d : Load m) : Fin m → ℝ :=
  fun j => assignmentCost w (canonical w d) -
    assignmentCost w (canonical w (plusUnit (removeFirst d) j))

def normalizedTree {m k : ℕ} [NeZero m] (w : Fin m → Fin k → ℝ) (d : Load m) :=
  neighboringTree w (tailSet d) (removeFirst d)

def restrictedTightGraph {m k : ℕ} (w : Fin m → Fin k → ℝ)
    (S : Finset (Fin m)) (a : Fin m → ℝ) := crossGraph S (TightEdge w a S)

/-- In a tree the adjacent vertex one step closer to the root is the unique parent. -/
def RootParent {V : Type} (T : SimpleGraph V) (root child parent : V) : Prop :=
  T.Adj child parent ∧ T.dist root parent + 1 = T.dist root child

/-- Newly assigned vertex. The minimum-index fallback is unused when Lemma 2.9 applies. -/
def newVertex {m k : ℕ} [NeZero m] [NeZero k]
    (A B : Assignment m k) (j : Fin m) : Fin k :=
  ((List.finRange k).find? (fun r => decide (B r = j ∧ A r ≠ j))).getD
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩

def coloringForestBy {m k : ℕ} [NeZero m] [NeZero k]
    (Ad : Load m → Assignment m k) (d : Load m) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun j l =>
    firstPositive d < j ∧ d j ≤ 1 ∧
      l = Ad d (newVertex (Ad d) (Ad (plusUnit (removeFirst d) j)) j))

def coloringForest {m k : ℕ} [NeZero m] [NeZero k]
    (w : Fin m → Fin k → ℝ) (d : Load m) := coloringForestBy (canonical w) d

def Compatible {m k : ℕ} (A : Assignment m k) (U : Finset (Vertex m k)) : Prop :=
  ∀ r, Sum.inr r ∈ U ↔ Sum.inl (A r) ∈ U

def compatibleFamily {m k : ℕ} [NeZero m] (w : Fin m → Fin k → ℝ) :
    Finset (Finset (Vertex m k)) :=
  Finset.univ.filter (fun U => ∃ d : Fin m → Fin (k+1),
    feasible k (fun l => (d l).val) ∧ balanced (fun l => (d l).val) ∧
      Compatible (canonical w (fun l => (d l).val)) U)

/-- Feasible loads bounded by k; this includes all nonnegative integer loads of total k. -/
def loadList (m k : ℕ) : List (Load m) :=
  ((Finset.univ : Finset (Fin m → Fin (k+1))).toList.mergeSort
    (fun a b => decide ((∑ l, (a l).val * (k+1)^l.val) ≤
      (∑ l, (b l).val * (k+1)^l.val)))).map (fun d l => (d l).val)

def balancedLoads (m k : ℕ) : List (Load m) :=
  (loadList m k).filter (fun d => decide (feasible k d ∧ balanced d))

def coloringList (m : ℕ) : List (Fin m → Bool) :=
  (Finset.univ : Finset (Fin m → Bool)).toList.mergeSort
    (fun a b => decide ((∑ l, (if a l then 1 else 0 : ℕ) * 2^l.val) ≤
      (∑ l, (if b l then 1 else 0 : ℕ) * 2^l.val)))

def ProperColoring {V : Type} (T : SimpleGraph V) (c : V → Bool) : Prop :=
  ∀ x y, T.Adj x y → c x ≠ c y

def coloringOutput {m k : ℕ} (A : Assignment m k) (c : Fin m → Bool) :
    Finset (Vertex m k) :=
  Finset.univ.filter (fun v => match v with
    | .inl l => c l = true
    | .inr r => c (A r) = true)

def enumerationBy {m k : ℕ} [NeZero m] [NeZero k]
    (Ad : Load m → Assignment m k) : List (Finset (Vertex m k)) :=
  (balancedLoads m k).flatMap (fun d =>
    ((coloringList m).filter (fun c => decide (ProperColoring (coloringForestBy Ad d) c))).map
      (coloringOutput (Ad d)))

def enumeration {m k : ℕ} [NeZero m] [NeZero k] (w : Fin m → Fin k → ℝ) :
    List (Finset (Vertex m k)) := enumerationBy (canonical w)

/-- Paper indices are 1-based, hence the +1 after Fin's first-positive index. -/
def componentExponent {m : ℕ} [NeZero m] (d : Load m) : ℕ :=
  (firstPositive d).val + 1 + (Finset.univ.filter (fun l => firstPositive d < l ∧ d l = 2)).card

def outputCount (m k : ℕ) [NeZero m] : ℕ :=
  ((balancedLoads m k).map (fun d => 2 ^ componentExponent d)).sum

end ProportionalTSP.Exact


