-- Prove2me | Definitions.Def_CountingLinExt33_Main_Orders
-- name    : CountingLinExt33_Main_Orders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:33.13721+00:00
-- url     : https://prove2.me/theorems/a3b8c7cf-f9ee-441a-84b2-1fed704c7081
-- title:
--   Poset inputs, compatible patterns and weighted deadline paths
-- statement:
--   An input gives a strict comparability matrix or a DAG adjacency matrix on $n$ labeled elements. Its validity means that the supplied matrix, or its computed transitive closure, is exactly the strict relation of a finite partial order $P$. Write $e(P)$ for the cardinality of the published set of order-preserving bijections defining linear extensions.
--
--   For an antichain $B$, put $X=V\setminus B$. Define $D_v=\{x\in X:x<_Pv\}$, $S_v=\{x\in X:v<_Px\}$ and $Y=\bigcup_{v\in B}S_v$. A pattern chooses $g(v)\in S_v$ whenever $S_v$ is nonempty. It is compatible when adjoining $g(v)\to y$ for $y\in S_v\setminus\{g(v)\}$ gives an acyclic relation. Its closure defines $P_g$. An absent successor gives the separate deadline $\infty$.
--
--   For a core ideal $I$, define
--
--   $$A_c(I)=|\{v\in B:\delta(v)=c,\ D_v\subseteq I\}|.$$
--
--   The initial state is $(\varnothing,(A_c(\varnothing))_c)$ and the terminal state is $(X,0)$. An antichain move decrements a positive $q_c$ with weight $q_c$. A core move inserts an eligible $x$, checks $q_x=0$ when $x\in Y$, and increases each coordinate by $A_c(I\cup\{x\})-A_c(I)$ with weight one. The release difference is explicitly required to be nonnegative. Path weights multiply and parallel contributions add. The zero-length path has weight one.
--
--   The same file defines realizability of finite choice tuples by a ranking bijection and their multiplicity vectors. These interfaces state the DP correctness and multiplicity milestones independently of the executable program.
--
--   **Formalization Note** All poset comparisons use the supplied order explicitly, avoiding the numeric order on vertex labels. Counts reuse `FCP.Order.LinearExtensions`. The deadline type has zero-padded coordinates for all vertices and a separate sentinel; each availability coordinate lies in $\{0,\ldots,n\}$, which contains every reachable value.
-- source:
--   Keigo Oka, STOC 2027 submission #725 (October 2026), printed pp. 2–5 (PDF pp. 3–6), §2, §3.2 equations (4)–(5), Lemma 4 and §3.3; printed p. 7 (PDF p. 8), §4 any-antichain extension

import Mathlib
import Definitions.Def_FCP_LinearExtensions

namespace CountingLinExt33.Main

/-- The tag distinguishes a strict comparability matrix from a DAG matrix. -/
structure OrderInput (n : ℕ) where
  closed : Bool
  edge : Fin n → Fin n → Bool

/-- Floyd--Warshall Boolean closure, with no reflexive diagonal inserted. -/
def boolClosure {n : ℕ} (a : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  (List.finRange n).foldl (fun m k i j => m i j || (m i k && m k j)) a

def ValidInput {n : ℕ} (P : PartialOrder (Fin n)) (a : OrderInput n) : Prop :=
  if a.closed then ∀ i j, a.edge i j = true ↔ P.lt i j
  else ∀ i j, boolClosure a.edge i j = true ↔ P.lt i j

def encodeOrder {n : ℕ} (a : OrderInput n) : List ℕ :=
  [n, if a.closed then 1 else 0] ++
    (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => if a.edge i j then 1 else 0))

noncomputable def extensionCount {n : ℕ} (P : PartialOrder (Fin n)) : ℕ :=
  (@FCP.Order.LinearExtensions (Fin n) _ P).ncard

def comparability {n : ℕ} (P : PartialOrder (Fin n)) : SimpleGraph (Fin n) :=
  { Adj := fun i j => P.lt i j ∨ P.lt j i
    symm := ⟨by intro i j h; exact h.elim Or.inr Or.inl⟩
    loopless := ⟨by intro i h; exact h.elim (@lt_irrefl _ P.toPreorder i) (@lt_irrefl _ P.toPreorder i)⟩ }

noncomputable def encodeGraph {n : ℕ} (G : SimpleGraph (Fin n)) : List ℕ := by
  classical
  exact [n, 0] ++ (List.finRange n).flatMap (fun i =>
    (List.finRange n).map (fun j => if G.Adj i j then 1 else 0))

noncomputable def graphNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ b ∈ B, G.Adj b x)

def Antichain {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n)) : Prop :=
  ∀ u ∈ B, ∀ v ∈ B, ¬ P.lt u v

def IdealOn {n : ℕ} (P : PartialOrder (Fin n)) (U I : Finset (Fin n)) : Prop :=
  I ⊆ U ∧ ∀ y ∈ I, ∀ x ∈ U, P.lt x y → x ∈ I

noncomputable def idealCount {n : ℕ} (P : PartialOrder (Fin n)) (U : Finset (Fin n)) : ℕ := by
  classical
  exact (U.powerset.filter (IdealOn P U)).card

noncomputable def core {n : ℕ} (B : Finset (Fin n)) : Finset (Fin n) := Finset.univ \ B

noncomputable def predecessors {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact (core B).filter (fun x => P.lt x v)

noncomputable def successors {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact (core B).filter (fun x => P.lt v x)

noncomputable def upperCore {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n)) : Finset (Fin n) :=
  B.biUnion (successors P B)

/-- `none` is the separate infinite-deadline sentinel. Outside B it is just padding. -/
def IsPattern {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n)) (g : Fin n → Option (Fin n)) : Prop :=
  ∀ v, (v ∈ B ∧ (successors P B v).Nonempty → ∃ y ∈ successors P B v, g v = some y) ∧
    (v ∉ B ∨ ¬ (successors P B v).Nonempty → g v = none)

def augmented {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n)) (g : Fin n → Option (Fin n)) : Fin n → Fin n → Prop :=
  fun x y => P.lt x y ∨ ∃ v ∈ B, g v = some x ∧ y ∈ successors P B v ∧ x ≠ y

def Compatible {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n)) (g : Fin n → Option (Fin n)) : Prop :=
  IsPattern P B g ∧ ∀ x, ¬ Relation.TransGen (augmented P B g) x x

/-- Structural partial-order instance for an acyclic relation's transitive closure. -/
@[instance_reducible] def reachOrder {n : ℕ} (r : Fin n → Fin n → Prop) (h : ∀ x, ¬ Relation.TransGen r x x) : PartialOrder (Fin n) where
  le x y := x = y ∨ Relation.TransGen r x y
  lt x y := (x = y ∨ Relation.TransGen r x y) ∧ ¬ (y = x ∨ Relation.TransGen r y x)
  lt_iff_le_not_ge := by intros; rfl
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    exact Or.inr (hxy.trans hyz)
  le_antisymm x y hxy hyx := by
    rcases hxy with hxy | hxy
    · exact hxy
    rcases hyx with hyx | hyx
    · exact hyx.symm
    exact False.elim (h x (hxy.trans hyx))

@[instance_reducible] def patternOrder {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n))
    (g : Fin n → Option (Fin n)) (h : Compatible P B g) : PartialOrder (Fin n) :=
  reachOrder (augmented P B g) h.2

noncomputable def released {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n))
    (g : Fin n → Option (Fin n)) (I : Finset (Fin n)) (c : Option (Fin n)) : ℕ := by
  classical
  exact (B.filter (fun v => g v = c ∧ predecessors P B v ⊆ I)).card

/-- Coordinates outside Y are zero on reachable states. Each coordinate is bounded by n. -/
abbrev DPState (n : ℕ) := Finset (Fin n) × (Option (Fin n) → Fin (n + 1))

noncomputable def dpInitial {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n))
    (g : Fin n → Option (Fin n)) : DPState n := by
  classical
  exact (∅, fun c => ⟨released P B g ∅ c, Nat.lt_succ_of_le
    ((Finset.card_filter_le _ _).trans (by simpa using Finset.card_le_univ B))⟩)

noncomputable def dpTerminal {n : ℕ} (B : Finset (Fin n)) : DPState n := (core B, fun _ => 0)

def AntichainStep {n : ℕ} (c : Option (Fin n)) (s t : DPState n) : Prop :=
  0 < (s.2 c).val ∧ t.1 = s.1 ∧ (t.2 c).val + 1 = (s.2 c).val ∧ ∀ d, d ≠ c → t.2 d = s.2 d

def CoreStep {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n))
    (g : Fin n → Option (Fin n)) (h : Compatible P B g) (x : Fin n) (s t : DPState n) : Prop :=
  x ∈ core B ∧ x ∉ s.1 ∧ t.1 = insert x s.1 ∧ IdealOn (patternOrder P B g h) (core B) t.1 ∧
    (x ∈ upperCore P B → (s.2 (some x)).val = 0) ∧
    ∀ c, released P B g s.1 c ≤ released P B g t.1 c ∧
      (t.2 c).val = (s.2 c).val + (released P B g t.1 c - released P B g s.1 c)

/-- Parallel transition weights are added; antichain moves carry their availability multiplicity. -/
noncomputable def dpEdge {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n))
    (g : Fin n → Option (Fin n)) (h : Compatible P B g) (s t : DPState n) : ℕ := by
  classical
  exact (∑ c : Option (Fin n), if AntichainStep c s t then (s.2 c).val else 0) +
    ∑ x : Fin n, if CoreStep P B g h x s t then 1 else 0

/-- Weight of paths of exactly l steps from the initial state, including the empty path. -/
noncomputable def dpPaths {n : ℕ} (P : PartialOrder (Fin n)) (B : Finset (Fin n))
    (g : Fin n → Option (Fin n)) (h : Compatible P B g) : ℕ → DPState n → ℕ
  | 0, t => by
    classical
    exact if t = dpInitial P B g then 1 else 0
  | l + 1, t => ∑ s : DPState n, dpPaths P B g h l s * dpEdge P B g h s t

/-- Distinct orders may witness realizability of different tuples. -/
def Realizable {m t : ℕ} (S : Fin t → Finset (Fin m)) (g : Fin t → Fin m) : Prop :=
  ∃ rank : Fin m ≃ Fin m, ∀ i, g i ∈ S i ∧ ∀ y ∈ S i, rank (g i) ≤ rank y

noncomputable def multiplicity {m t : ℕ} (g : Fin t → Fin m) (y : Fin m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => g i = y)).card

/-- Exact sixth root; exponent division is in the reals. -/
noncomputable def rho : ℝ := (33 : ℝ) ^ ((1 : ℝ) / 6)

end CountingLinExt33.Main


