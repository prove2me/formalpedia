-- Prove2me | Definitions.Def_MinimaxInterventions1429_Separable_BitPrograms
-- name    : MinimaxInterventions1429_Separable_BitPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:37.848328+00:00
-- url     : https://prove2.me/theorems/1b3c08fc-2478-4be8-86f4-c96a9dbbdf33
-- title:
--   Adaptive bit-query programs and the literal tolerant interval recurrence
-- statement:
--   A finite adaptive bit-query program is either a leaf containing its result or a query $(B,h)$ with a continuation for each of the two possible response bits. The number of calls is its maximum root-to-leaf depth. Evaluation consults an arbitrary oracle that receives the entire observed query-bit history, appends the new query and bit, and continues. The resulting transcript records only public queries and returned bits.
--
--   For slack $\psi\ge0$, tolerant interval search initializes $[l,u]=[-1,1]$, asks at $t=(l+u)/2$, and updates
--
--   $$v=1:\quad u\leftarrow\min(u,t+\psi),\qquad
--   v=0:\quad l\leftarrow\max(l,t-\psi).$$
--
--   After exactly $T$ calls its output is the midpoint clipped to $[-1,1]$. Both the direct recurrence on a list of bits and the adaptive query-program version are defined. Contrast search uses the exposure surcharge and $\psi=2\alpha$; level search uses the saturated surcharge and $\psi=2(\alpha+2\kappa)$.
--
--   For Lemma 3.4, a rooted spanning tree is represented by a root, a parent function, and a natural rank strictly decreasing towards the root. Its undirected edges are the parent edges, and diameter at most three means that every pair is connected by a path of at most three edges. Levels are computed by summing the supplied edge estimates along the parent path to the root. These are generic tree data, not assumptions supplied to the reconstruction algorithm.
--
--   The module exposes the observable computation needed to state comparison and alignment correctness. It contains no accuracy or reconstruction guarantee.
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Section 2 response model, printed pp.8–9 (PDF pp.10–11); Section 3.1 interval search and Lemmas 3.1–3.4, printed pp.10–11 (PDF pp.12–13)

import Definitions.Def_MinimaxInterventions1429_Separable_Model
set_option autoImplicit false

noncomputable section

namespace MinimaxInterventions1429.Separable

/-- A finite adaptive bit-query tree. Its leaves may contain any result type. -/
inductive BitProgram (m k : ℕ) (A : Type) where
  | done : A → BitProgram m k A
  | ask : Query m k → (Bool → BitProgram m k A) → BitProgram m k A

def BitProgram.bind {m k : ℕ} {A C : Type}
    (p : BitProgram m k A) (f : A → BitProgram m k C) : BitProgram m k C :=
  match p with
  | .done a => f a
  | .ask q next => .ask q (fun v => (next v).bind f)

def BitProgram.maxQueries {m k : ℕ} {A : Type} : BitProgram m k A → ℕ
  | .done _ => 0
  | .ask _ next => 1 + max (next true).maxQueries (next false).maxQueries

def BitProgram.queriesSatisfy {m k : ℕ} {A : Type}
    (P : Query m k → Prop) : BitProgram m k A → Prop
  | .done _ => True
  | .ask q next => P q ∧ ∀ v, (next v).queriesSatisfy P

def BitProgram.run {m k : ℕ} {A : Type} (O : BitOracle m k) :
    BitProgram m k A → History m k → A × History m k
  | .done a, hist => (a, hist)
  | .ask q next, hist =>
    let v := O hist q
    (next v).run O (hist ++ [(q, v)])

def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

def intervalUpdate (ψ : ℝ) (bounds : ℝ × ℝ) (v : Bool) : ℝ × ℝ :=
  let t := (bounds.1 + bounds.2) / 2
  if v then (bounds.1, min bounds.2 (t + ψ))
  else (max bounds.1 (t - ψ), bounds.2)

def intervalBounds (ψ : ℝ) (bits : List Bool) : ℝ × ℝ :=
  bits.foldl (intervalUpdate ψ) (-1, 1)

def intervalThreshold (ψ : ℝ) (bits : List Bool) : ℝ :=
  ((intervalBounds ψ bits).1 + (intervalBounds ψ bits).2) / 2

def intervalEstimate (ψ : ℝ) (bits : List Bool) : ℝ :=
  clip (intervalThreshold ψ bits)

/-- The actual T-step recurrence, with the query constructed from its public threshold. -/
def searchProgram {m k : ℕ} (query : ℝ → Query m k) (ψ : ℝ) :
    ℕ → (ℝ × ℝ) → BitProgram m k ℝ
  | 0, bounds => .done (clip ((bounds.1 + bounds.2) / 2))
  | n + 1, bounds =>
    .ask (query ((bounds.1 + bounds.2) / 2))
      (fun v => searchProgram query ψ n (intervalUpdate ψ bounds v))

def contrastSearch {m k : ℕ} [NeZero k]
    (α : ℝ) (T : ℕ) (g : Fin m) (h : Fin k) : BitProgram m k ℝ :=
  searchProgram (fun t => ⟨exposed g h t, h⟩) (2 * α) T (-1, 1)

def levelSearch {m k : ℕ} [NeZero k] (α κ : ℝ) (T : ℕ)
    (w : Table m k) (g r : Fin m) (h : Fin k) : BitProgram m k ℝ :=
  searchProgram (fun t => ⟨saturated w g r h t, h⟩)
    (2 * effectiveTolerance α κ) T (-1, 1)

/-- A rooted spanning tree described by its parent and a strictly decreasing rank.
These are tree data for Lemma 3.4, never a contract assumed of the algorithm. -/
structure ParentTree (m : ℕ) where
  root : Fin m
  parent : Fin m → Fin m
  rank : Fin m → ℕ
  root_parent : parent root = root
  root_rank : rank root = 0
  decreases : ∀ g, g ≠ root → rank (parent g) < rank g

def ParentTree.Adj {m : ℕ} (tree : ParentTree m) (g r : Fin m) : Prop :=
  g ≠ r ∧ (tree.parent g = r ∨ tree.parent r = g)

def ParentTree.diameterAtMostThree {m : ℕ} (tree : ParentTree m) : Prop :=
  ∀ g r, ∃ n : ℕ, n ≤ 3 ∧ ∃ path : Fin (n + 1) → Fin m,
    path 0 = g ∧ path (Fin.last n) = r ∧
      ∀ i : Fin n, tree.Adj (path i.castSucc) (path i.succ)

def pathSum {m : ℕ} (root : Fin m) (parent : Fin m → Fin m) (delta : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0, _ => 0
  | n + 1, g => if g = root then 0 else delta g + pathSum root parent delta n (parent g)

def ParentTree.levels {m : ℕ} (tree : ParentTree m) (delta : Fin m → ℝ) (g : Fin m) : ℝ :=
  pathSum tree.root tree.parent delta (tree.rank g) g

end MinimaxInterventions1429.Separable


