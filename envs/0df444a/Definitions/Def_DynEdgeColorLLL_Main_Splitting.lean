-- Prove2me | Definitions.Def_DynEdgeColorLLL_Main_Splitting
-- name    : DynEdgeColorLLL_Main_Splitting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:34.977369+00:00
-- url     : https://prove2.me/theorems/bf98560e-0d84-404e-bf6a-aa14bce613b2
-- title:
--   The splitting tree, the static splitting algorithms A and Ā, seed failures, clusters and completeness
-- statement:
--   **Parameters (§5.1).** For a degree bound $\Delta$ and a threshold $E$ (the paper's $\Delta_\epsilon$), set $U_0=\Delta$ and
--   $$U_{d+1}=\frac{U_d}{2}\Bigl(1+\frac{10}{\log^2U_d}\Bigr),\qquad q_d=\frac1{\log^2U_d},\qquad m_d=\lceil1/q_d\rceil .$$
--   $R$ is the least index with $U_R\le e^{E}$. Further, $L_d=\sum_{i=d}^{R-1}2m_i$, $\tau_d=U_dq_d^3$ and $\rho_d=2L_d+1$. Logarithms are base 2.
--
--   **Tree and choices (§5.2).** $T$ is the full binary tree of depth $R$. Its nodes are the direction strings of length at most $R$, and $\mathrm{dep}(a)$ is the length. Every edge $e$ and depth $d<R$ carry a direction $\mathrm{dir}_{e,d}\in\{LC,RC\}$ and a category $\mathrm{cat}_{e,d}\in[m_d]$. The routing path $\mathrm{path}_{e,0},\dots,\mathrm{path}_{e,R}$ follows the directions (Eq. (6)), and $\bar E_a=\{e\in E(G):\mathrm{path}_{e,\mathrm{dep}(a)}=a\}$ (Definition 2).
--
--   **Algorithms A and $\bar{\rm A}$.** At a node $a$ of depth $d<R$ with edge set $E_a$, the categories $i=1,\dots,m_d$ are processed in order. $H_{a,i}$ is the set of category-$i$ edges of $E_a$ that are not yet bad. Each active vertex $x$ is tested: the degree test fails if $x$ has more than $2U_d/m_d$ incident edges in $H_{a,i}$, and the discrepancy test fails if its incident $LC$ and $RC$ counts differ by more than $U_dq_d/m_d$. For each failure, its incident edges of $H_{a,i}$ become bad, and so do all edges of later categories incident to a neighbour, in $H_{a,i}$, of the failed vertex. The other edges of $H_{a,i}$ follow their directions. Then the bad edges are split by an edge bipartition with degree discrepancy at most two at every vertex.
--
--   Algorithm A tests every vertex. Algorithm $\bar{\rm A}$, given $F\subseteq V\times T$, tests only the active set. That set starts as $\bar V_{a,0}=V^\star_a\cup\{x:(x,a)\in F\}$, with $V^\star_{r_T}=\emptyset$, and grows by both endpoints of every edge entering the bad set. Both children receive the final active set $\bar V_a$.
--
--   **Seed failures, clusters, completeness (Definitions 3–5).** $(u,a)$ is a **seed failure** if $\deg_{\bar E_a}(u)>U_d$, or if $a$ is internal and some category of $\bar E_a$ fails one of the two tests at $u$. The **cluster** of $(w,b)$ consists of the pairs $(x,c)$ with $c$ a descendant of $b$ such that $\bar E_b$ contains a path from $w$ to $x$ of length at most $L_{\mathrm{dep}(b)}$ on which every vertex except $x$ has degree at most $U_{\mathrm{dep}(b)}$. $F$ is **complete** when four conditions hold:
--   1. every pair in $F$ is a seed failure;
--   2. every seed failure in the cluster of a pair of $F$ is in $F$;
--   3. $(w,b)\in F$, $b\ne r_T$ and $\deg_{\bar E_b}(w)>U_{\mathrm{dep}(b)}$ imply $(w,P(b))\in F$;
--   4. for a leaf $c$, $\deg_{\bar E_c}(x)>U_R$ implies $(x,P(c))\in F$.
--
--   **Formalization Note.** Directions are booleans (`false` = LC). The post-shattering bipartition is a parameter: any choice with discrepancy at most two at every vertex, which includes the paper's per-component Euler-tour choice. $R$ is an infimum over the naturals, attained in the regime $\Delta>e^{E}$ with $E$ large.
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §5.1 (end), printed p. 21 (PDF p. 23); §5.2 Algorithm A and Table 2, printed pp. 22–23 (PDF pp. 24–25); §6.1 Equation (6), Definitions 2–5, Algorithm Ā and Table 3, printed pp. 24–25 (PDF pp. 26–27); τ_d printed p. 34 (PDF p. 36); ρ_d printed p. 34 (PDF p. 36)

import Mathlib

namespace DynEdgeColorLLL.Main

/-! # The splitting tree, the static splitting algorithms A and Ā, seed failures, clusters and
completeness

Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §5.1 (end), printed p. 21
(PDF p. 23); §5.2, Algorithm A and Table 2, printed pp. 22–23 (PDF pp. 24–25); §6.1,
Definitions 2–5 and Algorithm Ā, printed pp. 24–25 (PDF pp. 26–27).

* **Parameters** (degree bound `Δ`, threshold `E` standing for `Δ_ε`): `U_0 = Δ`,
  `U_{d+1} = (U_d/2)(1 + 10/log² U_d)`, `q_d = 1/log² U_d`, `m_d = ⌈1/q_d⌉`, `R` the least index
  with `U_R ≤ exp(E)`, `L_d = ∑_{i=d}^{R-1} 2 m_i`, `τ_d = U_d q_d³`, `ρ_d = 2 L_d + 1`. Logarithms
  are base 2 (`Real.logb 2`), `exp` is the natural exponential.
* **Tree.** A node of the full binary tree `T` of depth `R` is a list of directions of length
  `≤ R` (`false` = LC, `true` = RC); the root is `[]`, `dep(a)` is the length, the parent is
  `dropLast`, and `b` is an ancestor of `a` (possibly `a` itself) when `b` is a prefix of `a`.
* **Random choices.** `dir e d` and `cat e d` are the direction and category of edge `e` at depth
  `d`; categories are `1, …, m_d`.
* **Algorithms.** `splitAt` is one call at a node of depth `d < R`: steps 2–4 (pre-shattering,
  categories processed in the order `1, …, m_d`, tests only on the current active set) and step 5
  (post-shattering). The post-shattering choice is a parameter `post a B ⊆ B` (the part sent to
  LC; `B \ post a B` goes to RC); `IsValidPost` asks degree discrepancy at most two at every
  vertex, which every per-component choice of the paper (an Euler tour after pairing odd-degree
  vertices) satisfies. Algorithm A of §5.2 tests every vertex: its active set is `univ` at every
  node. Algorithm Ā of §6.1 starts at node `a` from `V̄_{a,0} = V⋆_a ∪ {x : (x, a) ∈ F}` with
  `V⋆_{r_T} = ∅`, and passes `V̄_a` to both children. -/

section Parameters

/-- `U_d`: `U_0 = Δ`, `U_{d+1} = (U_d/2)(1 + 10/log₂² U_d)`. -/
noncomputable def U (Δ : ℕ) : ℕ → ℝ
  | 0 => Δ
  | d + 1 => U Δ d / 2 * (1 + 10 / Real.logb 2 (U Δ d) ^ 2)

/-- `q_d = 1/log₂² U_d`. -/
noncomputable def qd (Δ : ℕ) (d : ℕ) : ℝ := 1 / Real.logb 2 (U Δ d) ^ 2

/-- `m_d = ⌈1/q_d⌉`, the number of categories at depth `d`. -/
noncomputable def md (Δ : ℕ) (d : ℕ) : ℕ := ⌈1 / qd Δ d⌉₊

/-- `R`: the smallest index with `U_R ≤ exp(E)`. -/
noncomputable def depthR (Δ : ℕ) (E : ℝ) : ℕ := sInf {d : ℕ | U Δ d ≤ Real.exp E}

/-- `L_d = ∑_{i=d}^{R-1} 2 m_i` (`L_R = 0`). -/
noncomputable def Ld (Δ : ℕ) (E : ℝ) (d : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico d (depthR Δ E), 2 * md Δ i

/-- `τ_d = U_d q_d³`. -/
noncomputable def taud (Δ : ℕ) (d : ℕ) : ℝ := U Δ d * qd Δ d ^ 3

/-- `ρ_d = 2 L_d + 1`. -/
noncomputable def rhod (Δ : ℕ) (E : ℝ) (d : ℕ) : ℕ := 2 * Ld Δ E d + 1

end Parameters

section Tree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The random choices of the edges: `dir e d` (`false` = LC, `true` = RC) and `cat e d`. -/
structure Choices (V : Type*) where
  dir : Sym2 V → ℕ → Bool
  cat : Sym2 V → ℕ → ℕ

/-- The degree of `v` in the edge set `S`. -/
def edgeDeg (S : Finset (Sym2 V)) (v : V) : ℕ := (S.filter fun e => v ∈ e).card

/-- `path_{e,d}`: the node at depth `d` on the routing path of `e` (Equation (6)). -/
def routePath (c : Choices V) (e : Sym2 V) (d : ℕ) : List Bool :=
  List.ofFn fun j : Fin d => c.dir e j

open Classical in
/-- `Ē_a` (Definition 2): the edges of `G` whose routing path passes through `a`. -/
noncomputable def idealEdges (G : SimpleGraph V) (c : Choices V) (a : List Bool) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => routePath c e a.length = a

/-- Every edge of `G` has a category in `{1, …, m_d}` at every depth `d < R`. -/
def ValidCategories (Δ : ℕ) (E : ℝ) (G : SimpleGraph V) (c : Choices V) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ d < depthR Δ E, 1 ≤ c.cat e d ∧ c.cat e d ≤ md Δ d

/-- A post-shattering choice: `post a B ⊆ B` is sent to the left child, `B \ post a B` to the
right child, and at every vertex the two parts differ in degree by at most two. -/
def IsValidPost (post : List Bool → Finset (Sym2 V) → Finset (Sym2 V)) : Prop :=
  ∀ a B, post a B ⊆ B ∧ ∀ v : V,
    |(edgeDeg (post a B) v : ℤ) - (edgeDeg (B \ post a B) v : ℤ)| ≤ 2

end Tree

section Algorithms

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The state of the pre-shattering loop at a node: the bad set `E^bad_a` so far, the surviving
edges sent left and right so far, and the active set `V̄_{a,i}`. -/
structure LoopState (V : Type*) where
  bad : Finset (Sym2 V)
  left : Finset (Sym2 V)
  right : Finset (Sym2 V)
  active : Finset V

open Classical in
/-- Step 4 (Ā) / step 3 (A) for category `i` at a node of depth `d` with edge set `Ea`: the edges
`H_{a,i}` of category `i` not yet bad propose their directions; every active vertex is tested
(degree test: more than `2U_d/m_d` incident edges of `H_{a,i}`; discrepancy test: incident `LC`
and `RC` counts differing by more than `U_d q_d/m_d`); the edges of `H_{a,i}` incident to a failed
vertex become bad, and so do the edges of categories `j > i` incident to a neighbour, in
`H_{a,i}`, of a failed vertex; the endpoints of every edge entering the bad set are activated;
the other edges of `H_{a,i}` follow their directions. -/
noncomputable def categoryStep (Δ : ℕ) (c : Choices V) (d : ℕ) (Ea : Finset (Sym2 V)) (i : ℕ)
    (st : LoopState V) : LoopState V :=
  let Ud := U Δ d
  let m := (md Δ d : ℝ)
  let H := (Ea.filter fun e => c.cat e d = i) \ st.bad
  let nL := fun x : V => (H.filter fun e => x ∈ e ∧ c.dir e d = false).card
  let nR := fun x : V => (H.filter fun e => x ∈ e ∧ c.dir e d = true).card
  let fails := st.active.filter fun x =>
    2 * Ud / m < (edgeDeg H x : ℝ) ∨ Ud * qd Δ d / m < |(nL x : ℝ) - (nR x : ℝ)|
  let failedEdges := H.filter fun e => ∃ x ∈ fails, x ∈ e
  let nbrs := Finset.univ.filter fun y : V =>
    ∃ x ∈ fails, ∃ e ∈ H, x ∈ e ∧ y ∈ e ∧ y ≠ x
  let frozen := Ea.filter fun e => i < c.cat e d ∧ ∃ y ∈ nbrs, y ∈ e
  let newBad := failedEdges ∪ frozen
  let survivors := H \ failedEdges
  { bad := st.bad ∪ newBad
    left := st.left ∪ survivors.filter fun e => c.dir e d = false
    right := st.right ∪ survivors.filter fun e => c.dir e d = true
    active := st.active ∪ Finset.univ.filter fun x => ∃ e ∈ newBad, x ∈ e }

/-- One call at node `a` of depth `d = a.length < R` with edge set `Ea` and initial active set
`V̄_{a,0} = A0`: the categories `1, …, m_d` in order, then post-shattering. Returns
`(E_{LC(a)}, E_{RC(a)}, V̄_a)`. -/
noncomputable def splitAt (Δ : ℕ) (c : Choices V)
    (post : List Bool → Finset (Sym2 V) → Finset (Sym2 V)) (a : List Bool)
    (Ea : Finset (Sym2 V)) (A0 : Finset V) : Finset (Sym2 V) × Finset (Sym2 V) × Finset V :=
  let d := a.length
  let st := (List.range' 1 (md Δ d)).foldl (fun st i => categoryStep Δ c d Ea i st)
    ⟨∅, ∅, ∅, A0⟩
  (st.left ∪ post a st.bad, st.right ∪ (st.bad \ post a st.bad), st.active)

/-- Descend from node `pre` (with edge set and active set `st`) along the directions `rest`,
calling `splitAt` at every node passed; `act0 a V⋆` is the initial active set at node `a`. -/
noncomputable def descend (Δ : ℕ) (c : Choices V)
    (post : List Bool → Finset (Sym2 V) → Finset (Sym2 V))
    (act0 : List Bool → Finset V → Finset V) :
    List Bool → List Bool → Finset (Sym2 V) × Finset V → Finset (Sym2 V) × Finset V
  | _, [], st => st
  | pre, b :: rest, st =>
      let r := splitAt Δ c post pre st.1 (act0 pre st.2)
      descend Δ c post act0 (pre ++ [b]) rest (if b then r.2.1 else r.1, r.2.2)

open Classical in
/-- Algorithm A of §5.2 (every vertex is tested): `(E_a, ·)` at node `a`, from `E_{r_T} = E(G)`. -/
noncomputable def runA (Δ : ℕ) (G : SimpleGraph V) (c : Choices V)
    (post : List Bool → Finset (Sym2 V) → Finset (Sym2 V)) (a : List Bool) : Finset (Sym2 V) :=
  (descend Δ c post (fun _ _ => Finset.univ) [] a (G.edgeFinset, Finset.univ)).1

open Classical in
/-- Algorithm Ā of §6.1 with seed-failure set `F`: `(E_a, V⋆_a)` at node `a`, from
`E_{r_T} = E(G)` and `V⋆_{r_T} = ∅`, with `V̄_{a,0} = V⋆_a ∪ {x : (x, a) ∈ F}`. -/
noncomputable def runAbar (Δ : ℕ) (G : SimpleGraph V) (c : Choices V)
    (post : List Bool → Finset (Sym2 V) → Finset (Sym2 V)) (F : Set (V × List Bool))
    (a : List Bool) : Finset (Sym2 V) × Finset V :=
  descend Δ c post (fun b Vs => Vs ∪ Finset.univ.filter fun x => (x, b) ∈ F) [] a
    (G.edgeFinset, ∅)

end Algorithms

section Failures

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The number of category-`i` edges of `S` at depth `d` incident to `u` with direction `b`. -/
noncomputable def catDirDeg (c : Choices V) (S : Finset (Sym2 V)) (d i : ℕ) (b : Bool) (u : V) :
    ℕ :=
  (S.filter fun e => u ∈ e ∧ c.cat e d = i ∧ c.dir e d = b).card

/-- Definition 3 (seed failure): `a` is a node of `T`, and `deg_{Ē_a}(u) > U_d`, or `a` is
internal and some category `i ∈ [m_d]` has, in `Ē_a`, more than `2U_d/m_d` category-`i` edges at
`u`, or `LC` and `RC` counts of category-`i` edges at `u` differing by more than `U_d q_d/m_d`. -/
def IsSeedFailure (Δ : ℕ) (E : ℝ) (G : SimpleGraph V) (c : Choices V) (p : V × List Bool) :
    Prop :=
  let u := p.1
  let a := p.2
  let d := a.length
  let Ea := idealEdges G c a
  d ≤ depthR Δ E ∧
    (U Δ d < edgeDeg Ea u ∨
      (d < depthR Δ E ∧ ∃ i ∈ Finset.Icc 1 (md Δ d),
        2 * U Δ d / md Δ d < ((catDirDeg c Ea d i false u + catDirDeg c Ea d i true u : ℕ) : ℝ) ∨
        U Δ d * qd Δ d / md Δ d <
          |((catDirDeg c Ea d i false u : ℕ) : ℝ) - ((catDirDeg c Ea d i true u : ℕ) : ℝ)|))

/-- Definition 4 (cluster): `(x, c')` is in the cluster of `(w, b)` when `c'` is a descendant of
`b` in `T` and `Ē_b` contains a path from `w` to `x` of length at most `L_{dep(b)}` on which every
vertex except the terminal vertex `x` has degree at most `U_{dep(b)}` in `Ē_b`. -/
def InCluster (Δ : ℕ) (E : ℝ) (G : SimpleGraph V) (c : Choices V) (p q : V × List Bool) :
    Prop :=
  let Eb := idealEdges G c p.2
  p.2 <+: q.2 ∧ q.2.length ≤ depthR Δ E ∧
    ∃ P : (SimpleGraph.fromEdgeSet (Eb : Set (Sym2 V))).Walk p.1 q.1,
      P.IsPath ∧ P.length ≤ Ld Δ E p.2.length ∧
        ∀ y ∈ P.support.dropLast, (edgeDeg Eb y : ℝ) ≤ U Δ p.2.length

/-- Definition 5 (completeness) of `F ⊆ V × T` for the instance `(G, c)`. -/
def IsComplete (Δ : ℕ) (E : ℝ) (G : SimpleGraph V) (c : Choices V) (F : Set (V × List Bool)) :
    Prop :=
  -- (I)
  (∀ p ∈ F, IsSeedFailure Δ E G c p) ∧
  -- (II)
  (∀ p ∈ F, ∀ q, InCluster Δ E G c p q → IsSeedFailure Δ E G c q → q ∈ F) ∧
  -- (III)
  (∀ p ∈ F, p.2 ≠ [] → U Δ p.2.length < edgeDeg (idealEdges G c p.2) p.1 →
      (p.1, p.2.dropLast) ∈ F) ∧
  -- (IV)
  (∀ (x : V) (a : List Bool), a.length = depthR Δ E →
      U Δ (depthR Δ E) < edgeDeg (idealEdges G c a) x → (x, a.dropLast) ∈ F)

end Failures

end DynEdgeColorLLL.Main


