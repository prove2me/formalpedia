-- Prove2me | Definitions.Def_CollectiveTreeExploration_Async_Exploration
-- name    : CollectiveTreeExploration_Async_Exploration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:02:52.264921+00:00
-- url     : https://prove2.me/theorems/6a9dba20-d6d4-40d6-89d3-705e756fe68e
-- title:
--   Asynchronous collective tree exploration, online algorithms, moves and normalized regret
-- statement:
--   This file fixes the model of **asynchronous collective tree exploration** (ACTE).
--
--   **Trees.** A finite rooted tree is given with port numbers, in Ulam–Harris form: a vertex is the list $(i_1,\dots,i_j)$ of child indices on the path from the root (the root is the empty list), and the children of a vertex $a$ are $a0, a1, \dots, a(\deg a - 1)$. Every finite rooted tree admits such a description; the numbering of the children is part of the (adversarial) input. The tree has $n$ vertices and depth $D$, the largest number of edges between the root and a vertex.
--
--   **Exploration.** $k$ agents start at the root. At step $s = 0,1,2,\dots$ an adversary activates an agent $\sigma(s)\in\{1,\dots,k\}$; the **activation sequence** $\sigma$ is arbitrary (no fairness is assumed). The algorithm then chooses an edge adjacent to that agent's position for it to traverse: to the parent, or to the child with a given port number. A move to the parent of the root, or to a non-existent child, is illegal.
--
--   **Information.** When an agent arrives at a vertex, the team learns the number of children of that vertex (the edges adjacent to it). A **deterministic online algorithm** is a function that, from the number of children of the root, the shared history of all previous steps (activated agent, move, number of children of the vertex reached) and the identity of the activated agent, returns that agent's move. It sees nothing else of the tree, and in particular nothing of unexplored subtrees or of future activations.
--
--   **Legality.** A policy is legal when it chooses an adjacent edge at every reachable unfinished history, for every activated agent. This independent predicate assumes neither termination nor a performance bound.
--
--   **Moves and regret.** The algorithm has explored the tree after $N$ moves under $\sigma$ when the first $N$ moves are legal and every vertex has been visited. $M(A,T,\sigma)\in\mathbb N\cup\{\infty\}$ is the least such $N$ (infinite if exploration is never completed, in particular after an illegal move before completion). The **normalized regret** of $A$ (eq. (1)) is
--   $$r(A)=\inf\{\,r\ge0:\ M(A,T,\sigma)\le 2n+r\,kD\ \text{for every tree }T\text{ and every activation sequence }\sigma\,\},$$
--   with $r(A)=\infty$ if no such $r$ exists.
--
--   **Formalization Note** Vertices are lists of natural numbers; the history entries are triples (agent, move, revealed number of children). The normalized regret takes values in $[0,\infty]$.
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; §1, p.1, eq. (1) and the model description; Theorem 1.1, p.2; §2.1, p.5

import Mathlib

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

noncomputable section

open Classical

/-! # Asynchronous collective tree exploration (ACTE) (§1, pp.1–2; §2, p.5)

`k` agents start at the root of an unknown finite rooted (unweighted) tree. At each step an
adversary activates one agent, and the algorithm chooses an edge adjacent to that agent's
position for it to traverse. The team learns the edges adjacent to a vertex when an agent first
stands on it. Performance: the number of moves until every vertex has been visited.

**Trees with port numbers.** A finite rooted tree is given in Ulam–Harris form: a vertex is the
list of child indices on the path from the root (the root is `[]`), and the children of a vertex
`a` are `a ++ [0], …, a ++ [deg a - 1]`. Every finite rooted tree has such a representation; the
child numbering is part of the (adversarial) input. -/

/-- A finite rooted tree in Ulam–Harris form: a finite set of addresses containing the root `[]`,
closed under taking parents, and whose children of each vertex are numbered `0, 1, …`. -/
structure ExpTree where
  nodes : Finset (List ℕ)
  root_mem : [] ∈ nodes
  parent_mem : ∀ a : List ℕ, ∀ i : ℕ, a ++ [i] ∈ nodes → a ∈ nodes
  ports_consecutive : ∀ a : List ℕ, ∀ i : ℕ, a ++ [i + 1] ∈ nodes → a ++ [i] ∈ nodes

namespace ExpTree

variable (T : ExpTree)

/-- `n`, the number of vertices. -/
def size : ℕ := T.nodes.card

/-- `D`, the depth: the largest distance from the root to a vertex (the root has depth `0`). -/
def depth : ℕ := T.nodes.sup List.length

/-- The number of children of the vertex `a` (the edges revealed when `a` is first visited,
besides the edge to its parent). -/
def deg (a : List ℕ) : ℕ := ((Finset.range (T.nodes.card + 1)).filter (fun i => a ++ [i] ∈ T.nodes)).card

end ExpTree

/-- A move of the activated agent: `none` = go to the parent, `some i` = go to child number `i`. -/
abbrev Move := Option ℕ

/-- One entry of the shared history: the activated agent, its move, and the number of children of
the vertex it arrived at (the information revealed by the move). -/
abbrev HistEntry (k : ℕ) := Fin k × Move × ℕ

/-- A deterministic online ACTE algorithm for `k` agents: given the number of children of the root
(revealed at time `0`), the history of all previous steps, and the activated agent, it chooses the
activated agent's move. It sees nothing else of the tree. -/
def ExplorationAlgorithm (k : ℕ) := ℕ → List (HistEntry k) → Fin k → Move

/-- The state of an exploration: agents' positions, the history so far, the visited vertices. -/
structure ExpState (k : ℕ) where
  pos : Fin k → List ℕ
  hist : List (HistEntry k)
  visited : Finset (List ℕ)

/-- Initial state: all agents at the root; only the root is visited. -/
def ExpState.init (k : ℕ) : ExpState k := ⟨fun _ => [], [], {[]}⟩

/-- One step: the activated agent `i` makes the move chosen by `A`. Returns `none` if the move is
illegal (to the parent of the root, or to a child that does not exist). -/
def expStep {k : ℕ} (T : ExpTree) (A : ExplorationAlgorithm k) (st : ExpState k) (i : Fin k) :
    Option (ExpState k) :=
  let a := st.pos i
  let mv := A (T.deg []) st.hist i
  let target : Option (List ℕ) :=
    match mv with
    | none => if a = [] then none else some a.dropLast
    | some j => if a ++ [j] ∈ T.nodes then some (a ++ [j]) else none
  target.map fun b =>
    { pos := Function.update st.pos i b
      hist := st.hist ++ [(i, mv, T.deg b)]
      visited := insert b st.visited }

/-- The state after the first `N` activations of the sequence `σ` (`none` if an illegal move
occurred). -/
def expRun {k : ℕ} (T : ExpTree) (A : ExplorationAlgorithm k) (σ : ℕ → Fin k) :
    ℕ → Option (ExpState k)
  | 0 => some (ExpState.init k)
  | N + 1 => (expRun T A σ N).bind fun st => expStep T A st (σ N)

/-- `A` has explored `T` after `N` moves under the activation sequence `σ`: the first `N` moves are
legal and every vertex has been visited. -/
def ExploredBy {k : ℕ} (A : ExplorationAlgorithm k) (T : ExpTree) (σ : ℕ → Fin k) (N : ℕ) :
    Prop :=
  ∃ st, expRun T A σ N = some st ∧ T.nodes ⊆ st.visited

/-- Legality is independent of completion or a cost guarantee: at every reachable
unfinished history and for every activated agent the policy chooses an adjacent edge.
There is no condition on moves after the tree has already been explored. -/
def LegalExploration {k : ℕ} (A : ExplorationAlgorithm k) : Prop :=
  ∀ (T : ExpTree) (σ : ℕ → Fin k) (N : ℕ) (st : ExpState k),
    expRun T A σ N = some st → ¬ T.nodes ⊆ st.visited →
      ∀ i : Fin k, expStep T A st i ≠ none

/-- `M(A, T, σ)`, the number of moves `A` needs to explore `T` under `σ` (`⊤` if it never
completes the exploration). -/
def movesToExplore {k : ℕ} (A : ExplorationAlgorithm k) (T : ExpTree) (σ : ℕ → Fin k) : ℕ∞ :=
  sInf {N : ℕ∞ | ∃ m : ℕ, N = m ∧ ExploredBy A T σ m}

/-- The normalized regret of `A` (eq. (1), p.1): the least `r ≥ 0` such that
`M(A, T, σ) ≤ 2n + r · k · D` for every tree `T` (with `n` vertices and depth `D`) and every
activation sequence `σ`; `⊤` if there is none. -/
def normalizedRegret {k : ℕ} (A : ExplorationAlgorithm k) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∀ (T : ExpTree) (σ : ℕ → Fin k),
    ((movesToExplore A T σ : ℕ∞) : ℝ≥0∞) ≤ 2 * (T.size : ℝ≥0∞) + r * (k : ℝ≥0∞) * (T.depth : ℝ≥0∞)}

end

end CollectiveTreeExploration.Async


