-- Prove2me | Definitions.Def_CollectiveTreeExploration_Async_Supplement_Synchronous
-- name    : CollectiveTreeExploration_Async_Supplement_Synchronous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:31.488242+00:00
-- url     : https://prove2.me/theorems/60ad9586-7887-4269-bcd4-04cce921c159
-- title:
--   Synchronous collective tree exploration — round policies, completion time in rounds, and the offline optimum
-- statement:
--   This file fixes the model of **synchronous collective tree exploration** (Fraigniaud–Gąsieniec–Kowalski–Pelc), on top of the trees and moves of the published asynchronous model.
--
--   **Trees and moves.** A finite rooted tree $T$ is given with port numbers (Ulam–Harris addresses; the root is the empty address), exactly as in the asynchronous model: $n=|T|$ is its number of vertices and $D$ its depth. A move is either "go to the parent" or "go to child number $i$".
--
--   **Rounds.** All $k$ agents start at the root. Time is measured in rounds, and in every round **each** agent traverses one edge adjacent to its current position. Communication is unrestricted, so a deterministic algorithm is one centralized rule.
--
--   1. A **round record** consists of the move of every agent in that round and the number of children of the vertex each agent reached.
--   2. A **synchronous algorithm** $A$ for $k$ agents maps the number of children of the root and the list of records of all completed rounds to a move for each agent $i\in\{1,\dots,k\}$. It sees nothing else of the tree. All moves of a round are chosen from the information available at the beginning of the round; the numbers of children of the reached vertices become known only at the end of the round.
--   3. The **run** of $A$ on $T$ applies the rounds one after another; it stops (is undefined) as soon as some agent is told to make a move that does not exist (to the parent of the root, or to a missing child). The visited set grows by the positions reached.
--   4. $A$ is **legal** if, in every reachable state in which some vertex is still unvisited, every agent's chosen move exists. Nothing is required after the exploration has finished, and legality says nothing about termination or cost.
--   5. The **completion time** $R(A,T)\in\mathbb N\cup\{\infty\}$ is the least number of rounds after which all rounds so far were legal and every vertex of $T$ has been visited; it is $\infty$ if this never happens. On the one-vertex tree it is $0$. Agents need not return to the root.
--
--   **Offline optimum.** $T$ is **explorable offline in $m$ rounds** by $k$ agents if there are walks $p_t(i)$ (position of agent $i$ after $t$ rounds) that start at the root, traverse an edge of $T$ in each of the first $m$ rounds, and together visit every vertex of $T$ by round $m$. Then
--   $$\mathrm{OPT}_k(T)=\min\{m : T \text{ is explorable offline in } m \text{ rounds by } k \text{ agents}\}\in\mathbb N\cup\{\infty\},$$
--   the least number of rounds a team that knows the tree needs to go through all its edges; it is $0$ on the one-vertex tree and finite whenever $k\ge1$.
--
--   These objects state Theorem 1.2, the synchronous consequence of the paper's main asynchronous theorem; an algorithm is **$c$-competitive** when $R(A,T)\le c\cdot\mathrm{OPT}_k(T)$ for every tree $T$.
--
--   **Formalization Note** The completion time and the offline optimum are infima in $\mathbb N_\infty$ (`ℕ∞`), so an empty set gives $\infty$, never $0$. As in the asynchronous model every agent must move in every round (no idle step), both online and offline; offline this does not change the optimum, because an idle agent can instead walk back and forth along an edge.
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_Exploration

namespace CollectiveTreeExploration.Async.Supplement

open CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

noncomputable section

open Classical

/-! # Synchronous collective tree exploration (§1, pp.1–3)

`k` agents start at the root of an unknown finite rooted tree (the published `ExpTree`, with its
port numbering). Time is measured in rounds: in every round **each** of the `k` agents traverses
one edge adjacent to its current position. Communication is unrestricted, so a deterministic
algorithm is a single centralized rule that chooses the whole vector of `k` moves of a round from
the shared history. The moves of a round are chosen simultaneously, from the information available
at the beginning of the round; the number of children of each vertex reached in the round is
revealed only at the end of the round.

The offline optimum `OPT_k(T)` is the least number of rounds in which `k` agents that know the
tree `T` can walk from the root and visit every vertex. -/

/-- The record of one synchronous round: the move of every agent, and the number of children of
the vertex each agent arrived at (the information revealed by the round). -/
abbrev RoundRecord (k : ℕ) := (Fin k → Move) × (Fin k → ℕ)

/-- A deterministic online synchronous exploration algorithm for `k` agents with unrestricted
communication: from the number of children of the root (revealed at time `0`) and the records of
all completed rounds, it chooses the move of every agent for the next round. It sees nothing else
of the tree. -/
def SyncAlgorithm (k : ℕ) := ℕ → List (RoundRecord k) → Fin k → Move

/-- The state of a synchronous exploration: positions, history of completed rounds, visited
vertices. -/
structure SyncState (k : ℕ) where
  pos : Fin k → List ℕ
  hist : List (RoundRecord k)
  visited : Finset (List ℕ)

/-- Initial state: all agents at the root; only the root is visited. -/
def SyncState.init (k : ℕ) : SyncState k := ⟨fun _ => [], [], {[]}⟩

/-- The vertex reached from `a` by the move `mv` in `T`, or `none` if the move is illegal (to the
parent of the root, or to a child that does not exist). -/
def moveTarget (T : ExpTree) (a : List ℕ) (mv : Move) : Option (List ℕ) :=
  match mv with
  | none => if a = [] then none else some a.dropLast
  | some j => if a ++ [j] ∈ T.nodes then some (a ++ [j]) else none

/-- One synchronous round: all agents simultaneously make the moves chosen by `A` from the history
of the previous rounds; afterwards the numbers of children of the reached vertices are appended to
the history. Returns `none` if some agent's move is illegal. -/
def syncStep {k : ℕ} (T : ExpTree) (A : SyncAlgorithm k) (st : SyncState k) :
    Option (SyncState k) :=
  let mv : Fin k → Move := A (T.deg []) st.hist
  let tgt : Fin k → Option (List ℕ) := fun i => moveTarget T (st.pos i) (mv i)
  if ∀ i, (tgt i).isSome then
    let newPos : Fin k → List ℕ := fun i => (tgt i).getD []
    some
      { pos := newPos
        hist := st.hist ++ [(mv, fun i => T.deg (newPos i))]
        visited := st.visited ∪ Finset.univ.image newPos }
  else none

/-- The state after the first `R` rounds (`none` if an illegal move occurred). -/
def syncRun {k : ℕ} (T : ExpTree) (A : SyncAlgorithm k) : ℕ → Option (SyncState k)
  | 0 => some (SyncState.init k)
  | R + 1 => (syncRun T A R).bind fun st => syncStep T A st

/-- `A` has explored `T` after `R` rounds: the first `R` rounds are legal and every vertex has been
visited. -/
def SyncExploredBy {k : ℕ} (A : SyncAlgorithm k) (T : ExpTree) (R : ℕ) : Prop :=
  ∃ st, syncRun T A R = some st ∧ T.nodes ⊆ st.visited

/-- Legality, independent of completion or of any bound: in every reachable unfinished state the
algorithm makes every agent traverse an existing adjacent edge. Nothing is required once the tree
has been explored. -/
def LegalSyncExploration {k : ℕ} (A : SyncAlgorithm k) : Prop :=
  ∀ (T : ExpTree) (R : ℕ) (st : SyncState k),
    syncRun T A R = some st → ¬ T.nodes ⊆ st.visited → syncStep T A st ≠ none

/-- The synchronous completion time of `A` on `T`: the least number of rounds after which `T` has
been explored (`⊤` if this never happens). -/
def roundsToExplore {k : ℕ} (A : SyncAlgorithm k) (T : ExpTree) : ℕ∞ :=
  sInf {N : ℕ∞ | ∃ m : ℕ, N = m ∧ SyncExploredBy A T m}

/-- `b` is adjacent to `a` in `T`: `b` is a vertex of `T` that is a child or the parent of `a`. -/
def TreeAdj (T : ExpTree) (a b : List ℕ) : Prop :=
  b ∈ T.nodes ∧ ((∃ i : ℕ, b = a ++ [i]) ∨ (a ≠ [] ∧ b = a.dropLast))

/-- Offline exploration in `m` rounds: `k` agents knowing `T` follow walks `p t i` (position of
agent `i` after `t` rounds) that start at the root, traverse an edge of `T` in every one of the
first `m` rounds, and together visit every vertex of `T` within these `m` rounds. -/
def OfflineExplores (T : ExpTree) (k : ℕ) (m : ℕ) : Prop :=
  ∃ p : ℕ → Fin k → List ℕ, (∀ i, p 0 i = []) ∧
    (∀ t < m, ∀ i, TreeAdj T (p t i) (p (t + 1) i)) ∧
    ∀ v ∈ T.nodes, ∃ t ≤ m, ∃ i, p t i = v

/-- `OPT_k(T)`: the least number of synchronous rounds in which `k` agents with full knowledge of
`T` can visit every vertex (`⊤` if impossible, which happens only for `k = 0` and a tree with more
than one vertex). -/
def offlineOpt (T : ExpTree) (k : ℕ) : ℕ∞ :=
  sInf {N : ℕ∞ | ∃ m : ℕ, N = m ∧ OfflineExplores T k m}

end

end CollectiveTreeExploration.Async.Supplement


