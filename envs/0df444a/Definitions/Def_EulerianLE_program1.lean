-- Prove2me | Definitions.Def_EulerianLE_program1
-- name    : EulerianLE_program1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:50.969264+00:00
-- url     : https://prove2.me/theorems/482bc2d3-a06b-4daf-bc37-973e6c610ad9
-- title:
--   Program 1 (EulerianLeaderElection), the rounds $L_r$ and their compositions
-- statement:
--   **Program 1**, run by a node with identifier $\mathrm{ID}_u$ and degree $\deg(u)$: Init; repeat $\mathrm{ID}_u$ times `SynchronizedCount()`; if `CheckIfLocalLeader()` succeeds and then `CheckIfGlobalLeader()` succeeds, set $\mathit{result}\leftarrow$ Leader and terminate; then repeat: if `SynchronizedRelay()` detects termination, set $\mathit{result}\leftarrow$ Non-Leader and terminate. The output is Leader or Non-Leader.
--
--   **Round $r$** (Definition 3) is the algorithm $L_r$ in which every node $u$ executes the chunk $P^r_{\mathrm{ID}_u}$ on its input $(\mathit{result},\pi)$. The module also defines the composition $(L_0,\dots,L_s)$ of the rounds $0,\dots,s$, built as $((L_0,\dots,L_{s-1}),L_s)$, the dummy input $(\emptyset,\emptyset)$ of round $0$, and the variables of a node in a state of Program 1 or of the composition.
--
--   Program 1 depends only on the node's identifier and degree, with no bound on the number of nodes, the number of edges or the identifiers; this is the uniformity in Theorem 1.
--
--   **Formalization Note** Program 1 is the concatenation of the four chunk blocks of `chunkCode`, so it and the composition of rounds run the same text chunk by chunk.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §4.1, p.19 (PDF p.21), Program 1; §5.1, pp.23–24 (PDF pp.25–26), Definition 3; §3.1, p.10 (iterated compositions)

import Mathlib
import Definitions.Def_EulerianLE_chunkCode
import Definitions.Def_EulerianLE_IsComposable

namespace EulerianLE

/-- The output of the leader election: `Leader` or `Non-Leader`. -/
inductive Outcome : Type
  | leader
  | nonLeader
  deriving DecidableEq, Repr

/-- `repeat n times b`. -/
def repB {deg : ℕ} : ℕ → Blk deg → Blk deg
  | 0, _ => fun k => k
  | n + 1, b => fun k => b (repB n b k)

/-- Program 1, `EulerianLeaderElection()` (Frei, Gelles, Ghazy, Nolin, STOC 2027 submission
(manuscript sha256 90954a93…), §4.1, p.19), for a node with identifier `id` and degree `deg`: Init;
`repeat ID_u times SynchronizedCount()`; if `CheckIfLocalLeader()` succeeds and then
`CheckIfGlobalLeader()` succeeds, `result ← Leader` and `terminate`; then `repeat`: if
`SynchronizedRelay()` detects termination, `result ← Non-Leader` and `terminate`. The output is
`result`.

**Formalization Note.** `program1 id deg` is a function of the node's identifier and degree only: it
has no access to `n`, `|E|` or a bound on the identifiers, which is the uniformity of Theorem 1. It is
deterministic and computable. It is the concatenation of the chunk blocks `initB`, `countingChunkB`,
`checkChunkB`, `relayChunkB` of `chunkCode`; ports are 0-based and the paper's "arbitrary" choices are
refined to the smallest index (paper.md decision 6). -/
def program1 (id deg : ℕ) : NodeProg deg Outcome :=
  (initB <| repB id countingChunkB <| checkChunkB <|
      Code.loop (fun _ => true) (relayChunkB .done) .done).prog
    (Store.fresh (.none, [])) fun c => if c.store.result = .leader then .leader else .nonLeader

variable (G : Network)

/-- Program 1 as an algorithm with no input: node `u` runs `program1 (ids u) (deg u)`. -/
def program1Alg (ids : G.V → ℕ) : Algorithm G.V G.deg (fun _ => Unit) (fun _ => Outcome) :=
  fun u _ => program1 (ids u) (G.deg u)

/-- The per-node type `(result, π)` of configurations. -/
abbrev CIO : G.V → Type := fun u => ChunkIO (G.deg u)

/-- Definition 3 (Rounds), p.24: round `r` is the algorithm `L_r` in which every node `u` executes the
chunk `P^r_{ID_u}` on its input `(result, π)`. -/
def roundAlg (ids : G.V → ℕ) (r : ℕ) : Algorithm G.V G.deg (CIO G) (CIO G) :=
  fun u x => chunkProg (G.deg u) (chunkKind r (ids u)) x

/-- The program of one node in the composition `(L_0, …, L_s)`, built as `((L_0, …, L_{s−1}), L_s)`
(§3.1, p.10). -/
def roundsProg (id deg : ℕ) : ℕ → ChunkIO deg → NodeProg deg (ChunkIO deg)
  | 0, x => chunkProg deg (chunkKind 0 id) x
  | s + 1, x => (roundsProg id deg s x).comp fun o => chunkProg deg (chunkKind (s + 1) id) o

/-- The composition `(L_0, …, L_s)` of the rounds `0, …, s`. -/
def roundsAlg (ids : G.V → ℕ) (s : ℕ) : Algorithm G.V G.deg (CIO G) (CIO G) :=
  fun u x => roundsProg (ids u) (G.deg u) s x

/-- The dummy input `(∅, ∅)` of round 0 ("Init takes the dummy input (∅, ∅)", p.23). -/
def dummyInput : ∀ u, CIO G u := fun _ => (.none, [])

/-- The variables of a node in a state of `(L_0, …, L_s)`: those of the chunk it is running. -/
def roundsStore (id deg : ℕ) : (s : ℕ) → (x : ChunkIO deg) → (roundsProg id deg s x).State → Store deg
  | 0, _, st => (st : RunState deg (Store deg)).ctx.store
  | s + 1, x, .inl st => roundsStore id deg s x st
  | _ + 1, _, .inr ⟨_, st⟩ => (st : RunState deg (Store deg)).ctx.store

/-- The variables of a node in a state of Program 1. -/
def program1Store (id deg : ℕ) (st : (program1 id deg).State) : Store deg :=
  (st : RunState deg (Store deg)).ctx.store

end EulerianLE


