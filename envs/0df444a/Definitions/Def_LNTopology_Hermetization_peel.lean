-- Prove2me | Definitions.Def_LNTopology_Hermetization_peel
-- name    : LNTopology_Hermetization_peel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:27:07.622428+00:00
-- url     : https://prove2.me/theorems/0340ffb6-93da-4959-b122-9034b9a8e210
-- title:
--   Peeling algorithm of Lemma B.3
-- statement:
--   The **peeling algorithm** takes adjacency lists $\mathrm{adj}$ of a graph on $n$ vertices and a degree test $\mathrm{bad}$ (in Lemma B.3, "degree $<\tau$" for $\tau=g_+^{-1}(2\,\mathrm{disc}(G))$), and repeatedly deletes every remaining vertex whose degree among the remaining vertices is bad, until no such vertex is left. It returns the set of vertices never deleted. It is implemented with a queue:
--
--   1. compute $\deg(v)=|\mathrm{adj}(v)|$ for every $v$;
--   2. put every $v$ with $\mathrm{bad}(\deg v)$ in the queue and mark it queued;
--   3. in each of $n+1$ rounds, take a vertex $v$ from the queue (if any) and mark it removed; for every neighbour $w$ of $v$ not yet removed, decrease $\deg(w)$ by one, and if $w$ is not queued and $\mathrm{bad}(\deg w)$ holds, put $w$ in the queue and mark it queued;
--   4. return the vertices not removed.
--
--   Each vertex enters the queue at most once, so $n+1$ rounds empty it, every list is scanned at most twice, and the algorithm makes $O(n+\sum_v|\mathrm{adj}(v)|)=O(V+E)$ ticks.
--
--   **Formalization Note** The test is a parameter. The paper's proof deletes "all the vertices of degree $\le g_+^{-1}(2\,\mathrm{disc}(G))$" while claiming the output has minimum degree $\ge g_+^{-1}(2\,\mathrm{disc}(G))$; that comparison misses graphs whose minimum degree equals the threshold ($K_4$ with threshold $3$). The algorithm here deletes exactly the vertices whose degree fails the test, and Lemma B.3's claim is its instance with the test "degree $<\tau$".
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemma B.3 and its proof, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_badAt

namespace LNTopology.Hermetization

/-- **The peeling algorithm of Lemma B.3.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemma B.3 and its proof, p. 12: "The algorithm is as follows: at each step, delete all
the vertices of degree ≤ g₊⁻¹(2disc(G)), until there are no more vertices to remove".

Input: adjacency lists `adj` of a graph on `Fin n` and a degree test `bad`. The algorithm
deletes, until stable, every remaining vertex whose degree among the remaining vertices is bad,
and returns the set of vertices never deleted. It runs with a queue:
1. compute `deg v = |adj v|` for every `v`;
2. enqueue (and mark queued) every `v` with `bad (deg v)`;
3. in each of `n + 1` rounds, pop a vertex `v` from the queue (if any), mark it removed, and for
   every neighbour `w` of `v` not yet removed decrement `deg w`; if `w` is not yet queued and
   `bad (deg w)` holds, enqueue `w` and mark it queued;
4. return the vertices not marked removed.

Each vertex is queued at most once, so `n + 1` rounds empty the queue, every vertex's list is
scanned at most twice, and the running time is `O(n + Σ_v |adj v|)` = O(V + E) ticks.

**Formalization Note.** Generalization G3 and encoding E1: the test `bad` is a parameter. The
printed proof deletes degrees `≤ τ` (with `τ = g₊⁻¹(2disc(G))`) but claims `δ(H) ≥ τ`, which
misses graphs with `δ(H) = τ` (`K₄` with `τ = 3`); Lemma B.3's claim is the instance
`bad d := (d : ℝ) < τ`, and Theorem 3.8's witness uses `bad d := d = 0 ∨ g₊(d) ≤ 2disc(G)`.
Ticks follow the real-RAM discipline of `tick`: one per loop iteration and one per test. The
`deg w - 1` is natural-number subtraction; on well-formed lists `deg w ≥ 1` there, because `v`
is a not-yet-discounted neighbour of `w`. -/
def peel {n : ℕ} (adj : Fin n → List (Fin n)) (bad : ℕ → Prop) [DecidablePred bad] :
    StateM ℕ (Finset (Fin n)) := do
  -- 1. degrees
  let mut deg : Fin n → ℕ := fun _ => 0
  for v in List.finRange n do
    tick 1
    for _w in adj v do
      tick 1
      deg := Function.update deg v (deg v + 1)
  -- 2. initial queue
  let mut queued : Fin n → Bool := fun _ => false
  let mut queue : List (Fin n) := []
  for v in List.finRange n do
    tick 1
    let b ← badAt bad (deg v)
    if b then
      queue := v :: queue
      queued := Function.update queued v true
  -- 3. peeling rounds
  let mut removed : Fin n → Bool := fun _ => false
  for _round in List.range (n + 1) do
    tick 1
    match queue with
    | [] => pure ()
    | v :: rest =>
      queue := rest
      removed := Function.update removed v true
      for w in adj v do
        tick 1
        if !(removed w) then
          deg := Function.update deg w (deg w - 1)
          if !(queued w) then
            let b ← badAt bad (deg w)
            if b then
              queue := w :: queue
              queued := Function.update queued w true
  -- 4. the vertices never removed
  pure (Finset.univ.filter fun v => removed v = false)

end LNTopology.Hermetization


