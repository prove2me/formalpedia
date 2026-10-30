-- Prove2me | Definitions.Def_Timetabling_StableHalf_propStep
-- name    : Timetabling_StableHalf_propStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:28:12.353971+00:00
-- url     : https://prove2.me/theorems/f106b0b1-060c-431f-b83a-d53441e4197b
-- title:
--   One scan step of the propagation of implications
-- statement:
--   The graph $G$ on the nodes $V = \{x_j, \bar x_j\}$ is accessed only through an **adjacency oracle** $\mathrm{adj}(u, w)$, which charges its own ticks. One step of a running trial $(a, W, \iota)$ costs one tick and does the following.
--
--   1. If $W$ is empty, the trial is **done** with assignment $a$.
--   2. If the head $u$ of $W$ has been compared with all $2n$ nodes ($\iota = 2n$), it is removed from $W$ and $\iota := 0$.
--   3. Otherwise $u$ is compared, by one oracle call, with the node $w$ of index $\iota$ (node $(\lfloor \iota/2 \rfloor, \iota \text{ even})$), and $\iota := \iota + 1$. If $u \sim w$:
--      - if $w$ is chosen, the trial **fails** (both nodes of the pair of $w$ are excluded);
--      - if the mate of $w$ is chosen, nothing changes;
--      - if the pair of $w$ is open, the mate of $w$ becomes chosen (an **implication**) and is pushed on $W$.
--
--   A failed or done trial is left unchanged.
--
--   This is one elementary step of "one considers all the implications of this choice. This may fix the schedules of some other teachers" in the proof of Proposition 2.4.
--
--   **Formalization Note** The oracle is `adj : Fin n × Bool → Fin n × Bool → StateM ℕ Bool`. Apart from the tick and the oracle call, a step does $O(1)$ work.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "then one considers all the implications of this choice. This may fix the schedules of some other teachers. Then either we arrive to the conclusion that for some tacher no schedule can be found". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_Cost_tick
import Definitions.Def_Timetabling_StableHalf_Trial

namespace Timetabling.StableHalf

/-- **One scan step of the propagation of implications.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155,
"then one considers all the implications of this choice. This may fix the schedules of some
other teachers. Then either we arrive to the conclusion that for some tacher no schedule can be
found."

The graph is given by an adjacency oracle `adj : V → V → StateM ℕ Bool` on the node set
`V = Fin n × Bool`, which charges its own ticks. One step of a running trial ticks once and:

1. if no chosen node is pending, the trial is `done`;
2. if the pending node `u` has been compared with all `2n` nodes, it is removed;
3. otherwise `u` is compared with the next node `w = (idx / 2, idx even)` by one oracle call.
   If `u` and `w` are adjacent: when `w` is chosen the trial `failed` (both nodes of pair
   `w.1` are excluded); when the mate `(w.1, !w.2)` is chosen nothing changes; when pair `w.1`
   is open the mate is chosen (an *implication*) and pushed onto `work`.

A `failed` or `done` trial is returned unchanged.

**Formalization Note.** Nodes are enumerated as `idx ↦ (idx / 2, decide (idx % 2 = 0))`, so each
of the `2n` nodes is visited once per scan. The step does `O(1)` unticked work. -/
def propStep {n : ℕ} (adj : Fin n × Bool → Fin n × Bool → StateM ℕ Bool) :
    Trial n → StateM ℕ (Trial n)
  | .failed => pure .failed
  | .done a => pure (.done a)
  | .running a work idx => do
    Cost.tick
    match work with
    | [] => pure (.done a)
    | u :: rest =>
      if h : idx < 2 * n then
        let w : Fin n × Bool := (⟨idx / 2, by omega⟩, decide (idx % 2 = 0))
        let e ← adj u w
        if e then
          match a w.1 with
          | some c =>
            if c = w.2 then pure .failed
            else pure (.running a (u :: rest) (idx + 1))
          | none =>
            pure (.running (Function.update a w.1 (some (!w.2))) (u :: (w.1, !w.2) :: rest)
              (idx + 1))
        else pure (.running a (u :: rest) (idx + 1))
      else pure (.running a rest 0)

end Timetabling.StableHalf


