-- Prove2me | Definitions.Def_LNTopology_Hermetization_tick
-- name    : LNTopology_Hermetization_tick
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:22:09.233271+00:00
-- url     : https://prove2.me/theorems/fe20e9b0-f3ee-4305-a705-c25859bc45ad
-- title:
--   Tick counter of the real-RAM cost model
-- statement:
--   The algorithms of the mission are programs in the state monad over a natural-number counter; $\mathrm{tick}(k)$ adds $k$ to the counter, and the **running time** of a run started at $0$ is the final value of the counter.
--
--   Running time is counted in the **real-RAM model**, because the inputs (real flows $\lambda_{i,j}$, the cost $c$, the function $g_+$) have no finite bit encoding. The discipline that binds every algorithm of the mission:
--
--   1. every read of an input flow, every query of $c$ or $g_+$ (oracle access), every comparison of two reals and every real arithmetic operation costs one tick, and so does every evaluation of a degree test;
--   2. every iteration of every loop costs at least one tick, and the unticked work inside one iteration is a bounded number of reads and updates of array-like state, each $O(1)$ on a RAM;
--   3. the only classical (non-constructive) decisions are these ticked primitives applied to concrete values; no algorithm uses choice, searches over subsets, or tests the cost, hermetizability or the discrepancy;
--   4. the algorithms never read the counter.
--
--   "Polynomial time" in Theorem 3.8 and "$O(V+E)$" in Lemma B.3 are bounds on this counter.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9), and Lemma B.3, p. 12 (PDF p. 13)

import Mathlib

namespace LNTopology.Hermetization

/-- **Charging `k` units of running time.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 ("there is a polynomial-time algorithm") and Lemma B.3, p. 12 ("The
running time of the algorithm is O(V + E)").

The algorithms of this mission are programs in the state monad `StateM ℕ`, whose state is a tick
counter; `tick k` adds `k` to it. The running time of a run started at `0` is the final value of
the counter.

**Formalization Note.** Reading R4: the inputs (flows `λ`, the cost `c`, the function `g₊`) are
real numbers and real functions, which have no finite bit encoding, so running time is counted in
the real-RAM model. The discipline binding every algorithm of the mission:
* every read of an input flow (`lamAt`), every query of `c` or `g₊` (`cAt`, `gAt`), every real
  comparison (`rlt`, `rle`, `req`), every real operation (`rabs`, `rmul`, `rdiv`) and every
  evaluation of a degree test (`badAt`) ticks once;
* every iteration of every loop ticks at least once, and the unticked code inside one iteration
  does a bounded number (independent of the input) of reads and updates of array-like state
  (`Fin n → ℕ`, `Fin n → Bool`, the head of a list), each `O(1)` on a RAM;
* the only classical decisions are the ticked primitives above, applied to concrete values; no
  algorithm uses `Classical.choose`, searches over subsets, or tests `cost`, `Hermetizable` or
  `disc`;
* the algorithms never read the counter, so the cost of a run does not depend on its start
  value. -/
def tick (k : ℕ) : StateM ℕ Unit := modify (· + k)

end LNTopology.Hermetization


