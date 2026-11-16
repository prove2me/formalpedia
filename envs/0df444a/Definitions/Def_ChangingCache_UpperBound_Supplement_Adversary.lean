-- Prove2me | Definitions.Def_ChangingCache_UpperBound_Supplement_Adversary
-- name    : ChangingCache_UpperBound_Supplement_Adversary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:25:50.484664+00:00
-- url     : https://prove2.me/theorems/c42e2547-cf96-4974-bf74-a519da80c0e2
-- title:
--   Operational greedy requests and useful-page cache transitions
-- statement:
--   A state consists of its request history, its useful pages in order of most recent request, and the policy's miss count. Both history and cache start empty. Let $U$ be the useful pages and $L$ the pages in the published LRU run on the history. The next request is
--   $$x\in U\setminus L\quad\hbox{if this set is nonempty, and otherwise a fresh page.}$$
--   Any picker selecting an element of every nonempty finite set is permitted. A fresh page is named by its first request position, as in Figure 7. On a cold miss numbered $k$, the old useful pages are trimmed only as necessary to fit $m(k)-1$ slots, retaining the least recently requested old pages. The incoming page becomes useful if the resulting useful set still leaves one free slot. On a useful hit it moves to the front of the recency list. LRU is always computed by the published finite run, not by a substitute occupancy rule.
--
--   The recursive construction returns actual histories, an infinite next-request stream and a single family of legal-policy candidate snapshots. The useful list records the state before advance discards; policy snapshots include discards before the next request. A non-useful temporary incoming page can be discarded immediately because the greedy rule never requests it again. Legality, cold misses and stage properties are conclusions of the supporting theorems, never fields of this state.
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), p. 17, greedy request and useful-page rules; pp. 19–20, first-drop retention; p. 28, Figure 7

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Supplement_Streams
import Definitions.Def_ChangingCache_UpperBound_Supplement_Staircase

namespace ChangingCache.UpperBound.Supplement

/-- Section 6's operational state: history, useful pages in recency order, and the policy's
miss clock. A temporary incoming page not retained as useful is discarded immediately;
it is never chosen again by the greedy rule. No stage invariant is a field. -/
structure GreedyState where
  history : List ℕ
  useful : List ℕ
  misses : ℕ

/-- Any tie rule selecting an element of a nonempty finite set is allowed. -/
def IsPicker (pick : Finset ℕ → ℕ) : Prop :=
  ∀ A, A.Nonempty → pick A ∈ A

/-- Request a useful page absent from the actual published LRU run, else a fresh page.
The label r+1 for a new page is its first request position, as in Figure 7. -/
noncomputable def greedyNext (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) (st : GreedyState) : ℕ :=
  let missing := st.useful.toFinset \ (lruRun (augCap 2 2 m) st.history).cache.toFinset
  if missing.Nonempty then pick missing else st.history.length + 1

/-- Old useful pages retained before the next request. A cold miss reserves its incoming
slot by keeping the deepest old useful pages. On a hit nothing is discarded. `drop` is the
usual suffix operation and handles a grant larger than the current occupancy as well. -/
noncomputable def greedyReady (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) (st : GreedyState) : List ℕ :=
  if greedyNext m pick st ∈ st.useful then st.useful
  else st.useful.drop (st.useful.length - (m (st.misses + 1) - 1))

/-- The useful-page rule on p. 17 and the deepest-old-pages rule on pp. 19–20.
This is an actual request/cache transition, with no invariant or lemma conclusion assumed. -/
noncomputable def greedyStep (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) (st : GreedyState) : GreedyState :=
  let x := greedyNext m pick st
  let old := greedyReady m pick st
  let hit := x ∈ old
  let k := st.misses + if hit then 0 else 1
  let kept := if hit then x :: old.erase x
    else if (old.length : ℤ) + 1 ≤ (m k : ℤ) - 1 then x :: old else old
  ⟨st.history ++ [x], kept, k⟩

noncomputable def greedyRun (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) : ℕ → GreedyState
  | 0 => ⟨[], [], 0⟩
  | r + 1 => greedyStep m pick (greedyRun m pick r)

/-- Published policy snapshots include voluntary discards before the next request.
`greedyRun.useful` records the useful pages just after the current request, before those discards. -/
noncomputable def greedyPolicy (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) (r : ℕ) : Finset ℕ :=
  (greedyReady m pick (greedyRun m pick r)).toFinset

noncomputable def greedyStream (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) (r : ℕ) : ℕ :=
  greedyNext m pick (greedyRun m pick r)

end ChangingCache.UpperBound.Supplement


