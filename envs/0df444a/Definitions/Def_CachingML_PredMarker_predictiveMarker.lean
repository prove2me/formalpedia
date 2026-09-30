-- Prove2me | Definitions.Def_CachingML_PredMarker_predictiveMarker
-- name    : CachingML_PredMarker_predictiveMarker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:02:42.155917+00:00
-- url     : https://prove2.me/theorems/193e48d9-5f1c-424c-ae0e-46014f5d4189
-- title:
--   Algorithm 1 — Predictive Marker, its run, expected cost and chain errors
-- statement:
--   **Predictive Marker** (Algorithm 1) serves requests $z_1, z_2, \dots$ with a cache $\mathcal C$ of size $k$ that starts empty. On each request $z_i$ it receives a prediction $h_i$ of the next arrival time of $z_i$ and saves it as $p(z_i) = h_i$. Elements are **marked** when requested; the algorithm runs in phases as the Marker algorithm does.
--
--   1. On a hit, or on a miss while $|\mathcal C| < k$, the element is loaded without eviction and marked.
--   2. On a miss with a full cache in which all elements are marked, a new phase begins: the phase counter $r$ increases, the clean counter $q_r$ is reset, the current cache is saved as the set $\mathcal S$ of possibly stale elements, and all marks are removed.
--   3. On a miss with a full cache, if $z_i \notin \mathcal S$ ($z_i$ is **clean**), a new **chain** $c = q_r + 1$ of length $n(r,c) = 1$ is opened and the evicted element is an unmarked cached element with the largest saved prediction, $e \in \arg\max_{z \in \mathcal C \setminus \mathcal M} p(z)$.
--   4. If $z_i \in \mathcal S$ ($z_i$ is **stale**), then $z_i$ is the representative $\omega(r,c)$ of some chain $c$ (it was evicted into that chain earlier in the phase). The length $n(r,c)$ is increased by one; if $n(r,c) \le H_k = 1 + \tfrac12 + \dots + \tfrac1k$ the evicted element is chosen by the same arg max, and otherwise it is chosen **uniformly at random** among the unmarked cached elements $\mathcal C \setminus \mathcal M$.
--   5. In cases 3 and 4 the chosen element $e$ is evicted, $z_i$ is loaded and marked, and $e$ becomes the new representative $\omega(r,c)$ of the chain.
--
--   Ties in the arg max may be broken by any rule, which is a parameter. The **expected cost** $\mathrm{cost}_{PM}(\sigma)$ is the expected number of misses, over the random evictions. The **error of chain** $c$ of phase $r$, $\eta_{r,c}$, is the sum, over the elements $e$ evicted into the chain, of the loss $\ell(y_j, h_j)$ of the saved prediction $p(e) = h_j$ on which the eviction was based ($j$ is the last request of $e$ before its eviction).
--
--   **Formalization Note** The state `PMState` holds the cache, the marked set, the stale set, the saved predictions and the request indices at which they were saved, the counters $r$ and $q_r$, the chain lengths $n(r,c)$, the chain of each representative, for each chain the request indices of the predictions of its evicted elements, the set of chains that made a random eviction, and the miss count. `step` is one round (lines 3–26) and `run` the distribution (a `PMF`) of the final state; `expCost` is $\sum_s \Pr[s] \cdot \mathrm{misses}(s)$ in $[0, \infty]$. A tie-breaking rule `tb` is admissible (`IsMaxTieBreak`) if in every state with $\mathcal C \setminus \mathcal M \ne \emptyset$ it returns an element of $\mathcal C \setminus \mathcal M$ maximizing $p$. **Printed slip:** in Algorithm 1 as printed, the eviction (lines 23–24) is inside the stale branch only, so a clean miss would select $e$ (line 13) but never evict it; the text before the algorithm and the analysis require the eviction and make $e$ the start of the new chain, so the eviction is performed in both branches, with $\omega(r, q_r) \leftarrow e$ for a clean element. The line-18 test compares the natural number $n(r,c)$ with the real $H_k$ (`harmonic k`). The two fall-back branches (uniform choice from an empty set; `tb` outside its specification) are never reached when $k \ge 1$, since after a phase change $\mathcal M = \emptyset$ and otherwise $|\mathcal M| < k = |\mathcal C|$.
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, pp. 12–13, §3.2, Algorithm 1 (Predictive Marker) and the chains paragraph; p. 15, Lemma 3.3 (η_{r,c})

import Mathlib
import Definitions.Def_CachingML_PredMarker_predError

open scoped ENNReal

namespace CachingML.PredMarker

/-- The state of Predictive Marker (Lykouris–Vassilvitskii, arXiv:1802.05399v4, Algorithm 1, p. 13),
together with the bookkeeping the analysis reads off a run.
* `cache` is the cache `𝒞`, `marked` the marked set `ℳ`, `stale` the tracking set `𝒮` (the cache saved at
  the start of the current phase, line 8).
* `pred z` is the saved prediction `p(z)` (line 3); `predIdx z` is the 0-based index of the request at
  which it was saved.
* `phase` is the phase counter `r`, `clean` the clean-element counter `q_r`.
* `chainLen r c` is the chain length `n(r, c)`; `chainOf e` is the index `c` of the chain of the current
  phase whose representative `ω(r, c)` is `e` (meaningful for elements evicted in the current phase).
* `chainIdx r c` lists, in eviction order, the request indices `predIdx e` of the elements `e` evicted
  into chain `c` of phase `r`; `randomChains` holds the chains `(r, c)` that made a random eviction
  (line 21).
* `misses` counts the cache misses so far. -/
structure PMState (α : Type*) where
  cache : Finset α
  marked : Finset α
  stale : Finset α
  pred : α → ℝ
  predIdx : α → ℕ
  phase : ℕ
  clean : ℕ
  chainLen : ℕ → ℕ → ℕ
  chainOf : α → ℕ
  chainIdx : ℕ → ℕ → List ℕ
  randomChains : Set (ℕ × ℕ)
  misses : ℕ

/-- The initial state (Require line and lines 1–2 of Algorithm 1): empty cache, nothing marked, empty
tracking set, phase `r = 1`, clean counter `0`, no chains, no misses. -/
def initState (α : Type*) : PMState α where
  cache := ∅
  marked := ∅
  stale := ∅
  pred := fun _ => 0
  predIdx := fun _ => 0
  phase := 1
  clean := 0
  chainLen := fun _ _ => 0
  chainOf := fun _ => 0
  chainIdx := fun _ _ => []
  randomChains := ∅
  misses := 0

/-- A tie-breaking rule for the `arg max` of lines 13 and 19: in every state whose set `𝒞 − ℳ` of
unmarked cached elements is nonempty it returns an unmarked cached element with the highest saved
prediction. It may depend on the whole state. -/
def IsMaxTieBreak {α : Type*} [DecidableEq α] (tb : PMState α → α) : Prop :=
  ∀ s : PMState α, (s.cache \ s.marked).Nonempty →
    tb s ∈ s.cache \ s.marked ∧ ∀ z ∈ s.cache \ s.marked, s.pred z ≤ s.pred (tb s)

/-- Lines 23–24 and 26 of Algorithm 1 after a miss on `z` with a full cache: evict `e`, load `z`, make
`e` the representative of chain `c` of the current phase (recording the request index of `e`'s saved
prediction in that chain), mark `z`, and count the miss. -/
def evictInto {α : Type*} [DecidableEq α] (s : PMState α) (z : α) (c : ℕ) (e : α) : PMState α :=
  { s with
    cache := insert z (s.cache.erase e)
    chainOf := Function.update s.chainOf e c
    chainIdx := Function.update s.chainIdx s.phase
      (Function.update (s.chainIdx s.phase) c (s.chainIdx s.phase c ++ [s.predIdx e]))
    marked := insert z s.marked
    misses := s.misses + 1 }

/-- One round of Predictive Marker (lines 3–26 of Algorithm 1) on the request `z` with 0-based index `i`
and prediction `hz`, for cache size `k` and tie-breaking rule `tb`. The eviction of lines 23–24 is
performed after the clean branch (line 13, with `ω(r, q_r) ← e`) as well as after the stale branch.
The random eviction of line 21 is uniform over the unmarked cached elements `𝒞 − ℳ`. -/
noncomputable def step {α : Type*} [DecidableEq α] (k : ℕ) (tb : PMState α → α)
    (s : PMState α) (i : ℕ) (z : α) (hz : ℝ) : PMF (PMState α) :=
  -- line 3: save the prediction
  let s1 : PMState α :=
    { s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i }
  -- lines 4–6 (and 26): hit, or cache not full
  if z ∈ s1.cache ∨ s1.cache.card < k then
    PMF.pure { s1 with
      cache := insert z s1.cache
      marked := insert z s1.marked
      misses := if z ∈ s1.cache then s1.misses else s1.misses + 1 }
  else
    -- lines 7–9: all cached elements marked, start a new phase
    let s2 : PMState α :=
      if s1.marked.card = k then
        { s1 with phase := s1.phase + 1, clean := 0, stale := s1.cache, marked := ∅ }
      else s1
    if z ∉ s2.stale then
      -- lines 10–14: clean element, new chain `q_r`, prediction-based eviction
      let q := s2.clean + 1
      let s3 : PMState α :=
        { s2 with
          clean := q
          chainLen := Function.update s2.chainLen s2.phase
            (Function.update (s2.chainLen s2.phase) q 1) }
      PMF.pure (evictInto s3 z q (tb s3))
    else
      -- lines 15–25: stale element, the representative of chain `c`
      let c := s2.chainOf z
      let n := s2.chainLen s2.phase c + 1
      let s3 : PMState α :=
        { s2 with
          chainLen := Function.update s2.chainLen s2.phase
            (Function.update (s2.chainLen s2.phase) c n) }
      if (n : ℝ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto s3 z c (tb s3))
      else if hne : (s3.cache \ s3.marked).Nonempty then
        (PMF.uniformOfFinset (s3.cache \ s3.marked) hne).map (fun e =>
          evictInto { s3 with randomChains := insert (s3.phase, c) s3.randomChains } z c e)
      else
        PMF.pure (evictInto s3 z c z)

/-- The run of Predictive Marker with cache size `k` and tie-breaking rule `tb` on the request sequence
`σ` with predictions `h` (one real per request): the distribution of the final state, starting from
`initState`. -/
noncomputable def run {α : Type*} [DecidableEq α] (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) : PMF (PMState α) :=
  (List.finRange σ.length).foldl
    (fun μ i => μ.bind (fun s => step k tb s i.val (σ.get i) (h i))) (PMF.pure (initState α))

/-- The expected number of cache misses `cost_PM(σ)` of Predictive Marker on `σ` with predictions `h`,
the expectation being over the algorithm's random evictions, as an extended nonnegative real. -/
noncomputable def expCost {α : Type*} [DecidableEq α] (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) : ℝ≥0∞ :=
  ∑' s, run k tb σ h s * (s.misses : ℝ≥0∞)

/-- The cumulative error `η_{r,c}` of the predictor on the elements of chain `c` of phase `r` in the final
state `s`: the sum, over the elements evicted into that chain, of the loss `ℓ(y_j, h_j)` of the saved
prediction `p(e) = h_j` that the eviction compared, `j` being the request at which it was saved. -/
noncomputable def chainError {α : Type*} [DecidableEq α] (ℓ : ℝ → ℝ → ℝ) (σ : List α)
    (h : Fin σ.length → ℝ) (s : PMState α) (r c : ℕ) : ℝ :=
  ((s.chainIdx r c).map (lossAt ℓ σ h)).sum

end CachingML.PredMarker


