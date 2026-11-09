-- Prove2me | Definitions.Def_ChangingCache_UpperBound_NormalForm
-- name    : ChangingCache_UpperBound_NormalForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:16.345212+00:00
-- url     : https://prove2.me/theorems/d14f421f-7100-44f8-bffe-1041dfdcffd1
-- title:
--   Runs, snapshots and the normal form (reduced runs, eager discarding, tight profile)
-- statement:
--   A **run** is a memory profile $m$, a request sequence $\sigma=(\sigma_1,\dots,\sigma_n)$, LRU under $(a,s)$ augmentation, and a legal policy, which is OPT unless stated otherwise. For a position $0\le i\le n$ write $P_{LRU}(i)$ and $P_{OPT}(i)$ for the sets of pages held after request $\sigma_i$, and $F_{LRU}(i)$, $F_{OPT}(i)$ for the miss counts after the first $i$ requests.
--
--   **Reduced run** (Definition 4.1, p. 7). A run of OPT and LRU on a memory profile $m$ is reduced, or in normal form, if
--   1. (R1) every request misses in LRU;
--   2. (R2) every miss of OPT is cold;
--   3. (R3) OPT has exactly one free slot before each of its misses: making its discards before a miss rather than at it, OPT holds $m(j)-1$ pages just before its $j$-th miss.
--
--   **Greedy requests** (Lemma 4.3, p. 8). Whenever OPT holds a page absent from LRU, the next request is to such a page.
--
--   **Eager discarding** (p. 11). After each request $\sigma_i$, OPT holds exactly the pages it has loaded that are requested after $\sigma_i$.
--
--   **Tight profile** (Lemma 4.7, p. 11). For a run in which OPT has $F$ misses, let $m'(j)$, for $1\le j\le F$, be one more than the number of pages OPT loaded at its first $j-1$ misses that are requested after its $j$-th miss; let $m'(0)=1$ and
--   $$m'(j)=\min\{m(j),\,m'(F)\}\qquad (j>F).$$
--
--   These notions carry the reduction of Section 4 and the whole of Section 5.
--
--   **Formalization Note** Positions are $0,\dots,n$ and position $i$ is the moment after the first $i$ requests; $P_{LRU}(i)$ is `lruCache C σ i` and $F_{LRU}(i)$ is `lruMissCount C σ i`; $P_{OPT}(i)$ is `S i` and $F_{OPT}(i)$ is `policyMisses σ S i`. `IsReduced a s m σ S` includes that $m$ is a memory profile and that $S$ is an optimal legal policy for $\sigma$ on $m$; (R3) reads $|S_i|+1=m(F_{OPT}(i)+1)$ at every request $i+1$ that misses in OPT, where $S_i$ already includes the discards made before that miss. `loadedIn σ S r' u` is the set of pages OPT loads at requests $\sigma_{r'+1},\dots,\sigma_u$. `IsGreedy` ranges over the positions $0\le i<n$, those that have a next request. When $F=0$, $m'(F)=m'(0)=1$, so $m'(j)=1$ for $j>0$.
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Definition 4.1, p. 7; Lemma 4.3 (greedy clause), p. 8; eager discarding, p. 11; Lemma 4.7 (tight profile), p. 11; §5 notation $P_{LRU}$, $P_{OPT}$, p. 12

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Model

namespace ChangingCache.UpperBound

/-! # Runs, snapshots and the normal form (Bender et al., STOC 2027 #93, §3–§4, pp. 7–11)

A run is a memory profile `m`, a request sequence `σ`, LRU under `(a, s)` augmentation (capacity law
`augCap a s m`), and a legal policy `S` (OPT unless stated otherwise). Positions are
`0, 1, …, σ.length`; position `i` is the moment just after the paper's request `σ_i`
(after the first `i` requests). -/

variable {α : Type*} [DecidableEq α]

/-- `P_LRU(i)`: the pages LRU (capacity law `C`) holds after the first `i` requests (p. 12). -/
def lruCache (C : ℕ → ℕ) (σ : List α) (i : ℕ) : Finset α :=
  (lruRun C (σ.take i)).cache.toFinset

/-- `F_LRU(i)`: LRU's number of misses after the first `i` requests (Definition 3.2, p. 7). -/
def lruMissCount (C : ℕ → ℕ) (σ : List α) (i : ℕ) : ℕ :=
  (lruRun C (σ.take i)).misses

/-- Property **(R1)** (Definition 4.1, p. 7): every request misses in LRU. -/
def LRUAlwaysMisses (C : ℕ → ℕ) (σ : List α) : Prop :=
  ∀ (i : ℕ) (h : i < σ.length), σ[i] ∉ (lruRun C (σ.take i)).cache

/-- The pages the policy `S` loads at its misses among requests `σ_{r'+1}, …, σ_u`
(`0`-based request indices `r' ≤ i < u`): "the pages it loaded in `(r', u]`". -/
def loadedIn (σ : List α) (S : ℕ → Finset α) (r' u : ℕ) : Finset α :=
  ((List.range u).filterMap
    (fun i => if r' ≤ i ∧ missB σ S i = true then σ[i]? else none)).toFinset

/-- **Reduced run** (Definition 4.1, p. 7) under `(a, s)` augmentation: `m` is a memory profile,
`S` is an OPT for `σ` on `m`, and
* (R1) every request misses in LRU;
* (R2) every miss of OPT is cold;
* (R3) with its discards made before a miss rather than at it, OPT holds `m(j) - 1` pages just
  before its `j`-th miss: `|S i| + 1 = m (F_OPT + 1)` at every request `i` that misses, where
  `F_OPT` is the number of misses before it. -/
def IsReduced (a : ℕ) (s : ℝ) (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) : Prop :=
  IsMemoryProfile m ∧ IsOptimal m σ S ∧
  LRUAlwaysMisses (augCap a s m) σ ∧
  AllMissesCold σ S ∧
  ∀ i < σ.length, missB σ S i = true → (S i).card + 1 = m (policyMisses σ S i + 1)

/-- The greedy clause of Lemma 4.3 (p. 8): whenever the policy `S` holds a page absent from LRU
(capacity law `C`), the next request is to such a page. It ranges over positions `i < σ.length`,
i.e. those with a next request. -/
def IsGreedy (C : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) : Prop :=
  ∀ (i : ℕ) (h : i < σ.length), (S i \ lruCache C σ i).Nonempty → σ[i] ∈ S i \ lruCache C σ i

/-- **Eager discarding** (p. 11): after each request `σ_i` (`0 ≤ i ≤ n`), OPT holds exactly the
pages it has loaded that are requested after `σ_i`. -/
def DiscardsEagerly (σ : List α) (S : ℕ → Finset α) : Prop :=
  ∀ i ≤ σ.length, S i = loadedIn σ S 0 i ∩ (σ.drop i).toFinset

/-- The `0`-based request indices at which the policy `S` misses, in increasing order; entry `j - 1`
is the request of its `j`-th miss. -/
def missIndices (σ : List α) (S : ℕ → Finset α) : List ℕ :=
  (List.range σ.length).filter (missB σ S)

/-- The **tight profile** `m'` of Lemma 4.7 (p. 11), for a run of OPT `S` with `F` misses:
for `1 ≤ j ≤ F`, `m'(j)` is one more than the number of pages OPT loaded at its first `j - 1`
misses that are requested after its `j`-th miss; `m'(0) = 1`; and `m'(j) = min (m j) (m'(F))` for
`j > F` (with `m'(F) = m'(0) = 1` when `F = 0`). -/
def tightProfile (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (j : ℕ) : ℕ :=
  let F := policyMisses σ S σ.length
  let core : ℕ → ℕ := fun j =>
    let t := (missIndices σ S).getD (j - 1) 0
    1 + (loadedIn σ S 0 t ∩ (σ.drop (t + 1)).toFinset).card
  let mF := if F = 0 then 1 else core F
  if j = 0 then 1 else if j ≤ F then core j else min (m j) mF

end ChangingCache.UpperBound


