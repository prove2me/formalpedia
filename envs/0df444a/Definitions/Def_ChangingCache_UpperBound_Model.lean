-- Prove2me | Definitions.Def_ChangingCache_UpperBound_Model
-- name    : ChangingCache_UpperBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:13.48074+00:00
-- url     : https://prove2.me/theorems/178eaf63-4dca-4df9-bcff-5cd79ef6b5ab
-- title:
--   The changing-cache model: memory profiles, augmented LRU, legal policies and OPT
-- statement:
--   This file fixes the model of caching with a cache that changes size, as on p. 2 and pp. 6–8.
--
--   1. **Pages and requests.** A page is an identifier and a request sequence is a finite list $\sigma=(\sigma_1,\dots,\sigma_n)$ of pages, with repetitions allowed. A request is a **hit** if the requested page is in the cache and a **miss** otherwise; a miss on a page's first request is a **cold** miss. Both caches start empty.
--   2. **Memory profile.** A memory profile is a sequence $m(0),m(1),\dots$ of positive integers with $m(j+1)\le m(j)+1$ for every $j$. Downward jumps are arbitrary.
--   3. **Time.** Time is measured in misses: a miss takes one unit of time and a hit none. A policy's $j$-th miss advances it to entry $j$ of the profile.
--   4. **Legal policy.** A cache loads only the requested page, one page per miss, and may discard any page at any time; on its $j$-th miss the loaded page must fit the capacity $m(j)$. A policy may use the whole request sequence.
--   5. **OPT.** $F_{OPT}$ is the fewest misses of a legal policy on $m$ over $\sigma$.
--   6. **LRU under $(a,s)$ augmentation.** LRU orders its pages by most recent request. On a request it puts the requested page first, loading it on a miss, and discards pages from the end until the rest fit its capacity. After $k$ misses its capacity is (Eq. (1))
--   $$C(k)=a\,m(\lfloor k/s\rfloor),\qquad s\ge1 .$$
--   A miss increments $k$ before the new capacity is applied; LRU never fills free slots except by requests, so the number of pages it holds is $c(0)=0$, $c(k+1)=\min\{C(k+1),c(k)+1\}$ (p. 8).
--   7. **Stack and depth.** The LRU stack lists every page requested so far, most recent first, including pages LRU no longer holds. The depth of a page is its one-based position in the stack, or $\infty$ if it has never been requested.
--
--   These definitions are shared by every statement of the mission: the reduction to normal form (Section 4), the analysis of reduced runs (Section 5) and Theorem 1.1.
--
--   **Formalization Note** Pages are elements of an arbitrary type `α` with decidable equality and the request sequence is a `List α`; request $\sigma_{i+1}$ is the 0-based entry `σ[i]`. A policy is the family $S_i$ (`S i : Finset α`) of pages it holds after the first $i$ requests, including every discard it makes before request $i+1$: `IsLegal m σ S` says $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ whenever request $i+1$ is its $j$-th miss. Moving a discard earlier changes no hit, miss or capacity check, and this is the placement used in (R3). `optMisses m σ` is the infimum of the miss counts of legal policies; for a memory profile the always-discard policy is legal, so the infimum is attained. LRU's state (`LRUState`) holds the stack, the ordered cache and the miss count; `lruStep` and `lruRun` run it from the empty cache with a capacity law `C`, and `augCap a s m k` $=a\,m(\lfloor k/s\rfloor)$ is Eq. (1) with $a\in\mathbb N$ and real $s$. Depth $\infty$ is `⊤ : ℕ∞`.
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, §1 p. 2 (model); §3 pp. 6–7 (requests, serving, legal policies, the two policies, Eq. (1)); §4 p. 8 (capacity vs. occupancy, LRU stack, stack depth)

import Mathlib

namespace ChangingCache.UpperBound

/-! # The changing-cache model (Bender et al., STOC 2027 #93, §1 p. 2 and §3 pp. 6–8)

Pages are elements of an arbitrary type `α` with decidable equality. A request sequence is a
`List α`; its `i`-th request (`0`-based) is `σ[i]`, i.e. the paper's `σ_{i+1}`. Both caches start
empty. -/

variable {α : Type*} [DecidableEq α]

/-- A **memory profile** (p. 2): positive integers `m 0, m 1, …` with `m (j + 1) ≤ m j + 1`.
Downward jumps are arbitrary; nothing else is assumed. -/
def IsMemoryProfile (m : ℕ → ℕ) : Prop :=
  (∀ j, 1 ≤ m j) ∧ ∀ j, m (j + 1) ≤ m j + 1

/-- **LRU's capacity under `(a, s)` augmentation**, Eq. (1), p. 7: after `k` misses it is
`C(k) = a · m(⌊k / s⌋)`, for a real speed `s ≥ 1` and an integer memory factor `a`. -/
noncomputable def augCap (a : ℕ) (s : ℝ) (m : ℕ → ℕ) (k : ℕ) : ℕ :=
  a * m ⌊(k : ℝ) / s⌋₊

/-! ## LRU -/

/-- The state of LRU: its recency stack (every page requested so far, each once, most recent
first, including pages LRU no longer holds), the pages it holds ordered by most recent request,
and its number of completed misses. -/
structure LRUState (α : Type*) where
  /-- The LRU stack (p. 8), most recent first. -/
  stack : List α
  /-- The pages held, most recently requested first. -/
  cache : List α
  /-- The number of misses so far. -/
  misses : ℕ

/-- One request to LRU with capacity law `C` (`C k` = capacity after `k` misses), p. 7: the
requested page is put first; on a miss it is loaded, the miss count advances to `k + 1`, and the
oldest pages are discarded until the rest fit `C (k + 1)`. A hit changes neither the miss count
nor the capacity. LRU loads only the requested page. -/
def lruStep (C : ℕ → ℕ) (st : LRUState α) (p : α) : LRUState α :=
  if p ∈ st.cache then
    { stack := p :: st.stack.erase p, cache := p :: st.cache.erase p, misses := st.misses }
  else
    { stack := p :: st.stack.erase p, cache := (p :: st.cache).take (C (st.misses + 1)),
      misses := st.misses + 1 }

/-- LRU with capacity law `C` run from the empty cache over the requests `σ`. -/
def lruRun (C : ℕ → ℕ) (σ : List α) : LRUState α :=
  σ.foldl (lruStep C) ⟨[], [], 0⟩

/-- The number of pages LRU holds after `k` misses (p. 8): `c(0) = 0`,
`c(k + 1) = min (C (k + 1)) (c k + 1)`. Capacity is not occupied size. -/
def lruOccupancy (C : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => min (C (k + 1)) (lruOccupancy C k + 1)

/-- The **stack depth** of a page (p. 8): its one-based position in the LRU stack, or `⊤` (the
paper's `∞`) if it has never been requested. -/
def stackDepth (stack : List α) (p : α) : ℕ∞ :=
  if p ∈ stack then ((stack.idxOf p + 1 : ℕ) : ℕ∞) else ⊤

/-! ## Legal policies -/

/-- Whether request `i` (`0`-based) of `σ` misses for a policy whose held pages before that
request are `S i`. -/
def missB (σ : List α) (S : ℕ → Finset α) (i : ℕ) : Bool :=
  match σ[i]? with
  | some p => decide (p ∉ S i)
  | none => false

/-- The number of misses of the policy `S` among the first `r` requests of `σ`. -/
def policyMisses (σ : List α) (S : ℕ → Finset α) (r : ℕ) : ℕ :=
  ((List.range r).filter (missB σ S)).length

/-- **Legal policy** (pp. 6–7). A policy is given by the sets `S i` of pages it holds after the
first `i` requests, including every discard it makes before request `i + 1` (`S 0 = ∅`: it starts
empty). It may discard any page at any time, loads only the requested page, and only on a miss:
`S (i + 1) ⊆ S i ∪ {σ[i]}`. On its `j`-th miss its capacity becomes `m j`, and the page just loaded
must fit: `|S i| + 1 ≤ m j`. Discards made at a miss are placed before it, which changes no hit or
miss; a hit loads nothing. The choices may depend on the whole sequence. -/
def IsLegal (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) : Prop :=
  S 0 = ∅ ∧ ∀ (i : ℕ) (h : i < σ.length),
    S (i + 1) ⊆ insert σ[i] (S i) ∧
    (σ[i] ∉ S i → (S i).card + 1 ≤ m (policyMisses σ S i + 1))

/-- **OPT's miss count** (p. 7): the fewest misses of a legal policy on the profile `m` over the
whole sequence `σ`. For a memory profile the set is nonempty (discard every page right after its
request), so the infimum is attained. -/
noncomputable def optMisses (m : ℕ → ℕ) (σ : List α) : ℕ :=
  sInf {k | ∃ S : ℕ → Finset α, IsLegal m σ S ∧ policyMisses σ S σ.length = k}

/-- `S` is an optimal legal policy (an OPT) for `σ` on `m`. -/
def IsOptimal (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) : Prop :=
  IsLegal m σ S ∧ policyMisses σ S σ.length = optMisses m σ

/-- Request `i` (`0`-based) is a **cold** request (p. 6): the first request to its page. A miss
on such a request is a cold miss. -/
def IsColdAt (σ : List α) (i : ℕ) : Prop :=
  ∃ h : i < σ.length, σ[i] ∉ σ.take i

/-- Every miss of the policy `S` on `σ` is cold (Property (R2), p. 7). -/
def AllMissesCold (σ : List α) (S : ℕ → Finset α) : Prop :=
  ∀ i < σ.length, missB σ S i = true → IsColdAt σ i

end ChangingCache.UpperBound


