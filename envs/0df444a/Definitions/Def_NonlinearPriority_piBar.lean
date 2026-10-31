-- Prove2me | Definitions.Def_NonlinearPriority_piBar
-- name    : NonlinearPriority_piBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:01.181163+00:00
-- url     : https://prove2.me/theorems/b486499c-e301-46ee-9b7c-da7684170383
-- title:
--   The policies $\pi_k$, $\pi_{k+1}$, $\bar\pi_k$ and $\pi_i$
-- statement:
--   Starting from the policy $\pi$ under which type $i$ has priority order $i$, fix two adjacent types $k,k+1$:
--
--   1. $\pi_k=\pi$;
--   2. $\pi_{k+1}$ is $\pi$ with the priority orders of types $k$ and $k+1$ switched;
--   3. $\bar\pi_k$ is $\pi$ with types $k$ and $k+1$ pooled: both get the same order and are served FCFS among themselves, and all other types keep their relative order.
--
--   For a type $i$ of the pair, $\pi_i$ denotes the policy that gives $i$ priority over the other type: $\pi_k$ or $\pi_{k+1}$.
--
--   **Formalization Note** Policies are order maps $\mathrm{Fin}\,K\to\mathbb N$. Types are 0-based, so the paper's pair $(k,k+1)$, $k\in\{1,\dots,K-1\}$, is the pair $k,k+1$ with $k+1<K$ here. $\bar\pi_k$ gives types $\le k$ their index and types $>k$ their index minus one. This module bundles the four policies.
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, §4, pp.4–5 (PDF 5–6)

import Mathlib

namespace NonlinearPriority

variable {K : ℕ}

/-- **The policy `π_k = π`** (§4, p. 4, PDF 5). Ouyang, Argon and Ziya, Management Science (2021),
doi:10.1287/mnsc.2020.3952: "we assume that type i customers have priority order i under policy π
for i = 1, 2, …, K … we also define policy πk, which is identical to policy π."

A fixed-priority policy of `Π^F` is its priority-order map `Fin K → ℕ` (smaller order served
first, equal orders served FCFS; see `waitingTime`). `π` gives type `i` order `i`.

**Formalization Note.** Types are 0-based: the paper's pair `(k, k+1)`, `k ∈ {1, …, K−1}`, is the
pair of types `k, k+1` with `k + 1 < K` here, i.e. the paper's `k` is this `k + 1`. -/
def piK (_k : ℕ) : Fin K → ℕ := fun i => (i : ℕ)

/-- **The policy `π_{k+1}`** (§4, p. 4, PDF 5): "the priority orders of all types are the same as
those under policy π except that the priority orders of type k and type k + 1 customers are
switched." -/
def piK1 (k : ℕ) : Fin K → ℕ := fun i =>
  if (i : ℕ) = k then k + 1 else if (i : ℕ) = k + 1 then k else (i : ℕ)

/-- **The policy `π̄_k`** (§4, p. 5, PDF 6): "the priority orders of all types of customers are the
same as those under policy π except that type k and type k + 1 customers are pooled and served
according to FCFS." Types `k` and `k+1` get the same order `k`; every other type keeps its
relative order (types after `k + 1` move up by one so that the orders stay consecutive). -/
def piBar (k : ℕ) : Fin K → ℕ := fun i => if (i : ℕ) ≤ k then (i : ℕ) else (i : ℕ) - 1

/-- `π_i` for a type `i` of the pair (§4, p. 5): the policy that gives type `i` priority over the
other type of the pair, `π_k` if `i = k` and `π_{k+1}` otherwise. -/
def prioPolicy (k : ℕ) (i : Fin K) : Fin K → ℕ := if (i : ℕ) = k then piK k else piK1 k

end NonlinearPriority


