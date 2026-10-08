-- Prove2me | Definitions.Def_SchedComplexity_Shops_Constructions
-- name    : SchedComplexity_Shops_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:10:09.312+00:00
-- url     : https://prove2.me/theorems/ae36c7fa-3302-4ada-b661-eea304fd774b
-- title:
--   The four scheduling instances built from a KNAPSACK instance in the proof of Theorem 4(g), (h), (i), (j)
-- statement:
--   Let $a_1,\dots,a_t$, $b$ be a KNAPSACK instance, $T=\{1,\dots,t\}$ and $A=\sum_{j\in T}a_j$. The proof of Theorem 4 constructs the following instances (jobs $J_1,\dots,J_t$ correspond to the items, the last one or two jobs are extra jobs; unless stated, release dates are $0$ and there are no precedence arcs).
--
--   1. **(i)**, two machines, $n=t+1$: $\mu_j=(M_1)$, $p_{j1}=a_j$ for $j\in T$; $\mu_n=(M_2,M_1,M_2)$ with $p_{n1}=b$, $p_{n2}=1$, $p_{n3}=A-b$; threshold $y=A+1$.
--   2. **(j)**, three machines, $n=t+2$: $\mu_j=(M_1,M_3)$, $p_{j1}=p_{j2}=a_j$ for $j\in T$; $\mu_{n-1}=(M_1,M_2)$ with $p_{n-1,1}=b$, $p_{n-1,2}=2(A-b)$; $\mu_n=(M_2,M_3)$ with $p_{n1}=2b$, $p_{n2}=A-b$; threshold $y=2A$.
--   3. **(g)**, two-machine flow shop, $n=t+1$: $r_j=0$, $p_{j1}=ta_j$, $p_{j2}=1$ for $j\in T$; $r_n=tb$, $p_{n1}=1$, $p_{n2}=t(A-b)$; threshold $y=t(A+1)$.
--   4. **(h)**, two-machine flow shop, $n=t+2$: $p_{j1}=ta_j$, $p_{j2}=1$ for $j\in T$; $p_{n-1,1}=1$, $p_{n-1,2}=tb$; $p_{n1}=1$, $p_{n2}=t(A-b)$; the single precedence arc $J_{n-1}<J_n$; threshold
--
--   $$y=t(A+1)+1.$$
--
--   These are exactly the data printed on pp. 16–18 of the report; the equivalence theorems of this mission are statements about them.
--
--   **Formalization Note** Item $j$ is the job with 0-based index $j-1$, and $J_{n-1}$, $J_n$ are the indices $t$, $t+1$ (or $J_n$ is index $t$ when $n=t+1$); machines $M_1,M_2,M_3$ are $0,1,2$. The quantity $A-b$ is natural-number subtraction; the report assumes $0<b<A$, where it agrees with integer subtraction, and the equivalence theorems carry that assumption.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 16 (proof of Theorem 4(i)), p. 17 (proof of Theorem 4(j)), p. 18 (proofs of Theorem 4(g), (h))

import Mathlib
import Definitions.Def_SchedComplexity_Shops_Model

namespace SchedComplexity.Shops

/-! # The four constructions of Theorem 4(g)–(j)

Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, pp. 16–18. The KNAPSACK data are the list
`a = [a_1, …, a_t]` and `b`; `t = a.length` and `A = ∑_{j ∈ T} a_j = a.sum`. Item `j ∈ T` is the job
with 0-based index `j - 1 < t`; the extra jobs `J_{n-1}`, `J_n` are the last indices. Machines
`M_1, M_2, M_3` are `0, 1, 2`. The paper assumes `0 < b < A`, so the natural-number subtraction
`A - b` is the integer one in that range. -/

/-- Theorem 4(i), p. 16: `n = t + 1`; `μ_j = (M_1)`, `p_j1 = a_j` (`j ∈ T`);
`μ_n = (M_2, M_1, M_2)`, `p_n1 = b`, `p_n2 = 1`, `p_n3 = A - b`; no release dates or precedence. -/
def constrI (a : List ℕ) (b : ℕ) : ShopInstance (a.length + 1) 2 where
  ops j := if h : j.val < a.length then [(0, a.get ⟨j.val, h⟩)]
    else [(1, b), (0, 1), (1, a.sum - b)]
  release _ := 0
  prec := ∅

/-- The threshold of Theorem 4(i): `y = A + 1`. -/
def yI (a : List ℕ) : ℕ := a.sum + 1

/-- Theorem 4(j), p. 17: `n = t + 2`; `μ_j = (M_1, M_3)`, `p_j1 = p_j2 = a_j` (`j ∈ T`);
`μ_{n-1} = (M_1, M_2)`, `p_{n-1,1} = b`, `p_{n-1,2} = 2(A - b)`; `μ_n = (M_2, M_3)`,
`p_n1 = 2b`, `p_n2 = A - b`; no release dates or precedence. -/
def constrJ (a : List ℕ) (b : ℕ) : ShopInstance (a.length + 2) 3 where
  ops j := if h : j.val < a.length then [(0, a.get ⟨j.val, h⟩), (2, a.get ⟨j.val, h⟩)]
    else if j.val = a.length then [(0, b), (1, 2 * (a.sum - b))]
    else [(1, 2 * b), (2, a.sum - b)]
  release _ := 0
  prec := ∅

/-- The threshold of Theorem 4(j): `y = 2A`. -/
def yJ (a : List ℕ) : ℕ := 2 * a.sum

/-- Theorem 4(g), p. 18: `n = t + 1`; `r_j = 0`, `p_j1 = t a_j`, `p_j2 = 1` (`j ∈ T`);
`r_n = t b`, `p_n1 = 1`, `p_n2 = t(A - b)`; flow shop (every job visits `M_1` then `M_2`), no
precedence. -/
def constrG (a : List ℕ) (b : ℕ) : ShopInstance (a.length + 1) 2 where
  ops j := if h : j.val < a.length then [(0, a.length * a.get ⟨j.val, h⟩), (1, 1)]
    else [(0, 1), (1, a.length * (a.sum - b))]
  release j := if j.val < a.length then 0 else a.length * b
  prec := ∅

/-- The threshold of Theorem 4(g): `y = t(A + 1)`. -/
def yG (a : List ℕ) : ℕ := a.length * (a.sum + 1)

/-- Theorem 4(h), p. 18: `n = t + 2`; `p_j1 = t a_j`, `p_j2 = 1` (`j ∈ T`);
`p_{n-1,1} = 1`, `p_{n-1,2} = t b`; `p_n1 = 1`, `p_n2 = t(A - b)`; flow shop, all release dates
`0`, and the single precedence arc `J_{n-1} < J_n`. -/
def constrH (a : List ℕ) (b : ℕ) : ShopInstance (a.length + 2) 2 where
  ops j := if h : j.val < a.length then [(0, a.length * a.get ⟨j.val, h⟩), (1, 1)]
    else if j.val = a.length then [(0, 1), (1, a.length * b)]
    else [(0, 1), (1, a.length * (a.sum - b))]
  release _ := 0
  prec := {(⟨a.length, by omega⟩, Fin.last (a.length + 1))}

/-- The threshold of Theorem 4(h): `y = t(A + 1) + 1`. -/
def yH (a : List ℕ) : ℕ := a.length * (a.sum + 1) + 1

end SchedComplexity.Shops


