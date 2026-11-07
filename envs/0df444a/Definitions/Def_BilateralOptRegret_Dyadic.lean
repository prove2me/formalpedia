-- Prove2me | Definitions.Def_BilateralOptRegret_Dyadic
-- name    : BilateralOptRegret_Dyadic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:20.706103+00:00
-- url     : https://prove2.me/theorems/c36903e1-82a8-4ef6-ae03-8df9bb279253
-- title:
--   (9), (18) — dyadic pairs, the canonical decomposition, permitted intervals
-- statement:
--   For $K=2^n+1$ the **dyadic family** is
--   $$\mathcal I^\star=\bigcup_{k=0}^{\ell_K-2}\Big\{(q2^k,(q+1)2^k):q=0,\dots,\frac{K-1}{2^k}-1\Big\}.$$
--   The **canonical decomposition** $\mathcal B(i,i')$, for $i'<i$, is the greedy chain: starting from $i'$, repeatedly select the longest $(a,b)\in\mathcal I^\star$ with $a$ the current endpoint and $b\le i$, and continue from $b$. For an internal index $i\in\{1,\dots,K-2\}$ the **permitted radius** is $h_i=2^{\nu_2(i)}$, with $\nu_2$ the $2$-adic valuation, and the **permitted interval** is $I_i=\{i-h_i,\dots,i+h_i\}$. Each pair of $\mathcal I^\star$ is assigned to its internal endpoint of larger permitted radius.
--
--   These are the combinatorial objects behind the rerouting of CDF differences.
--
--   **Formalization Note** $\mathcal B$ is a list in chain order, computed with a step budget of $K$ steps, which is never binding when $n\ge1$ because each step moves right. At $n=0$ we have $\mathcal I^\star=\emptyset$ and the chain is empty.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), (9), p.18; App. B, p.43; (18), p.28

import Mathlib
import Definitions.Def_BilateralOptRegret_Model

namespace BilateralOptRegret

/-! # The dyadic family (9), the canonical decomposition and the permitted intervals (18)

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…), (9), p.18; App. B, p.43; (18), p.28.

**Formalization Note.** Indices are `Idx n = Fin (2^n + 1)`. `B n i i'` is the greedy chain of App. B as a
list, in chain order (the order is used by Lemmas 7.2 and 7.3): from the current endpoint `c`, take the
longest `(c, b) ∈ I⋆` with `b ≤ i`. The recursion carries a step budget `K`; each step moves right, so the
budget is never the reason the chain stops when `n ≥ 1`. For `n = 0` we have `I⋆ = ∅` and the chain is empty.
`radius i = 2^{ν₂(i)}`; for internal `i` we have `radius i ≤ i` and `i + radius i ≤ 2^n`, so the truncating
subtraction in `lo` and the `min` in `hiI` do nothing on internal indices, the only ones they are used on. -/

/-- The dyadic family `I⋆ = ⋃_{k=0}^{ℓ_K−2} {(q 2^k, (q + 1) 2^k) : q = 0, …, (K − 1)/2^k − 1}`, (9), p.18. -/
def Istar (n : ℕ) : Finset (Idx n × Idx n) :=
  (Finset.range n).biUnion fun k =>
    (Finset.range (2 ^ (n - k))).image fun q =>
      (Fin.ofNat (Kof n) (q * 2 ^ k), Fin.ofNat (Kof n) ((q + 1) * 2 ^ k))

/-- The greedy chain from the current endpoint `c` towards `i`, with a step budget. -/
def bChain (n : ℕ) (i : Idx n) : ℕ → Idx n → List (Idx n × Idx n)
  | 0, _ => []
  | f + 1, c =>
      let ends := ((Istar n).filter fun p => p.1 = c ∧ p.2 ≤ i).image Prod.snd
      if h : ends.Nonempty then
        (c, ends.max' h) :: bChain n i f (ends.max' h)
      else
        []

/-- The canonical dyadic decomposition `B(i, i′)` (Lemma 5.1, p.18; App. B, p.43), in chain order. -/
def B (n : ℕ) (i i' : Idx n) : List (Idx n × Idx n) := bChain n i (Kof n) i'

/-- The internal junctions of a chain: the left endpoints of all intervals but the first (p.29). -/
def junctions {n : ℕ} (chain : List (Idx n × Idx n)) : List (Idx n) := chain.tail.map Prod.fst

/-- The chain endpoints: every index `u` with `(u, w)` or `(w, u)` in the chain. -/
def chainPoints {n : ℕ} (chain : List (Idx n × Idx n)) : List (Idx n) :=
  chain.map Prod.fst ++ chain.map Prod.snd

/-- The internal indices `{1, …, K − 2}` (p.28). -/
def internal (n : ℕ) : Finset (Idx n) :=
  Finset.univ.filter fun i => 0 < i.val ∧ i.val < 2 ^ n

/-- The permitted radius `h_i = 2^{ν₂(i)}` (p.28). -/
def radius (i : ℕ) : ℕ := 2 ^ padicValNat 2 i

/-- The permitted interval `I_i = {i − h_i, …, i + h_i}`, (18), p.28. -/
def perm {n : ℕ} (i : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun u => i.val - radius i.val ≤ u.val ∧ u.val ≤ i.val + radius i.val

/-- The index `i − h_i`. -/
def lo {n : ℕ} (i : Idx n) : Idx n := ⟨i.val - radius i.val, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- The index `i + h_i`. -/
def hiI {n : ℕ} (i : Idx n) : Idx n :=
  ⟨min (i.val + radius i.val) (2 ^ n), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The endpoint of `p ∈ I⋆` whose interval `p` is assigned to (Lemma 7.8, p.35, and its proof, p.36): the
internal endpoint with the larger permitted radius; a boundary endpoint is never chosen. -/
def assignedEnd {n : ℕ} (p : Idx n × Idx n) : Idx n :=
  if p.1 ∈ internal n ∧ (p.2 ∉ internal n ∨ radius p.2.val ≤ radius p.1.val) then p.1 else p.2

end BilateralOptRegret


