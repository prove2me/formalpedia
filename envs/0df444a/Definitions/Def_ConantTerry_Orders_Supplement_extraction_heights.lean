-- Prove2me | Definitions.Def_ConantTerry_Orders_Supplement_extraction_heights
-- name    : ConantTerry_Orders_Supplement_extraction_heights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:24:36.994201+00:00
-- url     : https://prove2.me/theorems/7dcb049a-2932-4cb7-afe7-199643f87f1e
-- title:
--   Exact extraction heights
-- statement:
--   For natural numbers $p,q,k$, define the proto-ladder height by
--   $$
--   t_k(p,q)=\sum_{i=0}^{k-1}(pq)^i.
--   $$
--   For $\epsilon>0$, put $K(\epsilon)=\lceil2/\epsilon\rceil$. For Theorem 1.14 set $p=K(\epsilon)$, $n=p^2(k-1)+1$ and
--   $$
--   H(k,\epsilon)=\sum_{i=0}^{n-1}p^{2i}.
--   $$
--   For Theorem 5.2 define
--   $$
--   T(t,\epsilon)=\sum_{i=0}^{t-1}K(\epsilon)^i.
--   $$
--   These are computed natural numbers independent of the ambient sets and function. On $k\ge1$, $0<\epsilon<1/2$, the first theorem's height equals $(p^{2n}-1)/(p^2-1)$; on $0<\epsilon<1$, the second equals $(K^t-1)/(K-1)$. Both denominators are positive on their stated domains. Finite sums preserve the case $pq=1$, where $t_k=k$, without dividing by zero. They are the source's exact heights, not extraction assumptions or oracle parameters.
--
--   **Formalization Note** Empty finite sums are zero outside the positive-length theorem domains. The ceiling and natural subtraction are total operations; every consuming theorem imposes the domain on which they agree with the source. Theorem 1.14 uses the proof's parameter $\epsilon/2$, so $p=\lceil2/\epsilon\rceil$.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), pp. 16, 18–19, Lemma 4.3, proof of Theorem 1.14 and footnote 7, Theorem 5.2

import Mathlib

namespace ConantTerry.Orders.Supplement

/-- Lemma 4.3, p.16: exact geometric-sum height, also valid at p*q=1. -/
def protoHeight (p q k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (p * q) ^ i

/-- Theorem 5.2, p.19, and Theorem 1.14 after ε/2 substitution, p.18. -/
noncomputable def partitionCount (ε : ℝ) : ℕ := ⌈2 / ε⌉₊

/-- Theorem 1.14, p.18 and footnote 7: p=ceil(2/ε), n=p²(k-1)+1.
At the stated domain k≥1 and 0<ε<1/2 this equals (p^(2*n)-1)/(p²-1). -/
noncomputable def tightHeight (k : ℕ) (ε : ℝ) : ℕ :=
  let p := partitionCount ε
  ∑ i ∈ Finset.range (p ^ 2 * (k - 1) + 1), p ^ (2 * i)

/-- Theorem 5.2: the finite sum equals (K^t-1)/(K-1) when 0<ε<1.
No division or minimum of an empty set is used to define a height. -/
noncomputable def agnosticHeight (t : ℕ) (ε : ℝ) : ℕ :=
  ∑ i ∈ Finset.range t, partitionCount ε ^ i

end ConantTerry.Orders.Supplement


