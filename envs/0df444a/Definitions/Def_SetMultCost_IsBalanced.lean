-- Prove2me | Definitions.Def_SetMultCost_IsBalanced
-- name    : SetMultCost_IsBalanced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:59.8052+00:00
-- url     : https://prove2.me/theorems/4c8f9abd-c122-43e4-86f0-99c7d3d2c4c6
-- title:
--   Balanced partition
-- statement:
--   Let $n=2^k$ and $n^\alpha=2^\ell$. A set $\mathcal P\subseteq[d]$, with complement $\mathcal N$, is **balanced** when every prefix $[t]$ has
--
--   $$\big|\ell\cdot|\mathcal P\cap[t]|-k\cdot|\mathcal N\cap[t]|\big|\le k.$$
--
--   **Formalization Note** This condition does not appear in the paper. It is what corrects Proposition 2.6, which names no partition and is false for an arbitrary one; see that item.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Correction of Proposition 2.6, p.10

import Mathlib

namespace SetMultCost

/-- **A balanced partition.** With `n = 2^k`, `n^α = 2^ℓ`: every prefix `[t]` of the parts has
imbalance `|ℓ · |P ∩ [t]| − k · |N ∩ [t]|| ≤ k`, where `N` is the complement of `P`.

**Formalization Note.** This condition is not in the paper; it is the correction of Proposition 2.6
(Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.10), which names no partition and is false for arbitrary `π`. See `proposition_2_6`. -/
def IsBalanced {d : ℕ} (k ℓ : ℕ) (P : Finset (Fin d)) : Prop :=
  ∀ t : ℕ, t ≤ d →
    |(ℓ : ℤ) * (P.filter fun i => i.1 < t).card - (k : ℤ) * (Pᶜ.filter fun i => i.1 < t).card|
      ≤ (k : ℤ)

end SetMultCost


