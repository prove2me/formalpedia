-- Prove2me | Definitions.Def_DSICCompComp_amObj
-- name    : DSICCompComp_amObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:17.838508+00:00
-- url     : https://prove2.me/theorems/1235898d-fd43-48a2-b808-1cfcf72f0791
-- title:
--   Affine-maximizer objective
-- statement:
--   For a value profile $v$ and an allocation $S = (S_1,\dots,S_n)$, the objective of the affine maximizer with parameters $a, \varepsilon, t, T$ is
--   $$
--   \varepsilon\sum_{i=1}^{r}\sum_{j\in S_i}(v_{ij}-a) \;+\; \sum_{i=r+1}^{n}\Bigl(\sum_{j\in S_i}(v_{ij}-a) - t\cdot\mathbb 1(|S_i|=1) - T\cdot\mathbb 1(|S_i|=2)\Bigr).
--   $$
--   Reserve bidders carry weight $\varepsilon$; non-reserve bidders pay an allocation-dependent penalty $t$ for a single item and $T$ for a pair. A bidder with $S_i = \varnothing$ contributes $0$.
--
--   **Formalization Note** Reserve bidders are $i < r$ (0-based).
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, p.11 (pdf p.12)

import Mathlib

open scoped NNReal

namespace DSICCompComp

/-- The objective of the affine maximizer of §3.3 (Ryu–Weinberg–Xue, *The DSIC Competition
Complexity of Additive Buyers over Independent Items*, STOC 2027 submission, manuscript of
Nov. 3, 2026, sha256 bf61bfdb…, §3.3, p.11 (pdf p.12)): for a value profile `v` and an allocation
`S = (S_1, …, S_n)`,
`ε ∑_{i=1}^r ∑_{j ∈ S_i} (v_{ij} − a) + ∑_{i=r+1}^n (∑_{j ∈ S_i} (v_{ij} − a) − t·𝟙(|S_i| = 1) − T·𝟙(|S_i| = 2))`.

**Formalization Note** 0-based bidders: the reserve bidders `1, …, r` are `i : Fin n` with
`i < r`. A bidder with `S_i = ∅` contributes `0`, so the objective restricted to allocations with
`S_i = ∅` is the objective "without bidder `i`". -/
def amObj {n m : ℕ} (r : ℕ) (a ε t T : ℝ) (v : Fin n → Fin m → ℝ≥0)
    (S : Fin n → Finset (Fin m)) : ℝ :=
  ∑ i : Fin n,
    if i.val < r then ε * ∑ j ∈ S i, ((v i j : ℝ) - a)
    else (∑ j ∈ S i, ((v i j : ℝ) - a)) - (if (S i).card = 1 then t else 0) -
      (if (S i).card = 2 then T else 0)

end DSICCompComp


