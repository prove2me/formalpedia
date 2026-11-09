-- Prove2me | Definitions.Def_DSICCompComp_spPrice
-- name    : DSICCompComp_spPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:04.959473+00:00
-- url     : https://prove2.me/theorems/bf02eef4-1f06-4508-931a-35816523651a
-- title:
--   Price in the second-price auction with reserve $a$
-- statement:
--   The winner $i$ of item $j \notin [\ell]$ in the second-price auction with reserve $a$ pays
--   $$
--   \max\Bigl\{a,\ \max_{h\ne i} v_{hj}\Bigr\},
--   $$
--   the larger of the reserve and the highest competing bid.
--
--   **Formalization Note** With no other bidder the inner maximum is $0$ (values are nonnegative), so the price is $\max\{a, 0\}$, the least winning bid.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, p.12 (pdf p.13)

import Mathlib

open scoped NNReal

namespace DSICCompComp

/-- The price paid by the winner `i` of item `j` in the second-price auction with reserve `a`
used by the mechanism `M` of §3.3 on the items `j ∉ [ℓ]` (Ryu–Weinberg–Xue, *The DSIC
Competition Complexity of Additive Buyers over Independent Items*, STOC 2027 submission,
manuscript of Nov. 3, 2026, sha256 bf61bfdb…, §3.3, p.12 (pdf p.13)):
`max{a, max_{h ≠ i} v_{hj}}`, the larger of the reserve and the highest competing bid.

**Formalization Note** The maximum over the other bidders is a `Finset.sup` in `ℝ≥0`, equal to
`0` when there is no other bidder; values are nonnegative, so the price is then `max{a, 0}`, the
least winning bid. -/
noncomputable def spPrice {n m : ℕ} (a : ℝ) (i : Fin n) (j : Fin m)
    (v : Fin n → Fin m → ℝ≥0) : ℝ :=
  max a (((Finset.univ.erase i).sup fun h => v h j : ℝ≥0) : ℝ)

end DSICCompComp


