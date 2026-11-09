-- Prove2me | Definitions.Def_DSICCompComp_spWins
-- name    : DSICCompComp_spWins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:19.7682+00:00
-- url     : https://prove2.me/theorems/06d4189e-feda-47ed-8a7e-2d8e69b1621b
-- title:
--   Winner of the second-price auction with reserve $a$
-- statement:
--   On each item $j \notin [\ell]$ the mechanism $M$ runs Myerson's optimal auction for $D$, which is a **second-price auction with reserve $a$**: bidder $i$ wins item $j$ if $v_{ij} \ge a$ and $v_{ij}$ is a highest bid for $j$, ties being broken in favour of the lowest index.
--
--   **Formalization Note** For the distribution of Section 3.2 the virtual value is $0$ on $[ab, a)$ and $a-1$ above $a$, so the item is sold exactly when some value exceeds $a$; any reserve in $[ab, a]$ earns the same revenue, and the reserve $a$ is chosen here.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, p.12 (pdf p.13)

import Mathlib

open scoped NNReal

namespace DSICCompComp

/-- The winner rule of the second-price auction with reserve `a` used by the mechanism `M` of §3.3
on each item `j ∉ [ℓ]` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers
over Independent Items*, STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
§3.3, p.12 (pdf p.13): the remaining items are sold "separately using Myerson's optimal
auction"): bidder `i` wins item `j` iff `v_{ij} ≥ a`, `v_{ij}` is a highest bid for `j`, and
every bidder of lower index bids strictly less.

**Formalization Note** For the regular distribution `D` of §3.2 the virtual value is `0` on
`[ab, a)` and `a − 1` above `a`, so Myerson's optimal auction is the second-price auction with
reserve `a` (any reserve in `[ab, a]` earns the same); ties are broken towards the lowest index. -/
def spWins {n m : ℕ} (a : ℝ) (i : Fin n) (j : Fin m) (v : Fin n → Fin m → ℝ≥0) : Prop :=
  a ≤ (v i j : ℝ) ∧ (∀ h, v h j ≤ v i j) ∧ ∀ h, h < i → v h j < v i j

end DSICCompComp


