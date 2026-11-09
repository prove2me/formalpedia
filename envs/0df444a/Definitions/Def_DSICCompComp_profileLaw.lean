-- Prove2me | Definitions.Def_DSICCompComp_profileLaw
-- name    : DSICCompComp_profileLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:05.240198+00:00
-- url     : https://prove2.me/theorems/bf8cd463-7d0a-4e9f-bb98-951d3f67d83c
-- title:
--   Value-profile law $(D_1\times\cdots\times D_m)^n$ of $n$ iid additive bidders
-- statement:
--   There are $n$ bidders and $m$ items. Each item $j$ has a value distribution $D_j$ on $[0,\infty)$, and each bidder $i$ draws her value $v_{ij}$ for item $j$ from $D_j$, independently over items and over bidders. The value profile $v = (v_{ij})_{i \le n,\, j \le m}$ therefore has law
--   $$
--   \Bigl(\prod_{j=1}^m D_j\Bigr)^{\otimes n}.
--   $$
--   All expectations $\mathbb E_v[\cdot]$ over value profiles in this mission are taken under this law.
--
--   **Formalization Note** Bidders are indexed by $\{0,\dots,n-1\}$ and items by $\{0,\dots,m-1\}$; $v_{ij}$ is bidder $i$'s value for item $j$, the index order of the published multi-buyer model. Each $D_j$ is a probability measure on $\mathbb R_{\ge 0}$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, p.5 (pdf p.6)

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- The law of the value profile `v = (v_{ij})` of `n` iid additive bidders over `m` independent
items (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent
Items*, STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Section 2, p.5
(pdf p.6)): each bidder `i` draws `v_i = (v_{i1}, …, v_{im})` from the product distribution
`D = D_1 × ⋯ × D_m`, independently of the other bidders; i.e. the law is `(D_1 × ⋯ × D_m)^n`.

**Formalization Note** Bidders are `Fin n` and items are `Fin m` (0-based); `v i j` is bidder
`i`'s value for item `j`, matching the index order of the published model
`MultiItemRev.MultiBuyer` (`x j i` = buyer `j`'s value for good `i`). Each marginal `D_j` is a
probability measure on `ℝ≥0`, and the bidder-iid profile law is a `Measure.pi`. -/
noncomputable abbrev profileLaw (n : ℕ) {m : ℕ} (D : Fin m → ProbabilityMeasure ℝ≥0) :
    Measure (Fin n → Fin m → ℝ≥0) :=
  Measure.pi fun _ : Fin n => Measure.pi fun j : Fin m => (D j : Measure ℝ≥0)

end DSICCompComp


