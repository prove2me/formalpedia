-- Prove2me | Definitions.Def_DSICCompComp_sRev
-- name    : DSICCompComp_sRev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:13.477282+00:00
-- url     : https://prove2.me/theorems/0e0a7483-8742-4d2a-95f0-618c8b6c4752
-- title:
--   Selling-separately revenue $\mathrm{SRev}_n(D)$
-- statement:
--   For $n$ iid additive bidders with values drawn from $D = D_1\times\cdots\times D_m$, $\mathrm{SRev}_n(D)$ is the revenue of selling each item separately using Myerson's optimal auction:
--   $$
--   \mathrm{SRev}_n(D) = \sum_{j=1}^m \mathrm{Rev}_n(D_j),
--   $$
--   where $\mathrm{Rev}_n(D_j)$ is the optimal revenue from selling item $j$ alone to $n$ bidders whose values for it are iid from $D_j$. When $D$ is regular, each item is sold by a second-price auction with a reserve that depends on $D_j$.
--
--   **Formalization Note** $\mathrm{Rev}_n(D_j)$ is the published `RevDS` of the one-good profile law $D_j^{\otimes n}$: the supremum over one-good DSIC/IR mechanisms with measurable payments. It equals the revenue of Myerson's optimal auction, which belongs to that class, while no BIC/BIR mechanism earns more.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, p.6 (pdf p.7)

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- `SRev_n(D)`, the revenue of selling each item separately using Myerson's optimal auction to
`n` bidders with values drawn iid from `D = D_1 × ⋯ × D_m` (Ryu–Weinberg–Xue, *The DSIC
Competition Complexity of Additive Buyers over Independent Items*, STOC 2027 submission,
manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Section 2, p.6 (pdf p.7)):
`SRev_n(D) = ∑_j Rev_n(D_j)`, where `Rev_n(D_j)` is the optimal revenue from selling item `j`
alone to `n` bidders with iid values from `D_j`.

**Formalization Note** The one-item optimum is the published
`MultiItemRev.MultiBuyer.RevDS` of the one-good profile law `D_j^n` (`oneGoodN`): the supremum
over one-good DSIC/IR mechanisms with measurable payments. It equals the revenue of Myerson's
optimal auction, which belongs to this class, while no BIC/BIR mechanism (in particular no
mechanism of the class) earns more. -/
noncomputable def sRev (n : ℕ) {m : ℕ} (D : Fin m → ProbabilityMeasure ℝ≥0) : ℝ≥0∞ :=
  ∑ j : Fin m, MultiItemRev.MultiBuyer.RevDS
    (MultiItemRev.MultiBuyer.oneGoodN (Measure.pi fun _ : Fin n => (D j : Measure ℝ≥0)))

end DSICCompComp


