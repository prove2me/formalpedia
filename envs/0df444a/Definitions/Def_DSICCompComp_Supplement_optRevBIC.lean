-- Prove2me | Definitions.Def_DSICCompComp_Supplement_optRevBIC
-- name    : DSICCompComp_Supplement_optRevBIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:22:51.261972+00:00
-- url     : https://prove2.me/theorems/76cd9159-d2e0-42f7-9ee5-b92b35644ef9
-- title:
--   $\mathrm{Rev}^{\mathcal B}_n(D)$, the optimal BIC/BIR revenue
-- statement:
--   For $n$ additive bidders whose value vectors are drawn iid from the product distribution $D = D_1 \times \cdots \times D_m$, the optimal BIC/BIR revenue is
--
--   $$
--   \mathrm{Rev}^{\mathcal B}_n(D) \;:=\; \sup_{M \in \mathcal B(D)} \mathrm{Rev}^M_n(D), \qquad \mathrm{Rev}^M_n(D) = \mathbb E_{v \sim D^n}\Big[\sum_{i=1}^n p_i(v)\Big].
--   $$
--
--   It is the benchmark that Theorem 4.1 compares with the optimal DSIC revenue $\mathrm{Rev}^{\mathcal D}_{n+c}(D)$.
--
--   **Formalization Note** Built exactly like the published `RevDS` and the base mission's `optRevDSIC`, so the two benchmarks are comparable in $[0, \infty]$: the supremum over `IsAdmissibleBIC D` mechanisms of the published expected revenue `expRevenueN` (an extended real, $\int^+ - \int^-$), truncated at $0$ per mechanism. The truncation does not change the supremum since the zero mechanism is admissible with revenue $0$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, p.6 (pdf p.7)

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model
import Definitions.Def_DSICCompComp_Supplement_IsAdmissibleBIC

open MeasureTheory
open scoped NNReal ENNReal

namespace DSICCompComp

namespace Supplement

/-- `Rev^B_n(D)`, the revenue of the optimal BIC/BIR mechanism for `n` bidders with values drawn
iid from the product distribution `D` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Section 2, p.6 (pdf p.7)): `Rev^B_n(D) := sup_{M ∈ B(D)} Rev^M_n(D)`, where
`Rev^M_n(D) = E_{v∼D^n}[∑_i p_i(v)]`.

**Formalization Note** Built exactly like the published `RevDS` (and the base mission's
`optRevDSIC`), so the two benchmarks are comparable in `ℝ≥0∞`: the supremum, over `IsAdmissibleBIC D`
mechanisms, of the published `expRevenueN (profileLaw n D) M` (an `EReal`, `∫⁺ − ∫⁻`) truncated at
`0`, which is harmless since the zero mechanism is admissible with revenue `0`. -/
noncomputable def optRevBIC (n : ℕ) {m : ℕ} (D : Fin m → ProbabilityMeasure ℝ≥0) : ℝ≥0∞ :=
  ⨆ (M : MultiItemRev.MultiBuyer.MechanismN n (Fin m)) (_ : IsAdmissibleBIC D M),
    (MultiItemRev.MultiBuyer.expRevenueN (profileLaw n D) M).toENNReal

end Supplement

end DSICCompComp


