-- Prove2me | Definitions.Def_DSICCompComp_optRevDSIC
-- name    : DSICCompComp_optRevDSIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:30:00.953407+00:00
-- url     : https://prove2.me/theorems/654394fb-7de6-4ef2-950f-da96a7130941
-- title:
--   Optimal DSIC/IR revenue $\mathrm{Rev}^{\mathcal D}_n(D)$
-- statement:
--   For $n$ iid additive bidders with values drawn from a product distribution $D$, the **optimal DSIC/IR revenue** is
--   $$
--   \mathrm{Rev}^{\mathcal D}_n(D) = \sup_{M \in \mathcal D} \mathrm{Rev}^M_n(D),
--   $$
--   where $\mathcal D$ is the set of dominant-strategy incentive compatible and individually rational mechanisms and $\mathrm{Rev}^M_n(D) = \mathbb E_v\bigl[\sum_i p_i(v)\bigr]$ is the expected revenue of $M$.
--
--   **Formalization Note** The supremum is the published `MultiItemRev.MultiBuyer.RevDS` of the profile law: over feasible mechanisms (ex-post allocation probabilities in $[0,1]$, each item allocated with total probability at most $1$) that are DSIC and IR at every profile in $\mathbb R_{\ge 0}^{n\times m}$ and have measurable payments. Revenues are taken in the extended reals and truncated at $0$ per mechanism, which does not change the supremum because the zero mechanism is admissible.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, p.6 (pdf p.7)

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model
import Definitions.Def_DSICCompComp_profileLaw

open MeasureTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- `Rev^𝒟_n(D)`, the revenue of the optimal DSIC/IR mechanism for `n` iid additive bidders with
values drawn from the product distribution `D` (Ryu–Weinberg–Xue, *The DSIC Competition
Complexity of Additive Buyers over Independent Items*, STOC 2027 submission, manuscript of
Nov. 3, 2026, sha256 bf61bfdb…, Section 2, p.6 (pdf p.7)):
`Rev^𝒟_n(D) := sup_{M ∈ 𝒟} Rev^M_n(D)`.

**Formalization Note** The supremum is the published `MultiItemRev.MultiBuyer.RevDS` over
feasible mechanisms (ex-post allocation probabilities in `[0,1]`, each item allocated at most
once) that are DSIC and IR at every value profile in `(ℝ≥0)^{n×m}` and have measurable
payments; revenue is `E[∑_i p_i(v)]` in `EReal`, truncated at `0` per mechanism (harmless, since
the zero mechanism is admissible). -/
noncomputable def optRevDSIC (n : ℕ) {m : ℕ} (D : Fin m → ProbabilityMeasure ℝ≥0) : ℝ≥0∞ :=
  MultiItemRev.MultiBuyer.RevDS (profileLaw n D)

end DSICCompComp


