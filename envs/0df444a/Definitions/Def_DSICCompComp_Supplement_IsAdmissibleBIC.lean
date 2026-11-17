-- Prove2me | Definitions.Def_DSICCompComp_Supplement_IsAdmissibleBIC
-- name    : DSICCompComp_Supplement_IsAdmissibleBIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:21:55.539207+00:00
-- url     : https://prove2.me/theorems/331fbb25-887b-48cc-8ba6-dab8d796fe3b
-- title:
--   The class $\mathcal B(D)$ of BIC/BIR mechanisms
-- statement:
--   $\mathcal B(D)$ is the set of mechanisms for $n$ additive bidders over $m$ items that are BIC and BIR with respect to $D$ and feasible: for every value profile $v$, $0 \le x_{ij}(v) \le 1$ for all $i, j$, and $\sum_i x_{ij}(v) \le 1$ for every item $j$ (each item is allocated at most once).
--
--   This is the mechanism class over which the optimal BIC revenue $\mathrm{Rev}^{\mathcal B}_n(D)$ is taken.
--
--   **Formalization Note** Regularity requirements are added: payments are measurable, mirroring the published DSIC class `IsAdmissibleDS`, and the BIC/BIR definitions themselves require the relevant ex-post utility integrands to be integrable against $D^n$. These conditions make the expected revenue and interim expectations meaningful and can only shrink $\mathcal B(D)$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, pp.5–6 (pdf pp.6–7)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_IsBIC
import Definitions.Def_DSICCompComp_Supplement_IsBIR

open MeasureTheory
open scoped NNReal

namespace DSICCompComp

namespace Supplement

/-- The class `B(D)` of mechanisms that are BIC/BIR with respect to `D`
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Section 2, pp.5–6 (pdf pp.6–7)): feasible (ex-post allocation probabilities in `[0,1]`, each item
allocated at most once), BIC and BIR with respect to `D`.

**Formalization Note** Measurable payments are required, mirroring the published
`MultiItemRev.MultiBuyer.IsAdmissibleDS`, so that expected revenue is defined. Integrability of
the interim-utility integrands is part of `IsBIC` and `IsBIR` themselves. These regularity
requirements shrink `B(D)`. -/
def IsAdmissibleBIC {n m : ℕ} (D : Fin m → ProbabilityMeasure ℝ≥0)
    (M : MultiItemRev.MultiBuyer.MechanismN n (Fin m)) : Prop :=
  MultiItemRev.MultiBuyer.IsFeasibleN M ∧ IsBIC D M ∧ IsBIR D M ∧
    ∀ i, Measurable fun v => M.s v i

end Supplement

end DSICCompComp


