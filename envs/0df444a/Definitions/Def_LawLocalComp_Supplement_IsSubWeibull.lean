-- Prove2me | Definitions.Def_LawLocalComp_Supplement_IsSubWeibull
-- name    : LawLocalComp_Supplement_IsSubWeibull
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:07:18.076216+00:00
-- url     : https://prove2.me/theorems/6bdfd910-3515-49fd-9d81-086c02558bba
-- title:
--   The activity-normalized sub-Weibull class (Definition 9.1)
-- statement:
--   Fix rational $\alpha > 0$ and $A \ge 1$. For a nonconstant finite nonnegative law $X$ put $b = \min \operatorname{supp} X$, $R = X - b$, $p = P(R > 0)$ and $\nu = \mathbb E[R \mid R > 0]$. $X$ satisfies the **activity-normalized sub-Weibull promise** if
--   $$
--   P(R \ge A\nu u \mid R > 0) \le 2^{-u^\alpha} \qquad (u \ge 1). \tag{44}
--   $$
--   Point masses are included in the class separately.
--
--   The class constrains only the tail of the active part of $X$, relative to its activity-normalized mean $\nu$; it requires no lattice support and no hazard-rate structure. Theorem 9.3 determines the sharp atom order for this class.
--
--   **Formalization Note** For nonconstant $X$, $p > 0$ and $A\nu u > 0$, so $\{R \ge A\nu u\} \subseteq \{R > 0\}$ and (44) is written as $P(X - b \ge A\nu u) \le 2^{-u^\alpha}\,p$. $b$, $p$ and $\nu$ are the base mission's published `baseline`, `activity` and `activeMean`; $u^\alpha$ is the real power.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Definition 9.1, (44), p.16

import Mathlib
import Definitions.Def_LawLocalComp_baseline
import Definitions.Def_LawLocalComp_activeMean

namespace LawLocalComp

namespace Supplement

/-- **The activity-normalized sub-Weibull class (Definition 9.1).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Definition 9.1, (44), p.16: "Fix rational α > 0, A ≥ 1. For nonconstant X, put b = min supp X,
R = X − b, p = P(R > 0), ν = E[R | R > 0]. The activity-normalized sub-Weibull promise is
P(R ≥ Aνu | R > 0) ≤ 2^{−u^α} (u ≥ 1). Point masses are included separately."

`IsSubWeibull α A X`: `X` is a point mass, or for every real `u ≥ 1`,
`P(X − b ≥ A ν u) ≤ 2^{−u^α} · p` with `b = baseline X`, `p = activity X b = P(X > b)` and
`ν = activeMean X b = E[X − b | X > b]`.

**Formalization Note.** For a nonconstant law `p > 0` and `ν > 0`, so `A ν u > 0` and the event
`{R ≥ A ν u}` lies inside `{R > 0}`; the conditional bound (44) is therefore the unconditional bound
multiplied by `p`. `u^α` is `Real.rpow`. The support need not be a lattice. -/
def IsSubWeibull (α A : ℚ) (X : Law) : Prop :=
  (∃ t : ℝ, X.w = Finsupp.single t 1) ∨
    ∀ u : ℝ, 1 ≤ u →
      ∑ x ∈ X.w.support with (A : ℝ) * activeMean X (baseline X) * u ≤ x - baseline X, X.w x ≤
        (2 : ℝ) ^ (-(u ^ (α : ℝ))) * activity X (baseline X)

end Supplement

end LawLocalComp


