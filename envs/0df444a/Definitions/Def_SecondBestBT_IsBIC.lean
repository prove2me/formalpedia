-- Prove2me | Definitions.Def_SecondBestBT_IsBIC
-- name    : SecondBestBT_IsBIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:14.798977+00:00
-- url     : https://prove2.me/theorems/2aeba117-a6db-458e-ba3b-8a4019dee3c7
-- title:
--   Bayesian incentive compatibility on $T$
-- statement:
--   A mechanism is **Bayesian incentive compatible** (BIC) on the type set $T$ if truth-telling maximizes each agent's interim expected utility: for all $b,b',s,s'\in T$,
--   $$
--   u_B(b,b)\ge u_B(b,b'),\qquad u_S(s,s)\ge u_S(s,s').
--   $$
--
--   **Formalization Note** The inequalities are required at every type of $T$, not only on the support of the priors and not almost everywhere. The type set is a parameter: $T=[0,1]$ in Section 3 of the paper and $T=[0,\infty)$ for the main theorem.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.4

import Mathlib
import Definitions.Def_SecondBestBT_uB
import Definitions.Def_SecondBestBT_uS

open MeasureTheory

namespace SecondBestBT

/-- Bayesian incentive compatibility on the type set `T` (Liu–Qin–Ren–Wang, arXiv:2606.03849,
held version sha256 17184930…, Section 2, p.4): for all true types and reports
`b, b', s, s' ∈ T`, `u_B(b, b) ≥ u_B(b, b')` and `u_S(s, s) ≥ u_S(s, s')`.

**Formalization Note** The constraints hold at **every** type of `T`, not only on the support of
the priors and not almost everywhere, exactly as the paper's "for any b, b′, s, s′ ∈ [0, 1]". The
type set is a parameter: `[0, 1]` in Section 3, `[0, ∞)` for the main theorem. -/
def IsBIC (T : Set ℝ) (μS μB : Measure ℝ) (M : Mechanism) : Prop :=
  (∀ b ∈ T, ∀ b' ∈ T, uB μS M b b' ≤ uB μS M b b) ∧
  (∀ s ∈ T, ∀ s' ∈ T, uS μB M s s' ≤ uS μB M s s)

end SecondBestBT


