-- Prove2me | Definitions.Def_OnlineMatchFrameworks_PatienceModels
-- name    : OnlineMatchFrameworks_PatienceModels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:32.273408+00:00
-- url     : https://prove2.me/theorems/16cfa50b-4cd1-4322-a252-f99cd6131de1
-- title:
--   Patience models as survival functions; the budget $\mathbb E[\theta_v]$
-- statement:
--   The three patience models of the paper, written as survival functions.
--
--   1. **Arbitrary patience law.** If $q_v(k)=\Pr[\theta_v\ge k]$, then $S_v(l)=q_v(|l|+1)$.
--   2. **Deterministic patience.** $q_v(k)=1$ for $k\le\theta_v$ and $q_v(k)=0$ otherwise.
--   3. **Item hazard rates.** If item $u$ makes $v$ leave with probability $r_{u,v}$ after a failed offer, then $S_v(l)=\prod_{u\in l}(1-r_{u,v})$.
--
--   The expected patience, the right side of (1c), is
--   $$
--   \mathbb E[\theta_v]=\sum_{k\ge 1}q_v(k)\in[0,\infty].
--   $$
--
--   **Formalization Note** The tail form admits $\theta_v=0$ and $\theta_v=\infty$.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §3, p.11; §5.1, pp.22–23; §5.2, pp.23–25; LP (1), p.15

import Mathlib

open scoped ENNReal

namespace OnlineMatchFrameworks

/-- **Survival function of an item-independent patience law.** arXiv:1907.03963v6, §3, pp.11–12,
and §5.2, pp.23–25. Here `q v k = Pr[θ_v ≥ k]` is the tail of the patience `θ_v`, so the customer is
available for the `(|l|+1)`-st probe with probability `q v (|l| + 1)`.

**Formalization Note.** The tail is assumed nonnegative and antitone with `q v 0 = 1`. This admits
`θ_v = 0` (`q v 1 = 0`) and `θ_v = ∞` (positive limit). -/
def tailSurvival {U V : Type*} (q : V → ℕ → ℝ) (v : V) (l : List U) : ℝ :=
  q v (l.length + 1)

/-- **Tail of a deterministic patience.** arXiv:1907.03963v6, §3, p.11: `q k = 1` if `k ≤ θ_v`, and
`0` otherwise, for the deterministic patience value `θ_v`. -/
def deterministicTail {V : Type*} (θ : V → ℕ) (v : V) (k : ℕ) : ℝ :=
  if k ≤ θ v then 1 else 0

/-- **Survival function of the item-dependent hazard rate model.** arXiv:1907.03963v6, §5.1, pp.22–23:
item `u`, if seen by customer `v` and undesired, makes the customer leave with probability
`r u v`, independently; `v` survives the failed probes of `l` with probability
`∏_{u ∈ l} (1 - r u v)`. -/
def hazardSurvival {U V : Type*} (r : U → V → ℝ) (v : V) (l : List U) : ℝ :=
  (l.map fun u => 1 - r u v).prod

/-- **Expected patience `E[θ_v]`, the right side of (1c).** arXiv:1907.03963v6, LP (1), p.15:
`E[θ_v] = ∑_{k ≥ 1} Pr[θ_v ≥ k]`.

**Formalization Note.** The value lies in `ℝ≥0∞`, since `E[θ_v]` may be infinite. It is not
truncated. -/
noncomputable def tailBudget {V : Type*} (q : V → ℕ → ℝ) (v : V) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (q v (k + 1))

end OnlineMatchFrameworks


