-- Prove2me | Definitions.Def_JRPHard_RangeDiv_Setting
-- name    : JRPHard_RangeDiv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:21.643629+00:00
-- url     : https://prove2.me/theorems/0148382f-8203-4834-b54d-121eb59ea2e0
-- title:
--   §2.2, §3 and §3.1, pp. 10–14 — EOQ cost, the periodic JRP objective (3), RangeDivisor, the instance JRP_{M,U,L}, its threshold, and problem (5)
-- statement:
--   This file fixes the objects of the reduction from RangeDivisor to the two-item periodic joint replenishment problem (JRP). Items 1 and 2 below, and the item-2 coefficients of item 4, are imported from the aperiodic and periodic setting files; the rest is defined here.
--
--   1. **EOQ cost.** An item with ordering cost $K$ and holding cost $H$, replenished every $q$ periods ($q$ a positive integer), costs per unit time
--   $$\mathrm{EOQ}_{K,H}(q) = \frac{K}{q} + Hq.$$
--   2. **Periodic two-item JRP (objective (3)).** For ordering periods $q_1, q_2 \in \mathbb{Z}_+$ and a joint ordering cost $K_0$,
--   $$\mathrm{JRP}(q_1,q_2) = \mathrm{EOQ}_{K_1,H_1}(q_1) + \mathrm{EOQ}_{K_2,H_2}(q_2) + \frac{K_0}{\gcd(q_1,q_2)}.$$
--   3. **RangeDivisor.** An instance is a triple of integers $M \ge U \ge L > 0$ with $L + U < 2\sqrt{2LU}$; it is a yes-instance when $M$ has a divisor $q$ with $L \le q \le U$.
--   4. **The instance $\mathrm{JRP}_{M,U,L}$.** Objective (3) with
--   $$K_0 = LU,\quad K_1 = 0,\quad H_1 = 1,\quad K_2 = M^3(M+1),\quad H_2 = M(M+1).$$
--   The item-2 coefficients are those of Lemma 2 of the paper, which the proof of Lemma 3 invokes.
--   5. **The threshold** $z_{M,L,U} = L + U + 2M^2(M+1)$, which is $L + U + \mathrm{EOQ}_{K_2,H_2}(M)$.
--   6. **Problem (5).** The objective of the reduced one-item problem, $\dfrac{LU}{\gcd(q,M)} + q$.
--   7. **The comparison function** $f(x) = LU/x + x$ for real $x > 0$, used in the proof of Lemma 3.
--
--   These are the objects that Lemma 3 and its proof steps are stated about.
--
--   **Formalization Note** Periods are natural numbers. Every statement that quantifies over a period also assumes it is positive, because Lean sets $K/0 = 0$ and $\gcd(0, M) = M$. Costs are real numbers, and the integer coefficients are natural-number expressions cast to $\mathbb{R}$. Objective (3) is the model itself, in the form the paper derives for $K_0 > 0$ (where the joint period is $\gcd(q_1, q_2)$ at every optimum). The paper leaves $K_2, H_2$ as "sufficiently large values … as in … Lemma 2". Here they are pinned to Lemma 2's values. The threshold adds item 2's cost at $q_2 = M$ to the printed bound $L + U$; see the goal theorem.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 2 (EOQ), p. 10 (objective (3)), p. 11 (K₂, H₂ of Lemma 2), p. 12 (RangeDivisor), p. 13 (§3.1, threshold z_{M,L,U}, instance JRP_{M,U,L}, problem (5)), p. 14 (proof of Lemma 3, f(q))

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting
import Definitions.Def_JRPHard_Periodic_Setting

namespace JRPHard.RangeDiv

/-- RangeDivisor's instance condition (p. 12): integers `M ≥ U ≥ L > 0` with
`L + U < 2 √(2 L U)`. -/
def IsRangeDivisorInstance (M L U : ℕ) : Prop :=
  0 < L ∧ L ≤ U ∧ U ≤ M ∧ ((L : ℝ) + U < 2 * Real.sqrt (2 * (L : ℝ) * U))

/-- RangeDivisor's yes-instances (p. 12): `M` has a divisor in the interval `[L, U]`. -/
def HasDivisorIn (M L U : ℕ) : Prop := ∃ q : ℕ, q ∣ M ∧ L ≤ q ∧ q ≤ U

/-- Joint ordering cost of `JRP_{M,U,L}` (p. 13): `K₀ = L U`. -/
def coefK0 (L U : ℕ) : ℕ := L * U

/-- The two-item periodic instance `JRP_{M,U,L}` (pp. 13–14): objective (3) with
`K₀ = L U`, `K₁ = 0`, `H₁ = 1`, `K₂ = M³ (M + 1)`, `H₂ = M (M + 1)`. -/
noncomputable def rangeCost (M L U : ℕ) : ℕ → ℕ → ℝ :=
  JRPHard.Periodic.periodicCost (coefK0 L U : ℝ) 0 (JRPHard.Periodic.coefK2 M : ℝ) 1 (JRPHard.Periodic.coefH2 M : ℝ)

/-- The threshold `z_{M,L,U} = L + U + EOQ_{K₂,H₂}(M) = L + U + 2 M² (M + 1)` (§3.1, p. 13). -/
def threshold (M L U : ℕ) : ℕ := L + U + 2 * M ^ 2 * (M + 1)

/-- The objective of the reduced problem (5), p. 13: `L U / gcd(q, M) + q`. -/
noncomputable def obj5 (M L U q : ℕ) : ℝ :=
  ((L * U : ℕ) : ℝ) / (Nat.gcd q M : ℝ) + (q : ℝ)

/-- The convex comparison function of the proof of Lemma 3 (p. 14):
`f(x) = K₀ / x + x` for `x > 0`, with `K₀ = L U`. -/
noncomputable def fConv (L U : ℕ) (x : ℝ) : ℝ := ((L * U : ℕ) : ℝ) / x + x

end JRPHard.RangeDiv


