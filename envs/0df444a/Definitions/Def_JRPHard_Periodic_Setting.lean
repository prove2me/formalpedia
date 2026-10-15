-- Prove2me | Definitions.Def_JRPHard_Periodic_Setting
-- name    : JRPHard_Periodic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:53.672246+00:00
-- url     : https://prove2.me/theorems/710a3a65-8785-4d38-9b41-8d2bc51f3628
-- title:
--   §1.1 and §2.2, pp. 2, 10–11 — EOQ cost, the two-item periodic JRP objective (3), optimal solutions, the instance of Lemma 2 and problem (4)
-- statement:
--   This file fixes the objects of the reduction from integer factorization to the two-item **periodic joint replenishment problem** (JRP).
--
--   1. **EOQ cost** (imported from the aperiodic setting file). An item with ordering cost $K$ and holding cost $H$, replenished every $q$ time units ($q$ a positive integer), costs
--   $$\mathrm{EOQ}_{K,H}(q) = \frac{K}{q} + Hq.$$
--   2. **Periodic JRP, objective (3).** Two items with parameters $(K_1,H_1)$ and $(K_2,H_2)$ are replenished with periods $q_1, q_2 \in \mathbb{Z}^+$; a joint ordering cost $K_0$ is incurred every $\gcd(q_1,q_2)$ time units. The objective is
--   $$\mathrm{JRP}(q_1,q_2) = \mathrm{EOQ}_{K_1,H_1}(q_1) + \mathrm{EOQ}_{K_2,H_2}(q_2) + \frac{K_0}{\gcd(q_1,q_2)}.$$
--   3. **Optimal solution** (imported from the aperiodic setting file). A pair $(q_1,q_2)$ of positive integers is optimal for an objective $f$ if $f(q_1,q_2) \le f(a,b)$ for all positive integers $a,b$.
--   4. **The instance of Lemma 2.** For a natural number $M$: $K_0 = M$, $K_1 = 0$, $H_1 = 1$, $H_2 = M(M+1)$, $K_2 = M^3(M+1)$. The coefficients are natural numbers; the cost of this instance is $\mathrm{JRP}_M(q_1,q_2)$, and item 2's EOQ cost in it is $\mathrm{EOQ}_2(q) = \mathrm{EOQ}_{M^3(M+1),\,M(M+1)}(q)$.
--   5. **Problem (4).** The single-variable objective obtained after fixing $q_2 = M$:
--   $$\frac{M}{\gcd(q,M)} + q, \qquad q \in \mathbb{Z}^+.$$
--
--   These are the objects about which Lemma 2 and the steps of its proof are stated.
--
--   **Formalization Note** Periods are natural numbers cast to $\mathbb{R}$; every theorem quantifies over positive periods only, because in Lean $K/0 = 0$ and $\gcd(0,M) = M$. The paper derives the joint cost $K_0/\gcd(q_1,q_2)$ from the joint cycle $\rho$ ("one has $\rho = \gcd(q_1,q_2)$ for every optimal solution", p. 10, with $B = 1$); objective (3) is the model the paper minimizes, so it is defined directly. The model's standing assumption $K_0 > 0$ is a property of the instance, asserted in Lemma 2.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 2 (§1.1, EOQ), p. 10 (§2.2, objective (3)), p. 11 (instance and problem (4))

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Periodic

/-- Objective (3), p. 10, of the two-item periodic JRP (with `B = 1`):
`JRP(q₁, q₂) = EOQ_{K₁,H₁}(q₁) + EOQ_{K₂,H₂}(q₂) + JC_{K₀}(q₁, q₂)`, with the joint ordering cost
`JC_{K₀}(q₁, q₂) = K₀ / gcd(q₁, q₂)`. -/
noncomputable def periodicCost (K₀ K₁ K₂ H₁ H₂ : ℝ) (q₁ q₂ : ℕ) : ℝ :=
  JRPHard.Aperiodic.eoq K₁ H₁ q₁ + JRPHard.Aperiodic.eoq K₂ H₂ q₂ + K₀ / (Nat.gcd q₁ q₂ : ℝ)

/-- Joint ordering cost of the instance of Lemma 2 (p. 11): `K₀ = M`. -/
def coefK0 (M : ℕ) : ℕ := M

/-- Ordering cost of item 1 in the instance of Lemma 2 (p. 11): `K₁ = 0`. -/
def coefK1 : ℕ := 0

/-- Holding cost of item 1 in the instance of Lemma 2 (p. 11): `H₁ = 1`. -/
def coefH1 : ℕ := 1

/-- Holding cost of item 2 in the instance of Lemma 2 (p. 11): `H₂ = M (M + 1)`. -/
def coefH2 (M : ℕ) : ℕ := M * (M + 1)

/-- Ordering cost of item 2 in the instance of Lemma 2 (p. 11): `K₂ = M³ (M + 1)`. -/
def coefK2 (M : ℕ) : ℕ := M ^ 3 * (M + 1)

/-- The two-item periodic instance of Lemma 2 (p. 11): objective (3) with `K₀ = M`, `K₁ = 0`,
`H₁ = 1`, `H₂ = M (M + 1)`, `K₂ = M³ (M + 1)`. -/
noncomputable def lemma2Cost (M : ℕ) : ℕ → ℕ → ℝ :=
  periodicCost (coefK0 M : ℝ) (coefK1 : ℝ) (coefK2 M : ℝ) (coefH1 : ℝ) (coefH2 M : ℝ)

/-- Item 2's EOQ cost in the instance of Lemma 2: `EOQ_{K₂,H₂}(q)` with `K₂ = M³ (M + 1)`,
`H₂ = M (M + 1)`. -/
noncomputable def eoq2 (M q : ℕ) : ℝ := JRPHard.Aperiodic.eoq (coefK2 M : ℝ) (coefH2 M : ℝ) q

/-- The objective of problem (4), p. 11: `M / gcd(q, M) + q`. -/
noncomputable def obj4 (M q : ℕ) : ℝ := (M : ℝ) / (Nat.gcd q M : ℝ) + (q : ℝ)

end JRPHard.Periodic


