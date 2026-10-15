-- Prove2me | Definitions.Def_JRPHard_Aperiodic_Setting
-- name    : JRPHard_Aperiodic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:40.943361+00:00
-- url     : https://prove2.me/theorems/259077ec-3a9c-43f8-8506-a2878089f176
-- title:
--   §1.1 and §2.1, pp. 2, 7–9 — EOQ cost, the two-item aperiodic JRP objective (1), optimal solutions, the instance of Lemma 1 and JRP^red
-- statement:
--   This file sets up the two-item **aperiodic joint replenishment problem** (JRP) of Schulz and Telha and the explicit instance used in their Lemma 1.
--
--   **EOQ cost.** An item with fixed ordering cost $K$ and holding cost rate $H$, replenished every $q$ time units, costs per unit of time
--   $$\mathrm{EOQ}_{K,H}(q) = \frac{K}{q} + Hq .$$
--   Periods are positive integers $q \in \mathbb Z^+$.
--
--   **Aperiodic two-item JRP (objective (1)).** Two items with data $(K_1,H_1)$ and $(K_2,H_2)$ receive a discount $K_0$ each time they are replenished together; with integer cycles $q_1, q_2$ the joint replenishments happen every $\mathrm{lcm}(q_1,q_2)$ time units, so the discount per unit time is $\mathrm{DC}(q_1,q_2;K_0) = K_0/\mathrm{lcm}(q_1,q_2)$ and the objective is
--   $$\mathrm{JRP}(q_1,q_2) = \mathrm{EOQ}_{K_1,H_1}(q_1) + \mathrm{EOQ}_{K_2,H_2}(q_2) - \frac{K_0}{\mathrm{lcm}(q_1,q_2)} .$$
--   The model requires $K_0 \le K_1, K_2$; this is a property of an instance and is asserted for the instance below by the goal theorem.
--
--   **Optimal solutions.** A pair $(q_1,q_2)$ is optimal for an objective $f$ if $q_1, q_2 \ge 1$ and $f(q_1,q_2) \le f(a,b)$ for all integers $a, b \ge 1$.
--
--   **The instance of Lemma 1.** For an integer $M$ the instance has
--   $$K_1 = K_0 = M(M-1), \qquad H_1 = 4, \qquad K_2 = M^3(M^2-1), \qquad H_2 = M(M^2-1).$$
--   $\mathrm{EOQ}_2(q)$ denotes item 2's cost $\mathrm{EOQ}_{K_2,H_2}(q)$ in this instance.
--
--   **The reduced objective (problem (2)).** With $q_2 = M$ fixed, item 1's part of the objective is
--   $$\mathrm{JRP}^{\mathrm{red}}(q) = M(M-1)\left(\frac1q - \frac{1}{\mathrm{lcm}(q,M)}\right) + 4q .$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Periods are natural numbers; every statement that quantifies over a period also requires it to be positive, because Lean evaluates $K/0$ as $0$ and $\mathrm{lcm}(0,M)$ as $0$. Costs are real numbers. The coefficients are natural numbers (`coefK0`, `coefK1`, `coefH1`, `coefK2`, `coefH2`) cast to reals, so that the size bound of Lemma 1 can be stated on $\mathbb N$; their natural-number subtractions $M-1$ and $M^2-1$ are exact for $M \ge 1$. In $\mathrm{JRP}^{\mathrm{red}}$ the factor $M-1$ is real subtraction.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 2 (§1.1, EOQ), p. 7 (§2.1, objective (1)), p. 8 (instance and problem (2)), p. 9 (proof of Lemma 1, JRP^red)

import Mathlib

namespace JRPHard.Aperiodic

/-- The EOQ cost of an item with ordering cost `K` and holding cost `H`, replenished every `q`
periods (§1.1, p. 2): `EOQ_{K,H}(q) = K / q + H q`. Periods are positive integers. -/
noncomputable def eoq (K H : ℝ) (q : ℕ) : ℝ := K / (q : ℝ) + H * (q : ℝ)

/-- Objective (1), p. 7, of the two-item aperiodic JRP:
`JRP(q₁, q₂) = EOQ_{K₁,H₁}(q₁) + EOQ_{K₂,H₂}(q₂) − DC(q₁, q₂; K₀)`, with the discount
`DC(q₁, q₂; K₀) = K₀ / lcm(q₁, q₂)`. The model's requirement `K₀ ≤ K₁, K₂` (p. 7) is a property of
an instance, not built into the objective. -/
noncomputable def aperiodicCost (K₀ K₁ K₂ H₁ H₂ : ℝ) (q₁ q₂ : ℕ) : ℝ :=
  eoq K₁ H₁ q₁ + eoq K₂ H₂ q₂ - K₀ / (Nat.lcm q₁ q₂ : ℝ)

/-- `(q₁, q₂)` is an optimal solution of `min { f(q₁, q₂) : q₁, q₂ ∈ ℤ⁺ }`: both periods are
positive integers and no pair of positive integers has a smaller objective value. -/
def IsOptimal (f : ℕ → ℕ → ℝ) (q₁ q₂ : ℕ) : Prop :=
  0 < q₁ ∧ 0 < q₂ ∧ ∀ a b : ℕ, 0 < a → 0 < b → f q₁ q₂ ≤ f a b

/-- Joint discount of the instance of Lemma 1 (p. 8): `K₀ = M (M − 1)`. -/
def coefK0 (M : ℕ) : ℕ := M * (M - 1)

/-- Ordering cost of item 1 in the instance of Lemma 1 (p. 8): `K₁ = M (M − 1)`. -/
def coefK1 (M : ℕ) : ℕ := M * (M - 1)

/-- Holding cost of item 1 in the instance of Lemma 1 (p. 8): `H₁ = 4`. -/
def coefH1 : ℕ := 4

/-- Ordering cost of item 2 in the instance of Lemma 1 (p. 8): `K₂ = M³ (M² − 1)`. -/
def coefK2 (M : ℕ) : ℕ := M ^ 3 * (M ^ 2 - 1)

/-- Holding cost of item 2 in the instance of Lemma 1 (p. 8): `H₂ = M (M² − 1)`. -/
def coefH2 (M : ℕ) : ℕ := M * (M ^ 2 - 1)

/-- The two-item aperiodic instance of Lemma 1 (pp. 8–9): objective (1) with
`K₁ = K₀ = M (M − 1)`, `H₁ = 4`, `K₂ = M³ (M² − 1)`, `H₂ = M (M² − 1)`. -/
noncomputable def lemma1Cost (M : ℕ) : ℕ → ℕ → ℝ :=
  aperiodicCost (coefK0 M : ℝ) (coefK1 M : ℝ) (coefK2 M : ℝ) (coefH1 : ℝ) (coefH2 M : ℝ)

/-- Item 2's EOQ cost in the instance of Lemma 1: `EOQ_{K₂,H₂}(q)` with `K₂ = M³ (M² − 1)`,
`H₂ = M (M² − 1)`. -/
noncomputable def eoq2 (M q : ℕ) : ℝ := eoq (coefK2 M : ℝ) (coefH2 M : ℝ) q

/-- The objective of problem (2), p. 8, named `JRP^red` on p. 9:
`JRP^red(q) = M (M − 1) (1/q − 1/lcm(q, M)) + 4 q`. -/
noncomputable def jrpRed (M q : ℕ) : ℝ :=
  ((M : ℝ) * ((M : ℝ) - 1)) * (1 / (q : ℝ) - 1 / (Nat.lcm q M : ℝ)) + 4 * (q : ℝ)

end JRPHard.Aperiodic


