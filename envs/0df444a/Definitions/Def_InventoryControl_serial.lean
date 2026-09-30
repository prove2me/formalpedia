-- Prove2me | Definitions.Def_InventoryControl_serial
-- name    : InventoryControl_serial
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:08:26.416897+00:00
-- url     : https://prove2.me/theorems/c923493f-0dcd-4fbe-9c0a-9f73a38aa00f
-- title:
--   Multi-echelon lot sizing with constant demand: the two-level serial system and the $N$-stage serial system of Sect. 9.2
-- statement:
--   The deterministic multi-echelon lot-sizing models of Axsäter, *Inventory Control*, Sect. 9.2,
--   built on the chapter 4 cost function $C(Q) = \frac{Q}{2}h + \frac{d}{Q}A$ (`eoqCost A d h Q`).
--   Customer demand $d$ for the end item is constant and continuous, lead-times are zero, no
--   shortages are allowed, and batch quantities are constant over time.
--
--   **Two levels** (Sect. 9.2.1). Item 1 is the final product, made from one unit of item 2. With
--   ordering costs $A_1, A_2$, installation holding costs $h_1, h_2$ and echelon holding costs
--   $e_1 = h_1 - h_2$, $e_2 = h_2$, and with $Q_2 = kQ_1$ for a positive integer $k$ (Eq. 9.4), the
--   total cost per time unit is (Eq. 9.6)
--
--   $$ C \;=\; \big(h_1 + (k-1)h_2\big)\frac{Q_1}{2} + \Big(A_1 + \frac{A_2}{k}\Big)\frac{d}{Q_1}, $$
--
--   which is `twoLevelCostInst d A1 A2 h1 h2 Q1 k`, or equivalently in echelon form (Eq. 9.9)
--
--   $$ C \;=\; (e_1 + ke_2)\frac{Q_1}{2} + \Big(A_1 + \frac{A_2}{k}\Big)\frac{d}{Q_1}, $$
--
--   which is `twoLevelCost d A1 A2 e1 e2 Q1 k`, literally `eoqCost (A1 + A2/k) d (e1 + k e2) Q1`.
--   The optimal cost for a given $k$ (Eq. 9.11) is `twoLevelOptCost d A1 A2 e1 e2 k` $=
--   \sqrt{2(A_1 + A_2/k)\,d\,(e_1 + ke_2)}$.
--
--   **$N$ stages** (Sect. 9.2.2). Installation $i$ produces item $i$ from one unit of item $i+1$;
--   item 1 faces the final demand. With ordering costs $A_i$ and echelon holding costs $e_i$, the
--   cost of batch quantities $Q_1, \dots, Q_N$ is (Eq. 9.17)
--
--   $$ \sum_{i=1}^{N}\Big(e_i\frac{Q_i}{2} + A_i\frac{d}{Q_i}\Big), $$
--
--   which is `serialCost A e d Q`. `SerialNested Q` is the relaxed constraint (9.18),
--   $Q_{i-1} \le Q_i$; `SerialPowerOfTwo Q` is Roundy's constraint (9.16), $Q_i = 2^{k_i}Q_{i-1}$
--   for nonnegative integers $k_i$. `potRound q Q` is the integer $m$ nearest to $\log_2(Q/q)$,
--   so that $2^m q$ is the power-of-two multiple of $q$ within a factor $\sqrt 2$ of $Q$; it is the
--   rounding step (9.22).
--
--   **Formalization Note** Stages are indexed by `Fin N` and "consecutive" means indices differing
--   by one; for $N \le 1$ both constraints are vacuous. No positivity is built into the
--   definitions; the theorems assume $d, A_i, e_i > 0$ and positive batch quantities. Divisions by
--   $k$ and $Q$ are Lean's total division, so $k = 0$ or $Q = 0$ give junk values that every
--   statement excludes.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, Sect. 9.2.1 pp. 174-177 (Eq. 9.6, 9.9, 9.11), Sect. 9.2.2 pp. 178-179 (Eq. 9.16-9.18, 9.22)

import Definitions.Def_InventoryControl_eoq

namespace InventoryControl

/-- Eq. (9.9): the two-level serial cost in echelon form, `k` being the ratio `Q₂ / Q₁`.
Definitionally `eoqCost (A₁ + A₂/k) d (e₁ + k e₂) Q₁`, cf. Eq. (9.14)-(9.15). -/
noncomputable def twoLevelCost (d A1 A2 e1 e2 Q1 k : ℝ) : ℝ :=
  eoqCost (A1 + A2 / k) d (e1 + k * e2) Q1

/-- Eq. (9.6): the same cost written with installation holding costs `h₁, h₂`. -/
noncomputable def twoLevelCostInst (d A1 A2 h1 h2 Q1 k : ℝ) : ℝ :=
  (h1 + (k - 1) * h2) * Q1 / 2 + (A1 + A2 / k) * d / Q1

/-- Eq. (9.11): the optimal two-level cost for a given ratio `k`. -/
noncomputable def twoLevelOptCost (d A1 A2 e1 e2 k : ℝ) : ℝ :=
  Real.sqrt (2 * (A1 + A2 / k) * d * (e1 + k * e2))

/-- Eq. (9.17): the cost of a serial system with `N` stages, ordering costs `A`, echelon holding
costs `e`, final demand `d` and batch quantities `Q`. -/
noncomputable def serialCost {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (Q : Fin N → ℝ) : ℝ :=
  ∑ i, eoqCost (A i) d (e i) (Q i)

/-- Eq. (9.18): nested batch quantities, `Q_{i-1} ≤ Q_i`. -/
def SerialNested {N : ℕ} (Q : Fin N → ℝ) : Prop :=
  ∀ i j : Fin N, j.val = i.val + 1 → Q i ≤ Q j

/-- Eq. (9.16): each batch quantity is a nonnegative power of two times the previous one. -/
def SerialPowerOfTwo {N : ℕ} (Q : Fin N → ℝ) : Prop :=
  ∀ i j : Fin N, j.val = i.val + 1 → ∃ k : ℕ, Q j = (2 : ℝ) ^ k * Q i

/-- The rounding step (9.22): the exponent `m` with `2^m q` nearest to `Q` on the log₂ scale. -/
noncomputable def potRound (q Q : ℝ) : ℤ := ⌊Real.logb 2 (Q / q) + 1 / 2⌋

end InventoryControl


