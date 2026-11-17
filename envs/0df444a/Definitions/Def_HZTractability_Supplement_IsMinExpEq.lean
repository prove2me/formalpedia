-- Prove2me | Definitions.Def_HZTractability_Supplement_IsMinExpEq
-- name    : HZTractability_Supplement_IsMinExpEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:29:09.882728+00:00
-- url     : https://prove2.me/theorems/638833ae-8c60-4953-8c00-78ca339c8fee
-- title:
--   Exact normalized HZ equilibrium with minimum-expenditure tie-breaking
-- statement:
--   Consider an HZ market with buyers $B$, goods $G$, unit budgets, unit supplies, and a utility function $U_i$ for each buyer. A pair $(p,x)$ is an **exact normalized equilibrium with minimum-expenditure tie-breaking** if
--
--   1. $x\ge0$ is feasible: $\sum_j x_{ij}=1$ for every buyer $i$ and $\sum_i x_{ij}=1$ for every good $j$;
--   2. $p\ge0$ is normalized: $\min_j p_j=0$;
--   3. every buyer is within budget: $p\cdot x_i\le1$;
--   4. every buyer is utility-maximizing: $U_i(x_i)\ge U_i(y)$ for every budget-one unit bundle $y$ ($y\ge0$, $\sum_j y_j=1$, $p\cdot y\le1$), i.e. $U_i(x_i)=V_i(p)$;
--   5. every buyer pays the least among such bundles: $p\cdot x_i\le p\cdot y$ for every budget-one unit bundle $y$ with $U_i(y)\ge U_i(x_i)$.
--
--   This is the output notion of Theorem 1.3, where $U_i$ is the two-slope utility (1).
--
--   **Formalization Note** Unit bundles are the published `HZTractability.IsUnitBundle`. Since $x_i$ is itself a budget-one unit bundle, clause 4 states $U_i(x_i)=V_i(p)$ with the maximum of (OptBundle) attained.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §2.2, p.7 (PDF p.9); Definition 6.1, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_HZTractability_IsUnitBundle

set_option autoImplicit false

namespace HZTractability.Supplement

/-- **Exact normalized HZ equilibrium with minimum-expenditure tie-breaking**, for arbitrary utility
functions (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held version, sha256 74b7bf9f…, §2.2,
p.7 (PDF 9): "A normalized exact equilibrium is a pair (p, x) with normalized prices and feasible
allocation such that p · x_i ≤ 1 and U_i(x_i) = V_i(p) for every buyer i. … An exact equilibrium has
minimum-expenditure tie-breaking if every buyer receives a cheapest utility-maximizing affordable unit
bundle"; Definition 6.1, p.24 (PDF 26): "the demand value V_i(p) is given by (OptBundle) with objective
U_i(y)").

`(p, x)` with buyers `B`, goods `G` and utility functions `U_i`: `x ≥ 0`, every row sum and every
column sum of `x` is exactly one, `p ≥ 0` with some price zero (`min_j p_j = 0`), and for every buyer
`i`:
1. `p · x_i ≤ 1`;
2. `U_i(x_i) ≥ U_i(y)` for every budget-one unit bundle `y` (`y ≥ 0`, `∑_j y_j = 1`, `p · y ≤ 1`);
3. `p · x_i ≤ p · y` for every budget-one unit bundle `y` with `U_i(y) ≥ U_i(x_i)`.

**Formalization Note** `x_i` is itself a budget-one unit bundle (by 1 and feasibility), so clause 2
says `U_i(x_i) = V_i(p)` with the maximum of (OptBundle) attained, without a supremum junk value.
Clause 3 says `x_i` is a cheapest bundle among the utility-maximizing affordable unit bundles. Unit
bundles are the published `HZTractability.IsUnitBundle`. -/
def IsMinExpEq {B G : Type} [Fintype B] [Fintype G] (U : B → (G → ℝ) → ℝ)
    (x : B → G → ℝ) (p : G → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ j, 0 ≤ p j) ∧ (∃ j, p j = 0) ∧
  (∀ i, ∑ j, x i j = 1) ∧ (∀ j, ∑ i, x i j = 1) ∧
  (∀ i, ∑ j, p j * x i j ≤ 1) ∧
  (∀ i y, IsUnitBundle p y → U i y ≤ U i (x i)) ∧
  ∀ i y, IsUnitBundle p y → U i (x i) ≤ U i y → ∑ j, p j * x i j ≤ ∑ j, p j * y j

end HZTractability.Supplement


