-- Prove2me | Definitions.Def_BassokSubstitution_Model
-- name    : BassokSubstitution_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T08:05:44.439197+00:00
-- url     : https://prove2.me/theorems/2d032e2f-5433-4df8-823b-7efee7640473
-- title:
--   Single-period $N$-product model with downward substitution: data and Assumptions 1–3 (§2.1)
-- statement:
--   This file fixes the economic data of the single-period, $N$-product inventory model with full downward substitution of Bassok, Anupindi and Akella.
--
--   There are $N$ products and $N$ demand classes, both numbered $1,\dots,N$. Demand of class $i$ may be satisfied from stock of product $j$ whenever $j \le i$; product $1$ is the most flexible. The data are:
--
--   1. $c_j$, the unit purchase cost of product $j$;
--   2. $p_i$, the unit revenue earned for a satisfied unit of class $i$ (it depends only on the class, not on the product used);
--   3. $\pi_i$, the unit backorder (penalty) cost of an unmet unit of class $i$;
--   4. $s_j = \bar s_j - \bar h_j$, the effective unit salvage value of a leftover unit of product $j$ (salvage minus holding cost; it may be negative);
--   5. $b$, the unit cost of substitution.
--
--   The net revenue of using a unit of product $j$ for a unit of class $i \ge j$ is
--   $$a_{ji} = \begin{cases} p_i, & j = i,\\ p_i - b, & j < i,\end{cases}$$
--   and $T_k = p_k + \pi_k - b$. The paper's standing assumptions are
--
--   - **Assumption 1.** $\pi_i + p_i \ge \pi_j + p_j$ for $i < j$;
--   - **Assumption 2.** $s_i \ge s_j$ for $i < j$;
--   - **Assumption 3.** $a_{ij} + \pi_j - s_i \ge 0$ for $i \le j$.
--
--   Assumption 1 says unmet demand of a lower-indexed class is more costly; Assumption 2 that more flexible products have higher effective salvage value; Assumption 3 that substitution is profitable compared with leaving demand unmet and salvaging the unit.
--
--   **Formalization Note.** Products and classes are indexed by `Fin N`, so the paper's index $k$ is Lean index $k-1$ and product `0` is the most flexible product. The penalty $\pi_i$ is the field `penalty`. `netRevenue j i` is $a_{ji}$ (product first, class second); it is only used for $j \le i$.
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 633, §2.1 (notation, Assumptions 1–3), and p. 634 (definition of T_k)

import Mathlib

namespace BassokSubstitution

/-- The economic data of the single-period `N`-product model with full downward substitution
(Bassok–Anupindi–Akella 1999, §2.1). Products and demand classes are both indexed by `Fin N`;
the paper's product/class `k` (1-based) is index `k - 1` here, so product `0` is the most
flexible product. Demand of class `i` may be served by product `j` only when `j ≤ i`.

* `c j` — unit purchase cost of product `j`;
* `p i` — unit revenue of a satisfied unit of class `i` (independent of the product used);
* `penalty i` — unit backorder (shortage) cost `π_i` of class `i`;
* `s j` — effective unit salvage value `s̄_j - h̄_j` of a leftover unit of product `j`
  (may be negative);
* `b` — unit substitution cost. -/
structure Model (N : ℕ) where
  c : Fin N → ℝ
  p : Fin N → ℝ
  penalty : Fin N → ℝ
  s : Fin N → ℝ
  b : ℝ

variable {N : ℕ}

/-- Net revenue `a_{j i}` of using one unit of product `j` for one unit of demand class `i`
(meaningful for `j ≤ i`): `p_i` if `j = i`, and `p_i - b` if `j < i`. -/
def Model.netRevenue (M : Model N) (j i : Fin N) : ℝ :=
  if j = i then M.p i else M.p i - M.b

/-- `T_k = p_k + π_k - b`. -/
def Model.T (M : Model N) (k : Fin N) : ℝ :=
  M.p k + M.penalty k - M.b

/-- Assumption 1: `π_i + p_i ≥ π_j + p_j` for `i < j`. -/
def Model.Assumption1 (M : Model N) : Prop :=
  ∀ i j : Fin N, i < j → M.penalty j + M.p j ≤ M.penalty i + M.p i

/-- Assumption 2: `s_i ≥ s_j` for `i < j`. -/
def Model.Assumption2 (M : Model N) : Prop :=
  ∀ i j : Fin N, i < j → M.s j ≤ M.s i

/-- Assumption 3: `a_{ij} + π_j - s_i ≥ 0` for `i ≤ j` (product `i`, class `j`). -/
def Model.Assumption3 (M : Model N) : Prop :=
  ∀ i j : Fin N, i ≤ j → 0 ≤ M.netRevenue i j + M.penalty j - M.s i

end BassokSubstitution


