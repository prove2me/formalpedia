-- Prove2me | Definitions.Def_ComonoNetPricing_DebtEquity_Network
-- name    : ComonoNetPricing_DebtEquity_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:07.891671+00:00
-- url     : https://prove2.me/theorems/338d52b8-89c0-417c-95eb-049256ae2e29
-- title:
--   §2.1, (1), (6), Assumption 2.1, Definition 2.2, pp. 7–9, 33 — Rogers–Veraart network, clearing maps Ψ and Ψ*, greatest clearing wealth, payments and equity
-- statement:
--   The financial network with exogenous recovery rates of Rogers and Veraart, as set up in §2.1 of Banerjee and Feinstein.
--
--   **Data.** There are $n$ banks. Bank $i$ owes a total of $\bar p_i$, and $\pi_{ij}$ is the fraction of that amount owed to bank $j$; the matrix $\Pi = (\pi_{ij})$ is the relative liabilities matrix, and the remaining fraction $1-\sum_{j}\pi_{ij}$ is owed to an outside society node. A defaulting bank recovers only a fraction $\alpha_x$ of its external assets and $\alpha_L$ of its interbank assets. The **standing assumptions** are
--
--   1. $\pi_{ij} \ge 0$ and $\pi_{ii} = 0$ (no bank owes itself);
--   2. Assumption 2.1: $\sum_{j=1}^n \pi_{ij} < 1$ and $\bar p_i > 0$ for every bank $i$;
--   3. $\alpha_x, \alpha_L \in [0,1]$.
--
--   **Clearing maps.** For endowments $x \in \mathbb R^n$ and wealths $V \in \mathbb R^n$, write $V^- = \max(-V,0)$ and $y^+ = \max(y,0)$ componentwise. The clearing process (1) is
--   $$\Psi^*_i(V) = \big(\mathbb I_{\{V_i\ge 0\}} + \mathbb I_{\{V_i<0\}}\alpha_x\big)x_i + \big(\mathbb I_{\{V_i\ge 0\}} + \mathbb I_{\{V_i<0\}}\alpha_L\big)\sum_{j=1}^n \pi_{ji}(\bar p_j - V_j^-) - \bar p_i,$$
--   and the clearing map (6) of Appendix A is
--   $$\Psi_i(V) = \mathbb I_{\{V_i\ge 0\}}\Big[x_i + \sum_{j=1}^n \pi_{ji}(\bar p_j - V_j^-)^+ - \bar p_i\Big] + \mathbb I_{\{V_i<0\}}\Big[\alpha_x x_i + \alpha_L\sum_{j=1}^n \pi_{ji}(\bar p_j - V_j^-)^+ - \bar p_i\Big].$$
--
--   **Greatest clearing wealth (Definition 2.2).** $V(x)$ is the maximal clearing wealth, the componentwise supremum of all real fixed points $V = \Psi^*(V)$. The payments and the equity are
--   $$p(x) = \bar p - V(x)^-, \qquad E(x) = V(x)^+.$$
--
--   These are the objects in which every statement of the mission is written. The general network data are kept apart from the paper's comonotonic constructions, which are in the companion definition `Model`.
--
--   **Formalization Note** Banks are indexed by `Fin n`: bank `i` is the paper's bank $i+1$. The network is given by $\Pi$ and $\bar p$ directly (the paper works with "the square matrix $\Pi$" from p. 8 on), not by the nominal liabilities $L_{ij}$. The standing assumptions are the predicate `Network.Standing`. $V(x)$ is defined as an `sSup` in the conditionally complete lattice `Fin n → ℝ`, for every $x$; that the supremum is attained, and is the greatest fixed point of $\Psi$, is Proposition A.3. On an empty or unbounded fixed-point set `sSup` would be a junk value, which is why the identification is a theorem rather than built in.
-- source:
--   Banerjee & Feinstein, Pricing of debt and equity in a financial network with comonotonic endowments, arXiv:1810.01372v5, pp. 7–9, 33, §2.1, (1) p. 8, Assumption 2.1 and Definition 2.2 p. 9, (6) p. 33

import Mathlib

namespace ComonoNetPricing.DebtEquity

open Matrix

/-- The data of a financial network with exogenous recovery rates (Rogers–Veraart), §2.1,
pp. 7–8 of Banerjee & Feinstein: `n` banks indexed by `Fin n` (bank `i : Fin n` is the paper's
bank `i + 1`), the relative liabilities matrix `piM` (the paper's `Π`, `piM i j = π_ij` is the
fraction of bank `i`'s total liabilities owed to bank `j`), the total liabilities `pbar` (`p̄`),
and the recovery rates `ax` (`α_x`, on external assets) and `aL` (`α_L`, on interbank assets).
The remaining fraction `1 - ∑ j, π_ij` of bank `i`'s liabilities is owed to the society node. -/
structure Network (n : ℕ) where
  piM : Matrix (Fin n) (Fin n) ℝ
  pbar : Fin n → ℝ
  ax : ℝ
  aL : ℝ

/-- The standing assumptions of the paper on the network (p. 8 and Assumption 2.1, p. 9):
`π_ij ≥ 0`, no bank owes itself (`π_ii = 0`), every bank owes something to the society node
(`∑_j π_ij < 1`) and has positive total liabilities (`p̄_i > 0`), and the recovery rates lie in
`[0, 1]`. Together they give `Π ∈ [0, 1]^{n×n}`. -/
structure Network.Standing {n : ℕ} (N : Network n) : Prop where
  piM_nonneg : ∀ i j, 0 ≤ N.piM i j
  piM_diag : ∀ i, N.piM i i = 0
  row_sum_lt_one : ∀ i, ∑ j, N.piM i j < 1
  pbar_pos : ∀ i, 0 < N.pbar i
  ax_mem : N.ax ∈ Set.Icc (0 : ℝ) 1
  aL_mem : N.aL ∈ Set.Icc (0 : ℝ) 1

namespace Network

variable {n : ℕ} (N : Network n)

/-- The clearing map `Ψ` of (6), p. 33: for endowments `x` and wealths `V`,
`Ψ_i(V) = 1{V_i ≥ 0} [x_i + ∑_j π_ji (p̄_j − V_j⁻)⁺ − p̄_i]
        + 1{V_i < 0} [α_x x_i + α_L ∑_j π_ji (p̄_j − V_j⁻)⁺ − p̄_i]`,
where `V_j⁻ = max(−V_j, 0)` and `y⁺ = max(y, 0)`. -/
noncomputable def Psi (x V : Fin n → ℝ) : Fin n → ℝ := fun i =>
  if 0 ≤ V i then
    x i + ∑ j, N.piM j i * max (N.pbar j - max (-V j) 0) 0 - N.pbar i
  else
    N.ax * x i + N.aL * ∑ j, N.piM j i * max (N.pbar j - max (-V j) 0) 0 - N.pbar i

/-- The clearing process `Ψ*` of (1), p. 8:
`Ψ*_i(V) = (1{V_i ≥ 0} + 1{V_i < 0} α_x) x_i
          + (1{V_i ≥ 0} + 1{V_i < 0} α_L) ∑_j π_ji (p̄_j − V_j⁻) − p̄_i`. -/
noncomputable def PsiStar (x V : Fin n → ℝ) : Fin n → ℝ := fun i =>
  (if 0 ≤ V i then 1 else N.ax) * x i
    + (if 0 ≤ V i then 1 else N.aL) * ∑ j, N.piM j i * (N.pbar j - max (-V j) 0) - N.pbar i

/-- The greatest clearing wealth `V(x)` of Definition 2.2, p. 9: the maximal solution of the
clearing process `V = Ψ*(V)` of (1) under endowments `x`, taken as the componentwise supremum
of all real-valued fixed points of `Ψ*` (in the conditionally complete lattice `Fin n → ℝ`). -/
noncomputable def clearingWealth (x : Fin n → ℝ) : Fin n → ℝ :=
  sSup (Function.fixedPoints (N.PsiStar x))

/-- The payments `p(x) = p̄ − V(x)⁻` of Definition 2.2, p. 9. -/
noncomputable def payment (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => N.pbar i - max (-(N.clearingWealth x i)) 0

/-- The equity `E(x) = V(x)⁺` of Definition 2.2, p. 9. -/
noncomputable def equity (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max (N.clearingWealth x i) 0

end Network

end ComonoNetPricing.DebtEquity


