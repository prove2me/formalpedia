-- Prove2me | Definitions.Def_ReverseLogisticsNEBS_nebsE
-- name    : ReverseLogisticsNEBS_nebsE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:01.712051+00:00
-- url     : https://prove2.me/theorems/3cdb0cb4-c7b8-4892-8ffe-dd7e921d19f9
-- title:
--   Nested echelon basestock (NEBS) decision rule (15)–(17), its trajectory and its reverse orders
-- statement:
--   Given basestock levels $S^E_j, S^R_j, S_j$ and an echelon state $y$, the **nested echelon basestock (NEBS)** rule sets, from the top location down,
--   $$
--   \widehat Y^E_N = \max[y_N, S^E_N],\qquad \widehat Y^E_j = \max\big[y_j, \min(S^E_j, \widehat Y^E_{j+1})\big]\quad (15)
--   $$
--   then
--   $$
--   \widehat Y^R_1 = \max\big[[\widehat Y^E_1]^-, \min(S^R_1, \widehat Y^E_1)\big],\qquad \widehat Y^R_j = \max\big[\widehat Y^E_{j-1}, \min(S^R_j, \widehat Y^E_j)\big]\ (j\ge 2)\quad (16)
--   $$
--   and
--   $$
--   \widehat Y_j = \max\big[\widehat Y^R_j, \min(S_j, \widehat Y^R_{j+1})\big]\ (j \le N-1),\qquad \widehat Y_N = \max[\widehat Y^R_N, S_N].\quad (17)
--   $$
--
--   The module also defines the **trajectory** of the stationary NEBS policy with real levels: $y_1$ is the initial state of period $1$ and $y_{t+1} = \widehat Y_t - d_t$ for a demand path $(d_t)$; and the **reverse order** $X^R_{jt} = \widehat Y^E_{jt} - \widehat Y^R_{jt}$ placed at location $j$ in period $t$.
--
--   This rule is the optimal policy of Theorem 4, and its trajectory is the object of Theorem 8.
--
--   **Formalization Note** The rule is defined over any linearly ordered type with a zero, so that it applies to real levels and to the extended-real levels of Theorem 4 (with the state coerced). $[x]^- = \min(x, 0)$. Periods are $1$-based; the trajectory's value at index $0$ is never used.
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Theorem 4, (15)–(17), p.15; transition below (6), p.11; Theorem 8, p.17

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Sched

namespace ReverseLogisticsNEBS

variable {β : Type*} [LinearOrder β] [Zero β] {N : ℕ}

/-- **The nested echelon basestock (NEBS) decision rule** of Theorem 4, (15)–(17), p.15, for the
levels `S^E, S^R, S` at the echelon state `y`. This declaration is the post-expedite echelon
schedule (15), computed from the top location down:
`Ŷ^E_N = max[y_N, S^E_N]` and `Ŷ^E_j = max[y_j, min(S^E_j, Ŷ^E_{j+1})]` for `j ∈ [1, N − 1]`.

The module also defines the post-reverse-order schedule (16) `nebsR`, the post-regular-order
schedule (17) `nebsY`, the real schedule `nebsSched`, the trajectory of the stationary NEBS
policy under a demand path, and the reverse order it places.

**Formalization Note.** The rule is stated over any linearly ordered type with a zero, so that it
applies both to real levels and to the extended-real levels `S^E_jt = inf arg min w_jt`,
`S^R_jt, S_jt = sup arg min (·)` of Theorem 4 (with a real state coerced to `EReal`). Locations
are `Fin N`, index `j` = location `j + 1`, index `N − 1` = location `N`. -/
def nebsE (SE : Fin N → β) (y : Fin N → β) (j : Fin N) : β :=
  if h : j.val + 1 < N then max (y j) (min (SE j) (nebsE SE y ⟨j.val + 1, h⟩))
  else max (y j) (SE j)
termination_by N - j.val
decreasing_by omega

/-- **(16)**, p.15: `Ŷ^R_1 = max[[Ŷ^E_1]^−, min(S^R_1, Ŷ^E_1)]` (with `[x]^− = min(x, 0)`) and
`Ŷ^R_j = max[Ŷ^E_{j−1}, min(S^R_j, Ŷ^E_j)]` for `j ∈ [2, N]`. -/
def nebsR (SE SR : Fin N → β) (y : Fin N → β) (j : Fin N) : β :=
  if _h : j.val = 0 then max (min (nebsE SE y j) 0) (min (SR j) (nebsE SE y j))
  else max (nebsE SE y ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩)
    (min (SR j) (nebsE SE y j))

/-- **(17)**, p.15: `Ŷ_j = max[Ŷ^R_j, min(S_j, Ŷ^R_{j+1})]` for `j ∈ [1, N − 1]` and
`Ŷ_N = max[Ŷ^R_N, S_N]`. -/
def nebsY (SE SR S : Fin N → β) (y : Fin N → β) (j : Fin N) : β :=
  if h : j.val + 1 < N then max (nebsR SE SR y j) (min (S j) (nebsR SE SR y ⟨j.val + 1, h⟩))
  else max (nebsR SE SR y j) (S j)

/-- The NEBS schedule `(Ŷ^E, Ŷ^R, Ŷ)` of (15)–(17) for real levels and a real state. -/
noncomputable def nebsSched (SE SR S : Fin N → ℝ) (y : Fin N → ℝ) : Sched N where
  YE := nebsE SE y
  YR := nebsR SE SR y
  Y := nebsY SE SR S y

/-- **The trajectory of the stationary NEBS policy** with real levels `S^E, S^R, S`, initial
echelon state `y₁` in period `1`, and demand `d t` in period `t`:
`y_1 = y₁` and `y_{t+1} = Ŷ_t − d_t` (transition below (6), p.11), where `Ŷ_t` is the NEBS
post-regular-order schedule at `y_t`. Periods are `1`-based; the value at index `0` is `y₁` and
is never used. -/
noncomputable def traj (SE SR S : Fin N → ℝ) (y₁ : Fin N → ℝ) (d : ℕ → ℝ) : ℕ → Fin N → ℝ
  | 0 => y₁
  | 1 => y₁
  | t + 2 => fun j => nebsY SE SR S (traj SE SR S y₁ d (t + 1)) j - d (t + 1)

/-- The **reverse order** `X^R_jt = Ŷ^E_jt − Ŷ^R_jt` placed at location `j` in period `t` by the
stationary NEBS policy along `traj`. -/
noncomputable def reverseOrder (SE SR S : Fin N → ℝ) (y₁ : Fin N → ℝ) (d : ℕ → ℝ) (t : ℕ)
    (j : Fin N) : ℝ :=
  nebsE SE (traj SE SR S y₁ d t) j - nebsR SE SR (traj SE SR S y₁ d t) j

end ReverseLogisticsNEBS


