-- Prove2me | Definitions.Def_UnknownBudgetAdwords_Augment
-- name    : UnknownBudgetAdwords_Augment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:08.480414+00:00
-- url     : https://prove2.me/theorems/c76499aa-b4fa-4d77-a533-66a9f0578852
-- title:
--   Budget augmentation, $z_j$, $z_j^{a,f}$ and the bracket defining $\alpha$
-- statement:
--   Given an instance with budgets $B_i$, the **augmented instance** has the same bids and budgets
--
--   $$
--   B_i^a=B_i+\max_{t\in T}b_{i,t}.
--   $$
--
--   The comparison of GPG with f-GPG on the augmented instance uses, for a seed $Y$ and a resource $j$,
--
--   $$
--   z_j(t,Y)=(B_j-x_j(t,Y))^+,\qquad z_j^{a,f}(t,Y)=(B_j-x_j^{a,f}(t,Y))^+,
--   $$
--
--   where $x_j(t,Y)$ and $x_j^{a,f}(t,Y)$ are the budget of $j$ used before arrival $t$ by GPG and by f-GPG on the augmented instance. The original budget $B_j$ appears in both.
--
--   The constant of Theorem 2 is the minimum over $v\in[0,1]$ of
--
--   $$
--   \alpha(v)=1-g(v)+\int_0^v\min\Big\{g(y),\frac{g(v)-g(y)}{1-g(y)}\Big\}\,dy.
--   $$
--
--   **Formalization Note** The paper calls $x_j$ and $x_j^{a,f}$ the "remaining budget"; they are the budget used, which is the only reading under which $\{j\mid z_j(t,Y)>0\}$ is the available set of GPG, as (14) says. With no arrivals the maximum is $0$. In `alphaAt` the integrand at the single point $y=1$ is Lean's value $0$, which does not affect the integral.
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, p.21 (budget augmentation, α); pp.22–23 (x, z)

import Definitions.Def_UnknownBudgetAdwords_FGPG
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds maxWithZero)
noncomputable section

namespace UnknownBudgetAdwords

/-- Budget augmentation: the instance with the same bids and budgets
`B_i^a = B_i + max_{t ∈ T} b_{i,t}` (Udwani, arXiv:2110.00504v5, p.21).

**Formalization Note** With no arrivals the maximum is `0`; otherwise, bids being nonnegative,
`maxWithZero` is the maximum. -/
def augment {N M : ℕ} (I : Instance N M) : Instance N M where
  budget i := I.budget i + maxWithZero (List.ofFn fun t : Fin M => I.bid i t)
  budget_pos i := by
    have h : ∀ l : List ℝ, 0 ≤ maxWithZero l := by
      intro l
      induction l with
      | nil => simp [maxWithZero]
      | cons a l ih =>
        simp only [maxWithZero, List.foldr_cons] at ih ⊢
        exact le_max_of_le_right ih
    exact add_pos_of_pos_of_nonneg (I.budget_pos i) (h _)
  bid := I.bid
  bid_nonneg := I.bid_nonneg

/-- `z_j(t, Y) = (B_j − x_j(t, Y))⁺`, where `x_j(t, Y)` is the budget of `j` used by GPG on seed `Y`
before arrival `t` (Udwani, arXiv:2110.00504v5, p.23).

**Formalization Note** The paper calls `x_j` the "remaining budget" (p.22); it is the budget used,
since otherwise `z ≡ 0` at the first arrival and the left side of (14) is not the available set. -/
def zGPG {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (j : Fin N) (t : ℕ) : ℝ :=
  max 0 (I.budget j - spend I (gpgAlloc I β Y) j t)

/-- `z_j^{a,f}(t, Y) = (B_j − x_j^{a,f}(t, Y))⁺`, where `x_j^{a,f}(t, Y)` is the budget of `j` used
by f-GPG on the augmented instance on seed `Y` before arrival `t`; the original budget `B_j` is
used here (Udwani, arXiv:2110.00504v5, p.23). -/
def zAug {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (j : Fin N) (t : ℕ) : ℝ :=
  max 0 (I.budget j - fUsedBefore (augment I) β Y j t)

/-- The bracket `1 − g(v) + ∫_0^v min {g(y), (g(v) − g(y)) / (1 − g(y))} dy` whose minimum over
`v ∈ [0, 1]` is `α` in the proof of Theorem 2 (Udwani, arXiv:2110.00504v5, p.21). -/
def alphaAt (β v : ℝ) : ℝ :=
  1 - g β v + ∫ y in (0 : ℝ)..v, min (g β y) ((g β v - g β y) / (1 - g β y))

end UnknownBudgetAdwords


