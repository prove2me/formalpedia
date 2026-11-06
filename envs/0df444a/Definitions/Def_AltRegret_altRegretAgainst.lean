-- Prove2me | Definitions.Def_AltRegret_altRegretAgainst
-- name    : AltRegret_altRegretAgainst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:09.517956+00:00
-- url     : https://prove2.me/theorems/50599d40-c4d1-46af-a68a-d00d1144b6eb
-- title:
--   Alternating regret against a comparator $x\in\Delta_d$
-- statement:
--   Let $x_1,x_2,\dots\in\mathbb R^d$ be plays, $c_1,c_2,\dots\in\mathbb R^d$ losses with $c_0=\mathbf 0$, $T\in\mathbb N$ a horizon and $u\in\mathbb R^d$ a comparator. In round $t$ the learner suffers the loss $(c_{t-1}+c_t)^\top x_t$. The **alternating regret against $u$** is
--   $$
--   \sum_{t=1}^{T}(c_{t-1}+c_t)^\top x_t-\sum_{t=1}^{T}(c_{t-1}+c_t)^\top u .
--   $$
--   The paper's alternating regret (1) is
--   $$
--   \mathrm{Reg}^T_{\mathrm{Alt}}=\sum_{t=1}^{T}(c_{t-1}+c_t)^\top x_t-\min_{x\in\Delta_d}\sum_{t=1}^{T}(c_{t-1}+c_t)^\top x,
--   $$
--   the maximum of this quantity over comparators $u\in\Delta_d$. A bound $\mathrm{Reg}^T_{\mathrm{Alt}}\le B$ is thus the bound $\le B$ for every $u\in\Delta_d$.
--
--   **Formalization Note** The minimum in (1) is attained on the compact simplex, which is why the "for every comparator" form is equivalent.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2, p.6, Eq. (1)

import Mathlib
import Definitions.Def_AltRegret_lossAt

namespace AltRegret

/-- **Alternating regret against a comparator.** Tao–Zheng, arXiv:2608.24731, §2, p.6, Eq. (1):
"The learner then observes `c_t` and suffers loss `(c_{t−1} + c_t)ᵀx_t`. In this case, the
alternating regret can be written as
`Reg^T_Alt = ∑_{t=1}^T (c_{t−1} + c_t)ᵀx_t − min_{x∈Δ_d} ∑_{t=1}^T (c_{t−1} + c_t)ᵀx`."

`altRegretAgainst x c T u` is `∑_{t=1}^T (c_{t−1} + c_t)ᵀx_t − ∑_{t=1}^T (c_{t−1} + c_t)ᵀu` for
plays `x : ℕ → Fin d → ℝ` (round `t` uses `x t`), losses `c` with `c₀ = 0` (see `lossAt`), and a
comparator `u`.

**Formalization Note.** The paper's `Reg^T_Alt` is the supremum of this quantity over
comparators `u ∈ Δ_d` (the minimum in (1) is attained on the compact simplex), so
"`Reg^T_Alt ≤ B`" is "`altRegretAgainst x c T u ≤ B` for every `u ∈ Δ_d`". The plays at index
`0` and the losses after round `T` are not read. -/
def altRegretAgainst {d : ℕ} (x : ℕ → Fin d → ℝ) (c : ℕ → Fin d → ℝ) (T : ℕ)
    (u : Fin d → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∑ i, (lossAt c (t - 1) i + lossAt c t i) * x t i
    - ∑ t ∈ Finset.Icc 1 T, ∑ i, (lossAt c (t - 1) i + lossAt c t i) * u i

end AltRegret


