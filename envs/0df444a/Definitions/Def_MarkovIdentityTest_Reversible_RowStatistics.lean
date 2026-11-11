-- Prove2me | Definitions.Def_MarkovIdentityTest_Reversible_RowStatistics
-- name    : MarkovIdentityTest_Reversible_RowStatistics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:37:04.668501+00:00
-- url     : https://prove2.me/theorems/a702278e-de65-4345-9320-0c3f05d99247
-- title:
--   The centered pair statistic $U_b(p;c)$, the weights $w=1/(p+\tau)$, the capped weights $v$, the coefficients $\kappa$ and the row signal $F$
-- statement:
--   Fix a finite alphabet of destinations.
--
--   - The **centered pair statistic** (p. 12) of weights $b$, a reference vector $p$ and a count vector $c$ with total $k=\sum_jc_j$ is
--   $$U_b(p;c)=\sum_jb_j\big[c_j(c_j-1)-2(k-1)p_jc_j+k(k-1)p_j^2\big].$$
--   - The test weights are $w_j=1/(p_j+\tau)$.
--   - The **capped weights** (§4.3.2) of weights $w$ against a row $q$ are $v_j=\min\{w_j,3/q_j\}$, and $v_j=w_j$ when $q_j=0$.
--   - The **clipping coefficient** is $\kappa_j=v_jq_j-w_jp_j$, and the **retained row signal** is
--   $$F(p,q)=\sum_j\big(v_jq_j^2+w_jp_j^2-2w_jp_jq_j\big).$$
--
--   In the Lean, $F$ and $\kappa$ take the weight vector $w$ as an explicit argument, because §5.4 uses weights that are not of the form $1/(p+\tau)$ (weight $M$ on an extra outcome).
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 8 (w), p. 12 (U_b), p. 20 §4.3.2 (v, κ, F)

import Mathlib

set_option autoImplicit false

open Finset

namespace MarkovIdentityTest.Reversible

/-- The centered pair statistic (p. 12 / PDF 14): for weights `b`, a reference vector `p` and a
count vector `c` with total `k = ∑ c`,
`U_b(p; c) = ∑ⱼ bⱼ [cⱼ(cⱼ - 1) - 2(k - 1) pⱼ cⱼ + k(k - 1) pⱼ²]`. -/
noncomputable def pairStat {α : Type*} [Fintype α] (b p : α → ℝ) (c : α → ℕ) : ℝ :=
  ∑ a, b a * ((c a : ℝ) * ((c a : ℝ) - 1) - 2 * ((∑ z, (c z : ℝ)) - 1) * p a * (c a : ℝ)
    + (∑ z, (c z : ℝ)) * ((∑ z, (c z : ℝ)) - 1) * p a ^ 2)

/-- The test weights `wⱼ = 1/(pⱼ + τ)` (p. 8 / PDF 10, §4.3.2). -/
noncomputable def tauWeight {α : Type*} (τ : ℝ) (p : α → ℝ) (a : α) : ℝ :=
  1 / (p a + τ)

/-- Capped weights (§4.3.2, p. 20 / PDF 22): `vⱼ = min {wⱼ, 3/qⱼ}`, and `vⱼ = wⱼ` when `qⱼ = 0`. -/
noncomputable def cappedWeight {α : Type*} (w q : α → ℝ) (a : α) : ℝ :=
  if q a = 0 then w a else min (w a) (3 / q a)

/-- The clipping coefficient `κⱼ = vⱼ qⱼ - wⱼ pⱼ` (p. 20 / PDF 22). -/
noncomputable def clipCoeff {α : Type*} (w p q : α → ℝ) (a : α) : ℝ :=
  cappedWeight w q a * q a - w a * p a

/-- The retained row signal (p. 20 / PDF 22):
`F(p, q) = ∑ⱼ (vⱼ qⱼ² + wⱼ pⱼ² - 2 wⱼ pⱼ qⱼ)`, with `v` the capped weights of `w`. -/
noncomputable def rowSignal {α : Type*} [Fintype α] (w p q : α → ℝ) : ℝ :=
  ∑ a, (cappedWeight w q a * q a ^ 2 + w a * p a ^ 2 - 2 * w a * p a * q a)

end MarkovIdentityTest.Reversible


