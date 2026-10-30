-- Prove2me | Definitions.Def_DDROFB_fbBound
-- name    : DDROFB_fbBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:06:14.854441+00:00
-- url     : https://prove2.me/theorems/6fe0833d-3f13-4c7b-bc7f-4eb44282f173
-- title:
--   Right-hand side of (24), the support function of $\mathcal U^{FB}_\epsilon$
-- statement:
--   Let $m_b, m_f, \bar\sigma_f, \bar\sigma_b \in \mathbb R^d$, $\epsilon \in \mathbb R$ and $v \in \mathbb R^d$. The right-hand side of (24) is
--
--   $$
--   \sum_{i : v_i \ge 0} m_{fi} v_i + \sum_{i : v_i < 0} m_{bi} v_i + \sqrt{2\log(1/\epsilon)\Bigl(\sum_{i : v_i \ge 0} \bar\sigma_{fi}^2 v_i^2 + \sum_{i : v_i < 0} \bar\sigma_{bi}^2 v_i^2\Bigr)} .
--   $$
--
--   Theorem 6 identifies it as the support function $\delta^*(v \mid \mathcal U^{FB}_\epsilon)$; it is also the worst case of the bound (22) over $\mathcal P^{FB}$. As a function of $v$ it is second-order cone representable, which makes the robust constraint tractable.
--
--   **Formalization Note** The sums over $\{v_i \ge 0\}$ and $\{v_i < 0\}$ are one sum with a case split on the sign of $v_i$. The expression is used only for $0 < \epsilon < 1$.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, eq. (24), p. 19

import Mathlib

namespace DDROFB

/-- **The right-hand side of (24)**, the support function of `U^FB_ε`.
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, eq. (24),
p. 19: "`δ∗(v| U^FB_ϵ) = Σ_{i:v_i≥0} m_{fi} v_i + Σ_{i:v_i<0} m_{bi} v_i +
√(2 log(1/ϵ) (Σ_{i:v_i≥0} σ̄²_{fi} v²_i + Σ_{i:v_i<0} σ̄²_{bi} v²_i))`."

`fbBound mb mf σf σb ε v` is
`Σ_i (mf_i v_i if v_i ≥ 0, mb_i v_i if v_i < 0) + √(2 log(1/ε) · Σ_i (σf_i² if v_i ≥ 0, σb_i² if v_i < 0) v_i²)`.

**Formalization Note.** The two sums over `{i : v_i ≥ 0}` and `{i : v_i < 0}` are one sum over
all `i` with an `if` on the sign of `v_i`, using the printed split. The expression is used only for
`0 < ε < 1`, where `log(1/ε) > 0` and the radicand is nonnegative. -/
noncomputable def fbBound {d : ℕ} (mb mf σf σb : Fin d → ℝ) (ε : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, (if 0 ≤ v i then mf i * v i else mb i * v i) +
    Real.sqrt (2 * Real.log (1 / ε) *
      ∑ i, (if 0 ≤ v i then σf i ^ 2 else σb i ^ 2) * v i ^ 2)

end DDROFB


