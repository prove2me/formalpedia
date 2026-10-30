-- Prove2me | Definitions.Def_DDROFB_UFB
-- name    : DDROFB_UFB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:05:25.525735+00:00
-- url     : https://prove2.me/theorems/5c12786c-7189-4972-96c9-ec35d566ae62
-- title:
--   The forward–backward uncertainty set $\mathcal U^{FB}_\epsilon$, eq. (23)
-- statement:
--   Let $m_b, m_f, \bar\sigma_f, \bar\sigma_b \in \mathbb R^d$ and $\epsilon \in \mathbb R$. The **forward–backward uncertainty set** is
--
--   $$
--   \mathcal U^{FB}_\epsilon \;=\; \Bigl\{ y_1 + y_2 - y_3 \;:\; y_2, y_3 \in \mathbb R^d_+,\ \ \sum_{i=1}^d \Bigl(\frac{y_{2i}^2}{2\bar\sigma_{fi}^2} + \frac{y_{3i}^2}{2\bar\sigma_{bi}^2}\Bigr) \le \log(1/\epsilon),\ \ m_{bi} \le y_{1i} \le m_{fi},\ i = 1,\dots,d \Bigr\}.
--   $$
--
--   It is a box $[m_b, m_f]$ plus an asymmetric ellipsoid that stretches by $\bar\sigma_f$ in positive and by $\bar\sigma_b$ in negative coordinate directions. Theorem 6 shows that, built from data, this family of sets simultaneously implies a probabilistic guarantee, with support function (24).
--
--   **Formalization Note** The printed "$y_2, y_2 \in \mathbb R^d_+$" is read as $y_2, y_3 \in \mathbb R^d_+$ ($y_3$ occurs in the constraint and the proof writes $y_2 \ge 0$, $y_3 \ge 0$). The thresholds are arbitrary real vectors in the definition; every statement that uses the set assumes $\bar\sigma_f, \bar\sigma_b > 0$, since Lean's $y^2/0 = 0$ would otherwise drop a constraint.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, eq. (23), p. 19

import Mathlib

namespace DDROFB

/-- **The forward–backward uncertainty set** `U^FB_ε`, eq. (23).
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, eq. (23),
p. 19: "`U^FB_ϵ = { y1 + y2 − y3 : y2, y2 ∈ ℝ^d_+, Σ_{i=1}^d y²_{2i}/(2σ̄²_{fi}) + y²_{3i}/(2σ̄²_{bi})
≤ log(1/ϵ), m_{bi} ≤ y_{1i} ≤ m_{fi}, i = 1,…,d }`."

`UFB mb mf σf σb ε` is the set of `y₁ + y₂ − y₃` with `y₂, y₃ ≥ 0` coordinatewise,
`mb ≤ y₁ ≤ mf` coordinatewise, and `Σ_i (y₂ᵢ²/(2σf_i²) + y₃ᵢ²/(2σb_i²)) ≤ log(1/ε)`.

**Formalization Note.** The printed "`y2, y2 ∈ ℝ^d_+`" is read as `y₂, y₃ ∈ ℝ^d_+` (`y₃` appears in
the constraint and the sum; the proof on p. ec5 writes `y₂ ≥ 0, y₃ ≥ 0`). The thresholds are
arbitrary real vectors here; every statement of the mission that uses the set assumes
`σf, σb > 0` coordinatewise, since for a zero threshold Lean's `y²/0 = 0` would silently drop
the constraint. -/
def UFB {d : ℕ} (mb mf σf σb : Fin d → ℝ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {u | ∃ y₁ y₂ y₃ : EuclideanSpace ℝ (Fin d),
    (∀ i, 0 ≤ y₂ i ∧ 0 ≤ y₃ i ∧ mb i ≤ y₁ i ∧ y₁ i ≤ mf i) ∧
    ∑ i, (y₂ i ^ 2 / (2 * σf i ^ 2) + y₃ i ^ 2 / (2 * σb i ^ 2)) ≤ Real.log (1 / ε) ∧
    u = y₁ + y₂ - y₃}

end DDROFB


