-- Prove2me | Definitions.Def_RegimeDRCVaR_normM
-- name    : RegimeDRCVaR_normM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:39.750433+00:00
-- url     : https://prove2.me/theorems/93e04a75-7e61-421a-b90e-d47dd8293cad
-- title:
--   The $\ell_m$ norm $\|a\|_m$ on $\mathbb R^I$
-- statement:
--   For a vector $a=(a_1,\dots,a_I)'\in\mathbb R^I$ and an exponent $m\in[1,+\infty]$, the **$\ell_m$-norm** is
--   $$
--   \|a\|_m=\Big(\sum_{i=1}^I |a_i|^m\Big)^{1/m}\quad(1\le m<\infty),\qquad \|a\|_\infty=\max_i |a_i|.
--   $$
--   The transport cost of the Wasserstein distance in this mission is $\rho(p,q)=\|p-q\|_m$, and the **conjugate norm** $\|\cdot\|_{m^*}$ is the $\ell_{m^*}$-norm with $1/m+1/m^*=1$ (so $m=1\mapsto m^*=\infty$, $m=2\mapsto 2$, $m=\infty\mapsto 1$).
--
--   Every constraint of the reformulation (12) that is not linear is a bound $\beta\ge\|x\|_{m^*}$ on a norm of this family.
--
--   **Formalization Note** Vectors are functions `Fin I → ℝ`; the norm is that of `PiLp m`, applied to the vector. Mathlib's default norm on `Fin I → ℝ` is the sup norm and is never used for $\|\cdot\|_m$. The conjugate exponent $m^*$ is Mathlib's `ENNReal.conjExponent m` $=1+(m-1)^{-1}$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Notation, p.4 (ℓm-norm); §3.1.1, p.9 (ρ(p,q) = ‖p − q‖_m); p.ec4 (m* is the conjugate norm)

import Mathlib

open scoped ENNReal

namespace RegimeDRCVaR

/-- **The ℓm norm** `‖a‖_m = (∑ⱼ |aⱼ|^m)^{1/m}` of a vector `a ∈ ℝ^I`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, Notation, p.4; the transport cost `ρ(p, q) = ‖p − q‖_m`, §3.1.1, p.9).

**Formalization Note** A vector of `ℝ^I` is a function `Fin I → ℝ`. The exponent is
`m : ℝ≥0∞`, so `m = ∞` (the max norm) is included; the norm is the `PiLp m` norm of the vector,
`(∑ᵢ |aᵢ|^m)^{1/m}` for `1 ≤ m < ∞` and `maxᵢ |aᵢ|` for `m = ∞`. The bare norm `‖·‖` that
Mathlib puts on `Fin I → ℝ` is the sup norm and is never used for the ℓm norm. The conjugate norm
`‖·‖_{m*}` of the paper is `normM (ENNReal.conjExponent m)`, with `ENNReal.conjExponent m =
1 + (m − 1)⁻¹` (so `1 ↦ ∞`, `2 ↦ 2`, `∞ ↦ 1`). -/
noncomputable def normM {I : ℕ} (m : ℝ≥0∞) (a : Fin I → ℝ) : ℝ :=
  ‖(WithLp.toLp m a : PiLp m (fun _ : Fin I => ℝ))‖

end RegimeDRCVaR


