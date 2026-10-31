-- Prove2me | Definitions.Def_TensorAHPE_RateConstants
-- name    : TensorAHPE_RateConstants
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:31.335043+00:00
-- url     : https://prove2.me/theorems/182e8924-c2cb-4b92-b8b9-a5e18a4d048d
-- title:
--   Constants $p,q,C,T,B_i,r_i$ of Proposition 3.5 and the proof of Theorem 3.4
-- statement:
--   For an order $d\ge2$, problem data $L_d$, parameters $M,\hat\sigma,\sigma_l,\sigma_u$ of Algorithm 2 and the distance $D$ from $x_0$ to $X_*$:
--
--   $$p=\frac{3d+1}{2d+2},\qquad q=\frac{3d+1}{d-1},\qquad C=\frac{D^2}{1-(\hat\sigma+\sigma_u)^2}\Big(\frac{d!\,\sigma_l}{L_d+M}\Big)^{-\frac2{d-1}},$$
--
--   $$T=\frac14\Big(\frac1C\Big)^{2p/q}\Big(\frac2{d+1}\Big)^{2p},\qquad B_i=T^{\frac{1-(2p/q)^{i-1}}{1-2p/q}}A_1^{(2p/q)^{i-1}},\qquad r_i=\frac{3d+1}2\big[1-(2p/q)^{i-1}\big]\quad(i\ge1).$$
--
--   They are the constants of Proposition 3.5 and of the induction (3.15) in the proof of Theorem 3.4. The formula for $B_i$ gives $B_1=A_1$.
--
--   **Formalization Note** Real powers (`Real.rpow`) throughout; $A_1$ is passed as an argument of $B_i$.
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Proposition 3.5, p.10 (p, q, C); proof of Theorem 3.4, p.11 (T, B_i, r_i)

import Mathlib
import Definitions.Def_TensorAHPE_Algorithm2

namespace TensorAHPE

/-! The constants of Proposition 3.5 and of the proof of Theorem 3.4,
Jiang, Wang & Zhang, arXiv:1812.06557v3, pp.10–12. They are used for `d ≥ 2` only. -/

/-- `p = (3d+1)/(2d+2)`, Proposition 3.5, p.10. -/
noncomputable def pExp (d : ℕ) : ℝ := (3 * (d : ℝ) + 1) / (2 * (d : ℝ) + 2)

/-- `q = (3d+1)/(d−1)`, Proposition 3.5, p.10 (real division; used for `d ≥ 2`). -/
noncomputable def qExp (d : ℕ) : ℝ := (3 * (d : ℝ) + 1) / ((d : ℝ) - 1)

/-- **The constant `C`.** Proposition 3.5 and Eq. (3.14), p.10:
"C = (D²/(1 − (σ̂ + σ_u)²)) (d!σ_l/(L_d + M))^{−2/(d−1)}", where `D` is the distance of `x₀` to
`X_*`. Real powers (`Real.rpow`) throughout; the base `d!σ_l/(L_d + M)` is positive under STEP 1. -/
noncomputable def rateC (d : ℕ) (L : ℝ) (prm : Params) (D : ℝ) : ℝ :=
  D ^ 2 / (1 - (prm.σhat + prm.σu) ^ 2) *
    ((d.factorial : ℝ) * prm.σl / (L + prm.M)) ^ (-2 / ((d : ℝ) - 1))

/-- **The constant `T`.** Proof of Theorem 3.4, p.11:
"T := (1/4)(1/C)^{2p/q}(2/(d+1))^{2p}". -/
noncomputable def rateT (d : ℕ) (L : ℝ) (prm : Params) (D : ℝ) : ℝ :=
  1 / 4 * (1 / rateC d L prm D) ^ (2 * pExp d / qExp d) * (2 / ((d : ℝ) + 1)) ^ (2 * pExp d)

/-- **The sequence `B_i`.** Proof of Theorem 3.4, p.11: "B₁ = A₁ and
B_i = T^{(1−(2p/q)^{i−1})/(1−2p/q)} (A₁)^{(2p/q)^{i−1}} for i ≥ 2". `A1` is `A₁`.

**Formalization Note.** The formula is used for every `i ≥ 1`; at `i = 1` it is
`T⁰ · A₁¹ = A₁`, the page's `B₁`. -/
noncomputable def rateB (d : ℕ) (L : ℝ) (prm : Params) (D A1 : ℝ) (i : ℕ) : ℝ :=
  rateT d L prm D ^ ((1 - (2 * pExp d / qExp d) ^ (i - 1)) / (1 - 2 * pExp d / qExp d)) *
    A1 ^ ((2 * pExp d / qExp d) ^ (i - 1))

/-- **The exponents `r_i`.** Proof of Theorem 3.4, Eq. (3.15), p.11:
"r_i = ((3d+1)/2)[1 − (2p/q)^{i−1}]" (for `i ≥ 1`). -/
noncomputable def rateR (d : ℕ) (i : ℕ) : ℝ :=
  (3 * (d : ℝ) + 1) / 2 * (1 - (2 * pExp d / qExp d) ^ (i - 1))

end TensorAHPE


