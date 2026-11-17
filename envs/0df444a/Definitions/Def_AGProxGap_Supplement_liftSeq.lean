-- Prove2me | Definitions.Def_AGProxGap_Supplement_liftSeq
-- name    : AGProxGap_Supplement_liftSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:18:35.017213+00:00
-- url     : https://prove2.me/theorems/63c5ff60-52c6-4ec5-bb9d-4119c9dfe477
-- title:
--   The Hensel-lifting rational functions $\alpha_{\nu,j}(Y,Z)$ of (7)
-- statement:
--   Fix $R=R_\nu$, the point $P_0$ and a local parameter $t$ at $P_0$, and write $R(t,Y,Z)=\sum_aR_a(Y,Z)t^a$. The rational functions $\alpha_j\in\overline{\mathbb F}_q(Y,Z)$ are defined by $\alpha_0=Y$ and, for $j\ge1$,
--   $$\alpha_j(Y,Z)=-\frac{[t^j]\,R\bigl(t,\ Y+\sum_{h=1}^{j-1}\alpha_h(Y,Z)t^h,\ Z\bigr)}{\partial_YR_{P_0}(Y,Z)}.\tag{7}$$
--   Here $Y_{j}(t)=Y+\sum_{h=1}^{j}\alpha_ht^h$ is built step by step, and $[t^j]R(t,Y_{j-1}(t),Z)=\sum_{a=0}^{j}[t^{j-a}]R_a(Y_{j-1}(t),Z)$.
--
--   For a parameter $z$ assigned to $\nu$, $\alpha_j(y_z,z)$ is the $j$-th local coefficient of $f_z^{\mu_\nu}$ at $P_0$ (Lemma 4.6).
--
--   **Formalization Note** $\overline{\mathbb F}_q(Y,Z)$ is the fraction field of $\overline{\mathbb F}_q[Z][Y]$; the lifts $Y_j(t)$ are polynomials in $t$ over it.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §4.2, (7), p.28

import Mathlib
import Definitions.Def_AGProxGap_Supplement_specAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

namespace AGProxGap.Supplement

/-- The field `K(Y, Z)` of rational functions in two variables, as the fraction field of
`K[Z][Y]` (outer variable `Y`, inner variable `Z`). -/
abbrev RatYZ (K : Type*) [Field K] : Type _ := FractionRing (Polynomial (Polynomial K))

/-- **The Hensel lifts `Y_j(t) = Y + Σ_{h=1}^{j} α_{ν,h}(Y, Z) t^h`** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4.2, (7), p.28:
"Set α_{ν,0}(Y, Z) := Y. For j ≥ 1, define recursively
α_{ν,j}(Y, Z) = − [t^j]R_ν(t, Y + Σ_{h=1}^{j−1} α_{ν,h}(Y, Z)t^h, Z) / ∂_Y R_{ν,P_0}(Y, Z)").

`liftSeq P_0 t R j ∈ K(Y, Z)[t]` is `Y_j(t)`: `Y_0(t) = Y` and
`Y_{j+1}(t) = Y_j(t) + α_{j+1} t^{j+1}` with
`α_{j+1} = −[t^{j+1}]R(t, Y_j(t), Z) / ∂_Y R_{P_0}(Y, Z)`, where
`[t^{j+1}]R(t, Y_j(t), Z) = Σ_{a=0}^{j+1} [t^{j+1−a}] R_a(Y_j(t), Z)` and
`R(t, Y, Z) = Σ_a R_a(Y, Z) t^a` is the local expansion at `P_0` (`expCoeff`).

**Formalization Note** `R_a(Y_j(t), Z)` is `R_a ∈ K[Z][Y]` evaluated at `Y = Y_j(t)` in
`K(Y, Z)[t]` (coefficients `K[Z] → K(Y, Z)`); only `a ≤ j + 1` contribute to `[t^{j+1}]`, so the
sum over `a` is finite. Division by `∂_Y R_{P_0}` is in the field `K(Y, Z)` (junk `0` if that
derivative were `0`, which the hypotheses of Theorem 4.8 exclude). -/
noncomputable def liftSeq {K F : Type*} [Field K] [Field F] [Algebra K F] (P0 : Place K F)
    (t : F) (R : Polynomial (Polynomial F)) : ℕ → Polynomial (RatYZ K)
  | 0 => C (algebraMap (Polynomial (Polynomial K)) (RatYZ K) X)
  | j + 1 =>
      liftSeq P0 t R j + C (-(∑ a ∈ Finset.range (j + 2),
          ((expCoeff P0 t R a).eval₂
              ((C : RatYZ K →+* Polynomial (RatYZ K)).comp
                ((algebraMap (Polynomial (Polynomial K)) (RatYZ K)).comp
                  (C : Polynomial K →+* Polynomial (Polynomial K))))
              (liftSeq P0 t R j)).coeff (j + 1 - a))
          / algebraMap (Polynomial (Polynomial K)) (RatYZ K) (derivative (specAt P0 R)))
        * X ^ (j + 1)

/-- **The rational functions `α_{ν,j}(Y, Z) ∈ F̄_q(Y, Z)`** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4.2, (7), p.28): `α_0 = Y` and
`α_j` (`j ≥ 1`) the coefficient of `t^j` added at step `j` of the recursion (`liftSeq`). -/
noncomputable def alpha {K F : Type*} [Field K] [Field F] [Algebra K F] (P0 : Place K F)
    (t : F) (R : Polynomial (Polynomial F)) (j : ℕ) : RatYZ K :=
  (liftSeq P0 t R j).coeff j

end AGProxGap.Supplement


