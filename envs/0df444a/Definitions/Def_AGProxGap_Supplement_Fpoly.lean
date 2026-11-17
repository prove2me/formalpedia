-- Prove2me | Definitions.Def_AGProxGap_Supplement_Fpoly
-- name    : AGProxGap_Supplement_Fpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:19:22.76492+00:00
-- url     : https://prove2.me/theorems/6f2cea96-6ea2-42a1-b4e8-93164424e9c0
-- title:
--   The polynomials $F_i$ of (9)
-- statement:
--   For fixed $\nu$, with $\mu=\mu_\nu$, the rational functions $\alpha_j=\alpha_{\nu,j}$ of (7), coefficients $\lambda_{i,0},\dots,\lambda_{i,\mu m}\in\overline{\mathbb F}_q$ and $r_i(Z)=\sum_ju_{j,i}Z^j$,
--   $$F_i(Y,Z):=\bigl(\partial_YR_{\nu,P_0}(Y,Z)\bigr)^{2\mu m}\Bigl(\sum_{j=0}^{\mu m}\lambda_{i,j}\alpha_j(Y,Z)-r_i(Z)^{\mu}\Bigr).\tag{9}$$
--
--   By Lemma 4.7 it is a polynomial whose vanishing at $(y_z,z)$ detects agreement $f_z(P_i)=r_i(z)$; Theorem 4.8 sorts coordinates by whether a factor $H$ divides $F_i$.
--
--   **Formalization Note** $F_i$ is formed in $\overline{\mathbb F}_q(Y,Z)$ exactly as displayed; that it is a polynomial is Lemma 4.7 and is not built into the definition.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §4.2, (9), p.30

import Mathlib
import Definitions.Def_AGProxGap_Supplement_liftSeq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

namespace AGProxGap.Supplement

/-- **The polynomials `F_i` of (9)** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4.2, (9), p.30: "For each i ∈ [n], define
F_i(Y, Z) := (∂_Y R_{ν,P_0}(Y, Z))^{2μ_ν m} (Σ_{j=0}^{μ_ν m} λ_{i,j} α_{ν,j}(Y, Z) − r_i(Z)^{μ_ν})
∈ F̄_q[Y, Z]").

Inputs: the point `P_0`, the local parameter `t`, the polynomial `R = R_ν`, `μ = μ_ν`, `m`,
the coefficients `λ_{i,0}, …, λ_{i,μm}` (`lam`), and `r_i(Z)` with coefficients in `F̄_q`.

**Formalization Note** `F_i` is formed in the field `F̄_q(Y, Z)` (`RatYZ`) exactly as the
displayed expression; that it lies in `F̄_q[Y, Z]` is the content of Lemma 4.7 and is not built
in. "`H | F_i` in `F̄_q[Y, Z]`" is then stated as `F_i = H·G` for some polynomial `G`. -/
noncomputable def Fpoly {K F : Type*} [Field K] [Field F] [Algebra K F] (P0 : Place K F)
    (t : F) (R : Polynomial (Polynomial F)) (μ m : ℕ) (lam : ℕ → K) (ri : Polynomial K) :
    RatYZ K :=
  algebraMap (Polynomial (Polynomial K)) (RatYZ K) (derivative (specAt P0 R)) ^ (2 * μ * m) *
    ((∑ j ∈ Finset.range (μ * m + 1),
        algebraMap (Polynomial (Polynomial K)) (RatYZ K) (C (C (lam j))) * alpha P0 t R j)
      - algebraMap (Polynomial (Polynomial K)) (RatYZ K) (C ri) ^ μ)

end AGProxGap.Supplement


