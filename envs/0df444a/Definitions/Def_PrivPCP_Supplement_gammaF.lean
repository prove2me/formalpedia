-- Prove2me | Definitions.Def_PrivPCP_Supplement_gammaF
-- name    : PrivPCP_Supplement_gammaF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:52:03.359302+00:00
-- url     : https://prove2.me/theorems/fe48f997-a229-4bf4-a09d-f3f774b64474
-- title:
--   The weighted common-zero count $\Gamma_F$ on the normalization $\mathcal X_F$ (eq. (18))
-- statement:
--   Let $\mathbb K$ be a field and $L=\mathbb K(\mathcal X_F)$ the function field of a curve over $\mathbb K$, with coordinate functions $x,y\in L$, and let $n_1,n_2$ be positive integers. The **weighted common-zero count** is
--   $$
--   \Gamma_F=\sum_{\nu\in\mathcal X_F:\ x(\nu),\,y(\nu)\in\mathbb K^\times}\min\bigl\{\operatorname{ord}_\nu(1-x^{n_1}),\ \operatorname{ord}_\nu(1-y^{n_2})\bigr\}.
--   $$
--   The points $\nu$ of the normalization $\mathcal X_F$ are the places of $L/\mathbb K$: the valuation subrings $\mathcal O_\nu\subsetneq L$ containing $\mathbb K$, each a discrete valuation ring with normalized order $\operatorname{ord}_\nu$. The condition $x(\nu),y(\nu)\in\mathbb K^\times$ (both coordinates finite and nonzero at $\nu$) is $\operatorname{ord}_\nu(x)=\operatorname{ord}_\nu(y)=0$. A singular point of the affine curve contributes once for each of its branches.
--
--   $\Gamma_F$ is the quantity bounded by the Corvaja–Zannier estimate (Theorem 4.12); at a nonsingular point of the subgroup grid $\{\alpha^{n_1}=\beta^{n_2}=1\}$ on $F=0$ the term is $1$, so for a curve whose grid points are all nonsingular $\Gamma_F$ counts them.
--
--   **Formalization Note** Places are the published `AlgebraicCurve.Place` (valuation subrings containing $\mathbb K$, other than $L$, that are principal ideal rings; for a function field of a curve every such valuation ring is one) with its normalized order `ord`. At the places summed over, both orders are nonnegative, and the sum is taken in $\mathbb N\cup\{\infty\}$, so it is the actual sum of its terms. Lean's $\operatorname{ord}_\nu(0)=0$; under the hypotheses of Theorem 4.12 the functions $x,y,1-x^{n_1},1-y^{n_2}$ are nonzero.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), §4.4.1, eq. (18), p.23 (PDF p.25)

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

namespace PrivPCP.Supplement

/-- The **weighted common-zero count** `Γ_F` (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC
2027 submission manuscript (sha256 c2cac1e0…), §4.4.1, eq. (18), p.23):
`Γ_F = ∑_{ν ∈ 𝒳_F : x(ν), y(ν) ∈ 𝕂^×} min{ord_ν(1 − x^{n₁}), ord_ν(1 − y^{n₂})}`,
for the function field `L = 𝕂(𝒳_F)` of the curve with coordinate functions `x, y`.

**Formalization Note** The points `ν` of the normalization `𝒳_F` (a smooth projective curve over the
algebraically closed field `𝕂`) are the places of `L/𝕂`: the published `AlgebraicCurve.Place`
(valuation subrings of `L` containing `𝕂`, other than `L`, which are principal ideal rings, as every
such ring of a function field of a curve is), with its normalized order `ord_ν`. "`x(ν) ∈ 𝕂^×`" (`x` is
finite and nonzero at `ν`) is `ord_ν(x) = 0`. At such a place `1 − x^{n₁}` and `1 − y^{n₂}` have
nonnegative order, so the minimum is a natural number; the sum is taken in `ℕ∞`, where it is the
honest (possibly infinite) sum of its terms. Lean's `ord_ν(0) = 0`; under the hypotheses of
Theorem 4.12, `x`, `y`, `1 − x^{n₁}`, `1 − y^{n₂}` are nonzero. -/
noncomputable def gammaF (K L : Type) [Field K] [Field L] [Algebra K L] (x y : L) (n₁ n₂ : ℕ) : ℕ∞ :=
  ∑' v : {v : AlgebraicCurve.Place K L // v.ord x = 0 ∧ v.ord y = 0},
    ((min (v.1.ord (1 - x ^ n₁)) (v.1.ord (1 - y ^ n₂))).toNat : ℕ∞)

end PrivPCP.Supplement


