-- Prove2me | Definitions.Def_KedlayaUmans_Reduction_Psi
-- name    : KedlayaUmans_Reduction_Psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:23.758136+00:00
-- url     : https://prove2.me/theorems/1883aa5a-2629-45f3-970e-9f72e7e61823
-- title:
--   Definition 2.3 — the inverse Kronecker map $\psi_{h,\ell}$
-- statement:
--   Let $R$ be a commutative ring and let $h, \ell \ge 0$ be integers. For a natural number $a$, write $a$ in base $h$, $a = \sum_{j \ge 0} a_j h^j$ with digits $0 \le a_j < h$, and set
--   $$
--   M_a(Y_0, \dots, Y_{\ell-1}) = Y_0^{a_0} Y_1^{a_1} \cdots Y_{\ell-1}^{a_{\ell-1}} .
--   $$
--   The **inverse Kronecker map**
--   $$
--   \psi_{h,\ell} : R[X_0, \dots, X_{m-1}] \to R[Y_{0,0}, \dots, Y_{m-1,\ell-1}]
--   $$
--   sends a monomial $X_0^{e_0} \cdots X_{m-1}^{e_{m-1}}$ to $\prod_{i} M_{e_i}(Y_{i,0}, \dots, Y_{i,\ell-1})$ and is extended $R$-linearly. So the exponent of $Y_{i,j}$ in the image of a monomial is the $j$-th base-$h$ digit of the exponent of $X_i$; digits in positions $j \ge \ell$ are dropped.
--
--   The map increases the number of variables from $m$ to $m\ell$ while lowering every individual degree below $h$. It is $R$-linear but not multiplicative, because base-$h$ digits do not add.
--
--   **Formalization Note** The variables $X_i$ are indexed by `Fin m` and the $Y_{i,j}$ by `Fin m × Fin ℓ` (0-based, as in the paper). The auxiliary `digitExp h ℓ e` is the exponent vector $(i,j) \mapsto$ ($j$-th base-$h$ digit of $e_i$), computed with `Nat.digits` (0 beyond the last digit). `psi h ℓ f` is the sum over the support of $f$ of the coefficient times the image monomial. The definition is meaningful for $h \ge 2$; every statement assumes it.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 8, Definition 2.3

import Mathlib

namespace KedlayaUmans.Reduction

open MvPolynomial

/-- Base-`h` digit vector of an exponent vector (Definition 2.3): the exponent `e i` of the
variable `X_i` is written in base `h`, `e i = ∑_{j ≥ 0} a_j h^j`, and the new variable `Y_{i,j}`
(for `j = 0, …, ℓ - 1`) receives the exponent `a_j`, the `j`-th base-`h` digit of `e i`
(`0` if `e i` has fewer digits). Digits at positions `≥ ℓ` are dropped, as `M_a` uses only
`a_0, …, a_{ℓ-1}`. -/
noncomputable def digitExp {m : ℕ} (h ℓ : ℕ) (e : Fin m →₀ ℕ) : (Fin m × Fin ℓ) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ij => (Nat.digits h (e ij.1)).getD ij.2 0

/-- The map `ψ_{h,ℓ} : R[X_0, …, X_{m-1}] → R[Y_{0,0}, …, Y_{m-1,ℓ-1}]` of Definition 2.3
(Kedlaya–Umans, p. 8): the monomial `∏ᵢ Xᵢ^{eᵢ}` goes to `∏ᵢ M_{eᵢ}(Y_{i,0}, …, Y_{i,ℓ-1})`,
where `M_a(Y_0, …, Y_{ℓ-1}) = Y_0^{a_0} ⋯ Y_{ℓ-1}^{a_{ℓ-1}}` for the base-`h` digits `a_j` of `a`,
and the map is extended `R`-linearly. It is not a ring homomorphism. -/
noncomputable def psi {R : Type*} [CommSemiring R] {m : ℕ} (h ℓ : ℕ)
    (f : MvPolynomial (Fin m) R) : MvPolynomial (Fin m × Fin ℓ) R :=
  ∑ e ∈ f.support, monomial (digitExp h ℓ e) (f.coeff e)

end KedlayaUmans.Reduction


