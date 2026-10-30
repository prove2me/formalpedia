-- Prove2me | Definitions.Def_KUModComp_psi
-- name    : KUModComp_psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:57:22.281455+00:00
-- url     : https://prove2.me/theorems/cd13bef3-54a8-471f-8c8a-7185c56d6859
-- title:
--   The map $\psi_{h,\ell}$, inverse of the Kronecker substitution
-- statement:
--   Let $R$ be a commutative ring and $h, \ell \in \mathbb N$ (meant: $h \ge 2$). For an exponent $a \in \mathbb N$ write $a$ in base $h$, $a = \sum_{j \ge 0} a_j h^j$ with $a_j = \lfloor a/h^j \rfloor \bmod h$, and set
--   $$
--   M_a(Y_0,\dots,Y_{\ell-1}) = Y_0^{a_0} Y_1^{a_1} \cdots Y_{\ell-1}^{a_{\ell-1}} .
--   $$
--   The map
--   $$
--   \psi_{h,\ell} : R[X_0,\dots,X_{m-1}] \to R[Y_{0,0},\dots,Y_{m-1,\ell-1}]
--   $$
--   is the $R$-linear map sending each monomial $X_0^{a^{(0)}} \cdots X_{m-1}^{a^{(m-1)}}$ to $\prod_{i<m} M_{a^{(i)}}(Y_{i,0},\dots,Y_{i,\ell-1})$: it sends $X_i^a$ to $M_a(Y_{i,0},\dots,Y_{i,\ell-1})$ and extends multilinearly. Digits $a_j$ with $j \ge \ell$ are dropped, as in $M_a$.
--
--   It increases the number of variables from $m$ to $\ell m$ and lowers the individual degrees to at most $h-1$; it is the first step of the reduction of Theorem 3.1.
--
--   **Formalization Note** The variable $Y_{i,j}$ is `X (i, j)` of `MvPolynomial (Fin m × Fin ℓ) R`. `psi` is defined on the monomial basis (`Basis.constr`), with exponent map `psiExp`.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Definition 2.3, p. 8

import Mathlib

open MvPolynomial

namespace KUModComp

variable {R : Type*} [CommRing R]

/-- The exponent map of `ψ_{h,ℓ}`: the exponent `a` of `X_i` is written in base `h`,
`a = ∑_{j ≥ 0} a_j h^j`, and `Y_{i,j}` gets exponent `a_j = (a / h^j) mod h` for `j < ℓ`.
Digits of index `≥ ℓ` are dropped, as in the paper's `M_a(Y_0, …, Y_{ℓ-1})`. -/
noncomputable def psiExp {m : ℕ} (h ℓ : ℕ) (e : Fin m →₀ ℕ) : Fin m × Fin ℓ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => e p.1 / h ^ (p.2 : ℕ) % h

/-- **The map `ψ_{h,ℓ}`** (Definition 2.3, Kedlaya–Umans, Dagstuhl 08381 (2008), p. 8): the
`R`-linear map `R[X_0, …, X_{m-1}] → R[Y_{0,0}, …, Y_{m-1,ℓ-1}]` sending the monomial
`X_0^{a^{(0)}} ⋯ X_{m-1}^{a^{(m-1)}}` to `∏_i M_{a^{(i)}}(Y_{i,0}, …, Y_{i,ℓ-1})`, where
`M_a(Y_0, …, Y_{ℓ-1}) = Y_0^{a_0} ⋯ Y_{ℓ-1}^{a_{ℓ-1}}` and `a = ∑_j a_j h^j` in base `h`
("sends `X_i^a` to `M_a(Y_{i,0}, …, Y_{i,ℓ-1})` and extends multilinearly"). The variable
`Y_{i,j}` is `X (i, j)`. It is meant for `h ≥ 2`. -/
noncomputable def psi {m : ℕ} (h ℓ : ℕ) : MvPolynomial (Fin m) R →ₗ[R] MvPolynomial (Fin m × Fin ℓ) R :=
  (basisMonomials (Fin m) R).constr R fun e => monomial (psiExp h ℓ e) 1

end KUModComp


