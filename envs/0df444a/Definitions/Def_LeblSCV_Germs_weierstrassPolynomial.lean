-- Prove2me | Definitions.Def_LeblSCV_Germs_weierstrassPolynomial
-- name    : LeblSCV_Germs_weierstrassPolynomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:04.151953+00:00
-- url     : https://prove2.me/theorems/f846ba3a-38ce-4937-a6db-bbfa42719160
-- title:
--   Definition 6.2.2 — Weierstrass polynomial
-- statement:
--   Let $U \subset \mathbb{C}^{n-1}$ be open with $0 \in U$, and write $z' \in \mathbb{C}^{n-1}$ for its coordinates. A monic polynomial $P \in \mathcal{O}(U)[z_n]$ of degree $k \ge 0$,
--   $$ P(z', z_n) = z_n^k + \sum_{\ell=0}^{k-1} c_\ell(z')\, z_n^\ell, $$
--   whose coefficients $c_\ell$ are holomorphic on $U$ with $c_\ell(0) = 0$ for all $\ell$, is a **Weierstrass polynomial** of degree $k$. For $n = 1$ the only Weierstrass polynomial of degree $k$ is $z_n^k$; for $k = 0$ it is $P = 1$.
--
--   Weierstrass polynomials replace the model $z^k$ of one-variable theory: the preparation theorem says that, after a normalization, every holomorphic function near the origin is a nonvanishing function times a Weierstrass polynomial.
--
--   **Formalization Note.** $\mathbb{C}^{n-1}$ is `Fin d → ℂ` (with $d = n - 1$), and a point of $\mathbb{C}^{n-1} \times \mathbb{C}$ is a pair `(z', z_n)`. The polynomial is given by its coefficient tuple `c : Fin k → (Fin d → ℂ) → ℂ`; `weierstrassPolyFun c (z', z_n)` evaluates $z_n^k + \sum_{\ell<k} c_\ell(z') z_n^\ell$ (monic of degree $k$ by construction), and `IsWeierstrassPolynomial U c` says that $U$ is open, $0 \in U$, and every $c_\ell$ is holomorphic (`DifferentiableOn ℂ`) on $U$ with $c_\ell(0) = 0$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 169, Definition 6.2.2

import Mathlib

namespace LeblSCV.Germs

/-- The monic polynomial in `z_n` of degree `k` with coefficient functions `c_0, …, c_{k-1}` of
`z' ∈ ℂ^{n-1}` (Lebl, p. 169), evaluated at `z = (z', z_n) ∈ ℂ^{n-1} × ℂ`:
`P(z', z_n) = z_nᵏ + ∑_{ℓ=0}^{k-1} c_ℓ(z') z_nˡ`. Here `ℂ^{n-1}` is `Fin d → ℂ` (`d = n - 1`). -/
def weierstrassPolyFun {d k : ℕ} (c : Fin k → (Fin d → ℂ) → ℂ) (z : (Fin d → ℂ) × ℂ) : ℂ :=
  z.2 ^ k + ∑ ℓ : Fin k, c ℓ z.1 * z.2 ^ (ℓ : ℕ)

/-- Definition 6.2.2 (Lebl, p. 169). Let `U ⊆ ℂ^{n-1}` be open with `0 ∈ U`. The monic polynomial
`P(z', z_n) = z_nᵏ + ∑_{ℓ=0}^{k-1} c_ℓ(z') z_nˡ ∈ 𝒪(U)[z_n]` of degree `k ≥ 0` is a Weierstrass
polynomial of degree `k` if every coefficient `c_ℓ` is holomorphic on `U` and `c_ℓ(0) = 0`. -/
def IsWeierstrassPolynomial {d k : ℕ} (U : Set (Fin d → ℂ)) (c : Fin k → (Fin d → ℂ) → ℂ) :
    Prop :=
  IsOpen U ∧ (0 : Fin d → ℂ) ∈ U ∧ ∀ ℓ : Fin k, DifferentiableOn ℂ (c ℓ) U ∧ c ℓ 0 = 0

end LeblSCV.Germs


