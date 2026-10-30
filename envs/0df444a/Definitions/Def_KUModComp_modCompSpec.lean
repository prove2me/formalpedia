-- Prove2me | Definitions.Def_KUModComp_modCompSpec
-- name    : KUModComp_modCompSpec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:57:06.0218+00:00
-- url     : https://prove2.me/theorems/b0697adc-68c7-4fa4-9fd0-d5e6b3e46f54
-- title:
--   MODULAR COMPOSITION and the remainder by a polynomial with unit leading coefficient
-- statement:
--   Let $R$ be a commutative ring.
--
--   1. For coefficients $a_0,\dots,a_{N-1} \in R$, $\mathrm{densePoly}(a) = \sum_{j<N} a_j X^j \in R[X]$.
--   2. **Remainder modulo $h$.** If $h \in R[X]$ has leading coefficient a unit $u$, then $u^{-1}h$ is monic, and $p \bmod h$ is the remainder of $p$ on division by the monic polynomial $u^{-1}h$ (division by $h$ and by $u^{-1}h$ have the same remainder).
--   3. **MODULAR COMPOSITION** with parameters $d, m, N$ (Problem 2.2): given $f \in R[X_0,\dots,X_{m-1}]$ with individual degrees at most $d-1$, polynomials $g_0,\dots,g_{m-1} \in R[X]$ of degree at most $N-1$, and $h = \sum_{j \le n} h_j X^j$ of degree $n$ with $h_n = u$ a unit, output
--   $$
--   f(g_0(X),\dots,g_{m-1}(X)) \bmod h(X),
--   $$
--   given by its $n$ coefficients of degrees $0,\dots,n-1$.
--
--   This is the problem whose reduction to MULTIVARIATE MULTIPOINT EVALUATION is Theorem 3.1.
--
--   **Formalization Note** The remainder is Mathlib's `modByMonic` by `h * C u⁻¹`. The degree $n$ of $h$ is part of the input: $h$ is given by exactly $n+1$ coefficients, and $u$ is the unit meant to equal $h_n$ (theorems using `modCompSpec` assume this).
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Problem 2.2, p. 7; dense representation, p. 8

import Mathlib
import Definitions.Def_KUModComp_mmeSpec

open Polynomial

namespace KUModComp

variable {R : Type*} [CommRing R]

/-- A univariate polynomial given by its coefficient list, low degree first:
`densePoly a = ∑_{j < N} a j · X^j`. -/
noncomputable def densePoly {N : ℕ} (a : Fin N → R) : R[X] :=
  ∑ j : Fin N, C (a j) * X ^ (j : ℕ)

/-- **Remainder by a polynomial whose leading coefficient is a unit.** If `hp` has leading
coefficient the unit `u`, then `hp * C u⁻¹` is the monic associate of `hp`, and the remainder of
`p` on division by `hp` is the remainder on division by its monic associate (they generate the
same ideal and have the same degree). `modU p hp u = p %ₘ (hp * C u⁻¹)`. -/
noncomputable def modU (p hp : R[X]) (u : Rˣ) : R[X] :=
  p %ₘ (hp * C ((u⁻¹ : Rˣ) : R))

/-- **MODULAR COMPOSITION** (Problem 2.2, p. 7). Input: the coefficients `f` of
`f(X_0, …, X_{m-1})` with individual degrees at most `d - 1` (see `densePolyMv`), the coefficients
`g i : Fin N → R` of `g_i(X)` (degree at most `N - 1`), the coefficients `h : Fin (n+1) → R` of
`h(X)` of degree `n` (low degree first, `h (Fin.last n)` its leading coefficient), and a unit `u`
(meant to equal `h (Fin.last n)`). Output: the `n` coefficients (degrees `0, …, n-1`) of
`f(g_0(X), …, g_{m-1}(X)) mod h(X)`. -/
noncomputable def modCompSpec {d m N n : ℕ} (f : (Fin m → Fin d) → R) (g : Fin m → Fin N → R)
    (h : Fin (n + 1) → R) (u : Rˣ) : Fin n → R :=
  fun j => (modU (MvPolynomial.aeval (fun i => densePoly (g i)) (densePolyMv f))
    (densePoly h) u).coeff (j : ℕ)

end KUModComp


