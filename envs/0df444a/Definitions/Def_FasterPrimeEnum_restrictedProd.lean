-- Prove2me | Definitions.Def_FasterPrimeEnum_restrictedProd
-- name    : FasterPrimeEnum_restrictedProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:37:49.751232+00:00
-- url     : https://prove2.me/theorems/82d7a860-394c-4260-8d3c-793542765211
-- title:
--   The restricted product $f\lhd g$
-- statement:
--   Let $R$ be a commutative ring, $f=\sum_{i\ge0}f_ix^i\in R[[x]]$ and $g=\sum_{j\ge0}g_jx^{-j}\in R[[x^{-1}]]$. The **restricted product** of $f$ and $g$ is
--
--   $$
--   (f\lhd g)(x)=\sum_{j\ge0,\ i\ge2j} f_i\,g_j\,x^{i-j}\in R[[x]].
--   $$
--
--   Its coefficient of $x^n$ is $\sum_{j=0}^{n} f_{n+j}\,g_j$, a finite sum. It keeps the part of the formal product $f(x)g(x)$ that corresponds to the indefinite form $a^2-2b^2$, and defines the series $H_2$.
--
--   **Formalization Note** Series are given by their coefficient functions $\mathbb N\to R$; the coefficient $g_j$ belongs to $x^{-j}$.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Definition 2.2, eq. (2.1), p.14

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **The restricted product** `f ⊲ g` — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), Definition 2.2, eq. (2.1), p.14: for
`f = Σ_{i⩾0} f_i x^i ∈ R⟦x⟧` and `g = Σ_{j⩾0} g_j x^{−j} ∈ R⟦x⁻¹⟧`,
`(f ⊲ g)(x) := Σ_{j⩾0, i⩾2j} f_i g_j x^{i−j} ∈ R⟦x⟧`.

A series is given by its coefficient function: `f i` is the coefficient of `x^i` and `g j` the
coefficient of `x^{−j}`. The coefficient of `x^n` in `f ⊲ g` is `restrictedProd f g n`.

**Formalization Note.** The pairs `(i, j)` with `i ⩾ 2j ⩾ 0` and `i − j = n` are exactly
`(n + j, j)` with `0 ⩽ j ⩽ n`, so the coefficient is `Σ_{j=0}^{n} f_{n+j} g_j`. -/
def restrictedProd {R : Type*} [CommRing R] (f g : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range (n + 1), f (n + j) * g j

end FasterPrimeEnum


