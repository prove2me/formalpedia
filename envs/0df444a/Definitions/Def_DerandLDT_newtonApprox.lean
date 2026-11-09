-- Prove2me | Definitions.Def_DerandLDT_newtonApprox
-- name    : DerandLDT_newtonApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:46.070911+00:00
-- url     : https://prove2.me/theorems/bb9ff8f5-a30a-4d19-8da2-c0fdd382494e
-- title:
--   Newton iteration $\Phi_k$ with a fixed derivative
-- statement:
--   Let $K$ be a field, $P(Y, Z) \in K[Y, Z]$ and $a \in K$, and write $\alpha = \partial_Z(P)(0, a)$. The **Newton approximations** $\Phi_k(Y) \in K[Y]$ are defined by $\Phi_0 = a$ and, for $k \ge 1$,
--   $$
--   \Phi_k(Y) = \Big(\Phi_{k-1}(Y) - \frac{P(Y, \Phi_{k-1}(Y))}{\alpha}\Big) \bmod Y^{k+1}.
--   $$
--   When $P(0, a) = 0$ and $\alpha \neq 0$, $\Phi_k$ is the degree-$\le k$ truncation of the power-series root $Z = \Phi(Y)$ of $P$ with $\Phi(0) = a$ (Theorem 3.15), and Theorem 3.16 gives it in closed form. The paper applies this over $K = \mathbb F(X)$ to lift a root on an anchor line to a global root (Lemma 4.1).
--
--   **Formalization Note** $P$ is a polynomial in $Z$ whose coefficients are polynomials in $Y$ (`K[X][X]`, $Z$ outer). "mod $Y^{k+1}$" is the remainder modulo the monic $Y^{k+1}$. If $\alpha = 0$ the division is by zero (value $0$); every theorem using the definition assumes $\alpha \neq 0$.
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Theorem 3.15 and Theorem 3.16, p.14

import Mathlib

set_option autoImplicit false

namespace DerandLDT

open Polynomial in
/-- **Newton iteration with a fixed derivative**: for `P(Y, Z) ∈ K[Y, Z]` and `a ∈ K`,
`Φ₀ := a` and, for `k ≥ 1`,
`Φ_k(Y) := (Φ_{k-1}(Y) − P(Y, Φ_{k-1}(Y)) / ∂_Z(P)(0, a)) mod Y^{k+1}`.
Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point low-degree test*,
STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Theorem 3.15 and Theorem 3.16, p.14.

**Formalization Note.** `P : K[X][X]` is a polynomial in `Z` (outer variable) whose
coefficients are polynomials in `Y` (inner variable). `P(Y, Φ)` is `P.eval Φ`,
`∂_Z(P)(0, a)` is `((derivative P).eval (C a)).eval 0`, and "mod `Y^{k+1}`" is the remainder
`%ₘ X ^ (k + 1)`. `newtonApprox P a k` is `Φ_k`. When `∂_Z(P)(0, a) = 0` the division is by
zero (Lean's `0⁻¹ = 0`); the theorems that use the definition assume `∂_Z(P)(0, a) ≠ 0`, as the
paper does. -/
noncomputable def newtonApprox {K : Type*} [Field K] (P : K[X][X]) (a : K) : ℕ → K[X]
  | 0 => C a
  | k + 1 =>
      (newtonApprox P a k -
          C (((derivative P).eval (C a)).eval 0)⁻¹ * P.eval (newtonApprox P a k)) %ₘ
        X ^ (k + 2)

end DerandLDT


