-- Prove2me | Definitions.Def_OgawaNagaoka_matPow
-- name    : OgawaNagaoka_matPow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:22:34.391509+00:00
-- url     : https://prove2.me/theorems/1e5e7837-5db4-4227-8a40-df4da2dc5d5c
-- title:
--   Operator power $B^p$ by functional calculus
-- statement:
--   For a Hermitian matrix $B=\sum_\lambda \lambda P_\lambda$ (spectral decomposition) and a real exponent $p$, the operator power is
--
--   $$
--   B^p=\sum_\lambda \lambda^p P_\lambda .
--   $$
--
--   The paper uses the powers $\rho^{1/\beta}$, $(\cdot)^\beta$, $S^{\beta-1}$ and $A^\gamma$ of positive semidefinite operators throughout; all of them are instances of this definition.
--
--   **Formalization Note** The power is `cfc (fun x : ℝ => x ^ p) B` with Lean's real power, so $0^p=0$ for $p\neq0$ and $0^0=1$. For $p<0$ the eigenvalue $0$ is sent to $0$: $B^p$ is then the power taken on the support of $B$ (a generalized inverse power), and $B^0=I$. The statements apply it only to positive semidefinite matrices.
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, pp.2–9 (operator powers in (1)–(8), (11), (17)–(18))

import Mathlib

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, pp.2–9 (the operator powers `ρ^{1/β}`, `(·)^β`, `S^{β−1}`, `A^γ`): the
real power `B^p` of a matrix, computed by the continuous functional calculus,
`B^p = Σ_λ λ^p P_λ` over the spectral decomposition of a Hermitian `B`.

**Formalization Note.** `matPow B p = cfc (fun x : ℝ => x ^ p) B` with Lean's `Real.rpow`. On a
positive semidefinite `B` and `p > 0` this is the usual power (`0 ^ p = 0`). For `p < 0` the
eigenvalue `0` is sent to `0` (`0 ^ p = 0` for `p ≠ 0`), so `B^p` is the power taken on the support
of `B` (a generalized inverse power); for `p = 0` the value is the identity (`0 ^ 0 = 1`). `cfc`
returns `0` on a non-Hermitian argument; every statement of this mission applies `matPow` only to
positive semidefinite matrices. -/
noncomputable def matPow {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (p : ℝ) :
    Matrix ι ι ℂ :=
  cfc (fun x : ℝ => x ^ p) B

end OgawaNagaoka


