-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_Negligible
-- name    : PPADSIS_SubexpSIS_Negligible
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:45:28.411209+00:00
-- url     : https://prove2.me/theorems/6a0cbce0-cd61-409c-bd29-a3154083d1f7
-- title:
--   Negligible functions and polynomially bounded functions
-- statement:
--   A function $\nu:\mathbb N\to\mathbb R$ is **negligible** if it is nonnegative and, for every real constant $c>0$, there is $\lambda_0$ with
--   $$\nu(\lambda)\le\lambda^{-c}\qquad\text{for all }\lambda\ge\lambda_0 .$$
--   A function $p:\mathbb N\to\mathbb N$ is **polynomially bounded** if $p(\lambda)\le(\lambda+2)^c$ for one exponent $c$ and every $\lambda$.
--
--   These are the asymptotic notions of the paper: $\mathrm{negl}(\lambda)$ in every hardness statement, and "polynomially bounded" for the lattice parameters $n=n(\lambda)$ and $m=m(\lambda)$ of Assumption 3.5.
--
--   **Formalization Note** The body is that of the published `NoisyOWMPC.Negligible` / `NoisyOWMPC.PolyBounded`, which are not modules of this workspace and so are redefined here.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 19, §3 Notation (negl(λ)); p. 21, Assumption 3.5 (polynomially bounded)

import Mathlib

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- **Negligible functions** (Choudhuri, *PPAD Hardness from SIS*, STOC 2027 submission
(manuscript sha256 17abad73…), §3 Notation, p. 19: "negl(λ) for a negligible function of λ").
A function `ν : ℕ → ℝ` is negligible if it is nonnegative and, for every real `c > 0`,
`ν(λ) ≤ λ^{−c}` for all sufficiently large `λ`.

**Formalization Note** Same body as the published `NoisyOWMPC.Negligible`, which is not a module
of this workspace. -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  (∀ lam, 0 ≤ ν lam) ∧ ∀ c : ℝ, 0 < c → ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, ν lam ≤ (lam : ℝ) ^ (-c)

/-- A function `p : ℕ → ℕ` is **polynomially bounded**: `p(λ) ≤ (λ + 2)^c` for one exponent `c`
and every `λ` (p. 21, Assumption 3.5: "polynomially bounded `n = n(λ)`", "polynomially bounded
`m = m(λ)`"). -/
def PolyBounded (p : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ lam, p lam ≤ (lam + 2) ^ c

end PPADSIS.SubexpSIS


