-- Prove2me | Definitions.Def_LaconicBarrier_THardAt
-- name    : LaconicBarrier_THardAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:26.734202+00:00
-- url     : https://prove2.me/theorems/b508bfd9-3eb2-432c-b395-daf7ba1b07bd
-- title:
--   Target hardness: $T$-hard at a target-parameter map
-- statement:
--   Let $T(\lambda, n) \ge \lambda + n$, let $f$ be a target-parameter map and let $p$ bound the allowed index lengths. A game $(\mathcal C, c)$ is **$T$-hard at $f$** if for every constant $K > 0$ there is a positive security bound $\Gamma'$ such that $(\mathcal C, c)$ has $\Gamma'$-security and
--   $$
--   \Gamma'\bigl(f(1^\lambda, n)\bigr) \ge T(\lambda, n)^K
--   $$
--   for all sufficiently large $\lambda$ and all $n \le p(\lambda)$.
--
--   For $f(1^\lambda,n) = \lambda$ and polynomial $T$ this is polynomial security; it is the hypothesis on the target assumption in all of the paper's lower bounds.
--
--   **Formalization Note** $K$ ranges over positive integers, which is equivalent since $T \ge 1$ for large $\lambda$. The hypothesis $T \ge \lambda + n$ is stated by the theorems.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.12, p.21

import Mathlib
import Definitions.Def_LaconicBarrier_HasSecurity

namespace LaconicBarrier

/-- **Target hardness** (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256
1af78662…), Definition 4.12, p.21): the game `(C, c)` is `T`-hard at the target-parameter map `f`,
for index lengths bounded by `p`, if for every constant `K > 0` there is a positive security bound
`Γ′` such that `(C, c)` has `Γ′`-security and `Γ′(f(1^λ, n)) ≥ T(λ, n)^K` for all sufficiently large
`λ` and all `n ≤ p(λ)`.

**Formalization Note** `K` ranges over positive integers; since `T(λ, n) ≥ λ + n ≥ 1` for large `λ`,
this is the same as all real `K > 0`. The paper's standing hypothesis `T(λ, n) ≥ λ + n` is a
hypothesis of the theorems that use this definition. -/
def THardAt (G : Game) (T : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, 0 < K → ∃ Γ' : ℕ → ℕ, (∀ l, 0 < Γ' l) ∧ HasSecurity G Γ' ∧
    ∀ᶠ lam : ℕ in Filter.atTop, ∀ n ≤ p lam, T lam n ^ K ≤ Γ' (f lam n)

end LaconicBarrier


