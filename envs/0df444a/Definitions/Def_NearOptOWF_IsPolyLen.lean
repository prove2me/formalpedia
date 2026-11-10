-- Prove2me | Definitions.Def_NearOptOWF_IsPolyLen
-- name    : NearOptOWF_IsPolyLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:20.13922+00:00
-- url     : https://prove2.me/theorems/4f7bc6b8-81b9-437d-bcf5-ad64e6c2a6ed
-- title:
--   Polynomially bounded, polynomial-time computable length
-- statement:
--   A length function $m : \mathbb N \to \mathbb N$ is **admissible** if $m(n) \le q(n)$ for a polynomial $q$ and $1^{m(n)}$ can be computed from $1^n$ in polynomial time. These are the output lengths $m$ for which Theorem 4.1 is stated ("$\lambda = \mathrm{poly}(n, m)$").
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace NearOptOWF

open LaconicBarrier

/-- `m : ℕ → ℕ` is a **polynomially bounded, polynomial-time computable length** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem
4.1, p.11 (PDF p.13): functions `{0,1}ⁿ → {0,1}ᵐ` with "`λ = poly(n, m)`"): `m(n) ≤ q(n)` for a
polynomial `q`, and one machine computes `1^{m(n)}` from `1ⁿ` in polynomial time. -/
def IsPolyLen (m : ℕ → ℕ) : Prop :=
  (∃ q : Polynomial ℕ, ∀ n, m n ≤ q.eval n) ∧
  PolyTimeOn (fun n : ℕ => [unary n]) (fun n => unary (m n))

end NearOptOWF


