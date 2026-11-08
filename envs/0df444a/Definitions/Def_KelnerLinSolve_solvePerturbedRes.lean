-- Prove2me | Definitions.Def_KelnerLinSolve_solvePerturbedRes
-- name    : KelnerLinSolve_solvePerturbedRes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:15.956684+00:00
-- url     : https://prove2.me/theorems/9679909b-54db-4439-90cd-696cb6539062
-- title:
--   $T_A$ and the residuals of Algorithm 1 (SolvePerturbed)
-- statement:
--   For $A \in \mathbb Z^{n\times n}$ and $b\in\mathbb Z^n$, $T_A = \max\{1, \max_{i,j}|A_{ij}|, \max_i|b_i|\}$. Lines 3–4 of Algorithm 1, $\mathrm{SolvePerturbed}(A,b,R)$, compute $b_0 = b$ and
--
--   $$
--   x_i = b_i \bmod R \in \{0,\dots,R-1\}^n, \qquad b_{i+1} = \frac{b_i - x_i}{R} - A x_i .
--   $$
--
--   This is Dixon's recurrence for $M = RA + I$ with $C = I$.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §3.1, p.9, Algorithm 1

import Mathlib
import Definitions.Def_KelnerLinSolve_dixonRes

open Matrix

namespace KelnerLinSolve

/-- `T_A = max{1, max_{i,j} |A_{ij}|, max_i |b_i|}` for an integer system `(A, b)` (Kelner,
*Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission (sha256 d1af55cb…),
§3.1, p.9, and Theorem 3.3, p.10). -/
def heightTA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) : ℕ :=
  max 1 (max (Finset.univ.sup fun p : Fin n × Fin n => (A p.1 p.2).natAbs)
    (Finset.univ.sup fun i => (b i).natAbs))

/-- The residuals of Lines 3–4 of **Algorithm 1** `SolvePerturbed(A, b, R)` (Kelner,
sha256 d1af55cb…, §3.1, p.9): `b₀ = b`, `xᵢ = bᵢ mod R ∈ {0, …, R − 1}ⁿ`,
`b_{i+1} = (bᵢ − xᵢ)/R − A xᵢ`.

**Formalization Note.** `%` and `/` on `ℤ` are `Int.emod` and `Int.ediv`; `bᵢ − xᵢ` is divisible by
`R`, so the division is exact. -/
def solvePerturbedRes {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (R : ℤ) (b : Fin n → ℤ) :
    ℕ → (Fin n → ℤ)
  | 0 => b
  | i + 1 => fun r =>
      (solvePerturbedRes A R b i r - solvePerturbedRes A R b i r % R) / R
        - (A *ᵥ fun c => solvePerturbedRes A R b i c % R) r

end KelnerLinSolve


