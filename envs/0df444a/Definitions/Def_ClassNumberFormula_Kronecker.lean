-- Prove2me | Definitions.Def_ClassNumberFormula_Kronecker
-- name    : ClassNumberFormula_Kronecker
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T12:51:56.863998+00:00
-- url     : https://prove2.me/theorems/9b141454-d8ac-4ce8-8f34-8098e6573249
-- title:
--   Kronecker symbol $\left(\frac{d}{m}\right)$ and fundamental discriminants
-- statement:
--   This file defines the two arithmetic notions used to state Dirichlet's class number formula.
--
--   1. **Fundamental discriminant.** An integer $d$ is a *fundamental discriminant* if $d \neq 1$ and either $d \equiv 1 \pmod 4$ and $d$ is squarefree, or $d = 4m$ with $m \equiv 2$ or $3 \pmod 4$ and $m$ squarefree. These are exactly the discriminants of quadratic number fields.
--
--   2. **Kronecker symbol.** For an integer $d$ and a natural number $m \ge 1$, write $m = 2^k m'$ with $m'$ odd. The Kronecker symbol is
--   $$\left(\frac{d}{m}\right) = \left(\frac{d}{2}\right)^{k}\left(\frac{d}{m'}\right),$$
--   where $\left(\frac{d}{m'}\right)$ is the Jacobi symbol and $\left(\frac{d}{2}\right)$ equals $0$ if $d$ is even, $1$ if $d \equiv \pm 1 \pmod 8$ and $-1$ if $d \equiv \pm 3 \pmod 8$. For $m = 0$ the value is $1$ if $d = \pm 1$ and $0$ otherwise.
--
--   For a fundamental discriminant $d$, the map $m \mapsto \left(\frac{d}{m}\right)$ is the real Dirichlet character $\chi$ modulo $|d|$ appearing in Dirichlet's class number formula.
--
--   **Formalization Note** `kroneckerTwo d` is Mathlib's character `ZMod.χ₈` evaluated at $d \bmod 8$; the odd part uses Mathlib's `jacobiSym`. The value at $m = 0$ never enters an $L$-series.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula" (definitions of $d$ and $\chi$); H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer 2000, Ch. 6 (pp. 43–53)

import Mathlib

namespace ClassNumberFormula

/-- The Kronecker symbol `(d/2)`: `0` if `d` is even, `1` if `d ≡ ±1 (mod 8)`,
`-1` if `d ≡ ±3 (mod 8)`. -/
def kroneckerTwo (d : ℤ) : ℤ := ZMod.χ₈ (d : ZMod 8)

/-- The Kronecker symbol `(d/m)` for an integer `d` and a natural number `m`.
For `m ≥ 1`, writing `m = 2^k * m'` with `m'` odd, it is `(d/2)^k * (d/m')`, where `(d/m')`
is the Jacobi symbol. For `m = 0` it is `1` if `d = ±1` and `0` otherwise. -/
def kroneckerSymbol (d : ℤ) (m : ℕ) : ℤ :=
  if m = 0 then (if d = 1 ∨ d = -1 then 1 else 0)
  else kroneckerTwo d ^ (m.factorization 2) * jacobiSym d (m / 2 ^ (m.factorization 2))

/-- `d` is a fundamental discriminant: `d ≠ 1` and either `d ≡ 1 (mod 4)` is squarefree, or
`d = 4m` with `m ≡ 2, 3 (mod 4)` squarefree. -/
def IsFundamentalDiscriminant (d : ℤ) : Prop :=
  d ≠ 1 ∧ ((d % 4 = 1 ∧ Squarefree d) ∨
    (∃ m : ℤ, d = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m))

end ClassNumberFormula


