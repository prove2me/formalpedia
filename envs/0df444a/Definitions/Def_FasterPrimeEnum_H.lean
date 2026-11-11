-- Prove2me | Definitions.Def_FasterPrimeEnum_H
-- name    : FasterPrimeEnum_H
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:36.998186+00:00
-- url     : https://prove2.me/theorems/2d39e351-9373-4435-ad2c-d60f0ba9a937
-- title:
--   The series $F$, $G_d$, $H_d$ for $d\in D=\{-1,-2,2\}$
-- statement:
--   Let $D=\{-1,-2,2\}$ and, for odd $n$, $\chi_d(n)=\left(\frac dn\right)$ (the Jacobi symbol). Define
--
--   $$
--   F(x)=\sum_{a\ge1,\ a\text{ odd}}x^{a^2},\quad G_{-1}(x)=\sum_{b\ge1}x^{4b^2},\quad G_{-2}(x)=\sum_{b\ge1}x^{2b^2},\quad G_{2}(x)=\sum_{b\ge1}x^{-2b^2},
--   $$
--
--   and
--
--   $$
--   H_{-1}=F\cdot G_{-1},\qquad H_{-2}=F\cdot G_{-2},\qquad H_2=F\lhd G_2,
--   $$
--
--   all in $\mathbb Z[[x]]$ except $G_2\in\mathbb Z[[x^{-1}]]$. For example $H_{-1,65}=2$, $H_{-2,99}=3$ and $H_{2,119}=2$.
--
--   Modulo $2$ these series detect the odd square-primes (Theorem 2.6), and their sum is the generating function the core algorithm evaluates.
--
--   **Formalization Note** Each series is its coefficient function $\mathbb N\to\mathbb Z$; for $G_2$ the coefficient at $j$ belongs to $x^{-j}$. The functions are $0$ for $d\notin D$.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Definitions 2.1 and 2.4, pp.13–15

import Mathlib
import Definitions.Def_FasterPrimeEnum_restrictedProd

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **The index set `D := {−1, −2, 2}`** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), Definition 2.1, p.13. The character
`χ_d(n) := (d/n)` for odd `n` is Mathlib's Jacobi symbol `jacobiSym d n`. -/
def D : Finset ℤ := {-1, -2, 2}

/-- **`F(x) := Σ_{a⩾1, a odd} x^{a²}`** — Definition 2.4, eq. (2.2), p.14. The coefficient of
`x^i`: the number of odd `a` with `a² = i` (`0` or `1`). -/
def F (i : ℕ) : ℤ := ((Finset.range (i + 1)).filter fun a => a % 2 = 1 ∧ a ^ 2 = i).card

/-- **`G_d`** — Definition 2.4, eqs. (2.3)–(2.5), p.14:
`G_{−1}(x) := Σ_{b⩾1} x^{4b²} ∈ Z⟦x⟧`, `G_{−2}(x) := Σ_{b⩾1} x^{2b²} ∈ Z⟦x⟧`,
`G_2(x) := Σ_{b⩾1} x^{−2b²} ∈ Z⟦x⁻¹⟧`.

`G d j` is the coefficient of `x^j` for `d = −1, −2`, and the coefficient of `x^{−j}` for
`d = 2` (the paper's `G_{2,j}`, p.15). It is `0` for `d ∉ D`. -/
def G (d : ℤ) (j : ℕ) : ℤ :=
  if d = -1 then ((Finset.range (j + 1)).filter fun b => 1 ≤ b ∧ 4 * b ^ 2 = j).card
  else if d = -2 ∨ d = 2 then ((Finset.range (j + 1)).filter fun b => 1 ≤ b ∧ 2 * b ^ 2 = j).card
  else 0

/-- **`H_d`** — Definition 2.4, p.15: `H_{−1} := F · G_{−1}`, `H_{−2} := F · G_{−2}`,
`H_2 := F ⊲ G_2`, all in `Z⟦x⟧`. `H d n` is the coefficient of `x^n` (the paper's `H_{d,n}`):
the Cauchy product `Σ_{i=0}^{n} F_i G_{d,n−i}` for `d = −1, −2`, and the restricted product
`Σ_{j=0}^{n} F_{n+j} G_{2,j}` (Definition 2.2) for `d = 2`. -/
def H (d : ℤ) (n : ℕ) : ℤ :=
  if d = 2 then restrictedProd F (G 2) n
  else ∑ i ∈ Finset.range (n + 1), F i * G d (n - i)

end FasterPrimeEnum


