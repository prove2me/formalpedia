-- Prove2me | Definitions.Def_QuantumLinSys_Chebyshev_Setting
-- name    : QuantumLinSys_Chebyshev_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:13.376188+00:00
-- url     : https://prove2.me/theorems/1b0b997b-458c-40eb-862f-95d96cfded97
-- title:
--   pp. 10, 16, 19, 21 — the domain D_κ, the binomial tail coefficients, the function (74), the odd Chebyshev series (55)/(77)/(88), and b, j₀ of Lemma 14
-- statement:
--   The objects of the Chebyshev approach to approximating $1/x$ in Childs, Kothari and Somma (§§2.2, 4).
--
--   1. **The domain** (p. 10). For a real number $\kappa$ (a condition number, so $\kappa \ge 1$),
--   $$D_\kappa := [-1, -1/\kappa] \cup [1/\kappa, 1].$$
--   2. **The binomial tail coefficients** (the bracket in (55), (77), (88)). For natural numbers $b, j$,
--   $$c_{b,j} := \frac{1}{2^{2b}} \sum_{i=j+1}^{b} \binom{2b}{b+i},$$
--   the probability of seeing more than $b+j$ heads in $2b$ fair coin flips. It is $0$ when $j \ge b$ (empty sum).
--   3. **The function (74).** For a natural number $b$, $f_b(x) := \dfrac{1 - (1 - x^2)^b}{x}$ for $x \ne 0$, with value $0$ at $x=0$. For $b>0$ this is a polynomial of degree $2b-1$; for $b=0$ it is the zero polynomial.
--   4. **The odd Chebyshev series.** For natural numbers $b, n$,
--   $$S_{b,n}(x) := 4 \sum_{j=0}^{n-1} (-1)^j\, c_{b,j}\, \mathcal T_{2j+1}(x),$$
--   where $\mathcal T_m$ is the $m$-th Chebyshev polynomial of the first kind ($\mathcal T_0 = 1$, $\mathcal T_1 = x$, $\mathcal T_{m+1} = 2x\mathcal T_m - \mathcal T_{m-1}$). The full series (77) is $S_{b,b}$, and the series (55)/(88) truncated at index $j_0$ (inclusive) is $S_{b,j_0+1}$.
--   5. **The parameters of Lemma 14.** $b(\kappa,\varepsilon) := \lceil \kappa^2 \log(\kappa/\varepsilon) \rceil$ (rounded up to a natural number, and $0$ when the logarithm is negative), and $j_0(b,\varepsilon) := \lfloor \sqrt{b \log(4b/\varepsilon)} \rfloor$.
--
--   A function $g$ is **$\varepsilon$-close** to $h$ on $D$ (p. 9) if $|g(x) - h(x)| \le \varepsilon$ for all $x \in D$; the theorems of this mission state this inequality inline.
--
--   **Formalization Note** The Chebyshev polynomials are Mathlib's `Polynomial.Chebyshev.T ℝ`, indexed by integers, with the paper's recursion. The paper's $b = \kappa^2\log(\kappa/\varepsilon)$ and $j_0 = \sqrt{b\log(4b/\varepsilon)}$ are real numbers, while $b$ is an exponent and $j_0$ an upper summation index; the formalization rounds $b$ up (so Lemma 17's hypothesis "integer $b \ge \kappa^2\log(\kappa/\varepsilon)$" holds) and $j_0$ down (the sum runs over $j = 0,\dots,\lfloor j_0\rfloor$). Lean's conventions $y/0 = 0$, $\log t = 0$ for $t \le 0$ and $\sqrt t = 0$ for $t \le 0$ apply: $f_b(0) = 0$, which is the value of the continuous extension of $f_b$ at $0$.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 9 (ε-close), p. 10 (D_κ), p. 16 (Lemma 14, eq. (55), Chebyshev polynomials), p. 19 (eqs. (74), (77)), p. 21 (eq. (88))

import Mathlib

namespace QuantumLinSys.Chebyshev

/-- The domain `D_κ := [−1, −1/κ] ∪ [1/κ, 1]` (p. 10). It is used with `1 ≤ κ`, where it is
nonempty and does not contain `0`. -/
def Dκ (κ : ℝ) : Set ℝ := Set.Icc (-1) (-1 / κ) ∪ Set.Icc (1 / κ) 1

/-- The bracket of (55)/(77)/(88): `2^{−2b} Σ_{i=j+1}^{b} C(2b, b+i)`, the probability of seeing
more than `b + j` heads in `2b` fair coin flips. It is `0` when `j ≥ b` (empty sum). -/
noncomputable def coeff (b j : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc (j + 1) b, ((2 * b).choose (b + i) : ℝ)) / 2 ^ (2 * b)

/-- The function (74), `f(x) = (1 − (1 − x²)^b)/x`. At `x = 0` Lean's convention `y / 0 = 0`
gives `0`, which is the value of the continuous extension of `f` at the origin. -/
noncomputable def fTamed (b : ℕ) (x : ℝ) : ℝ := (1 - (1 - x ^ 2) ^ b) / x

/-- The truncated odd Chebyshev series
`4 Σ_{j=0}^{n−1} (−1)^j coeff b j · T_{2j+1}(x)` (the sum is over `Finset.range n`, i.e.
`j = 0, …, n − 1`). The full series (77) is `chebSum b b`; the series (55)/(88) truncated at
`j₀` (inclusive) is `chebSum b (j₀ + 1)`. -/
noncomputable def chebSum (b n : ℕ) (x : ℝ) : ℝ :=
  4 * ∑ j ∈ Finset.range n,
    (-1 : ℝ) ^ j * coeff b j * (Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x

/-- Lemma 14's `b = κ² log(κ/ε)`, rounded up to a natural number (it is an exponent in (74)). -/
noncomputable def bOf (κ ε : ℝ) : ℕ := ⌈κ ^ 2 * Real.log (κ / ε)⌉₊

/-- The truncation index `j₀ = √(b log(4b/ε))` of (55)/(88), rounded down: the series runs over
`j = 0, …, ⌊j₀⌋`. -/
noncomputable def j0Of (b : ℕ) (ε : ℝ) : ℕ := ⌊Real.sqrt (b * Real.log (4 * b / ε))⌋₊

end QuantumLinSys.Chebyshev


