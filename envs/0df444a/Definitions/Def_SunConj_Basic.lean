-- Prove2me | Definitions.Def_SunConj_Basic
-- name    : SunConj_Basic
-- status  : Definition
-- author  : @williambc
-- created : 2026-10-03T21:51:50.037985+00:00
-- url     : https://prove2.me/theorems/e338285b-11c8-4ba4-bd35-1ee06051dd8a
-- title:
--   SunConj_Basic: shared definitions
-- statement:
--   This file fixes the special functions and constants shared by every statement of the Sun-conjecture project (Z.-W. Sun, arXiv:2603.29973v3).
--
--   **Constants.**
--
--   - $\zeta(3)=\sum_{n\ge1}1/n^3$ (Apéry's constant), as the real series $\sum_{n\ge0}1/(n+1)^3$.
--   - The Kronecker symbol $\chi_{-8}(n)=\left(\frac{-8}{n}\right)$: $1$ if $n\equiv1,3\pmod 8$, $-1$ if $n\equiv5,7\pmod 8$, $0$ if $n$ is even.
--   - $L_{-8}(2)=\sum_{n\ge1}\chi_{-8}(n)/n^2$. The $n=0$ term is $0$.
--   - $L_{-3}(2)=\sum_{n\ge0}\left(\frac1{(3n+1)^2}-\frac1{(3n+2)^2}\right)$.
--
--   Each is the real infinite sum (`tsum`) of an absolutely convergent series, so it equals the ordinary limit of partial sums.
--
--   **Gamma quotients** (Sun, Conjectures 5.2, 5.3, 5.6, 5.8), defined for every real $x$ by
--
--   $$g_2(x)=\frac{(74x+7)\,\Gamma(6x+1)}{(2x+1)\,4096^{x}\,\Gamma(3x+1)\,\Gamma(x+1)^3},\qquad g_3(x)=\frac{(27x^2+18x+2)\,\Gamma(3x+1)^2}{(2x+1)\,729^{x}\,\Gamma(x+1)^4\,\Gamma(2x+1)},$$
--
--   $$g_6(x)=\frac{(48x^2+32x+3)\,\Gamma(4x+1)^2}{(2x+1)\,4096^{x}\,\Gamma(x+1)^2\,\Gamma(2x+1)^3},\qquad g_8(x)=\frac{(88x^3+108x^2+36x+3)\,\Gamma(4x+1)^2}{(3x+1)(3x+2)\,1024^{x}\,\Gamma(x+1)^3\,\Gamma(2x+1)\,\Gamma(3x+1)}.$$
--
--   **Formalization Note** Sun defines $g_2$ on $x>-1/6$, $g_3$ on $x>-1/3$, and $g_6,g_8$ on $x>-1/4$. In Lean the formulas are total functions on $\mathbb R$, using Mathlib's `Real.Gamma` and real powers. Outside Sun's domain they take whatever value the total operations give (division by zero is $0$). Every statement evaluates them, or their derivatives, only at integers $k\ge0$, where the function near $k$ agrees with Sun's. Catalan's constant is not defined here: the statements use Prove2Me's published `FCP.Constants.catalanConstant`, which is $\sum_{n\ge0}(-1)^n/(2n+1)^2$.
-- source:
--   https://github.com/ten-thousand-agents/ten-thousand-agents/blob/e1194eed96224144b7e0f81b31ad961ed6a062ba/math-problems/lean/Definitions/Def_SunConj_Basic.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace SunConj

noncomputable section

/-- Apéry's constant `ζ(3) = ∑_{n ≥ 1} 1 / n^3`. -/
def zeta3 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

/-- The Kronecker symbol `(-8/n)`: `1` for `n ≡ 1, 3 (mod 8)`, `-1` for `n ≡ 5, 7 (mod 8)`,
and `0` for even `n`. -/
def chiNeg8 (n : ℕ) : ℝ :=
  if n % 8 = 1 ∨ n % 8 = 3 then 1 else if n % 8 = 5 ∨ n % 8 = 7 then -1 else 0

/-- `L_{-8}(2) = ∑_{n ≥ 1} (-8/n) / n^2` (the `n = 0` term is `0`). -/
def LNeg8Two : ℝ := ∑' n : ℕ, chiNeg8 n / (n : ℝ) ^ 2

/-- `L_{-3}(2) = ∑_{n ≥ 0} (1/(3n+1)^2 - 1/(3n+2)^2)`. -/
def LNeg3Two : ℝ := ∑' n : ℕ, (1 / (3 * (n : ℝ) + 1) ^ 2 - 1 / (3 * (n : ℝ) + 2) ^ 2)

/-- Sun's `g(x)` in Conjecture 5.2 of arXiv:2603.29973v3. -/
def g2 (x : ℝ) : ℝ :=
  (74 * x + 7) * Real.Gamma (6 * x + 1) /
    ((2 * x + 1) * (4096 : ℝ) ^ x * Real.Gamma (3 * x + 1) * Real.Gamma (x + 1) ^ 3)

/-- Sun's `g(x)` in Conjecture 5.3 of arXiv:2603.29973v3. -/
def g3 (x : ℝ) : ℝ :=
  (27 * x ^ 2 + 18 * x + 2) * Real.Gamma (3 * x + 1) ^ 2 /
    ((2 * x + 1) * (729 : ℝ) ^ x * Real.Gamma (x + 1) ^ 4 * Real.Gamma (2 * x + 1))

/-- Sun's `g(x)` in Conjecture 5.6 of arXiv:2603.29973v3. -/
def g6 (x : ℝ) : ℝ :=
  (48 * x ^ 2 + 32 * x + 3) * Real.Gamma (4 * x + 1) ^ 2 /
    ((2 * x + 1) * (4096 : ℝ) ^ x * Real.Gamma (x + 1) ^ 2 * Real.Gamma (2 * x + 1) ^ 3)

/-- Sun's `g(x)` in Conjecture 5.8 of arXiv:2603.29973v3. -/
def g8 (x : ℝ) : ℝ :=
  (88 * x ^ 3 + 108 * x ^ 2 + 36 * x + 3) * Real.Gamma (4 * x + 1) ^ 2 /
    ((3 * x + 1) * (3 * x + 2) * (1024 : ℝ) ^ x * Real.Gamma (x + 1) ^ 3 *
      Real.Gamma (2 * x + 1) * Real.Gamma (3 * x + 1))

end

end SunConj


