-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_Constants
-- name    : STOC2027BoolCSP_Approximation_Supplement_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:52.601397+00:00
-- url     : https://prove2.me/theorems/29449c74-6cb0-43f6-9d6b-7aa95c6c6b76
-- title:
--   The even-arity constants (2), the test constants $\gamma,\beta$ of (62) and the ratio $R_k$ of (3)
-- statement:
--   Fix an even integer $k\ge 4$. Equation (2) defines the rational constants
--   $$n=k-2,\quad t=\frac{1}{16n^2},\quad c=\frac{n(n-1)}{4},\quad C=2^{k-1}-1,\quad d=(k-1)t,\quad a=\frac{cd}{C^2},\quad x=ad,\quad \xi=\frac{x}{8(1+x)}.$$
--   With the all-positive atoms $q_0=1/(k+2)$ of the slice law (44) and $q_+=(1+(k-1)t)/(k+2)$ of the positive-correlation law (48), the soundness and completeness constants of (62) are
--   $$\beta=2^{-k}\Big(1+\frac{x}{4(1-a)}\Big),\qquad \gamma=(1-\xi)\big((1-a)q_0+aq_+\big)+\xi\,2^{-k},$$
--   and the hardness ratio of (3) is
--   $$R_k=\frac{k+2}{2^k}\cdot\frac{1+x/2}{1+7x/8}.$$
--
--   These constants enter the two-hub negative stability (Theorem 12.2) and the even-arity hardness theorem (Theorem 1.4).
--
--   **Formalization Note** All constants are functions of $k:\mathbb N$ with values in $\mathbb Q$; $n=k-2$ is natural-number subtraction, exact for $k\ge 4$. They are only used under the hypotheses $k\ge4$ even.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 2, 23–24, 28 (PDF 5, 26–27, 31), equations (2), (3), (44), (48), (62)

import Mathlib

namespace STOC2027BoolCSP.Approximation.Supplement

/-- `n = k − 2`, the number of leaves (equation (2)). -/
def nC (k : ℕ) : ℕ := k - 2

/-- `t = 1/(16 n²)` (equation (2)). -/
def tC (k : ℕ) : ℚ := 1 / (16 * (nC k : ℚ) ^ 2)

/-- `c = n(n − 1)/4` (equation (2)). -/
def cC (k : ℕ) : ℚ := (nC k : ℚ) * ((nC k : ℚ) - 1) / 4

/-- `C = 2^{k−1} − 1` (equation (2)). -/
def bigC (k : ℕ) : ℚ := 2 ^ (k - 1) - 1

/-- `d = (k − 1) t` (equation (2)). -/
def dC (k : ℕ) : ℚ := ((k : ℚ) - 1) * tC k

/-- `a = c d / C²` (equation (2)). -/
def aC (k : ℕ) : ℚ := cC k * dC k / bigC k ^ 2

/-- `x = a d` (equation (2)). -/
def xC (k : ℕ) : ℚ := aC k * dC k

/-- `ξ = x / (8(1 + x))` (equation (2)). -/
def xiC (k : ℕ) : ℚ := xC k / (8 * (1 + xC k))

/-- The all-positive atom `q_0 = 1/(k+2)` of the De–Mossel slice law (44). -/
def q0C (k : ℕ) : ℚ := 1 / ((k : ℚ) + 2)

/-- The all-positive atom `q_+ = (1 + (k−1)t)/(k+2)` of the positive-correlation law (48). -/
def qPlusC (k : ℕ) : ℚ := (1 + ((k : ℚ) - 1) * tC k) / ((k : ℚ) + 2)

/-- The soundness constant `β = 2^{−k}(1 + x/(4(1 − a)))` of (62). -/
def betaC (k : ℕ) : ℚ := (1 / 2 ^ k) * (1 + xC k / (4 * (1 - aC k)))

/-- The completeness constant `γ = (1 − ξ)((1 − a) q_0 + a q_+) + ξ 2^{−k}` of (62). -/
def gammaC (k : ℕ) : ℚ :=
  (1 - xiC k) * ((1 - aC k) * q0C k + aC k * qPlusC k) + xiC k * (1 / 2 ^ k)

/-- The hardness ratio `R_k = ((k+2)/2^k) · (1 + x/2)/(1 + 7x/8)` of (3). -/
def ratioR (k : ℕ) : ℚ := (((k : ℚ) + 2) / 2 ^ k) * ((1 + xC k / 2) / (1 + 7 * xC k / 8))

end STOC2027BoolCSP.Approximation.Supplement


