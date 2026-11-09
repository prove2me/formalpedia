-- Prove2me | Definitions.Def_HouseAllocLT_LowerBound_B
-- name    : HouseAllocLT_LowerBound_B
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:50.633561+00:00
-- url     : https://prove2.me/theorems/f74c5780-940c-4929-b0c1-2afe317ea875
-- title:
--   Harmonic cutoff and lower-bound constants
-- statement:
--   Write $H_r=\sum_{j=1}^r 1/j$ and $H_0=0$. For $n\ge2$, define
--
--   $$t_n=\max\{0\le t\le n-1:H_n-H_{n-t}\le1\},\quad J_n=H_n-H_{n-t_n},\quad B_n=t_n+(n-t_n)(1-J_n).$$
--
--   Also write $d_n=\sqrt{n\ln(n+1)/2}$ for the benchmark's deviation bound. These are explicit quantities computed from market size, not mechanism parameters.
--
--   **Formalization Note** Harmonic numbers are cast from rationals to reals. The maximum is finite; its candidate set contains zero for positive $n$. The function $B$ is set to zero at $n=0,1$; only $n\ge2$ or its limit at infinity is used. The lower-bound constant is represented by the extended nonnegative real image of $\exp(1)/(\exp(1)-1)$.
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), §3.2, equation (6) and Theorem 3.1 constants, PDF pp. 8–9 (printed pp. 6–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Mathlib

open Classical

open scoped ENNReal

namespace HouseAllocLT.LowerBound
noncomputable section

/-- Equation (6), PDF p.8. For n ≥ 1, the candidate set contains zero. -/
def t (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => (harmonic n : ℝ) - (harmonic (n - k) : ℝ) ≤ 1)).sup id

def J (n : ℕ) : ℝ := (harmonic n : ℝ) - (harmonic (n - t n) : ℝ)

/-- Equation (6) on its stated domain n ≥ 2; zero below it, irrelevant to the limit. -/
def B (n : ℕ) : ℝ :=
  if 2 ≤ n then (t n : ℝ) + ((n - t n : ℕ) : ℝ) * (1 - J n) else 0

def deviationBound (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log ((n : ℝ) + 1) / 2)

def lowerBoundConstant : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1 / (Real.exp 1 - 1))

end
end HouseAllocLT.LowerBound


