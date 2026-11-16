-- Prove2me | Definitions.Def_ApproxEquilibriumCost_General_Supplement_UpperParameters
-- name    : ApproxEquilibriumCost_General_Supplement_UpperParameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:45:50.857674+00:00
-- url     : https://prove2.me/theorems/c947e8d6-20d0-4dd0-adae-84fc5e7e14bb
-- title:
--   Definition 4.1 — inverse function and upper-bound thresholds
-- statement:
--   For every integer $d\ge1$ and $x\ge0$, put
--
--   $$\lambda_d(x)=\frac{x}{1+x}\bigl(1-(1+x)^{-1/d}\bigr).$$
--
--   For $0\le y<1$, define $\omega_d(y)=\inf\{x\ge0:y\le\lambda_d(x)\}$. Lemma A.1 makes this nonempty, bounded-below infimum the unique inverse of $\lambda_d$; the definition assumes none of those analytic conclusions. Outside $d\ge1$, $0\le y<1$, its value is explicitly zero. The constants and thresholds are
--
--   $$c_d=\frac{d}{(d+1)^{(d+1)/d}},\qquad \epsilon_1(d)=\frac{\lambda_d(d)}{1-\lambda_d(d)},\qquad\epsilon_2(d)=(d+1)^{1/d}-1.$$
--
--   These are computed from $d$, rather than free parameters. Real powers use real exponents. The thresholds and inverse provide the three regimes of Theorem 4.2.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Definition 4.1, printed p.16 = PDF p.16 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib

noncomputable section

namespace ApproxEquilibriumCost.General.Supplement

/-- Definition 4.1, printed/PDF p.16; intended domain `d ≥ 1`, `x ≥ 0`.
All divisions in the exponent are real. -/
def lambda (d : ℕ) (x : ℝ) : ℝ :=
  x / (1 + x) * (1 - Real.rpow (1 + x) (-(1 : ℝ) / (d : ℝ)))

/-- The canonical inverse on `[0,1)`, constructed from `lambda` rather
than supplied by a specification. For `d ≥ 1` and `0 ≤ y < 1` the set
is nonempty and bounded below by zero; Lemma A.1 identifies its infimum
with the unique inverse value. The explicit outside-domain value is zero. -/
def omega (d : ℕ) (y : ℝ) : ℝ :=
  if 1 ≤ d ∧ 0 ≤ y ∧ y < 1 then
    sInf {x : ℝ | 0 ≤ x ∧ y ≤ lambda d x}
  else 0

/-- Constant in the display after Definition 4.1, printed/PDF p.16. -/
def c (d : ℕ) : ℝ :=
  (d : ℝ) / Real.rpow ((d : ℝ) + 1) (((d : ℝ) + 1) / (d : ℝ))

/-- First threshold, using the first of the source's two equal formulas. -/
def epsilon1 (d : ℕ) : ℝ :=
  lambda d (d : ℝ) / (1 - lambda d (d : ℝ))

/-- Second threshold, printed/PDF p.16. -/
def epsilon2 (d : ℕ) : ℝ :=
  Real.rpow ((d : ℝ) + 1) ((1 : ℝ) / (d : ℝ)) - 1

end ApproxEquilibriumCost.General.Supplement


