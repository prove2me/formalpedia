-- Prove2me | Definitions.Def_PriceRobustness_Main_Bounds
-- name    : PriceRobustness_Main_Bounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:38:04.000516+00:00
-- url     : https://prove2.me/theorems/abe621c3-66b1-4f54-8668-1081b29d8e15
-- title:
--   Interpolated binomial tail and analytic envelope
-- statement:
--   For a natural number $n$ and integer $s$, define
--   $$U(n,s)=2^{-n}\sum_{\substack{0\le l\le n\\s\le l}}\binom nl.$$
--   Thus $U(n,s)=1$ for $s\le0$ and $0$ for $s>n$. For every real threshold $\Gamma$, set $\nu=(\Gamma+n)/2$, $\mu=\nu-\lfloor\nu\rfloor$ and
--   $$B(n,\Gamma)=(1-\mu)U(n,\lfloor\nu\rfloor)+\mu U(n,\lfloor\nu\rfloor+1).$$
--   For integer $l$ define the source envelope
--   $$C(n,l)=\begin{cases}2^{-n},&l=0\text{ or }l=n,\\
--   \displaystyle\frac1{\sqrt{2\pi}}\sqrt{\frac n{(n-l)l}}\exp\left(n\log\frac n{2(n-l)}+l\log\frac{n-l}{l}\right),&\text{otherwise}.\end{cases}$$
--   Only $0\le l\le n$ is used by the theorem. The endpoint branch is tested before the interior formula. Finally $\Phi(\theta)$ is the actual standard normal probability of $(-\infty,\theta]$, using Mathlib's Gaussian measure of mean zero and variance one. Integer floors, rather than natural truncation, define the tails at negative thresholds as needed for the limit.
-- source:
--   Bertsimas and Sim, The Price of Robustness, authors' preprint, August 2001; revised August, 2002; PDF SHA-256 63f0bffaff9128b706a084acc869e1020ce79adf86108ac23b5b0dd598f189cb; Theorem 3, pp. 10–11, Eqs. (17), (19), (20); appendix p. 29

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace PriceRobustness.Main

def binomialTail (n : ℕ) (s : ℤ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => s ≤ (l : ℤ)),
    (n.choose l : ℝ)

def nu (n : ℕ) (Γ : ℝ) : ℝ := (Γ + n) / 2

def mu (n : ℕ) (Γ : ℝ) : ℝ := nu n Γ - (⌊nu n Γ⌋ : ℤ)

def B (n : ℕ) (Γ : ℝ) : ℝ :=
  (1 - mu n Γ) * binomialTail n ⌊nu n Γ⌋ +
    mu n Γ * binomialTail n (⌊nu n Γ⌋ + 1)

def C (n : ℕ) (l : ℤ) : ℝ :=
  if l = 0 ∨ l = (n : ℤ) then (2 : ℝ)⁻¹ ^ n
  else 1 / Real.sqrt (2 * Real.pi) *
    Real.sqrt ((n : ℝ) / (((n : ℝ) - l) * l)) *
    Real.exp ((n : ℝ) * Real.log ((n : ℝ) / (2 * ((n : ℝ) - l))) +
      (l : ℝ) * Real.log (((n : ℝ) - l) / l))

def Phi (θ : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic θ)

end PriceRobustness.Main


