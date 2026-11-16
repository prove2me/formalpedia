-- Prove2me | Definitions.Def_GaussDiffSVP_Supplement_Readout
-- name    : GaussDiffSVP_Supplement_Readout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:46:17.971709+00:00
-- url     : https://prove2.me/theorems/14f98696-9450-4c68-9e81-3c6c1db1e88c
-- title:
--   Weighted readout of a random record list
-- statement:
--   Let $\Xi=(X_1,\dots,X_N)$ be a random finite record list with values in a countable space $\mathcal X$, $b:\mathcal X\to[0,1]$ a weight and $x_0$ a fallback point. Put $W=\sum_i b(X_i)$. **Weighted readout** chooses record $i$ with probability $b(X_i)/W$ when $W>0$ and returns its value, and returns $x_0$ when $W=0$. Its output law is
--   $$\Pr[X_{\mathrm{out}}=x]=\mathbb E\Big[\mathbf 1_{W>0}\sum_{i:X_i=x}\frac{b(X_i)}{W}+\mathbf 1_{W=0}\mathbf 1_{x=x_0}\Big],$$
--   and $\Pr[W=0]$ is the probability that the total weight vanishes.
--
--   These are the two quantities bounded by Theorem 4.7.
--
--   **Formalization Note** Records are list positions, so equal values at different positions are distinct records, as in the published intensity.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 4.7, p.26

import Mathlib

open scoped ENNReal

namespace GaussDiffSVP.Supplement

open Classical in
/-- The output law of **weighted readout** (Gao–Han–Hu, *Gaussian Difference Dynamics*,
arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 4.7, p.26): given a random record
list with law `μ`, a weight `b : α → [0, 1]` and a fallback point `x₀`, on a list `l` put
`W(l) = Σᵢ b(lᵢ)`; if `W(l) > 0`, choose record `i` with probability `b(lᵢ)/W(l)` and output its value
`lᵢ`; if `W(l) = 0`, output `x₀`. The value is the probability that the output is `x`.

**Formalization Note.** Records are list positions (as in the published `GaussDiffSVP.intensity`),
so a value occurring at several positions is chosen with the sum of their probabilities. The
weight is real; it is used with `0 ≤ b ≤ 1`, where `W(l) ≥ 0`. -/
noncomputable def readoutLaw {α : Type*} (μ : PMF (List α)) (b : α → ℝ) (x₀ : α) (x : α) :
    ℝ≥0∞ :=
  ∑' l : List α, μ l *
    (if 0 < (l.map b).sum then
      ENNReal.ofReal (∑ i : Fin l.length,
        if l.get i = x then b (l.get i) / (l.map b).sum else 0)
    else if x = x₀ then 1 else 0)

open Classical in
/-- The probability `P[W = 0]` that the total weight `W(l) = Σᵢ b(lᵢ)` of the random record list
vanishes (Gao–Han–Hu, Theorem 4.7, (37), p.26). -/
noncomputable def zeroWeightProb {α : Type*} (μ : PMF (List α)) (b : α → ℝ) : ℝ≥0∞ :=
  ∑' l : List α, μ l * (if (l.map b).sum = 0 then 1 else 0)

end GaussDiffSVP.Supplement


