-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:33:14.710879+00:00
-- url     : https://prove2.me/theorems/1dc0c878-fae1-4a39-a34e-0768d2370cf6
-- title:
--   The financial market of the multiperiod terminal wealth problem
-- statement:
--   **The financial market of the multiperiod terminal wealth problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.2, pp.79–80, PDF 93–94, with the market of §3.1, pp.60–63, PDF 74–77): $d$ risky assets and a riskless bond with deterministic interest rates $i_n \ge  0$ on $[n - 1, n)$, and independent (not necessarily identically distributed) relative risks $R_1, \dots , R_N$; $\nu  n$ is the law of $R_n$. Since $\tilde{R}^k_n > 0$ almost surely (p.61), $R^k_n = \tilde{R}^k_n/(1 + i_n) - 1 > -1$ almost surely.
--
--   **Formalization Note.** Only the laws of the $R_n$ and the rates enter the Markov Decision Model of §4.2 (data list p.80: $Q^Z_n(\cdot |x, a)$ = distribution of $R_{n+1}$), so the market is given by them; the independence of $R_1, \dots , R_N$ is what makes the path law the product of the $\nu  n$ (used in `twVpi`). Time is $\mathbb N $; only $1 \le  n \le  N$ is used. $i_n \ge  0$ is required at every index (an unused value can be set to $0$). $\mathbb R ^d$ is $Fin d \to  \mathbb R $.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.2, pp.79–80, PDF 93–94, with the market of §3.1, pp.60–63, PDF 74–77

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The financial market of the multiperiod terminal wealth problem** (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), §4.2, pp.79–80, PDF 93–94, with the market
of §3.1, pp.60–63, PDF 74–77): `d` risky assets and a riskless bond with deterministic interest rates
`i_n ≥ 0` on `[n − 1, n)`, and independent (not necessarily identically distributed) relative risks
`R_1, …, R_N`; `ν n` is the law of `R_n`. Since `R̃^k_n > 0` almost surely (p.61),
`R^k_n = R̃^k_n/(1 + i_n) − 1 > −1` almost surely.

**Formalization Note.** Only the laws of the `R_n` and the rates enter the Markov Decision Model of
§4.2 (data list p.80: `Q^Z_n(·|x, a)` = distribution of `R_{n+1}`), so the market is given by them;
the independence of `R_1, …, R_N` is what makes the path law the product of the `ν n` (used in
`twVpi`). Time is `ℕ`; only `1 ≤ n ≤ N` is used. `i_n ≥ 0` is required at every index (an unused
value can be set to `0`). `ℝ^d` is `Fin d → ℝ`. -/
structure TWMarket (d : ℕ) where
  /-- The interest rate `i_n` of the period `[n − 1, n)`. -/
  i : ℕ → ℝ
  i_nonneg : ∀ n, 0 ≤ i n
  /-- The law of the relative risk `R_n`. -/
  ν : ℕ → ProbabilityMeasure (Fin d → ℝ)
  /-- `R^k_n > −1` almost surely. -/
  gt : ∀ n, ∀ᵐ z ∂(ν n : Measure (Fin d → ℝ)), ∀ k, -1 < z k

end BauerleRiederMDP.LQ.Supplement


