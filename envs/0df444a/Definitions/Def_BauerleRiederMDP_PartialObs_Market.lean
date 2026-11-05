-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Market
-- name    : BauerleRiederMDP_PartialObs_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:32.507709+00:00
-- url     : https://prove2.me/theorems/1bc1f600-07a9-45ed-97a2-b0622159da5c
-- title:
--   The financial market driven by an unobservable Markov chain (6.1)
-- statement:
--   A financial market with one bond and $d$ stocks whose relative risk $R_{n+1}\in\mathbb R^d$ depends on a hidden Markov process $(Y_n)$ with state space $E_Y$. The pair $(R_n,Y_n)$ is a Markov process with
--   $$
--   \mathbb P\big(R_{n+1}\in B,\ Y_{n+1}\in C \mid Y_n=y,\ R_n\big)=Q^R(B\mid y)\,Q^Y(C\mid y),\qquad B\in\mathcal B(\mathbb R^d),\ C\in\mathcal B(E_Y). \tag{6.1}
--   $$
--   The data are:
--
--   1. the stochastic kernel $Q^R(\cdot\mid y)$, the law of $R_{n+1}$ given $Y_n=y$, with a density $q^R(z\mid y)$ with respect to a $\sigma$-finite measure $\lambda$ on $\mathbb R^d$;
--   2. the transition kernel $Q^Y(\cdot\mid y)$ of the hidden chain, with a density $q^Y(y'\mid y)$ with respect to a $\sigma$-finite measure $\nu$ on $E_Y$;
--   3. the prior law $Q_0$ of $Y_0$;
--   4. the requirement that every component of $R(y)\sim Q^R(\cdot\mid y)$ exceeds $-1$ almost surely (relative price changes of the stocks are positive), so that the relative risks take values in $\mathcal Z=[-1,\infty)^d$.
--
--   Given $(Y_n)$ the returns $R_1,R_2,\dots$ are independent, and given $Y_n$ the variables $R_{n+1}$ and $Y_{n+1}$ are independent. This is the common setting of Chapter 6 (terminal wealth and mean–variance problems under partial observation); the densities are the standing assumption of Section 5.2 that makes the Bayes filter explicit.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ`; densities are $[0,\infty]$-valued and jointly measurable. That $E_Y$ is a Borel subset of a Polish space is imposed in the theorems as a standard Borel space.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Chapter 6, eq. (6.1), p.175 (PDF 188); §6.1 model data, pp.176–177 (PDF 189–190); §5.2 density assumption, p.151 and p.154 (PDF 164, 167); §3.1, p.61 (PDF 75)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BauerleRiederMDP.PartialObs

/-- **The financial market with an unobservable Markov factor** of Chapter 6.
Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Chapter 6
introduction, eq. (6.1), p.175 (PDF 188); model data of §6.1, pp.176–177 (PDF 189–190) and of
§6.2, p.184 (PDF 197); density assumption of §5.2, p.151 (PDF 164) and p.154 (PDF 167), recalled
on p.177 ("It is assumed (see Section 5.2) that there exist densities of `Q^R` and `Q^Y`").

The hidden process `(Y_n)` lives on `E_Y` and the relative risk `R_{n+1} ∈ ℝ^d` of the `d` stocks
satisfies (6.1):
`P(R_{n+1} ∈ B, Y_{n+1} ∈ C | Y_n = y, R_n) = Q^R(B|y) Q^Y(C|y)`.
The fields are
* `QR : Kernel E_Y ℝ^d`, the conditional law `Q^R(·|y)` of `R_{n+1}` given `Y_n = y`, with a
  density `qR y` with respect to a σ-finite measure `lam` (`λ`);
* `QY : Kernel E_Y E_Y`, the transition kernel `Q^Y(·|y)` of `(Y_n)`, with a density `qY y` with
  respect to a σ-finite measure `nu` (`ν`), so that `Q^{Z,Y}(d(z,y')|y) = q^R(z|y) q^Y(y'|y)
  λ(dz) ν(dy')` as in §5.2;
* `Q0`, the prior law of `Y_0`;
* `relRisk_gt`: every component of `R(y)` exceeds `-1` almost surely (the standing assumption
  `R̃^k_{n+1} > 0` a.s. of §3.1, p.61, PDF 75, for the relative price change, so that
  `R^k = R̃^k/(1+i) - 1 > -1`; the disturbance space is `Z = [-1,∞)^d`).

**Formalization Note.** `ℝ^d` is `Fin d → ℝ`. Densities are `ℝ≥0∞`-valued and jointly
measurable. The book's standing requirement that `E_Y` be a Borel subset of a Polish space is
imposed in the theorems as `[StandardBorelSpace E_Y]`. -/
structure Market (EY : Type*) [MeasurableSpace EY] (d : ℕ) where
  /-- `Q^R(·|y)`, the law of `R_{n+1}` given `Y_n = y`. -/
  QR : Kernel EY (Fin d → ℝ)
  isMarkovKernel_QR : IsMarkovKernel QR
  /-- The σ-finite reference measure `λ` on `ℝ^d`. -/
  lam : Measure (Fin d → ℝ)
  sigmaFinite_lam : SigmaFinite lam
  /-- The density `q^R(z|y)` of `Q^R(·|y)` with respect to `λ`. -/
  qR : EY → (Fin d → ℝ) → ℝ≥0∞
  measurable_qR : Measurable (Function.uncurry qR)
  QR_eq : ∀ y, QR y = lam.withDensity (qR y)
  /-- `Q^Y(·|y)`, the transition kernel of the hidden chain. -/
  QY : Kernel EY EY
  isMarkovKernel_QY : IsMarkovKernel QY
  /-- The σ-finite reference measure `ν` on `E_Y`. -/
  nu : Measure EY
  sigmaFinite_nu : SigmaFinite nu
  /-- The density `q^Y(y'|y)` of `Q^Y(·|y)` with respect to `ν`. -/
  qY : EY → EY → ℝ≥0∞
  measurable_qY : Measurable (Function.uncurry qY)
  QY_eq : ∀ y, QY y = nu.withDensity (qY y)
  /-- The prior law `Q_0` of `Y_0`. -/
  Q0 : ProbabilityMeasure EY
  /-- `R^k(y) > -1` almost surely for every component `k`. -/
  relRisk_gt : ∀ y, ∀ᵐ z ∂QR y, ∀ k, -1 < z k

attribute [instance] Market.isMarkovKernel_QR Market.isMarkovKernel_QY

end BauerleRiederMDP.PartialObs


