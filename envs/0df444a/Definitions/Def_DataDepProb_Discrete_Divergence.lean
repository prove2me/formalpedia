-- Prove2me | Definitions.Def_DataDepProb_Discrete_Divergence
-- name    : DataDepProb_Discrete_Divergence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:09:47.561832+00:00
-- url     : https://prove2.me/theorems/1c672238-2b89-48d4-9968-3c7fb76aa577
-- title:
--   Relative entropy (discrete and for densities), the $\chi^2$-divergence and total variation
-- statement:
--   For distributions $\mu,\nu$ with densities $f,g$ the paper defines (§4.1)
--   $$\mathrm{TV}(\mu,\nu)=\tfrac12\int|f-g|,\qquad \mathrm{KL}(\mu\|\nu)=\int f\log\frac fg,\qquad \chi^2(\mu\|\nu)=\int\Big(\frac fg-1\Big)^2 g,$$
--   with sums for discrete distributions, and a positive numerator over a zero denominator giving infinite divergence.
--
--   * **Discrete relative entropy**: $\mathrm{KL}(p\|q)=\sum_{x\in[d]}p(x)\log\frac{p(x)}{q(x)}$, a real number; a term with $p(x)=0$ is $0$.
--   * **Relative entropy of densities** $w,r$ with respect to a measure $\mu$: $\int w\log(w/r)\,d\mu$.
--   * **Chi-squared divergence** of measures $\mu,\nu$ on any measurable space: $\chi^2(\mu\|\nu)=\int(\frac{d\mu}{d\nu}-1)^2\,d\nu\in[0,\infty]$ if $\mu\ll\nu$, and $+\infty$ otherwise.
--   * **Total variation**: $\mathrm{TV}(\mu,\nu)=\frac12\int|\frac{d\mu}{d\rho}-\frac{d\nu}{d\rho}|\,d\rho$ with $\rho=\mu+\nu$.
--
--   **Formalization Note.** The discrete KL uses `Real.log` with $\log 0=0$; at a coordinate with $q(x)=0<p(x)$ the Lean term is $0$ rather than $+\infty$, so every statement that uses `kl p q` has $q>0$ (all MW iterates and all points of $\tilde\Delta_d$ are positive). The density KL is a Bochner integral and is used together with an integrability hypothesis (finiteness of $\mathrm{KL}$). $\chi^2$ takes values in `ℝ≥0∞`, so infinite divergence is represented, not replaced by a junk value.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 8, §4.1

import Mathlib

open MeasureTheory

namespace DataDepProb.Discrete

/-!
# Relative entropy, chi-squared divergence and total variation

Feldman, Kale, Majid, Talwar, *Data-Dependent Probability Estimation via Sample Amplification*,
STOC 2027 submission (manuscript sha256 28400f1c…), §4.1 p. 8: for distributions `µ, ν` with
densities `f, g`, `TV(µ, ν) = ½∫|f − g|`, `KL(µ‖ν) = ∫ f log(f/g)`, `χ²(µ‖ν) = ∫ (f/g − 1)² g`;
"for discrete distributions the integrals are sums. A positive numerator with a zero denominator
gives infinite divergence."

* `kl p q = ∑_x p(x) log(p(x)/q(x))` on `[d]`, real-valued. A term with `p(x) = 0` is `0`. It is
  used only where `q` has positive coordinates (MW iterates, points of `∆̃_d`), so the infinite
  case never arises; at a coordinate with `q(x) = 0 < p(x)` the Lean term is `0`, not `+∞`, and
  every statement therefore assumes `q > 0`.
* `klDensity μ w r = ∫ w log(w/r) dμ` for densities `w, r` on a measure space (Fact 4.9's last
  clause); a Bochner integral, so it is used together with an integrability hypothesis.
* `chiSq μ ν ∈ [0, ∞]` for measures on any measurable space: `∫ (dμ/dν − 1)² dν` when `μ ≪ ν`
  and `+∞` otherwise (the convention above: mass of `µ` where `ν` has none gives `+∞`).
* `tv μ ν = ½ ∫ |dμ/dρ − dν/dρ| dρ` with the dominating measure `ρ = μ + ν`.
-/

/-- Discrete relative entropy `KL(p‖q) = ∑_x p(x) log(p(x)/q(x))` (§4.1). -/
noncomputable def kl {d : ℕ} (p q : Fin d → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- Relative entropy of probability densities `w, r` with respect to a common measure `μ`:
`∫ w log(w/r) dμ` (§4.1, used in the last clause of Fact 4.9). -/
noncomputable def klDensity {α : Type*} [MeasurableSpace α] (μ : Measure α) (w r : α → ℝ) : ℝ :=
  ∫ x, w x * Real.log (w x / r x) ∂μ

open Classical in
/-- Chi-squared divergence `χ²(µ‖ν) = ∫ (dµ/dν − 1)² dν` if `µ ≪ ν`, and `+∞` otherwise
(§4.1). -/
noncomputable def chiSq {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ENNReal :=
  if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (((μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν else ⊤

/-- Total variation distance `TV(µ, ν) = ½ ∫ |f − g|`, with `f, g` the densities of `µ, ν`
with respect to `µ + ν` (§4.1). -/
noncomputable def tv {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  (1 / 2) * ∫ x, |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν)

end DataDepProb.Discrete


