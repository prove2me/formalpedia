-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_Phi
-- name    : BauerleRiederMDP_LQ_Supplement_BinomBayes_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:02:05.298199+00:00
-- url     : https://prove2.me/theorems/aea77603-226f-4e54-8e2e-7d434d27e7ef
-- title:
--   The Bayes operator of the binomial model
-- statement:
--   **The Bayes operator of the binomial model** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §6.1, p.179, PDF 192, the operator $\Phi $ of (5.6) for the Bayesian binomial model): after an up-movement ($z = ū = u/(1+i) - 1$) the belief $\rho $ becomes $\Phi (\rho , ū)(d\theta ) ∝ \theta  \rho (d\theta )$, after a down-movement ($z = \bar{d} = d/(1+i) - 1$) it becomes $\Phi (\rho , \bar{d})(d\theta ) ∝ (1 - \theta ) \rho (d\theta )$. `up = true` is the up-movement.
--
--   **Formalization Note.** The normalization is in $\mathbb R \ge 0\infty $; for beliefs carried by $(0, 1)$ the normalizing constants are in $(0, 1]$. For $\rho  = \delta _\theta $ both updates return $\delta _\theta $, the complete observation case.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §6.1, p.179, PDF 192, the operator `Φ` of (5.6) for the Bayesian binomial model

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes

open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The Bayes operator of the binomial model** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §6.1, p.179, PDF 192, the operator `Φ` of (5.6) for the Bayesian
binomial model): after an up-movement (`z = ū = u/(1+i) − 1`) the belief `ρ` becomes
`Φ(ρ, ū)(dθ) ∝ θ ρ(dθ)`, after a down-movement (`z = d̄ = d/(1+i) − 1`) it becomes
`Φ(ρ, d̄)(dθ) ∝ (1 − θ) ρ(dθ)`. `up = true` is the up-movement.

**Formalization Note.** The normalization is in `ℝ≥0∞`; for beliefs carried by `(0, 1)` the
normalizing constants are in `(0, 1]`. For `ρ = δ_θ` both updates return `δ_θ`, the complete
observation case. -/
noncomputable def BinomBayes.Phi (ρ : Measure ℝ) (up : Bool) : Measure ℝ :=
  if up then (∫⁻ θ, ENNReal.ofReal θ ∂ρ)⁻¹ • ρ.withDensity fun θ => ENNReal.ofReal θ
  else (∫⁻ θ, ENNReal.ofReal (1 - θ) ∂ρ)⁻¹ • ρ.withDensity fun θ => ENNReal.ofReal (1 - θ)

end BauerleRiederMDP.LQ.Supplement


