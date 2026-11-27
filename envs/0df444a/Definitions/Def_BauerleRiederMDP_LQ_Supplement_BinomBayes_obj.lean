-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_obj
-- name    : BauerleRiederMDP_LQ_Supplement_BinomBayes_obj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:02:29.644962+00:00
-- url     : https://prove2.me/theorems/48af1ded-791f-4242-9043-e6a294e01416
-- title:
--   The objective of (6.4)
-- statement:
--   **The objective of (6.4)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (6.4), p.179, PDF 192): for a function $v$ of the belief, a belief $\rho $ and a fraction $\alpha  \in  [0, 1]$ of wealth in the stock, $[v(\Phi (\rho , ū)) \bar{\rho} (1 + i + \alpha (u - 1 - i))^\gamma  + v(\Phi (\rho , \bar{d})) (1 - \bar{\rho})(1 + i + \alpha (d - 1 - i))^\gamma ] (1 + i)^{-\gamma }$, where $\bar{\rho} = \int  \theta  \rho (d\theta )$.
--
--   **Formalization Note.** Real-valued; for $\alpha  \in  [0, 1]$ the bases are $\ge  d > 0$, so `Real.rpow` is the usual power. $\bar{\rho}$ is a Bochner integral of the bounded function $\theta $ on $(0, 1)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (6.4), p.179, PDF 192

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_Phi

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The objective of (6.4)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), eq. (6.4), p.179, PDF 192): for a function `v` of the belief, a belief `ρ` and a
fraction `α ∈ [0, 1]` of wealth in the stock,
`[v(Φ(ρ, ū)) ρ̄ (1 + i + α(u − 1 − i))^γ + v(Φ(ρ, d̄)) (1 − ρ̄)(1 + i + α(d − 1 − i))^γ] (1 + i)^{−γ}`,
where `ρ̄ = ∫ θ ρ(dθ)`.

**Formalization Note.** Real-valued; for `α ∈ [0, 1]` the bases are `≥ d > 0`, so `Real.rpow` is
the usual power. `ρ̄` is a Bochner integral of the bounded function `θ` on `(0, 1)`. -/
noncomputable def BinomBayes.obj (B : BinomBayes) (v : Measure ℝ → ℝ) (ρ : Measure ℝ) (α : ℝ) :
    ℝ :=
  (v (BinomBayes.Phi ρ true) * (∫ θ, θ ∂ρ) * (1 + B.i + α * (B.u - 1 - B.i)) ^ B.γ +
    v (BinomBayes.Phi ρ false) * (1 - ∫ θ, θ ∂ρ) * (1 + B.i + α * (B.dd - 1 - B.i)) ^ B.γ) *
      (1 + B.i) ^ (-B.γ)

end BauerleRiederMDP.LQ.Supplement


