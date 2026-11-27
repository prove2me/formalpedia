-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes
-- name    : BauerleRiederMDP_LQ_Supplement_BinomBayes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:01:30.470709+00:00
-- url     : https://prove2.me/theorems/dee5003f-1fed-58b5-9e73-3dd207393605
-- title:
--   The binomial market with an unknown up-probability
-- statement:
--   **The binomial market with an unknown up-probability** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §6.1, pp.178–179, PDF 191–192): one stock whose relative price change $\tilde{R}$ takes the values $u$ and $d$ with $\mathbb P (\tilde{R} = u | \vartheta  = \theta ) = \theta $, $\mathbb P (\tilde{R} = d | \vartheta  = \theta ) = 1 - \theta $, $\theta  \in  (0, 1) = \Theta $, a bond with interest rate $i$, $d < 1 + i < u$, the power utility $U(x) = x^\gamma /\gamma $ ($0 < \gamma  < 1$, or $\gamma  < 0$ as in Remark 6.1.3), and a prior $Q_0$ of $\vartheta $ on $(0, 1)$.
--
--   **Formalization Note.** Measures on $\Theta  = (0, 1)$ are measures on $\mathbb R $ carried by $(0, 1)$ ($Q0_Ioo$), so that the point mass $\delta _{\bar{\rho}}$ at a mean $\bar{\rho} \in  (0, 1)$ is available. $0 < d$ because relative price changes are positive (p.61), and $i \ge  0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §6.1, pp.178–179, PDF 191–192

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The binomial market with an unknown up-probability** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §6.1, pp.178–179, PDF 191–192): one stock whose
relative price change `R̃` takes the values `u` and `d` with `ℙ(R̃ = u | ϑ = θ) = θ`,
`ℙ(R̃ = d | ϑ = θ) = 1 − θ`, `θ ∈ (0, 1) = Θ`, a bond with interest rate `i`, `d < 1 + i < u`, the
power utility `U(x) = x^γ/γ` (`0 < γ < 1`, or `γ < 0` as in Remark 6.1.3), and a prior `Q_0` of
`ϑ` on `(0, 1)`.

**Formalization Note.** Measures on `Θ = (0, 1)` are measures on `ℝ` carried by `(0, 1)`
(`Q0_Ioo`), so that the point mass `δ_{ρ̄}` at a mean `ρ̄ ∈ (0, 1)` is available. `0 < d` because
relative price changes are positive (p.61), and `i ≥ 0`. -/
structure BinomBayes where
  i : ℝ
  i_nonneg : 0 ≤ i
  u : ℝ
  dd : ℝ
  dd_pos : 0 < dd
  dd_lt : dd < 1 + i
  lt_u : 1 + i < u
  γ : ℝ
  γ_ne : γ ≠ 0
  γ_lt : γ < 1
  Q0 : Measure ℝ
  Q0_prob : IsProbabilityMeasure Q0
  Q0_Ioo : Q0 (Set.Ioo 0 1)ᶜ = 0

end BauerleRiederMDP.LQ.Supplement


