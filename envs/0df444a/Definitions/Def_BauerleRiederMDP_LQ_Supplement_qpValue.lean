-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_qpValue
-- name    : BauerleRiederMDP_LQ_Supplement_qpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:45:30.844282+00:00
-- url     : https://prove2.me/theorems/8ffb71a6-ad0c-5b9d-a5a1-5b3c482f7330
-- title:
--   The value functions $V_n(x, \rho )$ of problem QP(b) under partial observation
-- statement:
--   **The value functions $V_n(x, \rho )$ of problem QP(b) under partial observation** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §6.2, QP(b), p.185, PDF 198, with the model of p.184, PDF 197): the minimal expected squared distance $\mathbb E [(X_N - b)^2]$ of the terminal wealth from $b$, when at time $n$ the wealth is $x$ and the belief about the hidden state is $\rho $, over all history-dependent policies (functions of the observed relative risks $R_{n+1}, \dots , R_N$).
--
--   **Formalization Note.** From time $n$ the returns $(R_{n+1}, \dots , R_N)$ have the published law `M.returnLaw ρ (N − n)` (hidden chain started from $\rho $), and the wealth follows the published `wealth` with the rates $i_{n+1}, \dots , i_N$. The competitors are all measurable strategies ($D_n(x) = A = \mathbb R ^d$); the expectation is a Lebesgue integral in $[0, \infty ]$, so strategies with infinite second moment contribute $+\infty $ (no junk value). $V_0(x_0, Q_0)$ is the value of QP(b).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §6.2, QP(b), p.185, PDF 198, with the model of p.184, PDF 197

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_returnLaw
import Definitions.Def_BauerleRiederMDP_PartialObs_wealth

open MeasureTheory
open BauerleRiederMDP.PartialObs (Market wealth)
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The value functions `V_n(x, ρ)` of problem QP(b) under partial observation** (Bäuerle &
Rieder, *Markov Decision Processes with Applications to Finance* (2011), §6.2, QP(b), p.185,
PDF 198, with the model of p.184, PDF 197): the minimal expected squared distance
`𝔼[(X_N − b)²]` of the terminal wealth from `b`, when at time `n` the wealth is `x` and the belief
about the hidden state is `ρ`, over all history-dependent policies (functions of the observed
relative risks `R_{n+1}, …, R_N`).

**Formalization Note.** From time `n` the returns `(R_{n+1}, …, R_N)` have the published law
`M.returnLaw ρ (N − n)` (hidden chain started from `ρ`), and the wealth follows the published
`wealth` with the rates `i_{n+1}, …, i_N`. The competitors are all measurable strategies
(`D_n(x) = A = ℝ^d`); the expectation is a Lebesgue integral in `[0, ∞]`, so strategies with
infinite second moment contribute `+∞` (no junk value). `V_0(x_0, Q_0)` is the value of QP(b). -/
noncomputable def qpValue {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (i : ℕ → ℝ) (N : ℕ) (b : ℝ) (n : ℕ) (x : ℝ) (ρ : ProbabilityMeasure EY) : ℝ≥0∞ :=
  ⨅ φ ∈ {φ : (k : ℕ) → (Fin k → Fin d → ℝ) → Fin d → ℝ | ∀ k < N - n, Measurable (φ k)},
    ∫⁻ r, ENNReal.ofReal ((wealth (fun k => i (n + k)) x φ (N - n) r - b) ^ 2)
      ∂M.returnLaw ρ (N - n)

end BauerleRiederMDP.LQ.Supplement


