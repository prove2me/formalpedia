-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_FM
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_FM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:33:58.120617+00:00
-- url     : https://prove2.me/theorems/fd7669ef-0136-4704-b8c6-cfe45aeaa8a7
-- title:
--   Assumption (FM)
-- statement:
--   **Assumption (FM)** of §4.2 (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.79, PDF 93): (i) there are no arbitrage opportunities; (ii) $\mathbb E \|R_n\| < \infty $ for all $n = 1, \dots , N$.
--
--   **Formalization Note.** (i) is written in the local form of Theorem 3.1.5 (p.64, PDF 78; published as `BauerleRiederMDP.NoArbitrage.theorem_3_1_5`): for every $n$ and every $𝓕_{n-1}$-measurable $\varphi $, $\varphi  \cdot  R_n \ge  0$ a.s. implies $\varphi  \cdot  R_n = 0$ a.s. Because §4.2 takes the natural filtration and independent $R_n$, $R_n$ is independent of $𝓕_{n-1}$, and the condition is equivalent to the one for deterministic $\varphi  \in  \mathbb R ^d$ stated here. The norm in (ii) is the sup norm of $Fin d \to  \mathbb R $; all norms on $\mathbb R ^d$ give the same condition.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.79, PDF 93

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **Assumption (FM)** of §4.2 (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), p.79, PDF 93): (i) there are no arbitrage opportunities; (ii) `𝔼‖R_n‖ < ∞` for all
`n = 1, …, N`.

**Formalization Note.** (i) is written in the local form of Theorem 3.1.5 (p.64, PDF 78; published
as `BauerleRiederMDP.NoArbitrage.theorem_3_1_5`): for every `n` and every `𝓕_{n−1}`-measurable
`φ`, `φ · R_n ≥ 0` a.s. implies `φ · R_n = 0` a.s. Because §4.2 takes the natural filtration and
independent `R_n`, `R_n` is independent of `𝓕_{n−1}`, and the condition is equivalent to the one for
deterministic `φ ∈ ℝ^d` stated here. The norm in (ii) is the sup norm of `Fin d → ℝ`; all norms on
`ℝ^d` give the same condition. -/
def TWMarket.FM {d : ℕ} (Mk : TWMarket d) (N : ℕ) : Prop :=
  (∀ n, 1 ≤ n → n ≤ N → ∀ φ : Fin d → ℝ,
    (∀ᵐ z ∂(Mk.ν n : Measure (Fin d → ℝ)), 0 ≤ φ ⬝ᵥ z) →
      ∀ᵐ z ∂(Mk.ν n : Measure (Fin d → ℝ)), φ ⬝ᵥ z = 0) ∧
  (∀ n, 1 ≤ n → n ≤ N → ∫⁻ z, ‖z‖ₑ ∂(Mk.ν n : Measure (Fin d → ℝ)) < ⊤)

end BauerleRiederMDP.LQ.Supplement


