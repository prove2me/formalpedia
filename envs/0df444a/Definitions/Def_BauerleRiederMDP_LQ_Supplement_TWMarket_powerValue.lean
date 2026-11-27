-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_powerValue
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_powerValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:37:32.654876+00:00
-- url     : https://prove2.me/theorems/6d04bad8-7d58-51fe-bf18-a45f846f72ff
-- title:
--   The generic one-period problem (4.7)
-- statement:
--   **The generic one-period problem (4.7)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (4.7), p.83, PDF 97): with the admissible fractions `A_n := {α ∈ ℝ^d | 1 + α · R_{n+1} ≥ 0 ℙ-a.s.}`, $v_n := \sup _{\alpha  \in  A_n} \mathbb E  (1 + \alpha  \cdot  R_{n+1})^\gamma $.
--
--   **Formalization Note.** The integrand is nonnegative for $\alpha  \in  A_n$ (outside a null set), so the expectation is a Lebesgue integral and the supremum is taken in $[0, \infty ]$; that $v_n$ is finite and attained is Theorem 4.1.1, not part of the definition.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.7), p.83, PDF 97

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket

open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The generic one-period problem (4.7)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), eq. (4.7), p.83, PDF 97): with the admissible fractions
`A_n := {α ∈ ℝ^d | 1 + α · R_{n+1} ≥ 0 ℙ-a.s.}`,
`v_n := sup_{α ∈ A_n} 𝔼 (1 + α · R_{n+1})^γ`.

**Formalization Note.** The integrand is nonnegative for `α ∈ A_n` (outside a null set), so the
expectation is a Lebesgue integral and the supremum is taken in `[0, ∞]`; that `v_n` is finite and
attained is Theorem 4.1.1, not part of the definition. -/
noncomputable def TWMarket.powerValue {d : ℕ} (Mk : TWMarket d) (γ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ α ∈ {α : Fin d → ℝ | ∀ᵐ z ∂(Mk.ν (n + 1) : Measure (Fin d → ℝ)), 0 ≤ 1 + α ⬝ᵥ z},
    ∫⁻ z, ENNReal.ofReal ((1 + α ⬝ᵥ z) ^ γ) ∂(Mk.ν (n + 1) : Measure (Fin d → ℝ))

end BauerleRiederMDP.LQ.Supplement


