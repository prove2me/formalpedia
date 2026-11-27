-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_objective
-- name    : BauerleRiederMDP_LQ_Supplement_CIRandom_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:06:41.657522+00:00
-- url     : https://prove2.me/theorems/60358c41-82e0-408b-afa5-09c687159c61
-- title:
--   The objective of problem (9.1)
-- statement:
--   **The objective of problem (9.1)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (9.1), p.268, PDF 278): $\mathbb E _x [\sum _{n=0}^{\tau -1} \beta ^n U_c(c_n) + \beta ^\tau  U_p(X^{c,\varphi }_\tau )]$, with $\tau $ geometric, $\mathbb P (\tau  = n) = (1 - p)p^{n-1}$, $n \in  \mathbb N $, independent of the market.
--
--   **Formalization Note.** By the independence of $\tau $ and Fubini (all terms are nonnegative), the expectation equals $\sum _{n\ge 0} \beta ^n \mathbb P (\tau  > n) \mathbb E  U_c(c_n) + \sum _{n\ge 1} \beta ^n \mathbb P (\tau  = n) \mathbb E  U_p(X_n)$ with $\mathbb P (\tau  > n) = p^n$; this is the formula computed, in $[0, \infty ]$ (Lebesgue integrals of $U^+$; on admissible strategies $c_n, X_n \ge  0$ a.s., where $U_c, U_p \ge  0$). The path $(R_1, \dots , R_n)$ has law $\mu R^{\otimes n}$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (9.1), p.268, PDF 278

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_wealth

open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The objective of problem (9.1)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), eq. (9.1), p.268, PDF 278):
`𝔼_x [∑_{n=0}^{τ−1} β^n U_c(c_n) + β^τ U_p(X^{c,φ}_τ)]`, with `τ` geometric,
`ℙ(τ = n) = (1 − p)p^{n−1}`, `n ∈ ℕ`, independent of the market.

**Formalization Note.** By the independence of `τ` and Fubini (all terms are nonnegative), the
expectation equals `∑_{n≥0} β^n ℙ(τ > n) 𝔼 U_c(c_n) + ∑_{n≥1} β^n ℙ(τ = n) 𝔼 U_p(X_n)` with
`ℙ(τ > n) = p^n`; this is the formula computed, in `[0, ∞]` (Lebesgue integrals of
`U⁺`; on admissible strategies `c_n, X_n ≥ 0` a.s., where `U_c, U_p ≥ 0`). The path
`(R_1, …, R_n)` has law `μR^{⊗n}`. -/
noncomputable def CIRandom.objective {d : ℕ} (C : CIRandom d) (x : ℝ)
    (c : (n : ℕ) → (Fin n → Fin d → ℝ) → ℝ) (φ : (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ) :
    ℝ≥0∞ :=
  (∑' n : ℕ, ENNReal.ofReal (C.β ^ n * C.p ^ n) *
      ∫⁻ r, ENNReal.ofReal (C.Uc (c n r)) ∂(Measure.pi fun _ : Fin n => C.μR)) +
  ∑' n : ℕ, ENNReal.ofReal (C.β ^ (n + 1) * ((1 - C.p) * C.p ^ n)) *
      ∫⁻ r, ENNReal.ofReal (C.Up (CIRandom.wealth c φ x (n + 1) r))
        ∂(Measure.pi fun _ : Fin (n + 1) => C.μR)

end BauerleRiederMDP.LQ.Supplement


