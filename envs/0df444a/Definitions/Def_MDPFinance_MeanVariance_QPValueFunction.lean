-- Prove2me | Definitions.Def_MDPFinance_MeanVariance_QPValueFunction
-- name    : MDPFinance_MeanVariance_QPValueFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:06:49.931035+00:00
-- url     : https://prove2.me/theorems/35ec4fc6-4bb3-4c3f-9553-35827053c81d
-- title:
--   The value function of the auxiliary problem QP(b)
-- statement:
--   $V_n(x) := \inf_\pi \mathbb{E}[(X_N-b)^2 \mid X_n=x]$ over strategies $\pi$
--   admissible on $[n,N)$ (`VQP`), the value function of the tractable auxiliary problem $QP(b)$
--   introduced in Bäuerle–Rieder §4.6 (a stochastic linear-quadratic problem, cf. §2.6.3), whose
--   explicit solution is Theorem 4.6.5.
--
--   **Formalization Note.** Defined as an infimum over admissible strategies restricted to $[n,N)$,
--   mirroring the value-function pattern of the Structure Theorem missions (chunk `02a`) rather than
--   via a Bellman recursion, since $QP(b)$'s own Bellman recursion is exactly the content Theorem
--   4.6.5 proves.
--
--   **Formalization Note (moderation).** The infimum runs over policies admissible from $(n,x)$
--   in the sense of the model (measurable, square-integrable terminal wealth).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 121, PDF 135, unnumbered display defining $QP(b)$'s value function

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The value function of `QP(b)` from time `n`, state `x`:
`V_n(x) := inf_π 𝔼[(X_N-b)^2 | X_n = x]` over policies admissible from `(n,x)`
(Bäuerle–Rieder, p. 121, PDF 135). -/
noncomputable def MVMarket.VQP (M : MVMarket Ω d) (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ⨅ π ∈ {π : ℕ → ℝ → (Fin d → ℝ) | M.IsAdmissibleFrom n x π},
    ∫ ω, (M.terminalWealth π (M.N - n) n x ω - b) ^ 2 ∂M.measIP

end MDPFinance.MeanVariance


