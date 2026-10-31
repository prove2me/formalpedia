-- Prove2me | Definitions.Def_LearnManip_horizonValue
-- name    : LearnManip_horizonValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:55.473062+00:00
-- url     : https://prove2.me/theorems/50c88bd1-fd37-418c-bab6-b616700ef4b8
-- title:
--   Partial sums of the expected discounted profit
-- statement:
--   The expected discounted profit of a policy over the first $T$ periods,
--   $$J_T(M)=\sum_{n<T}\alpha^n\Bigl(E[\mu_{n+1}]-c_1\eta^nE[q_{n+1}]-\gamma E[\mathrm{KL}_{n+1}]\Bigr),$$
--   where $\mathrm{KL}_{n+1}$ is the relative entropy of the distorted law of $\mu_{n+1}$ from the undistorted one. Each term is the net profit (7) of a period.
--
--   **Formalization Note.** Costs are computed in $[0,\infty]$, so an infinite expected cost makes the period $-\infty$, never free. Each period is a real number minus a nonnegative extended real, so $\infty-\infty$ cannot occur. A zero weight annihilates a $-\infty$ period, the right convention at $\alpha=0$.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (6), p.9, (7), p.10, (8), p.11

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_baseLaw
import Definitions.Def_LearnManip_History
import Definitions.Def_LearnManip_varPath
import Definitions.Def_LearnManip_Policy
import Definitions.Def_LearnManip_pathLaw

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The first `T` terms of the sum in (8), p.11, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04):
`∑_{n<T} αⁿ (E[μ_{n+1}] − c₁ ηⁿ E[q_{n+1}] − γ E[KL_{n+1}])`, with (7) and (6) in each period.

**Formalization Note.** Costs are computed in `ℝ≥0∞` and cast to `EReal`, so an infinite expected
cost makes the period `⊥`, never free, and `⊤ − ⊤` cannot occur: each period is a real minus a
nonnegative extended real. In `EReal`, `0 * ⊥ = 0`, which is the right convention at `α = 0`. In
`ℝ≥0∞`, `0 * ⊤ = 0`, which is right at cost rate `0`. -/
noncomputable def horizonValue (P : Params) {s₀ : ℝ≥0} (M : Policy s₀) (μ₀ : ℝ) (c₁ : ℝ≥0)
    (T : ℕ) : EReal :=
  ∑ n ∈ Finset.range T,
    (((P.α : ℝ) ^ n : ℝ) : EReal) *
      (((∫ ω, ω (n + 1) ∂pathLaw M μ₀ : ℝ) : EReal) -
        (((((c₁ * P.η ^ n : ℝ≥0) : ℝ≥0∞) *
              ∫⁻ ω, (M.q n (History.ofPath n ω) : ℝ≥0∞) ∂pathLaw M μ₀ +
            (P.γ : ℝ≥0∞) *
              ∫⁻ ω, InformationTheory.klDiv (M.K n (History.ofPath n ω))
                (baseLaw (History.last (History.ofPath n ω))
                  (varPath M.q s₀ n (History.ofPath n ω))
                  (M.q n (History.ofPath n ω))) ∂pathLaw M μ₀ : ℝ≥0∞)) : EReal))

end LearnManip


