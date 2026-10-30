-- Prove2me | Definitions.Def_GastRestlessLP_Exponential_Rounding
-- name    : GastRestlessLP_Exponential_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:18:39.962867+00:00
-- url     : https://prove2.me/theorems/6e97a00d-7108-49c7-b5e6-bf7c7eed02a6
-- title:
--   Unbiased dependent rounding with the exact binding budget coin
-- statement:
--   A rounding family supplies a finite action distribution at each population size, time, and current labeled state assignment. For $N>0$ and $t<T$, let $y=\pi_t(M(x))$. Its probability weights must be nonnegative and sum to one. Every positive-probability action assignment activates either $\lfloor Ny_{s,1}\rfloor$ or $\lfloor Ny_{s,1}\rfloor+1$ arms in each state, and the expected number in that state is exactly $Ny_{s,1}$. Choosing actions for actual arms makes exceeding the available population impossible; passive counts are the remaining arms.
--
--   The total activated count is supported on $\lfloor\alpha N\rfloor$ and $\lfloor\alpha N\rfloor+1$, with probability $\alpha N-\lfloor\alpha N\rfloor$ at the latter. Thus the residual variables have the required Bernoulli marginals and may be dependent. Every joint law satisfying these operational conditions is allowed; no concentration or reward bound is part of the definition.
--
--   The floor/ceiling sum reads the obvious fractional-total typo on p. 6 according to (2d) and Remark 8, recorded as I2. The class includes nonintegral budgets, such as a single arm activated with probability $1/2$ at $\alpha=1/2$.
-- source:
--   Gast, Gaujal and Yan, arXiv:2106.10067v3 (22 December 2023), https://arxiv.org/abs/2106.10067v3, pp. 5–7 and 14, (2d), §2.3, (6), Remark 8

import Definitions.Def_GastRestlessLP_Exponential_Population
import Definitions.Def_GastRestlessLP_Exponential_Policy

open scoped BigOperators

namespace GastRestlessLP.Exponential

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A family of finite action kernels; N can vary, but the recommendation π does not. -/
abbrev Rounding (S : Type) :=
  (N : ℕ) → ℕ → (Fin N → S) → RawBlending.UB.FinLaw (Fin N → Fin 2)

/-- Operational rounding specification of §2.3 and (2d). The statewise floor is
augmented by a zero-one residual with the correct mean; the total has the exact
floor/ceiling coin law. No independence between residuals is imposed. -/
noncomputable def ValidRounding (M : Model S) (T : ℕ) (π : Policy S)
    (K : Rounding S) : Prop :=
  ∀ N, 0 < N → ∀ t, t < T → ∀ x : Fin N → S,
    let μ := K N t x
    let y := π t (empirical x)
    μ.IsProb ∧
    (∀ a ∈ μ.supp, μ.weight a ≠ 0 →
      (∀ s, count x a s 1 = ⌊(N : ℝ) * y s 1⌋₊ ∨
        count x a s 1 = ⌊(N : ℝ) * y s 1⌋₊ + 1) ∧
      (activeCount a = ⌊M.α * N⌋₊ ∨ activeCount a = ⌊M.α * N⌋₊ + 1)) ∧
    (∀ s, μ.expect (fun a => (count x a s 1 : ℝ)) = (N : ℝ) * y s 1) ∧
    probability μ (fun a => activeCount a = ⌊M.α * N⌋₊ + 1) =
      M.α * N - (⌊M.α * N⌋₊ : ℝ)

end GastRestlessLP.Exponential


