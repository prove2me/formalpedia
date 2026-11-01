-- Prove2me | Definitions.Def_RobustMultiStop_IsRhoMartingale
-- name    : RobustMultiStop_IsRhoMartingale
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:09.875622+00:00
-- url     : https://prove2.me/theorems/e4b077de-d20d-4be7-b39f-e971890dd1dd
-- title:
--   $\rho$-martingale: $M_t=\rho_t(M_{t+1})$
-- statement:
--   A process $M\in\mathcal H$ is a **$\rho$-martingale** if
--
--   $$M_t=\rho_t(M_{t+1}),\qquad 0\le t<N. \tag{2.1}$$
--
--   The set of $\rho$-martingales with $M_0=0$ is denoted $\mathcal M^\rho_0$. When $\rho_t$ is the conditional expectation these are the ordinary martingales; in Theorem 3.1 they play the role of the penalties in the additive dual.
--
--   **Formalization Note** $\mathcal M^\rho_0$ is written as $M$ being a $\rho$-martingale together with $M_0=0$.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, §2.1, (2.1), p.5

import Mathlib
import Definitions.Def_RobustMultiStop_IsAdapted

open MeasureTheory

namespace RobustMultiStop

/-- A `ρ`-martingale, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A
Pathwise Duality Approach*, arXiv:2006.01802v2, §2.1, (2.1), p.5: a process `M ∈ ℋ` with
`M_t = ρ_t(M_{t+1})`, `0 ≤ t < T`.

**Formalization Note** `N` is the horizon (the paper's `T`); only `M 0, …, M N` are constrained.
The paper's `𝓜^ρ_0` (p.6) is `IsRhoMartingale F N 𝔛 ρ M ∧ M 0 = 0`. -/
def IsRhoMartingale {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ)) (M : ℕ → Ω →ₘ[P] ℝ) : Prop :=
  IsAdapted F N 𝔛 M ∧ ∀ t < N, M t = ρ t (M (t + 1))

end RobustMultiStop


