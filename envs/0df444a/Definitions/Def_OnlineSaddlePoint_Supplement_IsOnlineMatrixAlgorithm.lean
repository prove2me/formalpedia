-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_IsOnlineMatrixAlgorithm
-- name    : OnlineSaddlePoint_Supplement_IsOnlineMatrixAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:53:06.69798+00:00
-- url     : https://prove2.me/theorems/88575a66-e605-4007-85e8-71b8681ff446
-- title:
--   Deterministic non-anticipating algorithm for online matrix games
-- statement:
--   An **algorithm for online matrix games** with $d_1$ and $d_2$ actions is a rule that, for every horizon $T$, every sequence of payoff matrices $A_1,A_2,\dots$ and every round $t=1,\dots,T$, chooses a pair of mixed strategies
--
--   $$
--   (x_t,y_t)\in\Delta_X\times\Delta_Y
--   $$
--
--   that depends on the matrices only through the past ones $A_1,\dots,A_{t-1}$. Formally the rule is a function $\mathrm{play}(T,A,t)=(x_t,y_t)$, and the predicate requires (1) $x_t\in\Delta_X$, $y_t\in\Delta_Y$ for $1\le t\le T$, and (2) $\mathrm{play}(T,A,t)=\mathrm{play}(T,A',t)$ whenever $A_s=A'_s$ for all $1\le s<t$.
--
--   This is the class of algorithms in the impossibility result, Theorem 6.
--
--   **Formalization Note** The rule may depend on the horizon $T$ (the paper assumes $T$ known, §4.1), so both anytime and horizon-dependent algorithms are covered. $\Delta_X$ and $\Delta_Y$ are restricted simplexes with $\theta=0$.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Theorem 6, p.27; §5, p.15

import Mathlib
import Definitions.Def_OnlineSaddlePoint_Supplement_restrictedSimplex

namespace OnlineSaddlePoint.Supplement

/-- **Deterministic online matrix-game algorithm.** Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3,
Theorem 6, p.27: "Consider any algorithm that selects a sequence of `x_t, y_t` pairs given the past
payoff matrices `A₁, ..., A_{t−1}`", with decision sets the probability simplexes `Δ_X`, `Δ_Y` of §5
(p.15). `play T A t = (x_t, y_t)` is the pair the algorithm plays in round `t` of a game with horizon
`T` against the matrix sequence `A`. The predicate says that for every `T` and every round
`t = 1, …, T`:

1. `x_t ∈ Δ_X` and `y_t ∈ Δ_Y`;
2. `(x_t, y_t)` depends on `A` only through `A₁, …, A_{t−1}` (non-anticipation).

**Formalization Note.** The rule may depend on the horizon `T` (the paper assumes `T` known, §4.1),
so it covers both anytime and horizon-dependent algorithms. Strategies are in
`PiLp 1 (fun _ : Fin d => ℝ)`; `Δ_X = restrictedSimplex d₁ 0`, `Δ_Y = restrictedSimplex d₂ 0`.
Values of `play` outside rounds `1, …, T` are unconstrained and never read. -/
def IsOnlineMatrixAlgorithm {d₁ d₂ : ℕ}
    (play : ℕ → (ℕ → Matrix (Fin d₁) (Fin d₂) ℝ) → ℕ →
      PiLp 1 (fun _ : Fin d₁ => ℝ) × PiLp 1 (fun _ : Fin d₂ => ℝ)) : Prop :=
  (∀ (T : ℕ) (A : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ), ∀ t ∈ Finset.Icc 1 T,
      (play T A t).1 ∈ restrictedSimplex d₁ 0 ∧ (play T A t).2 ∈ restrictedSimplex d₂ 0) ∧
    (∀ (T : ℕ) (A A' : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ), ∀ t ∈ Finset.Icc 1 T,
      (∀ s ∈ Finset.Ico 1 t, A s = A' s) → play T A t = play T A' t)

end OnlineSaddlePoint.Supplement


