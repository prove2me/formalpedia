-- Prove2me | Definitions.Def_DynTargetMV_Market_IsEquilibrium
-- name    : DynTargetMV_Market_IsEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:38.27399+00:00
-- url     : https://prove2.me/theorems/dbdf3ab3-3fd3-4d86-906f-e1d05c624d08
-- title:
--   Definition 1 — equilibrium strategy (corrected: $\Pi$ is the time-$t$ self\'s set)
-- statement:
--   A feasible strategy $\hat\pi$ is an equilibrium strategy if for any $t\in[0,T)$, $x\in\mathbb X_t$ and $\pi\in\Pi^{\hat\pi}_{t,x}$ with $\pi\neq\hat\pi(t,x)$, there exists $\varepsilon_0\in(0,T-t)$ such that
--   $$
--   \operatorname{var}_t\bigl(X^{\pi_{t,\varepsilon,\pi}}(T)\bigr)-\operatorname{var}_t\bigl(X^{\hat\pi}(T)\bigr)\ge0,\qquad\forall\varepsilon\in(0,\varepsilon_0].
--   $$
--   The agent at time $t$ therefore cannot lower the variance by any admissible deviation over a short period. This is the regular equilibrium (2.5), a stronger notion than the weak equilibrium (2.6), and it is the first such notion with an expected-value constraint.
--
--   **Formalization Note** Here $\operatorname{var}_t$ is the variance of the solution started at $(t,x)$. The definition also requires that $\hat\pi$ have a unique solution from each reachable $(t,x)$, with square-integrable terminal value.
--
--   Differences from the source:
--   - correction: Π^π̂_{t,x} (p.8) asks that π_{t,ε,π} be feasible in the sense of p.7, with all constraints at all times along the path from x₀ → Π requires Qπ ≥ 0 and, for all small ε, a unique solution from (t,x) with square-integrable strategy and terminal value and E[X(T)] ≥ L(t,x); reason: the printed set makes the uniqueness clauses false: with m = d = 1, r = 0, b = σ = 1, Q = 0, T = 1, x₀ = γ = 1, ψ ≡ 1, the strategy π̃ ≡ e − 1 is an equilibrium of (ii) under the printed Π, and it is not (2.12); and the printed Π can be empty for target (2.7). The corrected set is what (C.10), (C.11), p.26, test
--   - encoding: E_t and var_t, conditional on the information at time t → at (t,x): mean and variance of the solution started at (t,x); along the agent's own path: condExp given F t; reason: p.7: the conditional law of X(T) depends on the wealth at time t only
--   - encoding: Definition 1 takes for granted that var_t(X^π̂(T)) is defined for reachable (t,x) → IsEquilibrium also requires a unique solution of π̂ from each reachable (t,x), with L² terminal value; reason: so that (2.5) is not vacuous; this is automatic for the strategies of Theorem 1, which are affine in wealth with square-integrable coefficients
--   - encoding: 𝕏_t uses the distribution of X^π̂(t) conditional on the information at time 0 → the law of X^π̂(t) under P; reason: the start x₀ is deterministic, and the solution from it does not depend on the time-0 information
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Definition 1, p.8

import Definitions.Def_DynTargetMV_reachableStates
import Definitions.Def_DynTargetMV_Market_Feasible
import Definitions.Def_DynTargetMV_Market_admissibleSpikes

open MeasureTheory ProbabilityTheory Set

namespace DynTargetMV

/-- **Definition 1.** The feasible strategy `π̂` is an **equilibrium strategy** if for any `t ∈ [0,T)`,
`x ∈ 𝕏_t`, and `π ∈ Π^π̂_{t,x}` with `π ≠ π̂(t,x)`, there is `ε₀ ∈ (0,T−t)` such that
`var_t(X^{π_{t,ε,π}}(T)) − var_t(X^π̂(T)) ≥ 0` for all `ε ∈ (0,ε₀]`, (2.5). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Definition 1, p.8.

**Formalization Note** `Π` is the corrected `Market.admissibleSpikes`. `var_t` is the variance of the
terminal value of the solution started at `(t,x)` (p.7, Markov property). So that (2.5) is not vacuous,
the clause `∃ Xh` requires the strategy `π̂` to have a unique solution from each reachable `(t,x)`, with
`L²` terminal value. In (2.5) the solutions are quantified universally: for `ε ≤ ε̄` they exist and are
unique by the definition of `Π`. This is the regular equilibrium of (2.5), not the weak one of (2.6). -/
def Market.IsEquilibrium {m d n : ℕ} (M : Market m d n) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ mΩ) (W : Fin d → ℝ → Ω → ℝ) (L : ℝ → ℝ → ℝ)
    (πh : ℝ → ℝ → Fin m → ℝ) : Prop :=
  M.Feasible P F W L πh ∧
  ∀ X : ℝ → Ω → ℝ, M.IsWealthFrom P F W πh 0 M.x₀ X →
    ∀ t ∈ Ico 0 M.T, ∀ x ∈ reachableStates P (X t),
      (∃ Xh : ℝ → Ω → ℝ, M.IsUniqueWealthFrom P F W πh t x Xh ∧ MemLp (Xh M.T) 2 P) ∧
      ∀ π ∈ M.admissibleSpikes P F W L πh t x, π ≠ πh t x →
        ∃ ε₀ ∈ Ioo 0 (M.T - t), ∀ ε ∈ Ioc 0 ε₀, ∀ Xε Xh : ℝ → Ω → ℝ,
          M.IsWealthFrom P F W (spike t ε (fun _ _ => π) πh) t x Xε →
          M.IsWealthFrom P F W πh t x Xh →
          0 ≤ variance (Xε M.T) P - variance (Xh M.T) P

end DynTargetMV


