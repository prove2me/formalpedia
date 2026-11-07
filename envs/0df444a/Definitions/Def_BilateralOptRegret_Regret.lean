-- Prove2me | Definitions.Def_BilateralOptRegret_Regret
-- name    : BilateralOptRegret_Regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:18.683948+00:00
-- url     : https://prove2.me/theorems/958bd989-49a8-4762-ad82-8645d441e348
-- title:
--   (3) — one-bit policies, i.i.d. draws and the regret $R_T$
-- statement:
--   A **learner** is a policy mapping the past trade bits to the next action. Facing draws $X_0,X_1,\dots$, it plays $x_t=\pi(Y_0,\dots,Y_{t-1})$ and observes only $Y_t=\mathbb 1\{X_t\le x_t\}$. The draws are i.i.d. with law $L$. The **regret** is display (3):
--   $$R_T=T\sup_{x\in[0,1]^2}r(x)-\mathbb E\Big[\sum_{t=1}^T r(x_t)\Big].$$
--   This is the performance measure of the mission's main theorem. The benchmark ranges over all of $[0,1]^2$, not only the grid.
--
--   **Formalization Note** The policy's signature (`List Bool → ℝ × ℝ`) is what makes the feedback one bit. Rounds are numbered from $0$. The policies here are deterministic, since the paper's algorithm has no internal randomness; the expectation is over the draws.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), §2.1, p.12–13, display (3)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralOptRegret_Model

namespace BilateralOptRegret

open MeasureTheory

/-! # One-bit learners, the i.i.d. run and the regret (3)

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…), §2.1, pp.12–13, display (3).

**Formalization Note.** A learner is a deterministic policy `π : List Bool → ℝ × ℝ` of the past trade
bits, which is what makes the feedback one bit. The paper's algorithm uses no internal randomness, so
the expectation in (3) is only over the draws. `X t` is `X_{t+1}` of the paper (rounds `0, …, T − 1`).
The supremum in (3) is over the nonempty set `[0,1]²`, including `x₁ + x₂ > 1`, where the margin is
negative; `r ∈ [−1, 1]`, so it is finite. The Bochner integral in `regret` is of a bounded
measurable function on a probability space for every `π` with values in `[0,1]²`, under `IsIIDRun`
(checked in the sanity file); every policy in this mission has grid values. `Ω : Type` is an encoding of the underlying probability space. -/

/-- The bits seen before round `t` when the policy `π` faces the draws `X`. -/
noncomputable def hist {Ω : Type} (π : List Bool → ℝ × ℝ) (X : ℕ → Ω → ℝ × ℝ) (ω : Ω) :
    ℕ → List Bool
  | 0 => []
  | t + 1 => by
      classical
      exact hist π X ω t ++ [decide (X t ω ≤ π (hist π X ω t))]

/-- The action `x_t` played at round `t`. -/
noncomputable def act {Ω : Type} (π : List Bool → ℝ × ℝ) (X : ℕ → Ω → ℝ × ℝ) (ω : Ω) (t : ℕ) :
    ℝ × ℝ :=
  π (hist π X ω t)

/-- The draws `X_t` are i.i.d. with law `L` (p.12). -/
def IsIIDRun {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ × ℝ)
    (L : Measure (ℝ × ℝ)) : Prop :=
  (∀ t, Measurable (X t)) ∧ ProbabilityTheory.iIndepFun X P ∧ ∀ t, P.map (X t) = L

/-- The benchmark `sup_{x ∈ [0,1]²} r(x)` of (3), p.13. -/
noncomputable def benchmark (L : Measure (ℝ × ℝ)) : ℝ :=
  ⨆ x : {x : ℝ × ℝ // x ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1}, r L x

/-- The regret (3), p.13: `R_T = T sup_{x ∈ [0,1]²} r(x) − E[∑_{t=1}^T r(x_t)]`. -/
noncomputable def regret {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ × ℝ)
    (L : Measure (ℝ × ℝ)) (π : List Bool → ℝ × ℝ) (T : ℕ) : ℝ :=
  (T : ℝ) * benchmark L - ∫ ω, ∑ t ∈ Finset.range T, r L (act π X ω t) ∂P

end BilateralOptRegret


