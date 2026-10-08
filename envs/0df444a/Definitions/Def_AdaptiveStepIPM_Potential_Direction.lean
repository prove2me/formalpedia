-- Prove2me | Definitions.Def_AdaptiveStepIPM_Potential_Direction
-- name    : AdaptiveStepIPM_Potential_Direction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:17.618785+00:00
-- url     : https://prove2.me/theorems/cb2855ec-3cdc-4094-8c1b-6ba516a7d456
-- title:
--   The Newton direction (2), the line (3), the scaled vectors $p, q$ of (6), $Pq$ and the step bound $\theta_2^-$
-- statement:
--   Let $(x, s)$ satisfy $x, s > 0$, let $\mu = x^Ts/n$, and let $\gamma$ be a constant. A **search direction** $d = (d_x, d_y, d_s)$ is a solution of the system
--   $$
--   S d_x + X d_s = \gamma\mu e - Xs, \qquad A d_x = 0, \qquad A^T d_y + d_s = 0, \tag{2}
--   $$
--   where $X = \mathrm{diag}(x)$, $S = \mathrm{diag}(s)$. Along the direction the iterates are
--   $$
--   x(\theta) := x + \theta d_x, \qquad s(\theta) := s + \theta d_s \qquad (\theta \in \mathbb R). \tag{3}
--   $$
--   The **scaled vectors** of (6) are $p := X^{-1/2}S^{1/2}d_x$ and $q := X^{1/2}S^{-1/2}d_s$, i.e. $p_j = \sqrt{s_j/x_j}\,(d_x)_j$ and $q_j = \sqrt{x_j/s_j}\,(d_s)_j$, and $Pq$ is the vector with components $p_j q_j$ ($P = \mathrm{diag}(p)$); it equals the second-order term $D_x d_s$ of Newton's method. Finally, for $\beta, \gamma \in (0,1)$, Lemma 5 introduces the step bound
--   $$
--   \theta_2^- := \min\Bigl\{1, \frac{\beta\gamma\mu}{\|Pq\|_\infty^-}\Bigr\}.
--   $$
--
--   The step bound $\theta_2^-$ is the step length that the analysis of Algorithms 2 and 3 in the neighbourhood $\mathcal N_\infty^-(\beta)$ guarantees to be admissible.
--
--   **Formalization Note** System (2) is stated as a relation `IsNewtonDirection A γ x s dx dy ds`; the solution need not be unique. `lineStep v d θ` is $v + \theta d$. When $\|Pq\|_\infty^- = 0$ the quotient $\beta\gamma\mu/0$ is read as $+\infty$, so $\theta_2^- := 1$ (Lean's convention $a/0 = 0$ would otherwise give $\theta_2^- = 0$).
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 4, (2), (3), (6), (8); p. 10, Lemma 5 (θ₂⁻)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_Potential_Neighborhood
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

/-!
Mizuno, Todd, Ye, Cornell ORIE TR 944 (1990, rev. 1991), §2 (p. 4) and §4 (Lemma 5, p. 10).

The search direction `d = (d_x, d_y, d_s)` of system (2), the line `x(θ) = x + θd_x`,
`s(θ) = s + θd_s` of (3), the scaled vectors `p = X^{-1/2}S^{1/2}d_x`, `q = X^{1/2}S^{-1/2}d_s`
of (6), the componentwise product `Pq = (p_j q_j)_j`, and the step bound
`θ₂⁻ = min{1, βγμ/‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞}` of Lemma 5.
-/

open Matrix

namespace AdaptiveStepIPM.Potential

/-- `d = (d_x, d_y, d_s)` solves system (2) at `(x, s)` with parameter `γ` (p. 4):
`S d_x + X d_s = γμe − Xs`, `A d_x = 0`, `Aᵀ d_y + d_s = 0`, where `μ = xᵀs/n`. -/
def IsNewtonDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ)
    (x s : Fin n → ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) ∧
  A *ᵥ dx = 0 ∧ Aᵀ *ᵥ dy + ds = 0

/-- The point `v + θ d` on the line (3): `x(θ) = x + θ d_x` and `s(θ) = s + θ d_s`. -/
def lineStep {n : ℕ} (v d : Fin n → ℝ) (θ : ℝ) : Fin n → ℝ :=
  fun j => v j + θ * d j

/-- `p := X^{-0.5} S^{0.5} d_x`, i.e. `p_j = √(s_j/x_j) (d_x)_j` (6). -/
noncomputable def pVec {n : ℕ} (x s dx : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (s j / x j) * dx j

/-- `q := X^{0.5} S^{-0.5} d_s`, i.e. `q_j = √(x_j/s_j) (d_s)_j` (6). -/
noncomputable def qVec {n : ℕ} (x s ds : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (x j / s j) * ds j

/-- `θ₂⁻ := min{1, βγμ/‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞}` (Lemma 5, p. 10), with `μ = xᵀs/n`.
When `‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞ = 0` the quotient is read as `+∞`, so `θ₂⁻ := 1`. -/
noncomputable def theta2Minus {n : ℕ} (β γ : ℝ) (x s dx ds : Fin n → ℝ) : ℝ :=
  if negInfNorm (AdaptiveStepIPM.PredCorr.Pq x s dx ds) = 0 then 1
  else min 1 (β * γ * AdaptiveStepIPM.PredCorr.mu x s / negInfNorm (AdaptiveStepIPM.PredCorr.Pq x s dx ds))

end AdaptiveStepIPM.Potential


