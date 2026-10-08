-- Prove2me | Definitions.Def_ApproachRegret_Calibration_Algorithms
-- name    : ApproachRegret_Calibration_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:28:32.465985+00:00
-- url     : https://prove2.me/theorems/1234a6ef-74ab-436d-a3e4-76a96c2fcb79
-- title:
--   Algorithm 3 (the halfspace oracle), Algorithm 4 (online gradient descent) and Algorithm 5 (efficient calibration)
-- statement:
--   This file defines the three algorithms of Section 5.2 as relations between inputs and outputs. Fix a positive integer $m$, $\varepsilon=1/m$, and write $\delta_i$ for the point mass on coordinate $i\in\{0,\dots,m\}$.
--
--   1. **Algorithm 3 (the oracle $\theta\mapsto w$).** For $\theta\in\mathbb R^{m+1}$, $w$ is an output of Algorithm 3 when one of the following holds:
--      - $\theta(0)\le0$ and $w=\delta_0$;
--      - $\theta(0)>0$, $\theta(m)\ge0$ and $w=\delta_m$;
--      - $\theta(0)>0$, $\theta(m)<0$, and for some $i<m$ with $\theta(i)>0\ge\theta(i+1)$: if $\theta(i+1)=0$ then $w=\delta_{i+1}$, and otherwise
--      $$w=\frac{\theta(i)^{-1}}{\theta(i)^{-1}-\theta(i+1)^{-1}}\,\delta_i+\frac{-\theta(i+1)^{-1}}{\theta(i)^{-1}-\theta(i+1)^{-1}}\,\delta_{i+1}.$$
--      Any index $i$ found by the binary search is allowed.
--   2. **Algorithm 4 (online gradient descent).** Points $\theta_1,\theta_2,\dots$ form a run of online gradient descent on $\mathcal K$ with step size $\eta$ against loss vectors $g_1,\dots,g_T$ when, for $t=1,\dots,T$, $\theta_{t+1}$ is the Euclidean projection of $\theta_t-\eta g_t$ onto $\mathcal K$.
--   3. **Algorithm 5 (efficient calibration).** Weights $w_1,w_2,\dots$ and points $\theta_1,\theta_2,\dots$ form a run of Algorithm 5 with step size $\eta$ and horizon $T$ against outcomes $y_1,\dots,y_T$ when $\theta_1=0$, $w_1\in\Delta_{m+1}$ is arbitrary, and for $t=1,\dots,T$, with $u_t=u(w_t,y_t)$,
--   $$\theta_{t+1}=\Pi_{B_\infty(1)}\bigl(\theta_t+\eta\,u_t\bigr),\qquad w_{t+1}\text{ is an output of Algorithm 3 on }\theta_{t+1}.$$
--   That is, $\theta$ runs online gradient descent on the cube against the losses $f_t=-u_t$.
--
--   The forecaster of Algorithm 5 predicts $p_t=i_t/m$ with $i_t$ drawn from $w_t$; Theorem 22 bounds its calibration rate.
--
--   **Formalization Note** Algorithm 4 on p. 44 prints the step $\theta'_{t+1}=\theta_t-\eta u_t$. The proof of Theorem 22 runs the learner on the losses $f_t=-u(w_t,y_t)$ (condition 2, p. 42), so the gradient step is $\theta_t+\eta u_t$; the printed sign minimizes the wrong loss, and with it the rate bound fails (checked numerically). The Lean uses $+\eta u_t$. Algorithm 3's header prints "$\mathcal O: w\mapsto\theta$"; it maps $\theta\mapsto w$. The sampling of $p_t$ is not modelled: the run is the deterministic sequence of distributions $w_t$. The projection onto $B_\infty(1)$ is any Euclidean minimizer (it is coordinatewise clipping to $[-1,1]$, as the paper notes on p. 44). Outcomes and iterates are sequences indexed by $\mathbb N$ with rounds $1,\dots,T$; values at index $0$ are never read.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Algorithm 3, p. 43; Algorithms 4 and 5, p. 44

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game

namespace ApproachRegret.Calibration

/-- The outputs of Algorithm 3 (p. 43), the efficient halfspace oracle `θ ↦ w`, for an input
`θ ∈ ℝ^{m+1}` with `‖θ‖∞ ≤ 1` (coordinates `i = 0, …, m`). Since the binary search may return any
index `i` with `θ(i) > 0 ≥ θ(i+1)`, every such index is allowed:
1. if `θ(0) ≤ 0`, then `w = δ₀`;
2. else if `θ(m) ≥ 0`, then `w = δ_m`;
3. else, for some `i < m` with `θ(i) > 0` and `θ(i+1) ≤ 0`: if `θ(i+1) = 0`, then `w = δ_{i+1}`
   (the page's convention `0/∞ = 0`, `∞/∞ = 1`); otherwise
   `w = (θ(i)⁻¹ δᵢ − θ(i+1)⁻¹ δ_{i+1}) / (θ(i)⁻¹ − θ(i+1)⁻¹)`. -/
def IsAlg3Output (m : ℕ) (θ : ApproachRegret.ToOLO.E (m + 1)) (w : Fin (m + 1) → ℝ) : Prop :=
  (θ 0 ≤ 0 ∧ w = Pi.single 0 1) ∨
  (0 < θ 0 ∧ 0 ≤ θ (Fin.last m) ∧ w = Pi.single (Fin.last m) 1) ∨
  (0 < θ 0 ∧ θ (Fin.last m) < 0 ∧
    ∃ i : Fin m, 0 < θ i.castSucc ∧ θ i.succ ≤ 0 ∧
      (θ i.succ = 0 → w = Pi.single i.succ 1) ∧
      (θ i.succ ≠ 0 → w = fun j =>
        ((θ i.castSucc)⁻¹ * (Pi.single i.castSucc (1 : ℝ) : Fin (m + 1) → ℝ) j
            - (θ i.succ)⁻¹ * (Pi.single i.succ (1 : ℝ) : Fin (m + 1) → ℝ) j)
          / ((θ i.castSucc)⁻¹ - (θ i.succ)⁻¹)))

/-- A run of Online Gradient Descent (Algorithm 4, p. 44) on `K` with step size `η` against the
linear losses `θ ↦ ⟨g_t, θ⟩` for rounds `t = 1, …, T`: `θ_{t+1}` is the ℓ₂ projection of the
gradient step `θ_t − η g_t` onto `K`. The starting point `θ₁` is not constrained here. -/
def IsOGDRun {n : ℕ} (K : Set (ApproachRegret.ToOLO.E n)) (η : ℝ) (T : ℕ) (g θ : ℕ → ApproachRegret.ToOLO.E n) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → IsProj K (θ t - η • g t) (θ (t + 1))

/-- A run of Algorithm 5 (p. 44) with `ε = 1/m`, step size `η` and horizon `T` against the
outcomes `y₁, …, y_T`: `θ₁ = 0`, `w₁ ∈ Δ_{m+1}` arbitrary, and for `t = 1, …, T`,
`u_t = u(w_t, y_t)` (game (11)), `θ_{t+1}` is the OGD update of `θ_t` on the cube `B∞(1)` against
the loss vector `f_t = −u_t` (that is, the ℓ₂ projection of `θ_t + η u_t` onto the cube), and
`w_{t+1}` is an output of Algorithm 3 on `θ_{t+1}`. The sampling `p_t = i_t/m`, `i_t ∼ w_t`, does
not enter. -/
def IsAlg5Run (m : ℕ) (η : ℝ) (T : ℕ) (y : ℕ → ℝ) (w : ℕ → Fin (m + 1) → ℝ)
    (θ : ℕ → ApproachRegret.ToOLO.E (m + 1)) : Prop :=
  θ 1 = 0 ∧ w 1 ∈ stdSimplex ℝ (Fin (m + 1)) ∧
  IsOGDRun (cube (m + 1)) η T (fun t => -payoff m (w t) (y t)) θ ∧
  ∀ t, 1 ≤ t → t ≤ T → IsAlg3Output m (θ (t + 1)) (w (t + 1))

end ApproachRegret.Calibration


