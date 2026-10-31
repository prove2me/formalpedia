-- Prove2me | Definitions.Def_FrechetPrefs_Multiplier
-- name    : FrechetPrefs_Multiplier
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:16.629407+00:00
-- url     : https://prove2.me/theorems/8a3805e3-0d1b-48b0-9c11-e7f616885828
-- title:
--   The multiplier objective (4), the floor class, the threshold (EC.11), and the expansion terms of (8)
-- statement:
--   Fix models $Q_1,\dots,Q_n$, weights $w$, a utility $u$, a barycenter $Q_B$, constants $K_i$ as in Assumption 2, and a multiplier $\theta>0$.
--
--   1. $K_B=\sum_i w_iK_i$.
--   2. The **floor class** at $K$ is the set of measures in $P_2(\mathbb R)$ giving no mass to $(-\infty,K)$. It is the measure form of the admissible quantile class $\mathcal Q_{K^*}$ of the paper.
--   3. The **objective** of problem (4) is
--   $$J_\theta(Q)=\mathbb E_Q[u(X)]+\frac\theta2\big(F_{\mathbb M}(Q)-F_{\mathbb M}(Q_B)\big).$$
--   4. The **multiplier utility** $U_\theta(X)$ is the infimum of $J_\theta$ over the floor class.
--   5. $\psi(x)=\frac1\theta u'(x)+x$, the left side of equation (5) at $\rho=\theta$.
--   6. The **threshold** is $\theta_c=\max\{|u''(K)|,\ u'(K)/(K_B-K)\}$, as in (EC.11).
--   7. The second-order approximation of the quantile is $T_2(\theta,z)=z-\frac1\theta u'(z)+\frac1{\theta^2}u''(z)u'(z)$.
--   8. The effective utility is $V_\theta(x)=u(x)-\frac{(u'(x))^2}{2\theta}+\frac{(u'(x))^2u''(x)}{2\theta^2}$.
--
--   These are the objects in which Theorem 2 is stated.
--
--   **Formalization Note** $K$ is a free floor, the paper's being $K^*=\min_iK_i$. $U_\theta$ is a real infimum; the goal theorem proves it is attained, which is what makes it the printed minimum. $V_\theta$ is multiplied out because the printed form divides by $u(x)$, which can vanish. Measures are not restricted to continuous quantiles.
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), problem (4), p.7; Assumption 2, p.11; K_B, Q_{K*} and ψ, Section EC.2.3, pp.ec5–ec6; (EC.11), p.ec6; (8), p.11

import Mathlib
import Definitions.Def_FrechetPrefs_Wasserstein

open MeasureTheory Set

namespace FrechetPrefs

/-- `K_B = ∑ᵢ wᵢ Kᵢ`, Section EC.2.3, p.ec5 of Petracou–Xepapadeas–Yannacopoulos, manuscript
MS-DEC-19-01009-REV, where the `Kᵢ` are the constants of Assumption 2, p.11. -/
noncomputable def KB {n : ℕ} (w Kv : Fin n → ℝ) : ℝ := ∑ i, w i * Kv i

/-- The floor class: measures in `P₂(ℝ)` carried by `[K, ∞)`. This is the measure form of the
admissible class `Q_{K*} = {g ∈ L²([0,1]) : g (right) continuous increasing, g ≥ K*}`, Section EC.2.3,
p.ec5 of manuscript MS-DEC-19-01009-REV; see also p.11 ("quantile functions which are strictly
bounded below by a positive constant").

**Formalization Note.** `K` is a free floor. The paper's choice is `K = K* = minᵢ Kᵢ`. Measures with
a non-continuous quantile are admitted, whereas p.ec5 restricts to continuous quantiles "for
simplicity". -/
def floorClass (K : ℝ) : Set (ProbabilityMeasure ℝ) :=
  {μ | μ ∈ P2 ∧ (μ : Measure ℝ) (Iio K) = 0}

/-- The functional minimized in problem (4), p.7 of manuscript MS-DEC-19-01009-REV,
`E_Q[u(X)] + (θ/2)(F_M(Q) − F_M(Q_B))`, written on the law `μ = Q` of `X`.

**Formalization Note.** `∫ x, u x ∂μ` is meaningful on `floorClass K` for `K > 0`
(`inada_consequences`); that is the only place this mission evaluates it. -/
noncomputable def objective {n : ℕ} (u : ℝ → ℝ) (w : Fin n → ℝ)
    (Q : Fin n → ProbabilityMeasure ℝ) (B : ProbabilityMeasure ℝ) (θ : ℝ)
    (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, u x ∂(μ : Measure ℝ) + θ / 2 * (frechet w Q μ - frechet w Q B)

/-- The Fréchet–Wasserstein multiplier utility `U_θ(X)` of (4), p.7 of manuscript
MS-DEC-19-01009-REV, with the minimum taken over the floor class of p.ec5.

**Formalization Note.** This is a real `sInf`. It is the printed `min` because the goal theorem
proves that the infimum is attained. -/
noncomputable def multiplierUtility {n : ℕ} (u : ℝ → ℝ) (w : Fin n → ℝ)
    (Q : Fin n → ProbabilityMeasure ℝ) (B : ProbabilityMeasure ℝ) (θ K : ℝ) : ℝ :=
  sInf (objective u w Q B θ '' floorClass K)

/-- The function `ψ(x) = (1/θ) u′(x) + x` of p.ec6 of manuscript MS-DEC-19-01009-REV, the left side of
eq. (5), p.9, at `ρ = θ`. -/
noncomputable def psi (u : ℝ → ℝ) (θ x : ℝ) : ℝ := 1 / θ * deriv u x + x

/-- The critical multiplier (EC.11), p.ec6 of manuscript MS-DEC-19-01009-REV,
`θ_c = max {|u″(K*)|, u′(K*) / (K_B − K*)}`, written for a floor `K` in place of `K*`. -/
noncomputable def thetaC (u : ℝ → ℝ) (K KBv : ℝ) : ℝ :=
  max |deriv (deriv u) K| (deriv u K / (KBv - K))

/-- The second-order approximation of `F_θ⁻¹` in (8), p.11 of manuscript MS-DEC-19-01009-REV:
`z − (1/θ) u′(z) + (1/θ²) u″(z) u′(z)`, evaluated at `z = F_B⁻¹(s)`. -/
noncomputable def T2 (u : ℝ → ℝ) (θ z : ℝ) : ℝ :=
  z - 1 / θ * deriv u z + 1 / θ ^ 2 * (deriv (deriv u) z * deriv u z)

/-- The function `V_θ` of (8), p.11 of manuscript MS-DEC-19-01009-REV, without its `O(1/θ³)` term:
`u(x) − (u′(x))²/(2θ) + (u′(x))² u″(x)/(2θ²)`.

**Formalization Note.** The printed form is `u(x)(1 − (1/2θ)(u′)²/u + (1/2θ²)(u′)²u″/u)`. Multiplying it
out avoids the division by `u(x)`, which can vanish (`u = log` at `x = 1`). -/
noncomputable def effectiveUtility (u : ℝ → ℝ) (θ x : ℝ) : ℝ :=
  u x - (deriv u x) ^ 2 / (2 * θ) + (deriv u x) ^ 2 * deriv (deriv u) x / (2 * θ ^ 2)

end FrechetPrefs


