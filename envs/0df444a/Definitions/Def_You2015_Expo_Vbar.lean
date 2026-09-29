-- Prove2me | Definitions.Def_You2015_Expo_Vbar
-- name    : You2015_Expo_Vbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:09:56.946663+00:00
-- url     : https://prove2.me/theorems/a677f591-f1e9-4841-ae11-523426687e63
-- title:
--   The auxiliary functional V̄ of (4.7): θ∫_{t−τ}^t ∫_s^t [τ|f + u(x(δ_v))|² + |g|²] dv ds
-- statement:
--   Along a solution $x$ of the controlled system (2.1), with the Markov chain $r$ and sampling times $\delta_v=[v/\tau]\tau$, the paper defines in the proof of Theorem 4.2
--   $$\bar V(\hat x_t,\hat r_t,t)=\theta\int_{t-\tau}^t\int_s^t\Big[\tau\big|f(x(v),r(v),v)+u(x(\delta_v),r(v),v)\big|^2+\big|g(x(v),r(v),v)\big|^2\Big]dv\,ds.\tag{4.7}$$
--   Here $\theta>0$ is a constant (in the paper $\theta=K_3^2/\lambda_1$) and $|g|$ is the trace norm. $\bar V$ is the part of the Lyapunov–Krasovskii functional (3.1) that accounts for the delay $t-\delta_t$; it is a nonnegative random variable for each $t$.
--
--   **Formalization Note** The integrand is nonnegative, so $\bar V$ is defined as a lower Lebesgue integral with values in $[0,\infty]$, and $|g|^2=\sum_k|g_k|^2$ over the columns of $g$. The paper uses (4.7) for $t\ge2\tau$ in (4.11); for $t\ge\tau$ all times $v$ lie in $[0,\infty)$. For $t<\tau$ times $v<0$ are read as time $0$ (Lean's truncation `Real.toNNReal`), a convention the mission's statements never use.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 918, Eq. (4.7) (in the proof of Theorem 4.2)

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Solution

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Expo

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The functional (4.7) along a path, with values in `[0, ∞]`:
`V̄(x̂_t, r̂_t, t) = θ ∫_{t−τ}^t ∫_s^t [τ|f(x(v), r(v), v) + u(x(δ_v), r(v), v)|² + |g(x(v), r(v), v)|²] dv ds`,
where `|g|² = ∑ₖ |g_k|²` is the squared trace norm. The integrand is nonnegative, so the
integrals are lower Lebesgue integrals. Only `t ≥ τ` (so that `[t − τ, t] ⊆ [0, ∞)`) is used;
for `t < τ` the times `v < 0` are read as time `0`. -/
noncomputable def Vbar {P : Measure Ω} {n m N : ℕ} {Γ : Matrix (Fin N) (Fin N) ℝ}
    {r₀ : Fin N} (S : You2015.Shared.HybridSetup P m N Γ r₀)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (τ : ℝ≥0) (θ : ℝ) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal θ * ∫⁻ s in Set.Icc ((t : ℝ) - τ) t, ∫⁻ v in Set.Icc s (t : ℝ),
    ((τ : ℝ≥0∞) * ‖f (x v.toNNReal ω) (S.r v.toNNReal ω) v.toNNReal
        + u (x (You2015.Shared.delta τ v.toNNReal) ω) (S.r v.toNNReal ω) v.toNNReal‖ₑ ^ 2
      + ∑ k, ‖g (x v.toNNReal ω) (S.r v.toNNReal ω) v.toNNReal k‖ₑ ^ 2)

end You2015.Expo


