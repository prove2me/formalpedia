-- Prove2me | Definitions.Def_BorkarMeynODE_Bounded_SAModel
-- name    : BorkarMeynODE_Bounded_SAModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:47:02.418105+00:00
-- url     : https://prove2.me/theorems/96b62f2f-c541-484d-98a9-25515a4a5fc4
-- title:
--   The stochastic approximation recursion (1.1), assumptions (A1), (A2) and (BS)
-- statement:
--   Fix $d \in \mathbb{N}$, a vector field $h : \mathbb{R}^d \to \mathbb{R}^d$, a deterministic step sequence $\{a(n)\}$, and random sequences $X(n), M(n)$ in $\mathbb{R}^d$ on a probability space $(\Omega, \mathcal F, \mathsf P)$.
--
--   1. **Recursion (1.1).** For every $n \ge 0$ and every sample point,
--   $$X(n+1) = X(n) + a(n)\big[h(X(n)) + M(n+1)\big].$$
--   2. **Assumption (A1).** $h$ is Lipschitz; there is $h_\infty : \mathbb{R}^d \to \mathbb{R}^d$ with $\lim_{r\to\infty} h_r(x) = h_\infty(x)$ for every $x$, where $h_r(x) = r^{-1}h(rx)$; and the origin is an asymptotically stable equilibrium of the fluid ODE (1.5) $\dot x = h_\infty(x)$.
--   3. **Assumption (A2)** with constant $C_0$. Let $\mathcal F_n = \sigma(X(0), \dots, X(n))$. For every $n \ge 0$, $M(n+1)$ is integrable with $\mathsf E\|M(n+1)\|^2 < \infty$, $\mathsf E[M(n+1) \mid \mathcal F_n] = 0$ almost surely, and
--   $$\mathsf E\big[\|M(n+1)\|^2 \mid \mathcal F_n\big] \le C_0\big(1 + \|X(n)\|^2\big) \quad \text{a.s.}$$
--   4. **Assumption (BS)**, bounded stepsizes, with constants $\underline\alpha$, $\bar\alpha$: $0 < \underline\alpha < \bar\alpha < 1$ and $\underline\alpha \le a(n) \le \bar\alpha$ for all $n \ge 0$.
--
--   These are the standing hypotheses of every theorem of the mission. The upper bound $\bar\alpha$ is the parameter in which all the mission's error bounds are stated.
--
--   **Formalization Note** The state space is `EuclideanSpace ℝ (Fin d)`. The paper's filtration is $\sigma(X(i), M(i), i \le n)$; it differs from the natural filtration of $X$ only by $M(0)$, which never enters (1.1), because for $1 \le i \le n$ the noise $M(i)$ is a function of $X(i-1)$ and $X(i)$ ($a(i-1) > 0$). The integrability clauses are needed for the conditional expectations to be meaningful; they follow from the paper's hypotheses for a deterministic $X(0)$. Measurability of $X(n)$ and $M(n)$ is required separately in each theorem.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 447, Eq. (1.1); p. 449, Assumptions (A1), (A2), (BS)

import Mathlib
import Definitions.Def_BorkarMeynODE_Bounded_ODEStability

namespace BorkarMeynODE.Bounded

open MeasureTheory Filter Topology

/-- The stochastic approximation recursion (1.1):
`X(n+1) = X(n) + a(n) [h(X(n)) + M(n+1)]` for every `n ≥ 0` and every sample point. -/
def IsSARecursion {d : ℕ} {Ω : Type*}
    (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a : ℕ → ℝ)
    (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ (n : ℕ) (ω : Ω), X (n + 1) ω = X n ω + a n • (h (X n ω) + M (n + 1) ω)

/-- Assumption (A1): `h` is Lipschitz, the scaled fields `h_r(x) = r⁻¹ h(r x)` converge
pointwise to `h_∞` as `r → ∞`, and the origin is an asymptotically stable equilibrium of the
fluid ODE (1.5) `ẋ = h_∞(x)`. -/
def AssumptionA1 {d : ℕ}
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∃ K, LipschitzWith K h) ∧
    (∀ x, Tendsto (fun r : ℝ => scaledField h r x) atTop (𝓝 (hInf x))) ∧
    IsAsymptoticallyStable hInf 0

/-- Assumption (A2), with respect to the natural filtration `𝓕ₙ = σ(X(0), …, X(n))` of the
iterates. (The paper's `σ(X(i), M(i), i ≤ n)` differs only by `M(0)`, which never enters (1.1):
for `1 ≤ i ≤ n`, `M(i)` is a function of `X(i-1), X(i)` since `a(i-1) > 0`.)
For every `n`: `M(n+1)` is integrable and square integrable, `E[M(n+1) | 𝓕ₙ] = 0`, and
`E[‖M(n+1)‖² | 𝓕ₙ] ≤ C₀ (1 + ‖X(n)‖²)` almost surely. -/
def AssumptionA2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n))
    (C₀ : ℝ) : Prop :=
  ∀ n : ℕ,
    Integrable (M (n + 1)) P ∧
    Integrable (fun ω => ‖M (n + 1) ω‖ ^ 2) P ∧
    P[M (n + 1) | Filtration.natural (β := fun _ => EuclideanSpace ℝ (Fin d)) X hX n]
      =ᵐ[P] 0 ∧
    P[fun ω => ‖M (n + 1) ω‖ ^ 2 |
        Filtration.natural (β := fun _ => EuclideanSpace ℝ (Fin d)) X hX n]
      ≤ᵐ[P] fun ω => C₀ * (1 + ‖X n ω‖ ^ 2)

/-- Assumption (BS), bounded stepsizes: `0 < α̲ < ᾱ < 1` and `α̲ ≤ a(n) ≤ ᾱ` for all `n`.
Here `αlo = α̲` and `αhi = ᾱ`. -/
def BoundedStepsize (αlo αhi : ℝ) (a : ℕ → ℝ) : Prop :=
  0 < αlo ∧ αlo < αhi ∧ αhi < 1 ∧ ∀ n : ℕ, αlo ≤ a n ∧ a n ≤ αhi

end BorkarMeynODE.Bounded


